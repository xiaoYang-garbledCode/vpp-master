/*
 * Copyright (c) 2015 Cisco and/or its affiliates.
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at:
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include <vnet/vnet.h>
#include <vppinfra/vec.h>
#include <vppinfra/error.h>
#include <vppinfra/format.h>
#include <vppinfra/xxhash.h>

#include <vnet/ethernet/ethernet.h>
#include <dpdk/buffer.h>
#include <dpdk/device/dpdk.h>
#include <vnet/classify/vnet_classify.h>
#include <vnet/mpls/packet.h>
#include <vnet/devices/devices.h>
#include <vnet/interface/rx_queue_funcs.h>
#include <vnet/feature/feature.h>
#include <vnet/tcp/tcp_packet.h>

#include <dpdk/device/dpdk_priv.h>

static char *dpdk_error_strings[] = {
#define _(n,s) s,
  foreach_dpdk_error
#undef _
};

/* make sure all flags we need are stored in lower 32 bits */
STATIC_ASSERT ((u64) (RTE_MBUF_F_RX_IP_CKSUM_BAD | RTE_MBUF_F_RX_L4_CKSUM_BAD |
		      RTE_MBUF_F_RX_FDIR | RTE_MBUF_F_RX_LRO) < (1ULL << 32),
	       "dpdk flags not in lower word, fix needed");

STATIC_ASSERT (RTE_MBUF_F_RX_L4_CKSUM_BAD == (1ULL << 3),
	       "bit number of RTE_MBUF_F_RX_L4_CKSUM_BAD is no longer 3!");

// 处理 DPDK 的多段数据包，并将其转换为 VLIB 的缓冲区结构链。
static_always_inline uword
dpdk_process_subseq_segs (vlib_main_t * vm, vlib_buffer_t * b,
			  struct rte_mbuf *mb, vlib_buffer_t * bt)
{
  u8 nb_seg = 1;
  struct rte_mbuf *mb_seg = 0;
  vlib_buffer_t *b_seg, *b_chain = 0;
  mb_seg = mb->next;
  b_chain = b;

  if (mb->nb_segs < 2)
    return 0;

  b->flags |= VLIB_BUFFER_TOTAL_LENGTH_VALID;
  b->total_length_not_including_first_buffer = 0;

  while (nb_seg < mb->nb_segs)
    {
      ASSERT (mb_seg != 0);

      b_seg = vlib_buffer_from_rte_mbuf (mb_seg);
      vlib_buffer_copy_template (b_seg, bt);

      /*
       * The driver (e.g. virtio) may not put the packet data at the start
       * of the segment, so don't assume b_seg->current_data == 0 is correct.
       */
      b_seg->current_data =
	(mb_seg->buf_addr + mb_seg->data_off) - (void *) b_seg->data;

      b_seg->current_length = mb_seg->data_len;
      b->total_length_not_including_first_buffer += mb_seg->data_len;

      b_chain->flags |= VLIB_BUFFER_NEXT_PRESENT;
      b_chain->next_buffer = vlib_get_buffer_index (vm, b_seg);

      b_chain = b_seg;
      mb_seg = mb_seg->next;
      nb_seg++;
    }
  return b->total_length_not_including_first_buffer;
}

static_always_inline void
dpdk_prefetch_mbuf_x4 (struct rte_mbuf *mb[])
{
  clib_prefetch_load (mb[0]);
  clib_prefetch_load (mb[1]);
  clib_prefetch_load (mb[2]);
  clib_prefetch_load (mb[3]);
}

static_always_inline void
dpdk_prefetch_buffer_x4 (struct rte_mbuf *mb[])
{
  vlib_buffer_t *b;
  b = vlib_buffer_from_rte_mbuf (mb[0]);
  clib_prefetch_store (b);
  b = vlib_buffer_from_rte_mbuf (mb[1]);
  clib_prefetch_store (b);
  b = vlib_buffer_from_rte_mbuf (mb[2]);
  clib_prefetch_store (b);
  b = vlib_buffer_from_rte_mbuf (mb[3]);
  clib_prefetch_store (b);
}

/** \brief Main DPDK input node
    @node dpdk-input

    This is the main DPDK input node: across each assigned interface,
    call rte_eth_rx_burst(...) or similar to obtain a vector of
    packets to process. Derive @c vlib_buffer_t metadata from
    <code>struct rte_mbuf</code> metadata,
    Depending on the resulting metadata: adjust <code>b->current_data,
    b->current_length </code> and dispatch directly to
    ip4-input-no-checksum, or ip6-input. Trace the packet if required.

    @param vm   vlib_main_t corresponding to the current thread
    @param node vlib_node_runtime_t
    @param f    vlib_frame_t input-node, not used.

    @par Graph mechanics: buffer metadata, next index usage

    @em Uses:
    - <code>struct rte_mbuf mb->ol_flags</code>
	- RTE_MBUF_F_RX_IP_CKSUM_BAD

    @em Sets:
    - <code>b->error</code> if the packet is to be dropped immediately
    - <code>b->current_data, b->current_length</code>
	- adjusted as needed to skip the L2 header in  direct-dispatch cases
    - <code>vnet_buffer(b)->sw_if_index[VLIB_RX]</code>
	- rx interface sw_if_index
    - <code>vnet_buffer(b)->sw_if_index[VLIB_TX] = ~0</code>
	- required by ipX-lookup
    - <code>b->flags</code>
	- to indicate multi-segment pkts (VLIB_BUFFER_NEXT_PRESENT), etc.

    <em>Next Nodes:</em>
    - Static arcs to: error-drop, ethernet-input,
      ip4-input-no-checksum, ip6-input, mpls-input
    - per-interface redirection, controlled by
      <code>xd->per_interface_next_index</code>
*/

static_always_inline u32
dpdk_ol_flags_extract (struct rte_mbuf **mb, u32 *flags, int count)
{
  u32 rv = 0;
  int i;
  for (i = 0; i < count; i++)
    {
      /* all flags we are interested in are in lower 8 bits but
         that might change */
      flags[i] = (u32) mb[i]->ol_flags;
      rv |= flags[i];
    }
  return rv;
}
/*
  rte_mbuf 允许直接与硬件进行交互，支持快速数据包接收和发送，而 VLIB 的结构并未针对直接硬件访问进行优化。

  处理接收到的网络数据包，将其从 DPDK 的 rte_mbuf 结构转换为 VLIB 的 vlib_buffer_t 结构，
  同时复制模板数据并提取包的标志和长度。函数通过循环批量处理数据包以提高效率，并在可能的情况下处理分段包。
  最终，它返回处理的字节数，并将提取的标志存储在 or_flagsp 指向的变量中。
*/
static_always_inline uword
dpdk_process_rx_burst (vlib_main_t *vm, dpdk_per_thread_data_t *ptd,
		       uword n_rx_packets, int maybe_multiseg, u32 *or_flagsp)
{
  // 初始化 n_left 为接收到的包数量，表示剩余待处理的包。
  u32 n_left = n_rx_packets;
  // 定义一个指针数组 b，用于存储最多四个 VLIB 缓冲区的指针。
  vlib_buffer_t *b[4];
  // 从 ptd 中获取 DPDK 接收到的 rte_mbuf 指针数组，指向当前线程的接收缓冲区。
  struct rte_mbuf **mb = ptd->mbufs;
  // 初始化 n_bytes 为 0，用于累计成功处理的字节数。
  uword n_bytes = 0;
  // 声明一个指向标志的指针 flags，并初始化 or_flags 为 0，用于后续提取的标志信息。
  u32 *flags, or_flags = 0;
  // 定义一个 VLIB 缓冲区结构 bt，用于存储缓冲区模板。
  vlib_buffer_t bt;
  // 重新赋值 mb 和 flags，确保它们指向当前线程的数据。
  mb = ptd->mbufs;
  flags = ptd->flags;

  /* copy template into local variable - will save per packet load */
  vlib_buffer_copy_template (&bt, &ptd->buffer_template);
  while (n_left >= 8)
    {
      // 使用预取指令预加载下一个四个包，以提高缓存命中率和处理效率。
      dpdk_prefetch_buffer_x4 (mb + 4);
      // 将当前的 DPDK rte_mbuf 转换为 VLIB 缓冲区，存储在数组 b 中。
      b[0] = vlib_buffer_from_rte_mbuf (mb[0]);
      b[1] = vlib_buffer_from_rte_mbuf (mb[1]);
      b[2] = vlib_buffer_from_rte_mbuf (mb[2]);
      b[3] = vlib_buffer_from_rte_mbuf (mb[3]);
      // 为每个 VLIB 缓冲区复制模板数据，初始化各个缓冲区。
      vlib_buffer_copy_template (b[0], &bt);
      vlib_buffer_copy_template (b[1], &bt);
      vlib_buffer_copy_template (b[2], &bt);
      vlib_buffer_copy_template (b[3], &bt);
      // 预取下一个四个 DPDK 数据包以提高处理效率。
      dpdk_prefetch_mbuf_x4 (mb + 4);
      // 从当前处理的四个包中提取标志，并将其合并到 or_flags 中，更新 flags 指针。
      or_flags |= dpdk_ol_flags_extract (mb, flags, 4);
      flags += 4;
      // 设置第一个缓冲区的 current_data 为数据偏移量，减去头部空间。
      b[0]->current_data = mb[0]->data_off - RTE_PKTMBUF_HEADROOM;
      // 更新第一个缓冲区的长度，并累计到 n_bytes 中。
      // 重复以上步骤（设置 current_data 和 current_length）对 b[1]、b[2] 和 b[3] 进行相同的处理。
      n_bytes += b[0]->current_length = mb[0]->data_len;

      b[1]->current_data = mb[1]->data_off - RTE_PKTMBUF_HEADROOM;
      n_bytes += b[1]->current_length = mb[1]->data_len;

      b[2]->current_data = mb[2]->data_off - RTE_PKTMBUF_HEADROOM;
      n_bytes += b[2]->current_length = mb[2]->data_len;

      b[3]->current_data = mb[3]->data_off - RTE_PKTMBUF_HEADROOM;
      n_bytes += b[3]->current_length = mb[3]->data_len;
      // 检查 maybe_multiseg 标志，决定是否处理可能的分段数据包。
      if (maybe_multiseg)
	{
    // 调用处理函数来处理第一个缓冲区的分段数据，并将返回的字节数累计到 n_bytes。
	  n_bytes += dpdk_process_subseq_segs (vm, b[0], mb[0], &bt);
	  n_bytes += dpdk_process_subseq_segs (vm, b[1], mb[1], &bt);
	  n_bytes += dpdk_process_subseq_segs (vm, b[2], mb[2], &bt);
	  n_bytes += dpdk_process_subseq_segs (vm, b[3], mb[3], &bt);
	}
    // 更新指针 mb，指向下一个四个包，同时减少待处理包的数量。
      /* next */
      mb += 4;
      n_left -= 4;
    }
  // 当还有包待处理时，进入一个循环，处理剩余不满四个的包。
  while (n_left)
    {
      // 转换当前的 DPDK 包为 VLIB 缓冲区。
      b[0] = vlib_buffer_from_rte_mbuf (mb[0]);
      // 复制模板数据到当前缓冲区。
      vlib_buffer_copy_template (b[0], &bt);
      // 从当前包中提取标志并更新 or_flags，同时更新 flags 指针。
      or_flags |= dpdk_ol_flags_extract (mb, flags, 1);
      flags += 1;
      // 设置当前缓冲区的 current_data。
      b[0]->current_data = mb[0]->data_off - RTE_PKTMBUF_HEADROOM;
      // 更新当前缓冲区的长度，并累计到 n_bytes。
      n_bytes += b[0]->current_length = mb[0]->data_len;
      // 决定是否处理分段包。
      if (maybe_multiseg)
      // 如果需要，处理当前包的分段数据并累计字节数。
	n_bytes += dpdk_process_subseq_segs (vm, b[0], mb[0], &bt);
      // 更新指针 mb，指向下一个包，并减少待处理包的数量。
      /* next */
      mb += 1;
      n_left -= 1;
    }
  // 将提取到的标志存储在指针 or_flagsp 指向的变量中。
  *or_flagsp = or_flags;
  // 返回处理的总字节数 n_bytes，表示成功处理的数据量。
  return n_bytes;
}

static_always_inline void
dpdk_process_flow_offload (dpdk_device_t * xd, dpdk_per_thread_data_t * ptd,
			   uword n_rx_packets)
{
  uword n;
  dpdk_flow_lookup_entry_t *fle;
  vlib_buffer_t *b0;

  /* TODO prefetch and quad-loop */
  for (n = 0; n < n_rx_packets; n++)
    {
      if ((ptd->flags[n] & RTE_MBUF_F_RX_FDIR_ID) == 0)
	continue;

      fle = pool_elt_at_index (xd->flow_lookup_entries,
			       ptd->mbufs[n]->hash.fdir.hi);

      if (fle->next_index != (u16) ~ 0)
	ptd->next[n] = fle->next_index;

      if (fle->flow_id != ~0)
	{
	  b0 = vlib_buffer_from_rte_mbuf (ptd->mbufs[n]);
	  b0->flow_id = fle->flow_id;
	}

      if (fle->buffer_advance != ~0)
	{
	  b0 = vlib_buffer_from_rte_mbuf (ptd->mbufs[n]);
	  vlib_buffer_advance (b0, fle->buffer_advance);
	}
    }
}

static_always_inline u16
dpdk_lro_find_l4_hdr_sz (vlib_buffer_t *b)
{
  u16 l4_hdr_sz = 0;
  u16 current_offset = 0;
  ethernet_header_t *e;
  tcp_header_t *tcp;
  u8 *data = vlib_buffer_get_current (b);
  u16 ethertype;
  e = (void *) data;
  current_offset += sizeof (e[0]);
  ethertype = clib_net_to_host_u16 (e->type);
  if (ethernet_frame_is_tagged (ethertype))
    {
      ethernet_vlan_header_t *vlan = (ethernet_vlan_header_t *) (e + 1);
      ethertype = clib_net_to_host_u16 (vlan->type);
      current_offset += sizeof (*vlan);
      if (ethertype == ETHERNET_TYPE_VLAN)
	{
	  vlan++;
	  current_offset += sizeof (*vlan);
	  ethertype = clib_net_to_host_u16 (vlan->type);
	}
    }
  data += current_offset;
  if (ethertype == ETHERNET_TYPE_IP4)
    {
      data += sizeof (ip4_header_t);
      tcp = (void *) data;
      l4_hdr_sz = tcp_header_bytes (tcp);
    }
  else
    {
      /* FIXME: extension headers...*/
      data += sizeof (ip6_header_t);
      tcp = (void *) data;
      l4_hdr_sz = tcp_header_bytes (tcp);
    }
  return l4_hdr_sz;
}

static_always_inline void
dpdk_process_lro_offload (dpdk_device_t *xd, dpdk_per_thread_data_t *ptd,
			  uword n_rx_packets)
{
  uword n;
  vlib_buffer_t *b0;
  for (n = 0; n < n_rx_packets; n++)
    {
      b0 = vlib_buffer_from_rte_mbuf (ptd->mbufs[n]);
      if (ptd->flags[n] & RTE_MBUF_F_RX_LRO)
	{
	  b0->flags |= VNET_BUFFER_F_GSO;
	  vnet_buffer2 (b0)->gso_size = ptd->mbufs[n]->tso_segsz;
	  vnet_buffer2 (b0)->gso_l4_hdr_sz = dpdk_lro_find_l4_hdr_sz (b0);
	}
    }
}

/*
  它处理从特定 DPDK 设备的接收队列（rx_queues）中接收的数据包。
  该函数的目的是从 DPDK 的 PMD (Poll Mode Driver) 获取数据包，将其转换为 VPP 的 vlib_buffer_t 缓冲区，并进行进一步处理。
  vlib_main_t *vm：VPP 的主要上下文。
  dpdk_main_t *dm：全局的 DPDK 相关上下文。
  dpdk_device_t *xd：当前的 DPDK 设备。
  vlib_node_runtime_t *node：当前 VPP 节点的运行时信息。
  u32 thread_index：当前处理线程的索引。
  u16 queue_id：接收队列的 ID。
*/
static_always_inline u32
dpdk_device_input (vlib_main_t * vm, dpdk_main_t * dm, dpdk_device_t * xd,
		   vlib_node_runtime_t * node, u32 thread_index, u16 queue_id)
{
/*
  n_rx_packets：记录接收到的数据包数量，初始值为 0。
  n_rx_bytes：记录接收到的数据包的总字节数。
  rxq：指向设备的接收队列，从 xd->rx_queues 中获取特定队列（通过 queue_id）。
  n_left, n_trace：用于处理剩余数据包的计数器。
  buffers：用于存储接收到的缓冲区 ID。
  next_index：表示下一个处理阶段，初始化为 VNET_DEVICE_INPUT_NEXT_ETHERNET_INPUT，表示以太网输入。
  mb：指向 rte_mbuf 的指针数组，rte_mbuf 是 DPDK 中的基础数据结构，用于存储网络数据包。
  b0：指向 VPP 的 vlib_buffer_t，它是 VPP 中的缓冲区结构。
  next：用于存储下一个处理步骤的索引。
  or_flags：用于存储一些标志位信息。
  n：用于存储接收数据包的数量。
  single_next：一个标志，表示是否所有数据包都应该经过相同的路径。
*/
  uword n_rx_packets = 0, n_rx_bytes;
  // 通过 queue_id 获取对应的 DPDK 设备实例，xd->devices 是一个存储了所有 DPDK 设备的向量。
  dpdk_rx_queue_t *rxq = vec_elt_at_index (xd->rx_queues, queue_id);
  u32 n_left, n_trace;
  u32 *buffers;
  // 下一个节点
  u32 next_index = VNET_DEVICE_INPUT_NEXT_ETHERNET_INPUT;
  struct rte_mbuf **mb;
  vlib_buffer_t *b0;
  u16 *next;
  u32 or_flags;
  u32 n;
  int single_next = 0;
  /*
    ptd：指向当前线程的 DPDK 专用数据，存储在 dm->per_thread_data 中。
    bt：指向线程的 buffer_template，这个模板用于初始化 VPP 缓冲区。
  */
  dpdk_per_thread_data_t *ptd = vec_elt_at_index (dm->per_thread_data,
						  thread_index);
  vlib_buffer_t *bt = &ptd->buffer_template;
  /*
    检查设备的 flags 是否包含 DPDK_DEVICE_FLAG_ADMIN_UP 标志。
    如果设备没有处于 "管理启动" 状态，则返回 0，表示没有接收到任何数据包。
    如果设备没有启用，函数会直接返回 0，跳过接收数据包的处理。
  */
  if ((xd->flags & DPDK_DEVICE_FLAG_ADMIN_UP) == 0)
    return 0;

  /* get up to DPDK_RX_BURST_SZ buffers from PMD */
  while (n_rx_packets < DPDK_RX_BURST_SZ) // 确保接收到的数据包总数不会超过
    {
      // 每次尝试接收最多 32 个数据包（或剩余数量），但不会超过 DPDK_RX_BURST_SZ。
      u32 n_to_rx = clib_min (DPDK_RX_BURST_SZ - n_rx_packets, 32);
      /*
      rte_eth_rx_burst:
        用于从指定的端口（xd->port_id）和接收队列（queue_id）中接收数据包，将数据包存储在 ptd->mbufs 缓冲区中。
        xd->port_id：DPDK 设备的端口 ID。
        queue_id：DPDK 设备的接收队列 ID。
        ptd->mbufs + n_rx_packets：接收数据包的目标缓冲区位置。
        n_to_rx：每次接收的最大数据包数量。
      */
      n = rte_eth_rx_burst (xd->port_id, queue_id, ptd->mbufs + n_rx_packets,
			    n_to_rx);
      // 更新已接收到的数据包总数。
      n_rx_packets += n; 
      // 如果接收的数据包数量小于期望值，表示接收队列中没有更多数据包，跳出循环。
      if (n < n_to_rx)
	break;
    }
  // 如果没有接收到任何数据包，直接返回 0，表示该设备当前没有数据包可供处理。
  if (n_rx_packets == 0)
    return 0;

  /* Update buffer template */
  // 设置缓冲区的 sw_if_index，即源接口索引，来自 DPDK 设备的接口索引 xd->sw_if_index。
  vnet_buffer (bt)->sw_if_index[VLIB_RX] = xd->sw_if_index;
  // 初始化缓冲区的错误状态为 DPDK_ERROR_NONE，表示没有错误。
  bt->error = node->errors[DPDK_ERROR_NONE];
  // 设置缓冲区的标志位，来自设备的 buffer_flags。
  bt->flags = xd->buffer_flags;
  /* as DPDK is allocating empty buffers from mempool provided before interface
     start for each queue, it is safe to store this in the template */
  // 设置缓冲区池的索引，来自接收队列 rxq。
  bt->buffer_pool_index = rxq->buffer_pool_index;
  // 初始化缓冲区的引用计数为 1，表明该缓冲区当前被使用。
  bt->ref_count = 1;
  // 将特性弧索引初始化为 0，表示默认的处理路径。
  vnet_buffer (bt)->feature_arc_index = 0;
  // 初始化配置索引为 0，表示当前的默认配置。
  bt->current_config_index = 0;
  // PREDICT_FALSE 是一个宏，提示编译器当前条件为假（但可能偶尔为真），以帮助优化分支预测。
  /* receive burst of packets from DPDK PMD */
  if (PREDICT_FALSE (xd->per_interface_next_index != ~0))
    // 需要使用该索引作为后续处理路径。
    next_index = xd->per_interface_next_index;

  /* as all packets belong to the same interface feature arc lookup
     can be don once and result stored in the buffer template */
  /*
     这一部分检查是否需要针对特定接口（xd->sw_if_index）进行功能特性查找：
     vnet_device_input_have_features (xd->sw_if_index)：
            判断设备接口是否启用了某些特性（如 checksum offload、流分类等）。如果启用，则需要启动特性查找。
     vnet_feature_start_device_input：
            如果启用了接口特性查找，函数会启动该查找，并根据特性结果更新 next_index 和缓冲区模板 bt。
     PREDICT_FALSE：表示该条件大多数情况下是假的，目的是帮助优化分支预测。
  */
  if (PREDICT_FALSE (vnet_device_input_have_features (xd->sw_if_index)))
    vnet_feature_start_device_input (xd->sw_if_index, &next_index, bt);
  /*
     xd->flags & DPDK_DEVICE_FLAG_MAYBE_MULTISEG：
            检查设备标志是否设置了 DPDK_DEVICE_FLAG_MAYBE_MULTISEG，表示可能接收到多段数据包。
     dpdk_process_rx_burst (vm, ptd, n_rx_packets, 1, &or_flags)：
            处理接收到的网络数据包，将其从 DPDK 的 rte_mbuf 结构转换为 VLIB 的 vlib_buffer_t 结构，
    同时复制模板数据并提取包的标志和长度。
            如果接收到多段数据包，调用 dpdk_process_rx_burst 进行处理，并将 1 传递给函数，表示处理多段数据包。
     如果数据包不是多段，则传递 0，处理普通数据包。
  */
  if (xd->flags & DPDK_DEVICE_FLAG_MAYBE_MULTISEG)
    n_rx_bytes = dpdk_process_rx_burst (vm, ptd, n_rx_packets, 1, &or_flags);
  else
    n_rx_bytes = dpdk_process_rx_burst (vm, ptd, n_rx_packets, 0, &or_flags);
  /*
      这部分代码处理大接收卸载 (LRO, Large Receive Offload) 功能：
      or_flags & RTE_MBUF_F_RX_LRO：
            检查 or_flags 是否包含 RTE_MBUF_F_RX_LRO 标志，表示该数据包是一个经过 LRO 处理的大数据包。
      dpdk_process_lro_offload：如果存在 LRO 数据包，则调用此函数进行处理。
  */
  if (PREDICT_FALSE ((or_flags & RTE_MBUF_F_RX_LRO)))
    dpdk_process_lro_offload (xd, ptd, n_rx_packets);
  /*
    这里检查数据包是否存在 L4 (传输层) 校验和错误：
    or_flags & RTE_MBUF_F_RX_L4_CKSUM_BAD：检查 or_flags 是否包含
    RTE_MBUF_F_RX_L4_CKSUM_BAD 标志，表示某些接收的数据包存在 L4 校验和错误。
    xd->buffer_flags & VNET_BUFFER_F_L4_CHECKSUM_CORRECT：检查设备是否标记了该缓冲区的校验和为正确。
    如果两者都为真，则进入循环，遍历所有接收的数据包，进行进一步处理。
    b0 = vlib_buffer_from_rte_mbuf (ptd->mbufs[n])：
          将接收到的 DPDK mbuf 转换为 VPP 的 vlib_buffer 结构，以便后续操作。
    b0->flags ^= (ptd->flags[n] & RTE_MBUF_F_RX_L4_CKSUM_BAD)
		       << (VNET_BUFFER_F_LOG2_L4_CHECKSUM_CORRECT - 3):
          如果检测到 L4 校验和错误，重置 VNET_BUFFER_F_L4_CHECKSUM_CORRECT 标志，确保该缓冲区正确反映数据包的校验和状态。
  */
  if (PREDICT_FALSE ((or_flags & RTE_MBUF_F_RX_L4_CKSUM_BAD) &&
		     (xd->buffer_flags & VNET_BUFFER_F_L4_CHECKSUM_CORRECT)))
    {
      for (n = 0; n < n_rx_packets; n++)
	{
	  /* Check and reset VNET_BUFFER_F_L4_CHECKSUM_CORRECT flag
	     if RTE_MBUF_F_RX_L4_CKSUM_BAD is set.
	     The magic num 3 is the bit number of RTE_MBUF_F_RX_L4_CKSUM_BAD
	     which is defined in DPDK.
	     Have made a STATIC_ASSERT in this file to ensure this.
	   */
	  b0 = vlib_buffer_from_rte_mbuf (ptd->mbufs[n]);
    // 如果检测到 L4 校验和错误，重置 VNET_BUFFER_F_L4_CHECKSUM_CORRECT 标志，确保该缓冲区正确反映数据包的校验和状态。
	  b0->flags ^= (ptd->flags[n] & RTE_MBUF_F_RX_L4_CKSUM_BAD)
		       << (VNET_BUFFER_F_LOG2_L4_CHECKSUM_CORRECT - 3);
	}
    }
  /*
    这段代码的作用是处理 DPDK 接收到的 FDIR 数据包，并在启用流量卸载功能时，进一步优化这些数据包的流向。
    最终，它将这些数据包分配给下一个处理节点，以继续处理或转发。
    检查是否启用了 RX_FLOW_OFFLOAD 功能，并且是否有至少一个数据包标记了 FDIR 标志：
        FDIR 是一种硬件加速的流量分类技术，可以帮助将数据包分配给特定的流，并支持流量卸载和高级负载均衡。
    xd->flags & DPDK_DEVICE_FLAG_RX_FLOW_OFFLOAD：
        检查设备标志，确认设备是否启用了接收流量卸载功能。
    or_flags & RTE_MBUF_F_RX_FDIR：
        再次检查是否有数据包被 FDIR 标志标记。
    如果条件为真，调用 dpdk_process_flow_offload 函数处理流量卸载，进一步优化流量转发。
  */
  if (PREDICT_FALSE (or_flags & RTE_MBUF_F_RX_FDIR))
    {
      /* some packets will need to go to different next nodes */
      for (n = 0; n < n_rx_packets; n++)
	ptd->next[n] = next_index;

      /* flow offload - process if rx flow offload enabled and at least one
         packet is marked */
      if (PREDICT_FALSE ((xd->flags & DPDK_DEVICE_FLAG_RX_FLOW_OFFLOAD) &&
			 (or_flags & RTE_MBUF_F_RX_FDIR)))
	dpdk_process_flow_offload (xd, ptd, n_rx_packets);
  /*
    vlib_get_buffer_indices_with_offset：
        将 DPDK 接收的数据包 (ptd->mbufs) 转换为 VPP 的 vlib_buffer 结构，并获取缓冲区的索引。
    sizeof (struct rte_mbuf)：
        指定偏移量，即 rte_mbuf 结构的大小，这样可以准确地处理每个数据包的缓冲区。
    vlib_buffer_enqueue_to_next：
        将数据包缓冲区加入到下一个节点（由 ptd->next 指定）进行进一步处理。
        这里，ptd->next 数组已经在之前被设置为 next_index，所以数据包将被发送到该下游节点。
        n_rx_packets 表示一共接收了多少个数据包。
  */
      /* enqueue buffers to the next node */
      vlib_get_buffer_indices_with_offset (vm, (void **) ptd->mbufs,
					   ptd->buffers, n_rx_packets,
					   sizeof (struct rte_mbuf));

      vlib_buffer_enqueue_to_next (vm, node, ptd->buffers, ptd->next,
				   n_rx_packets);
    }
  /*
  这段代码的作用是将从 DPDK 接收的以太网数据包传递给下一个节点，通常是以太网输入节点。
  如果数据包的校验和正确，则会优化处理路径，避免重复检查 IP 校验和。
    vlib_get_new_next_frame:
        用于从 VPP 的框架系统中获取下一个节点的缓冲区指针 (to_next) 和可用缓冲区数量 (n_left_to_next)。
        next_index 指向下一个节点的索引。
        该函数确保有足够的空间将接收到的数据包传递给下一个节点。
    vlib_get_buffer_indices_with_offset：
        该函数从 ptd->mbufs（接收的 DPDK 数据包）中获取缓冲区，并将其索引存储到 to_next 中。
        sizeof(struct rte_mbuf) 用于确保偏移量正确，以处理 DPDK 数据包缓冲区结构。
  处理以太网输入节点
    PREDICT_TRUE (next_index == VNET_DEVICE_INPUT_NEXT_ETHERNET_INPUT)：
    假设多数情况下数据包将会流向 VNET_DEVICE_INPUT_NEXT_ETHERNET_INPUT 节点，表示将数据包传递到以太网输入节点。
    vlib_node_runtime_get_next_frame (vm, node, next_index)：
        从当前节点获取下一个节点的帧结构，nf 是一个指向下一个帧的指针。
    f = vlib_get_frame (vm, nf->frame)：
        通过 nf->frame 获取帧 f，并设置其标志位 ETH_INPUT_FRAME_F_SINGLE_SW_IF_IDX，表示所有数据包来自同一个软件接口。
    ef = vlib_frame_scalar_args (f)：
        获取帧的参数 ef，设置其 sw_if_index（软件接口索引）和 hw_if_index（硬件接口索引），
        这些参数将告知以太网输入节点数据包的来源接口。   
  */
  else
    {
      u32 *to_next, n_left_to_next;

      vlib_get_new_next_frame (vm, node, next_index, to_next, n_left_to_next);
      vlib_get_buffer_indices_with_offset (vm, (void **) ptd->mbufs, to_next,
					   n_rx_packets,
					   sizeof (struct rte_mbuf));

      if (PREDICT_TRUE (next_index == VNET_DEVICE_INPUT_NEXT_ETHERNET_INPUT))
	{
	  vlib_next_frame_t *nf;
	  vlib_frame_t *f;
	  ethernet_input_frame_t *ef;
    // 获取新的下一帧，填充 to_next 指针和剩余处理数量。
	  nf = vlib_node_runtime_get_next_frame (vm, node, next_index);
	  // 根据下一帧信息获取当前帧。
    f = vlib_get_frame (vm, nf->frame);
    // 设置当前帧的标志，指示它是单个软件接口索引的帧。
	  f->flags = ETH_INPUT_FRAME_F_SINGLE_SW_IF_IDX;
    // 获取当前帧的以太网输入帧参数。
	  ef = vlib_frame_scalar_args (f);
    // 将软件和硬件接口索引设置为上下文中的对应值，以便后续处理使用。
	  ef->sw_if_index = xd->sw_if_index;
	  ef->hw_if_index = xd->hw_if_index;

	  /* if PMD supports ip4 checksum check and there are no packets
	     marked as ip4 checksum bad we can notify ethernet input so it
	     can send pacets to ip4-input-no-checksum node */
    /*
      如果设备支持 IPv4 校验和检查 (DPDK_DEVICE_FLAG_RX_IP4_CKSUM)，
      并且接收的数据包没有 IP 校验和错误 (or_flags & RTE_MBUF_F_RX_IP_CKSUM_BAD == 0)，
      则将帧的标志位设置为 ETH_INPUT_FRAME_F_IP4_CKSUM_OK。
      这意味着以太网输入节点可以将这些数据包直接传递给 ip4-input-no-checksum 节点，
      进一步提高效率，因为不需要再次进行 IP 校验和检查。
    */
	  if (xd->flags & DPDK_DEVICE_FLAG_RX_IP4_CKSUM &&
	      (or_flags & RTE_MBUF_F_RX_IP_CKSUM_BAD) == 0)
	    f->flags |= ETH_INPUT_FRAME_F_IP4_CKSUM_OK;
      /*
        提交帧并更新缓冲区
        vlib_frame_no_append (f)：
              将帧标记为完成，不允许向其中追加更多数据包。
      */
	  vlib_frame_no_append (f);
	}
      /*
        更新剩余缓冲区数量 n_left_to_next，并将下一个节点的帧放回节点池中，表示已经处理完数据包。
        设置 single_next = 1，表示所有数据包都被分发到同一个下游节点。
      */
      n_left_to_next -= n_rx_packets;
      vlib_put_next_frame (vm, node, next_index, n_left_to_next);
      single_next = 1;
    }


  /*
  这段代码负责在启用数据包追踪时记录接收到的 DPDK 数据包。它实现了从接收到的 DPDK 数据包中提取信息，并将其保存为追踪数据。
  vlib_get_trace_count 获取追踪计数:
      从当前节点 (node) 中获取需要追踪的数据包数量 (n_trace)。
      这是为了确保只有在启用追踪时才会执行后续的追踪操作。
      PREDICT_FALSE 用于告诉编译器通常情况下不太可能启用追踪，以便优化代码路径。
  获取缓冲区索引:
      如果所有数据包都将发送到同一个节点 (single_next == 1)，
      则调用 vlib_get_buffer_indices_with_offset 来从 ptd->mbufs 中获取缓冲区的索引，并将这些索引存储到 ptd->buffers。
  */
  /* packet trace if enabled */
  if (PREDICT_FALSE ((n_trace = vlib_get_trace_count (vm, node))))
    {
      if (single_next)
	vlib_get_buffer_indices_with_offset (vm, (void **) ptd->mbufs,
					     ptd->buffers, n_rx_packets,
					     sizeof (struct rte_mbuf));
  /*
  初始化追踪相关变量
    n_left 表示还剩下多少个数据包需要处理。
    buffers 指向接收到的数据包的缓冲区索引数组。
    mb 指向 rte_mbuf（DPDK 数据包）的数组。
    next 指向数据包的下一个节点数组。
  */
      n_left = n_rx_packets;
      buffers = ptd->buffers;
      mb = ptd->mbufs;
      next = ptd->next;
  /*
  循环处理数据包追踪
    在 n_trace 和 n_left 都大于 0 的情况下，进入循环处理每一个数据包的追踪。
    通过 vlib_get_buffer 获取当前数据包的 VPP 缓冲区 (b0)。
    如果 single_next 为 0，意味着不同数据包可能会被转发到不同的节点，因此获取当前数据包的 next_index。
  */
      while (n_trace && n_left)
	{
	  b0 = vlib_get_buffer (vm, buffers[0]);
	  if (single_next == 0)
	    next_index = next[0];
  /*
  记录追踪数据
    vlib_trace_buffer:
        用于判断是否需要记录当前缓冲区的数据包。如果返回 true，则执行追踪。
    vlib_add_trace：
        为当前缓冲区添加追踪信息，t0 是指向追踪数据结构 (dpdk_rx_trace_t) 的指针。
    将数据包的相关信息记录到追踪结构中：
        queue_index 和 device_index 分别是队列索引和设备索引，表明数据包是从哪个接口接收的。
        buffer_index 是当前缓冲区的索引。
    使用 clib_memcpy_fast 将数据包的元数据、缓冲区内容等快速复制到追踪结构中，
    包括：
        mb[0]：DPDK 的 rte_mbuf 结构。
    b0->pre_data：数据包的前置数据。
    t0->data：数据包的实际内容，从 mb[0]->buf_addr + mb[0]->data_off 开始复制。
  */
	  if (PREDICT_TRUE
	      (vlib_trace_buffer
	       (vm, node, next_index, b0, /* follow_chain */ 0)))
	    {

	      dpdk_rx_trace_t *t0 =
		vlib_add_trace (vm, node, b0, sizeof t0[0]);
	      t0->queue_index = queue_id;
	      t0->device_index = xd->device_index;
	      t0->buffer_index = vlib_get_buffer_index (vm, b0);

	      clib_memcpy_fast (&t0->mb, mb[0], sizeof t0->mb);
	      clib_memcpy_fast (&t0->buffer, b0,
				sizeof b0[0] - sizeof b0->pre_data);
	      clib_memcpy_fast (t0->buffer.pre_data, b0->data,
				sizeof t0->buffer.pre_data);
	      clib_memcpy_fast (&t0->data, mb[0]->buf_addr + mb[0]->data_off,
				sizeof t0->data);
	      n_trace--;
	    }
    /*
    更新剩余数据包和追踪计数
      更新剩余数据包数量 (n_left)，并将指针 (buffers, mb, next) 前移，准备处理下一个数据包。
      每记录一个数据包的追踪，n_trace 减 1。
    */ 
	  n_left--;
	  buffers++;
	  mb++;
	  next++;
	}
    /*
    设置追踪计数
      在完成数据包的追踪处理后，调用 vlib_set_trace_count 更新节点的追踪计数，确保追踪状态与处理后的数据包数量一致。
    */
      vlib_set_trace_count (vm, node, n_trace);
    }
    /*
    更新接收统计
      使用 vlib_increment_combined_counter 更新接口的统计信息，尤其是接收的包数和字节数。
      vnet_get_main ()->interface_main.combined_sw_if_counters 是一个全局计数器，负责记录不同接口的统计数据。
      VNET_INTERFACE_COUNTER_RX 表示接收数据的计数器。
      thread_index 是当前线程的索引，xd->sw_if_index 是网络设备的接口索引，
      n_rx_packets 是接收的包数量，n_rx_bytes 是接收到的数据总字节数。
    */
  vlib_increment_combined_counter
    (vnet_get_main ()->interface_main.combined_sw_if_counters
     + VNET_INTERFACE_COUNTER_RX, thread_index, xd->sw_if_index,
     n_rx_packets, n_rx_bytes);
  /*
  更新设备层的包统计
    vnet_device_increment_rx_packets 函数增加当前线程在该设备上接收到的包的计数。
    这是一个更具体的设备层统计，用于进一步跟踪每个设备的包处理情况。
  */
  vnet_device_increment_rx_packets (thread_index, n_rx_packets);
  /*
  返回接收的包数量
    最后，这个函数返回接收并处理的包的数量 n_rx_packets。
  */
  return n_rx_packets;
}
/*
    该函数的作用是遍历当前 CPU 线程负责的所有 DPDK 设备和它们的接收队列，从中读取网络数据包，并返回接收到的数据包总数。
    vlib_main_t * vm    VPP 的主要上下文，它包含了当前线程的信息。
    vlib_node_runtime_t *node   当前节点的运行时信息。
    vlib_frame_t * f    当前节点的帧，表示它要处理的数据包。
*/
VLIB_NODE_FN (dpdk_input_node) (vlib_main_t * vm, vlib_node_runtime_t * node,
				vlib_frame_t * f)
{
  // 指向全局的 dpdk_main 结构体，包含 DPDK 相关的全局信息。
  dpdk_main_t *dm = &dpdk_main;  
  // 指向 DPDK 设备的指针，用于在循环中获取设备实例。
  dpdk_device_t *xd;
  // 记录接收的数据包数量的变量。
  uword n_rx_packets = 0;
  // 指向接收队列轮询向量的指针，用于存储当前 CPU 线程所轮询的设备及其接收队列信息。
  vnet_hw_if_rxq_poll_vector_t *pv;
  // 当前线程的索引，取自 vm->thread_index。
  u32 thread_index = vm->thread_index;

  /*
   * Poll all devices on this cpu for input/interrupts.
   */
  // 该行调用用于获取当前线程要轮询的所有接收队列（即硬件接口 RX 队列）的向量 pv。
  pv = vnet_hw_if_get_rxq_poll_vector (vm, node);
  // 使用 vec_len(pv) 获取 pv 中接收队列的数量，并遍历每一个队列。
  for (int i = 0; i < vec_len (pv); i++)
    {
      // 通过 dev_instance 获取对应的 DPDK 设备实例，dm->devices 是一个存储了所有 DPDK 设备的向量。
      xd = vec_elt_at_index (dm->devices, pv[i].dev_instance);
      /*
        dpdk_device_input()：调用该函数从指定设备的接收队列中读取数据包。
        它的参数包括：
              当前 VPP 上下文 vm；
              全局 DPDK 主结构 dm；
              当前轮询的 DPDK 设备 xd；
              当前节点 node；
              当前线程索引 thread_index；
              当前轮询的队列 ID pv[i].queue_id
      */
      n_rx_packets +=
	dpdk_device_input (vm, dm, xd, node, thread_index, pv[i].queue_id);
    }
  // n_rx_packets：累加从每个设备接收的数据包数量。
  return n_rx_packets;
}

VLIB_REGISTER_NODE (dpdk_input_node) = {
  .type = VLIB_NODE_TYPE_INPUT,
  .name = "dpdk-input",
  .sibling_of = "device-input",
  .flags = VLIB_NODE_FLAG_TRACE_SUPPORTED,

  /* Will be enabled if/when hardware is detected. */
  .state = VLIB_NODE_STATE_DISABLED,

  .format_buffer = format_ethernet_header_with_length,
  .format_trace = format_dpdk_rx_trace,

  .n_errors = DPDK_N_ERROR,
  .error_strings = dpdk_error_strings,
};

/*
 * fd.io coding-style-patch-verification: ON
 *
 * Local Variables:
 * eval: (c-set-style "gnu")
 * End:
 */
