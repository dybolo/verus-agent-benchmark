#![allow(unused_imports)]

use verus_state_machines_macros::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::cell::pcell::*;
use vstd::cell::pcell;
use vstd::arithmetic::power2::pow2;
use vstd::std_specs::bits::u64_leading_zeros;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// Logical identifiers for the various objects, which are based on the hierarchy outlined
// above. Note that the implementation just uses pointers.

verus!{

// Dependencies inlined from verus-mimalloc/types.rs and its direct imports.
pub const INTPTR_SIZE: u64 = 8;
pub const MAX_ALIGN_GUARANTEE: u64 = 8 * 16;
pub const BIN_HUGE: u64 = 73;
pub const BIN_FULL: u64 = BIN_HUGE + 1;
pub const PAGES_DIRECT: usize = 129;
pub const SLICE_SIZE: u64 = 65536;

pub struct ThreadId { pub thread_id: u64 }
pub struct Page;
pub struct PageInner;
pub tracked struct MemChunk;
pub struct SegmentHeaderMain;
pub struct SegmentHeaderMain2;
pub struct SegmentHeader {
    pub main: PCell<SegmentHeaderMain>,
    pub main2: PCell<SegmentHeaderMain2>,
}
pub struct TldPtr { pub tld_id: Ghost<TldId> }
pub struct PageQueue {
    pub first: *mut Page,
    pub last: *mut Page,
    pub block_size: usize,
}
pub struct Heap {
    pub tld_ptr: TldPtr,
    pub pages_free_direct: PCell<[*mut Page; 129]>,
    pub pages: PCell<[PageQueue; 75]>,
    pub page_count: PCell<usize>,
    pub page_retired_min: PCell<usize>,
    pub page_retired_max: PCell<usize>,
    pub page_empty_ptr: *mut Page,
}

pub closed spec fn start_offset(block_size: int) -> int {
    if block_size >= INTPTR_SIZE as int && block_size <= 1024 {
        3 * MAX_ALIGN_GUARANTEE
    } else {
        0
    }
}

pub open spec fn is_segment_ptr(ptr: *mut SegmentHeader, segment_id: SegmentId) -> bool {
    ptr@.provenance == segment_id.provenance
}

pub open spec fn is_heap_ptr(ptr: *mut Heap, heap_id: HeapId) -> bool {
    heap_id.id == ptr.addr() && ptr@.provenance == heap_id.provenance
}

impl SegmentHeader {
    pub open spec fn wf(&self, mim_instance: Mim::Instance, segment_id: SegmentId) -> bool {
        true
    }
}

impl Heap {
    pub open spec fn wf(&self, heap_id: HeapId, tld_id: TldId, mim_instance: InstanceId) -> bool {
        true
    }
}

pub open spec fn pages_free_direct_match(pfd_val: *mut Page, p_val: *mut Page, emp: *mut Page) -> bool {
    (p_val as int == 0 ==> pfd_val as int == emp as int)
    && (p_val as int != 0 ==> pfd_val as int == p_val as int)
}

pub open spec fn pages_free_direct_is_correct(
    pfd: Seq<*mut Page>, pages: Seq<PageQueue>, emp: *mut Page,
) -> bool {
    &&& pfd.len() == PAGES_DIRECT
    &&& pages.len() == BIN_FULL + 1
    &&& (forall |wsize|
      0 <= wsize < pfd.len() ==>
        pages_free_direct_match(
            #[trigger] pfd[wsize],
            pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first,
            emp)
    )
}

pub open spec fn valid_bin_idx(bin_idx: int) -> bool {
    1 <= bin_idx <= BIN_HUGE
}

#[verifier::opaque]
pub open spec fn size_of_bin(bin_idx: int) -> nat
    recommends valid_bin_idx(bin_idx)
{
    if 1 <= bin_idx <= 8 {
       (usize::BITS / 8) as nat * (bin_idx as nat)
    } else if bin_idx == BIN_HUGE {
        8 * (524288 + 1)
    } else {
        let group = (bin_idx - 9) / 4;
        let inner = (bin_idx - 9) % 4;
        ((usize::BITS / 8) * (inner + 5) * pow2((group + 1) as nat)) as nat
    }
}

pub open spec fn smallest_bin_fitting_size(size: int) -> int {
    let bytes_per_word = (usize::BITS / 8) as int;
    let wsize = (size + bytes_per_word - 1) / bytes_per_word;
    if wsize <= 1 { 1 }
    else if wsize <= 8 { wsize }
    else if wsize > 524288 { BIN_HUGE as int }
    else {
        let w = (wsize - 1) as u64;
        let lz = u64_leading_zeros(w);
        let b = (usize::BITS - 1 - lz) as u8;
        let shifted = (w >> (b - 2) as u64) as u8;
        ((b * 4) + (shifted & 0x03)) - 3
    }
}

pub ghost struct HeapId {
    pub id: nat,
    pub provenance: Provenance,
    pub uniq: int,
}

pub ghost struct TldId {
    pub id: nat,
    pub provenance: Provenance,
}

pub ghost struct SegmentId {
    pub id: nat,
    pub provenance: Provenance,
    pub uniq: int,
}

pub ghost struct PageId {
    pub segment_id: SegmentId,
    pub idx: nat,
}

pub ghost struct BlockId {
    pub page_id: PageId,

    // Index of the block within the *page*
    pub idx: nat,

    // Recall that a page may be multiple slices.
    // The `slice_idx` is the index of the *specific* slice that this block is in.
    // (Relative to the segment, so the slice's "offset" is going to be
    // slice_idx - page_id.idx)
    pub slice_idx: nat,

    pub block_size: nat,
}

impl PageId {
    pub open spec fn range_from(&self, lo: int, hi: int) -> Set<PageId> {
        // {page_id | page_id.segment_id == self.segment_id && self.idx + lo <= page_id.idx < self.idx + hi}
        Set::range(self.idx + lo, self.idx + hi).map_by(
            |idx: int| PageId { segment_id: self.segment_id, idx: idx as nat },
            |page_id: PageId| page_id.idx as int,
        )
    }
}

impl BlockId {
    pub open spec fn wf(&self) -> bool {
        self.slice_idx >= self.page_id.idx
    }

    pub open spec fn page_id_for_slice(&self) -> PageId {
        PageId {
            segment_id: self.page_id.segment_id,
            idx: self.slice_idx,
        }
    }

    pub open spec fn get_slice_idx(page_id: PageId, idx: nat, block_size: nat) -> nat {
        (page_id.idx + (start_offset(block_size as int) + idx * block_size) / (SLICE_SIZE as int)) as nat
    }

    pub open spec fn slice_idx_is_right(&self) -> bool {
        self.slice_idx == BlockId::get_slice_idx(self.page_id, self.idx, self.block_size)
    }
}

// States

pub ghost enum DelayState {
    UseDelayedFree,
    Freeing,
    NoDelayedFree,
    NeverDelayedFree
}

impl DelayState {
    pub open spec fn to_int(&self) -> int {
        match self {
            DelayState::UseDelayedFree => 0,
            DelayState::Freeing => 1,
            DelayState::NoDelayedFree => 2,
            DelayState::NeverDelayedFree => 3,
        }
    }
}

/*pub struct PageThreadListState {
    pub delayed: DelayedState,
    pub len: nat,
}*/

pub ghost struct PageState {
    pub offset: int,

    //pub prev: Option<PageId>,
    //pub next: Option<PageId>,

    pub block_size: nat,
    pub num_blocks: nat,

    pub shared_access: PageSharedAccess,
    pub is_enabled: bool,
}

pub ghost struct SegmentState {
    // TODO what do we need here?
    //pub has_extra_slice: bool,

    pub shared_access: SegmentSharedAccess,
    pub is_enabled: bool,
}

pub ghost struct BlockState {
    // Shared access this element can 'guard'
    pub segment_shared_access: SegmentSharedAccess,
    pub page_shared_access: PageSharedAccess,
    pub page_slice_shared_access: PageSharedAccess,

    pub heap_id: Option<HeapId>,
}

/*
pub ghost struct PageQueueIds {
    // TODO are these supposed to be options?
    pub first: Option<PageId>,
    pub last: Option<PageId>,
}
*/

pub ghost struct HeapState {
    // For the doubly-linked list of Pages
    //pub pages: Map<int, PageQueueIds>,
    //pub full_list: PageQueueIds,

    pub shared_access: HeapSharedAccess,
}

pub ghost struct ThreadState {
    pub heap_id: HeapId,
    pub heap: HeapState,

    pub segments: Map<SegmentId, SegmentState>,
    pub pages: Map<PageId, PageState>,
}

pub ghost struct ThreadCheckedState {
    pub pages: Set<PageId>,
}


// Shared States

pub tracked struct SegmentSharedAccess {
    pub points_to: raw_ptr::PointsTo<SegmentHeader>,
}

impl SegmentSharedAccess {
    pub open spec fn wf(&self, segment_id: SegmentId, mim_instance: Mim::Instance) -> bool {
        &&& is_segment_ptr(self.points_to.ptr(), segment_id)
        &&& (match self.points_to.opt_value() {
            MemContents::Init(segment_header) => segment_header.wf(mim_instance, segment_id),
            MemContents::Uninit => false,
        })
    }
}

pub tracked struct SegmentLocalAccess {
    pub mem: MemChunk,
    pub main: pcell::PointsTo<SegmentHeaderMain>,
    pub main2: pcell::PointsTo<SegmentHeaderMain2>,
}

impl SegmentLocalAccess {
    pub open spec fn wf(&self, segment_id: SegmentId, segment_state: SegmentState, mim_instance: Mim::Instance) -> bool {
        &&& segment_state.shared_access.wf(segment_id, mim_instance)
        &&& segment_state.shared_access.points_to.value().main.id() == self.main.id()

        &&& segment_state.shared_access.points_to.value().main2.id() == self.main2.id()

        &&& segment_state.is_enabled
    }
}

//pub struct PageSharedAccess { i: int }
//pub struct PageLocalAccess { i: int }
pub tracked struct PageSharedAccess {
    pub tracked points_to: raw_ptr::PointsTo<Page>,
    pub tracked exposed: raw_ptr::IsExposed,
}

pub tracked struct PageLocalAccess {
    pub tracked count: pcell::PointsTo<u32>,
    pub tracked inner: pcell::PointsTo<PageInner>,
    pub tracked prev: pcell::PointsTo<*mut Page>,
    pub tracked next: pcell::PointsTo<*mut Page>,
}

pub struct HeapSharedAccess {
    pub points_to: raw_ptr::PointsTo<Heap>,
}

pub struct HeapLocalAccess {
    pub pages_free_direct: pcell::PointsTo<[*mut Page; 129]>,
    pub pages: pcell::PointsTo<[PageQueue; 75]>,
    pub page_count: pcell::PointsTo<usize>,
    pub page_retired_min: pcell::PointsTo<usize>,
    pub page_retired_max: pcell::PointsTo<usize>,
}

impl HeapSharedAccess {
    pub open spec fn wf(&self, heap_id: HeapId, tld_id: TldId, mim_instance: InstanceId) -> bool {
        is_heap_ptr(self.points_to.ptr(), heap_id)
          && self.points_to.is_init()
          && self.points_to.value().wf(heap_id, tld_id, mim_instance)
    }

    pub open spec fn wf2(&self, heap_id: HeapId, mim_instance: InstanceId) -> bool {
        self.wf(heap_id, self.points_to.value().tld_ptr.tld_id@,
            mim_instance)
    }
}

impl HeapLocalAccess {
    pub open spec fn wf(&self, heap_id: HeapId, heap_state: HeapState, tld_id: TldId, mim_instance: InstanceId, emp: *mut Page) -> bool {

        self.wf_basic(heap_id, heap_state, tld_id, mim_instance)
          && pages_free_direct_is_correct(
                self.pages_free_direct.value()@,
                self.pages.value()@,
                emp)
          && heap_state.shared_access.points_to.value().page_empty_ptr == emp
    }

    pub open spec fn wf_basic(&self, heap_id: HeapId, heap_state: HeapState, tld_id: TldId, mim_instance: InstanceId) -> bool {
      heap_state.shared_access.wf(heap_id, tld_id, mim_instance)
        && {
            let heap = heap_state.shared_access.points_to.value();
              heap.pages_free_direct.id() == self.pages_free_direct.id()
              && heap.pages.id() == self.pages.id()
              && heap.page_count.id() == self.page_count.id()
              && heap.page_retired_min.id() == self.page_retired_min.id()
              && heap.page_retired_max.id() == self.page_retired_max.id()

              && (forall |i: int| #[trigger] valid_bin_idx(i) ==>
                  self.pages.value()[i].block_size == size_of_bin(i))
              // 0 isn't a valid_bin_idx
              && self.pages.value()[0].block_size == 8
              && self.pages.value()[BIN_FULL as int].block_size ==
                    8 * (524288 + 2) //MEDIUM_OBJ_WSIZE_MAX + 2

              && self.pages_free_direct.value()@.len() == PAGES_DIRECT
              && self.pages.value()@.len() == BIN_FULL + 1
        }
    }
}



// TODO this is currently unused, and I don't remember exactly why I made it.
// Is it going to be necessary when we do more cleanup stuff?
//
// Actor lets us track what a single thread is doing.
// The idea is that when the thread checks the 'thread id' of a page,
// it needs to then be sure that the page will remain valid for the duration
// of the period the thread is accessing it.
// That means we need to prevent the thread from modifying the page state
// while the 'AccessingMySegment' is in progress.

pub ghost enum Actor {
    Idle,
    //AccessingMySegment(SegmentId, SegmentLocalAccess),
    Abandoned,
}

pub ghost enum DelayFreeingActor {
    HeapUnknown,
    Heap(HeapId, HeapSharedAccess, PageSharedAccess),
}

// ThreadId is inlined above.

// PAPER CUT: doing this more than once, no generic finite condition for map,
// having to do the maximum thing
pub open spec fn segment_u_max(s: Set<SegmentId>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let x = s.choose();
        vstd::math::max(segment_u_max(s.remove(x)), x.uniq)
    }
}

proof fn segment_u_max_not_in(s: Set<SegmentId>)
    ensures forall |id: SegmentId| s.contains(id) ==> id.uniq < segment_u_max(s) + 1,
    decreases s.len(),
{
    vstd::set_lib::lemma_set_empty_equivalency_len(s);
    if s.len() == 0 {
        assert(s === Set::empty());
    } else {
        let x = s.choose();
        let t = s.remove(x);
        segment_u_max_not_in(t);
    }
}

pub open spec fn segment_get_unused_uniq_field(s: Set<SegmentId>) -> int {
    segment_u_max(s) + 1
}

pub proof fn lemma_segment_get_unused_uniq_field(s: Set<SegmentId>)
    ensures forall |id: SegmentId| s.contains(id) ==> id.uniq != segment_get_unused_uniq_field(s)
{
    segment_u_max_not_in(s);
}

pub open spec fn heap_u_max(s: Set<HeapId>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let x = s.choose();
        vstd::math::max(heap_u_max(s.remove(x)), x.uniq)
    }
}

proof fn heap_u_max_not_in(s: Set<HeapId>)
    ensures forall |id: HeapId| s.contains(id) ==> id.uniq < heap_u_max(s) + 1,
    decreases s.len(),
{
    vstd::set_lib::lemma_set_empty_equivalency_len(s);
    if s.len() == 0 {
        assert(s === Set::empty());
    } else {
        let x = s.choose();
        let t = s.remove(x);
        heap_u_max_not_in(t);
    }
}

pub open spec fn heap_get_unused_uniq_field(s: Set<HeapId>) -> int {
    heap_u_max(s) + 1
}

pub proof fn lemma_heap_get_unused_uniq_field(s: Set<HeapId>)
    ensures forall |id: HeapId| s.contains(id) ==> id.uniq != heap_get_unused_uniq_field(s)
{
    heap_u_max_not_in(s);
}

pub open spec fn all_thread_ids() -> Set<ThreadId> {
    vstd::contrib::set_build!{ ThreadId { thread_id }: ThreadId | thread_id: u64 }
}

pub open spec fn range_block_ids(lo: nat, hi: nat, page_id: PageId, block_size: nat) -> Set<BlockId> {
    vstd::contrib::set_build!{
        BlockId {
            page_id,
            idx,
            slice_idx: BlockId::get_slice_idx(page_id, idx, block_size),
            block_size,
        }: BlockId |
        idx: nat in lo..hi,
    }
}

}

tokenized_state_machine!{ Mim {
    fields {
        // Thread-local state to each entity

        #[sharding(bool)] pub right_to_set_inst: bool,
        #[sharding(persistent_option)] pub my_inst: Option<InstanceId>,

        /*
        #[sharding(map)] pub heap: Map<HeapId, HeapState>,
        #[sharding(map)] pub tld: Map<ThreadId, ThreadState>,
        #[sharding(map)] pub segment: Map<SegmentId, SegmentState>,
        #[sharding(map)] pub page: Map<PageId, PageState>,
        */
        #[sharding(map)] pub thread_local_state: Map<ThreadId, ThreadState>,
        #[sharding(set)] pub right_to_use_thread: Set<ThreadId>,

        // Blocks that are allocated (these ghost shards are handed to the user
        // to give them the right to 'deallocate')

        #[sharding(map)] pub block: Map<BlockId, BlockState>,

        // Atomics (accessed concurrently)

        #[sharding(map)] pub thread_of_segment: Map<SegmentId, ThreadId>,
        #[sharding(map)] pub delay: Map<PageId, DelayState>,
        #[sharding(map)] pub heap_of_page: Map<PageId, HeapId>,

        // Thread actors

        #[sharding(map)] pub actor: Map<ThreadId, Actor>,
        #[sharding(map)] pub delay_actor: Map<PageId, DelayFreeingActor>,

        // Storage

        #[sharding(storage_map)] pub segment_shared_access: Map<SegmentId, SegmentSharedAccess>,

        #[sharding(storage_map)] pub page_shared_access: Map<PageId, PageSharedAccess>,

        #[sharding(storage_map)] pub heap_shared_access: Map<HeapId, HeapSharedAccess>,

        // PAPER CUT
        // reason - deposit can't be after birds_eye so create_thread_mk_tokens needs to work
        // in two steps
        #[sharding(set)] pub reserved_uniq: Set<HeapId>,

        #[sharding(map)] pub thread_checked_state: Map<ThreadId, ThreadCheckedState>,

        // Extra state that doesn't form tokens but helps writing invariants

        //#[sharding(not_tokenized)] pub thread_segments: Map<ThreadId, Seq<SegmentId>>,

        #[sharding(not_tokenized)] pub heap_to_thread: Map<HeapId, ThreadId>,
    }

    init!{
        initialize() {
            init right_to_set_inst = true;
            init my_inst = Option::None;
            init right_to_use_thread = all_thread_ids();
            init thread_local_state = Map::empty();
            init thread_checked_state = Map::empty();
            init block = Map::empty();
            init thread_of_segment = Map::empty();
            init delay = Map::empty();
            init heap_of_page = Map::empty();
            init actor = Map::empty();
            init delay_actor = Map::empty();
            init segment_shared_access = Map::empty();
            init page_shared_access = Map::empty();
            init heap_shared_access = Map::empty();
            init heap_to_thread = Map::empty();
            init reserved_uniq = Set::empty();
        }
    }

    transition!{
        set_inst(inst: InstanceId) {
            remove right_to_set_inst -= true;
            add my_inst (union)= Some(inst);
        }
    }

    /*transition!{
        alloc_block(block_id: BlockId, thread_id: ThreadId) {
            remove block -= [block_id => let block_state];
            remove thread_local_state -= [thread_id => let tls];

            require(!block_state.allocated);
            require(tls.pages.dom().contains(block_id.page_id));
            let page = tls.pages.index(block_id.page_id);
            require(page.len >= 1);

            assert(page.len >= 1);

            let new_page = PageState {
                len: (page.len - 1) as nat,
                .. page
            };
            let new_tls = ThreadState {
                pages: tls.pages.insert(block_id.page_id, new_page),
                .. tls
            };
            let new_block_state = BlockState {
                allocated: true,
                .. block_state
            };

            add block += [block_id => new_block_state];
            add thread_local_state += [thread_id => new_tls];
        }
    }*/

    /*

    transition!{
        free_block_local(block_id: BlockId) {
            remove block -= [block_id => let block_state];
            remove page -= [block_id.page_id => let page_state];

            require(block_state.allocated);

            let new_block_state = BlockState {
                allocated: false,
                .. block_state
            };
            let new_page_state = PageState { len: page_state.len + 1, .. page_state };

            add block += [block_id => new_block_state];
            add page += [block_id.page_id => new_page_state];
        }
    }*/

    /*transition!{
        free_block_from_other_thread(block_id: BlockId) {
            remove block -= [block_id => let block_state];
            remove page_thread_list_state -= [block_id.page_id => let ptls];

            require(block_state.allocated);
            // TODO need some additional requirement on the 'delay' state

            let new_block_state = BlockState {
                allocated: false,
                .. block_state
            };
            let new_ptls = PageThreadListState { len: ptls.len + 1, .. ptls };

            add block += [block_id => new_block_state];
            add page_thread_list_state += [block_id.page_id => new_ptls];
        }
    }*/

    property!{
        block_on_the_local_thread(thread_id: ThreadId, block_id: BlockId) {
            have thread_of_segment >= [ block_id.page_id.segment_id => let tid ];
            have thread_local_state >= [ thread_id => let ts ];
            have block >= [ block_id => let _ ];
            require tid == thread_id;

            let page_id = block_id.page_id;
            let segment_id = page_id.segment_id;

            assert ts.segments.dom().contains(segment_id);
            assert ts.pages.dom().contains(page_id);
            assert ts.pages[page_id].block_size == block_id.block_size;
            assert ts.pages[page_id].offset == 0;
        }
    }

    //// Actors and accessing stuff

    property!{
        alloc_guards_segment_shared_access(block_id: BlockId) {
            have block >= [ block_id => let block_state ];
            let segment_id = block_id.page_id.segment_id;
            guard segment_shared_access >= [ segment_id => block_state.segment_shared_access ]
            by {
                let page_id = block_id.page_id_for_slice();
                let thread_id = pre.thread_of_segment[block_id.page_id.segment_id];
                assert(pre.thread_local_state[thread_id].pages.dom().contains(page_id));
                assert(pre.thread_local_state[thread_id].segments.dom().contains(segment_id));
                assert(pre.segment_shared_access.dom().contains(segment_id));
            };
        }
    }

    property!{
        alloc_guards_page_slice_shared_access(block_id: BlockId) {
            have block >= [ block_id => let block_state ];
            let page_id = block_id.page_id_for_slice();
            guard page_shared_access >= [ page_id => block_state.page_slice_shared_access ]
                by { assert(pre.page_shared_access.dom().contains(page_id)); };
        }
    }

    property!{
        alloc_guards_page_shared_access(block_id: BlockId) {
            have block >= [ block_id => let block_state ];
            let page_id = block_id.page_id;
            guard page_shared_access >= [ page_id => block_state.page_shared_access ]
                by { assert(pre.page_shared_access.dom().contains(page_id)); };
        }
    }

    transition!{
        actor_make_idle(thread_id: ThreadId) {
            remove actor -= [thread_id => let actor];
            require(actor != Actor::Abandoned);

            add actor += [thread_id => Actor::Idle];
        }
    }

    transition!{
        actor_abandon(thread_id: ThreadId) {
            remove actor -= [thread_id => let _];
            add actor += [thread_id => Actor::Abandoned];
        }
    }

    // Delay states and delay actors

    transition!{
        set_use_delayed_free(page_id: PageId) {
            remove delay -= [ page_id => DelayState::NoDelayedFree ];
            add delay += [ page_id => DelayState::UseDelayedFree ];
        }
    }

    transition!{
        delay_enter_freeing(page_id: PageId, block_id: BlockId) {
            remove delay -= [ page_id => DelayState::UseDelayedFree ];
            add delay += [ page_id => DelayState::Freeing ];
            require block_id.page_id == page_id;
            have block >= [ block_id => let _ ];

            add delay_actor += [ page_id => DelayFreeingActor::HeapUnknown ];
        }
    }

    transition!{
        delay_leave_freeing(page_id: PageId) {
            remove delay -= [ page_id => let prev_state ];
            add delay += [ page_id => DelayState::NoDelayedFree ];

            remove delay_actor -= [ page_id => let _ ];

            // This should follow from the existence of the 'delay_actor'
            assert(prev_state == DelayState::Freeing);
        }
    }

    transition!{
        delay_lookup_heap(block_id: BlockId) {
            have heap_of_page >= [ block_id.page_id => let heap_id ];
            have block >= [ block_id => let block_state ];
            have my_inst >= Some(let inst);

            remove delay_actor -= [ block_id.page_id => let _ ];
            birds_eye let hsa = pre.heap_shared_access.index(heap_id);
            birds_eye let psa = block_state.page_shared_access;
            add delay_actor += [ block_id.page_id => DelayFreeingActor::Heap(heap_id, hsa, psa) ];
            assert(hsa.wf2(heap_id, inst));

            //assert(hsa.wf(heap_id));
        }
    }

    transition!{
        block_set_heap_id(block_id: BlockId) {
            have delay_actor >= [ block_id.page_id => let DelayFreeingActor::Heap(heap_id, _hsa, _psa) ];
            remove block -= [ block_id => let block_state ];
            add block += [ block_id => BlockState { heap_id: Some(heap_id), .. block_state } ];
        }
    }

    property!{
        delay_guards_heap_shared_access(page_id: PageId) {
            have delay_actor >= [ page_id => let DelayFreeingActor::Heap(heap_id, hsa, _psa) ];
            guard heap_shared_access >= [ heap_id => hsa ];
        }
    }

    property!{
        delay_guards_page_shared_access(page_id: PageId) {
            have delay_actor >= [ page_id => let DelayFreeingActor::Heap(heap_id, _hsa, psa) ];
            guard page_shared_access >= [ page_id => psa ]
                by { assert(pre.page_shared_access.dom().contains(page_id)); };
        }
    }

    property!{
        thread_local_state_guards_page(thread_id: ThreadId, page_id: PageId) {
          have thread_local_state >= [ thread_id => let thread_state ];
          require(thread_state.pages.dom().contains(page_id));
          require(thread_state.pages[page_id].is_enabled);
          guard page_shared_access >= [ page_id =>
              thread_state.pages.index(page_id).shared_access ]

                by { assert(pre.page_shared_access.dom().contains(page_id)); };
        }
    }

    property!{
        thread_local_state_guards_heap(thread_id: ThreadId) {
          have thread_local_state >= [ thread_id => let thread_state ];
          guard heap_shared_access >= [ thread_state.heap_id =>
              thread_state.heap.shared_access ];
        }
    }

    property!{
        thread_local_state_guards_segment(thread_id: ThreadId, segment_id: SegmentId) {
            have thread_local_state >= [ thread_id => let thread_state ];
            require(thread_state.segments.dom().contains(segment_id));
            require(thread_state.segments[segment_id].is_enabled);
            guard segment_shared_access >= [ segment_id =>
                thread_state.segments.index(segment_id).shared_access ]
            /*by {
                assert(thread_state.segments.dom().contains(segment_id));
                assert(pre.segment_shared_access.dom().contains(segment_id));
            };*/
                by { assert(pre.segment_shared_access.dom().contains(segment_id)); };
        }
    }

    // Setting up a page

    /*pub open spec fn block_map_on_create_page(page_id: PageId, n_blocks: nat, block_size: nat)
        Map::new(
            |block_id: BlockId|
                block_id.page_id == page_id
                  && 0 <= block_id.idx < n_blocks
                  && block_id.block_size == block_size
                  && block_id.slice_idx_is_right(),
            |block_id: BlockId|
              BlockState {
                  segment_shared_access: ssa,
                  page_shared_access: psa_map[page_id],
                  page_slice_shared_access: psa_map[PageId {
                      segment_id: page_id.segment_id,
                      idx: block_id.slice_idx,
                  }]
              }
        );
    }*/

    transition!{
        reserve_uniq_identifier() {
            birds_eye let u = heap_get_unused_uniq_field(pre.heap_shared_access.dom() + pre.reserved_uniq);
            add reserved_uniq += set { HeapId { id: 0, uniq: u, provenance: Provenance::null() } }
            by {
                lemma_heap_get_unused_uniq_field(pre.heap_shared_access.dom() + pre.reserved_uniq);
                if pre.reserved_uniq.contains(HeapId { id: 0, uniq: u, provenance: Provenance::null() }) {
                    assert((pre.heap_shared_access.dom() + pre.reserved_uniq)
                        .contains(HeapId { id: 0, uniq: u, provenance: Provenance::null() }));
                }
            };
        }
    }

    transition!{
        create_thread_mk_tokens(
            thread_id: ThreadId,
            thread_state: ThreadState,
        ) {
            remove right_to_use_thread -= set { thread_id };
            remove reserved_uniq -= set { HeapId { id: 0, uniq: thread_state.heap_id.uniq, provenance: Provenance::null() } };
            require thread_state.pages.dom() =~= Set::empty();
            require thread_state.segments.dom() =~= Set::empty();
            have my_inst >= Some(let inst);

            require thread_state.heap.shared_access.wf2(thread_state.heap_id, inst);

            deposit heap_shared_access +=
                [ thread_state.heap_id => thread_state.heap.shared_access ]

              by {
                  lemma_heap_get_unused_uniq_field(pre.heap_shared_access.dom() + pre.reserved_uniq);
              };

            update heap_to_thread =
                pre.heap_to_thread.insert(thread_state.heap_id, thread_id);

            let real_thread_state = ThreadState {
                heap_id: thread_state.heap_id,
                .. thread_state
            };

            add thread_local_state += [ thread_id => real_thread_state ];
            add thread_checked_state += [ thread_id => ThreadCheckedState { pages: Set::empty() } ];
        }
    }

    pub closed spec fn mk_fresh_segment_id(tos: Map<SegmentId, ThreadId>, sid: SegmentId) -> SegmentId {
        let uniq = segment_get_unused_uniq_field(tos.dom());
        SegmentId { id: sid.id, provenance: sid.provenance, uniq: uniq }
    }

    transition!{
        create_segment_mk_tokens(
            thread_id: ThreadId,
            pre_segment_id: SegmentId,
            segment_state: SegmentState,
        ) {
            require !segment_state.is_enabled;
            remove thread_local_state -= [ thread_id => let ts ];

            birds_eye let real_segment_id = Self::mk_fresh_segment_id(pre.thread_of_segment,pre_segment_id);
            assert !ts.segments.dom().contains(real_segment_id)
              by { lemma_segment_get_unused_uniq_field(pre.thread_of_segment.dom()); };
            assert pre_segment_id.id == real_segment_id.id && pre_segment_id.provenance == real_segment_id.provenance;
            let new_segments = ts.segments.insert(real_segment_id, segment_state);
            let ts2 = ThreadState { segments: new_segments, .. ts };
            add thread_local_state += [ thread_id => ts2 ];
            add thread_of_segment += [ real_segment_id => thread_id ]
              by { lemma_segment_get_unused_uniq_field(pre.thread_of_segment.dom()); };
        }
    }

    transition!{
        segment_enable(
            thread_id: ThreadId,
            segment_id: SegmentId,
            shared_access: SegmentSharedAccess,
        ) {
            remove thread_local_state -= [ thread_id => let ts ];
            require ts.segments.dom().contains(segment_id);
            require !ts.segments[segment_id].is_enabled;
            let segment_state = SegmentState {
                shared_access,
                is_enabled: true,
            };
            let new_segments = ts.segments.insert(segment_id, segment_state);
            let ts2 = ThreadState { segments: new_segments, .. ts };
            add thread_local_state += [ thread_id => ts2 ];
            deposit segment_shared_access += [ segment_id => shared_access ];
        }
    }

    transition!{
        create_page_mk_tokens(
            thread_id: ThreadId,
            page_id: PageId,
            n_slices: nat,
            block_size: nat,
            page_map: Map<PageId, PageState>,
        ) {
            remove thread_local_state -= [ thread_id => let ts ];

            require ts.segments.dom().contains(page_id.segment_id);
            require ts.segments[page_id.segment_id].is_enabled;

            //let range = Set::new(|pid: PageId| pid.segment_id == page_id.segment_id
            //      && page_id.idx <= pid.idx < page_id.idx + n_slices);
            //let new_pages = Map::new(
            //    |pid: PageId| range.contains(pid),
            //    |pid: PageId|
            //);
            require(forall |pid: PageId| page_map.dom().contains(pid)
              <==> (pid.segment_id == page_id.segment_id
                  && page_id.idx <= pid.idx < page_id.idx + n_slices));
            require(forall |pid: PageId| page_map.dom().contains(pid) ==>
                page_map[pid].offset + page_id.idx == pid.idx);
            require(forall |pid: PageId| page_map.dom().contains(pid) ==>
                !page_map[pid].is_enabled);
            require(forall |pid: PageId| page_map.dom().contains(pid) ==>
                page_map[pid].num_blocks == 0);

            require(page_map.dom().contains(page_id));
            require(page_map[page_id].block_size == block_size);
            require(ts.pages.dom().disjoint(page_map.dom()));
            //require(page_map[page_id].reserved_blocks == n_blocks);

            let new_pages = ts.pages.union_prefer_right(page_map);
            let ts2 = ThreadState { pages: new_pages, .. ts };

            add thread_local_state += [ thread_id => ts2 ];

            /*birds_eye let ssa = pre.segment_shared_access[page_id.segment_id];

            let block_map = Map::new(
                |block_id: BlockId|
                    block_id.page_id == page_id
                      && 0 <= block_id.idx < n_blocks
                      && block_id.block_size == block_size
                      && block_id.slice_idx_is_right(),
                |block_id: BlockId|
                  BlockState {
                      segment_shared_access: ssa,
                      page_shared_access: arbitrary(),
                      page_slice_shared_access: arbitrary(),
                      is_enabled: false,
                  }
            );
            add block += (block_map);*/

            add heap_of_page += [ page_id => ts.heap_id ];
            add delay += [ page_id => DelayState::UseDelayedFree ];
        }
    }

    transition!{
        page_enable(
            thread_id: ThreadId,
            page_id: PageId,
            n_slices: nat,
            page_map: Map<PageId, PageState>,
            psa_map: Map<PageId, PageSharedAccess>
        ) {
            remove thread_local_state -= [ thread_id => let ts ];

            require(forall |pid: PageId| page_map.dom().contains(pid)
              <==> (pid.segment_id == page_id.segment_id
                  && page_id.idx <= pid.idx < page_id.idx + n_slices));
            require(page_map.dom() =~= psa_map.dom());
            require(forall |pid: PageId| page_map.dom().contains(pid) ==>
                psa_map[pid] == page_map[pid].shared_access);
            require(forall |pid: PageId| page_map.dom().contains(pid) ==>
                page_map[pid].offset + page_id.idx == pid.idx);

            require(forall |pid: PageId| page_map.dom().contains(pid) ==>
                ts.pages.dom().contains(pid) && !ts.pages[pid].is_enabled);

            require(forall |pid: PageId| page_map.dom().contains(pid) ==>
                page_map[pid] == PageState {
                    is_enabled: true,
                    shared_access: psa_map[pid],
                    .. ts.pages[pid]
                });

            let new_pages = ts.pages.union_prefer_right(page_map);
            let ts2 = ThreadState { pages: new_pages, .. ts };

            add thread_local_state += [ thread_id => ts2 ];
            deposit page_shared_access += (psa_map);
            /*by {
                assert forall |pid| psa_map.dom().contains(pid) implies pre.page_shared_access.dom().contains(pid) == false
                by {
                    assert(ts.pages.dom().contains(pid));
                    assert(ts.pages[pid].is_enabled == false);
                    if pre.page_shared_access.dom().contains(pid) {
                        assert(ts.pages.dom().contains(pid));
                        assert(ts.segments.dom().contains(pid.segment_id));
                        assert(pre.thread_of_segment[pid.segment_id] == thread_id);
                    }
                }
            };*/
        }
    }

    transition!{
        page_mk_block_tokens(
            thread_id: ThreadId,
            page_id: PageId,
            old_num_blocks: nat,
            new_num_blocks: nat,
            block_size: nat,
        ) {
            remove thread_local_state -= [ thread_id => let ts ];
            remove thread_checked_state -= [ thread_id => let cs ];

            require ts.pages.dom().contains(page_id);
            require ts.pages[page_id].is_enabled;
            require ts.pages[page_id].num_blocks == old_num_blocks;
            require ts.pages[page_id].block_size == block_size;
            require ts.pages[page_id].offset == 0;
            require old_num_blocks <= new_num_blocks;
            let new_page = PageState {
                num_blocks: new_num_blocks,
                .. ts.pages[page_id]
            };
            let cs2 = ThreadCheckedState {
                pages: cs.pages.remove(page_id)
            };

            require forall |idx: nat| old_num_blocks <= idx < new_num_blocks
                ==> Self::okay_to_add_block(ts, page_id, idx, block_size);

            birds_eye let ssa = pre.segment_shared_access[page_id.segment_id];
            //let ssa = ts.segments[page_id.segment_id].shared_access;
            let block_map = Map::new(
                range_block_ids(old_num_blocks, new_num_blocks, page_id, block_size),
                |block_id: BlockId|
                  BlockState {
                      segment_shared_access: ssa,
                      page_shared_access: ts.pages[page_id].shared_access,
                      page_slice_shared_access: ts.pages[block_id.page_id_for_slice()].shared_access,
                      heap_id: None,
                  }
            );

            add block += (block_map);

            let new_pages = ts.pages.insert(page_id, new_page);
            let ts2 = ThreadState { pages: new_pages, .. ts };
            add thread_local_state += [ thread_id => ts2 ];
            add thread_checked_state += [ thread_id => cs2 ];
        }
    }

    pub open spec fn okay_to_add_block(ts: ThreadState, page_id: PageId, idx: nat, block_size: nat) -> bool {
        let slice_id = PageId {
            segment_id: page_id.segment_id,
            idx: BlockId::get_slice_idx(page_id, idx, block_size),
        };
        ts.pages.dom().contains(slice_id)
        && ts.pages[slice_id].is_enabled
        && ts.pages[slice_id].offset == slice_id.idx - page_id.idx
    }

    transition!{
        page_destroy_block_tokens(
            thread_id: ThreadId,
            page_id: PageId,
            blocks: Map<BlockId, BlockState>,
        ) {
            remove thread_local_state -= [ thread_id => let ts ];
            require ts.pages.dom().contains(page_id);
            require blocks.len() == ts.pages[page_id].num_blocks;
            require forall |block_id: BlockId| blocks.dom().contains(block_id) ==>
                block_id.page_id == page_id;

            remove block -= (blocks);

            let new_page = PageState {
                num_blocks: 0,
                .. ts.pages[page_id]
            };
            let new_pages = ts.pages.insert(page_id, new_page);
            let ts2 = ThreadState { pages: new_pages, .. ts };
            add thread_local_state += [ thread_id => ts2 ];
        }
    }

    transition!{
        page_check_delay_state(
            thread_id: ThreadId,
            page_id: PageId,
        ) {
            have thread_local_state >= [ thread_id => let ts ];
            remove thread_checked_state -= [ thread_id => let cs ];
            require ts.pages.dom().contains(page_id);
            require ts.pages[page_id].num_blocks == 0;
            have delay >= [ page_id => let delay_state ];
            require delay_state != DelayState::Freeing;

            let cs2 = ThreadCheckedState {
                pages: cs.pages.insert(page_id),
            };
            add thread_checked_state += [ thread_id => cs2 ];
        }
    }

    transition!{
        page_disable(
            thread_id: ThreadId,
            page_id: PageId,
            n_slices: nat,
        ) {
            remove thread_local_state -= [ thread_id => let ts ];
            have thread_checked_state >= [ thread_id => let cs ];
            require ts.pages.dom().contains(page_id);
            require ts.pages[page_id].is_enabled;
            require cs.pages.contains(page_id);
            require ts.pages[page_id].num_blocks == 0;
            require page_id.range_from(0, n_slices as int).subset_of(ts.pages.dom());

            require forall |pid: PageId| #![all_triggers]
                  page_id.range_from(0, n_slices as int).contains(pid) ==>
                    ts.pages.dom().contains(pid)
                    && ts.pages[pid].is_enabled
                    && ts.pages[pid].offset == pid.idx - page_id.idx;
            //require forall |pid: PageId|
            //      pid.segment_id == page_id.segment_id
            //          && !page_id.range_from(0, n_slices as int).contains(pid)
            //          && ts.pages.dom().contains(pid)
            //          ==> ts.pages[pid].offset != pid.idx - page_id.idx;

            let new_pages0 = Map::<PageId, PageState>::new(
                page_id.range_from(0, n_slices as int),
                |pid: PageId|
                    PageState {
                        is_enabled: false,
                        .. ts.pages[pid]
                    }
            );

            let new_pages = ts.pages.union_prefer_right(new_pages0);
            let ts2 = ThreadState { pages: new_pages, .. ts };
            add thread_local_state += [ thread_id => ts2 ];

            let psa_map = Map::new(
                page_id.range_from(0, n_slices as int),
                |pid: PageId| ts.pages[pid].shared_access,
            );
            withdraw page_shared_access -= (psa_map)
            by {
                //page_disable_withdraw_ok(thread_id, page_id, n_slices);
                // PAPER CUT
                assert forall |pid: PageId| #![all_triggers]
                    psa_map.dom().contains(pid) implies
                        pre.page_shared_access.dom().contains(pid)
                        && psa_map[pid] == pre.page_shared_access[pid]
                by {
                    assert(page_id.range_from(0, n_slices as int).contains(pid));
                    assert(ts.pages.dom().contains(pid));
                    assert(pre.page_shared_access.dom().contains(pid));
                }
            };
        }
    }

    transition!{
        page_destroy_tokens(
            thread_id: ThreadId,
            page_id: PageId,
            n_slices: nat,
        ) {
            remove heap_of_page -= [ page_id => let _ ];
            remove delay -= [ page_id => let _ ];

            remove thread_local_state -= [ thread_id => let ts ];
            //require ts.pages.dom().contains(page_id);
            //require !ts.pages[page_id].is_enabled;
            require page_id.range_from(0, n_slices as int).subset_of(ts.pages.dom());
            require n_slices >= 1;

            require forall |pid: PageId|
                  page_id.range_from(0, n_slices as int).contains(pid) ==>
                    !ts.pages[pid].is_enabled;

            require forall |pid: PageId|
                  page_id.range_from(0, n_slices as int).contains(pid) ==>
                    page_id != pid ==> ts.pages[pid].offset != 0;

            let new_pages = ts.pages.remove_keys(page_id.range_from(0, n_slices as int));
            let ts2 = ThreadState { pages: new_pages, .. ts };
            add thread_local_state += [ thread_id => ts2 ];
        }
    }

    property!{
        heap_of_page_agree_with_thread_state(page_id: PageId, thread_id: ThreadId) {
            have thread_local_state >= [ thread_id => let ts ];
            have heap_of_page >= [ page_id => let heap_id ];
            require ts.pages.dom().contains(page_id);
            assert(ts.heap_id == heap_id);
        }
    }

    transition!{
        block_tokens_distinct(block_id1: BlockId, block_id2: BlockId) {
            require block_id1.page_id == block_id2.page_id;
            require block_id1.idx == block_id2.idx;
            remove block -= [block_id1 => let _];
            remove block -= [block_id2 => let _];
            assert false;
        }
    }

    transition!{
        block_in_range(thread_id: ThreadId, block_id: BlockId) {
            have thread_local_state >= [ thread_id => let ts ];
            have block >= [ block_id => let _ ];
            require ts.pages.dom().contains(block_id.page_id);
            assert 0 <= block_id.idx < ts.pages[block_id.page_id].num_blocks;
        }
    }

    property!{
        block_in_heap_has_valid_page(thread_id: ThreadId, block_id: BlockId) {
            have thread_local_state >= [ thread_id => let ts ];
            have block >= [ block_id => let block_state ];
            require block_state.heap_id == Some(ts.heap_id);
            assert ts.pages.dom().contains(block_id.page_id);
            assert ts.pages[block_id.page_id].block_size == block_id.block_size;
            assert ts.pages[block_id.page_id].offset == 0;
        }
    }

    property!{
        get_block_properties(thread_id: ThreadId, block_id: BlockId) {
            have block >= [ block_id => let block_state ];
            have thread_local_state >= [ thread_id => let ts ];
            require ts.pages.dom().contains(block_id.page_id);
            assert Self::block_properties(ts, block_id, block_state);
        }
    }

    // Invariants

    #[invariant]
    pub closed spec fn inv_reserved(&self) -> bool {
        (forall |heap_id: HeapId| self.reserved_uniq.contains(heap_id) ==> heap_id.id == 0 && heap_id.provenance == Provenance::null())
    }

    #[invariant]
    pub closed spec fn inv_reserved2(&self) -> bool {
        forall |hid1: HeapId, hid2: HeapId|
            self.reserved_uniq.contains(hid1)
            && self.heap_shared_access.dom().contains(hid2)
            ==> hid1.uniq != hid2.uniq
    }

    #[invariant]
    pub closed spec fn inv_right_to_set_inst(&self) -> bool {
        self.right_to_set_inst <==> self.my_inst.is_none()
    }

    #[invariant]
    pub closed spec fn inv_heap_of_page_delay(&self) -> bool {
        self.heap_of_page.dom() =~= self.delay.dom()
    }

    /*#[invariant]
    pub closed spec fn inv_heap_of_page_offset0(&self) -> bool {
        forall |thread_id, page_id| #![all_triggers]
            self.thread_local_state.dom().contains(thread_id)
            && self.thread_local_state[thread_id].pages.dom().contains(page_id)
                ==>
    }*/

    #[invariant]
    pub closed spec fn inv_delay_state(&self) -> bool {
        forall |page_id: PageId| #[trigger] self.delay.dom().contains(page_id) ==>
            self.inv_delay_state_for_page(page_id)
    }

    pub closed spec fn inv_delay_state_for_page(&self, page_id: PageId) -> bool {
        match self.delay[page_id] {
            DelayState::UseDelayedFree => {
                !self.delay_actor.dom().contains(page_id)
            }
            DelayState::Freeing => {
                self.delay_actor.dom().contains(page_id)
            }
            DelayState::NoDelayedFree => {
                !self.delay_actor.dom().contains(page_id)
            }
            DelayState::NeverDelayedFree => {
                false // not used right now
            }
        }
    }

    #[invariant]
    pub closed spec fn inv_delay_actor(&self) -> bool {
        forall |page_id: PageId| #[trigger] self.delay_actor.dom().contains(page_id) ==>
            self.inv_delay_actor_for_page(page_id)
    }

    pub closed spec fn inv_delay_actor_for_page(&self, page_id: PageId) -> bool {
        match self.delay_actor[page_id] {
            DelayFreeingActor::HeapUnknown => {
                let thread_id = self.thread_of_segment[page_id.segment_id];
                  self.thread_local_state.dom().contains(thread_id)
                  && self.thread_local_state[thread_id].pages.dom().contains(page_id)
                  && self.thread_local_state[thread_id].pages[page_id].is_enabled
            }
            DelayFreeingActor::Heap(heap_id, hsa, psa) => {
                let thread_id = self.heap_to_thread[heap_id];
                self.heap_shared_access.dom().contains(heap_id)
                  && self.heap_shared_access[heap_id] == hsa
                  && self.heap_to_thread.dom().contains(heap_id)
                  && self.thread_local_state.dom().contains(thread_id)
                  && self.thread_local_state[thread_id].pages.dom().contains(page_id)
                  && self.thread_local_state[thread_id].pages[page_id].shared_access == psa
                  && self.thread_local_state[thread_id].pages[page_id].is_enabled

            }
        }
    }

    #[invariant]
    pub closed spec fn inv_delay_actor_sub(&self) -> bool {
        self.delay_actor.dom() <= self.delay.dom()
    }

    #[invariant]
    pub closed spec fn inv_checked_threads(&self) -> bool {
        self.thread_local_state.dom() =~= self.thread_checked_state.dom()
    }

    #[invariant]
    pub closed spec fn inv_no_delay_actor_for_checked(&self) -> bool {
        forall |thread_id: ThreadId, page_id: PageId|
            self.thread_local_state.dom().contains(thread_id)
            && #[trigger] self.thread_local_state[thread_id].pages.dom().contains(page_id)
            && self.thread_checked_state[thread_id].pages.contains(page_id)
                ==> self.thread_local_state[thread_id].pages[page_id].num_blocks == 0
                      && !self.delay_actor.dom().contains(page_id)
    }

    //#[invariant]
    //pub closed spec fn inv_threads_hsa(&self) -> bool {
    //    forall |thread_id: ThreadId| self.thread_local_state.dom().contains(thread_id) ==>
    //        self.thread_local_state[thread_id]
    //}

    #[invariant]
    pub closed spec fn right_to_use_thread_complement(&self) -> bool {
        forall |thread_id: ThreadId|
            #![trigger self.right_to_use_thread.contains(thread_id)]
            #![trigger self.thread_local_state.dom().contains(thread_id)]
            self.right_to_use_thread.contains(thread_id)
              <==> !self.thread_local_state.dom().contains(thread_id)
    }

    #[invariant]
    pub closed spec fn heap_of_thread_is_valid(&self) -> bool {
        forall |thread_id|
            #[trigger] self.thread_local_state.dom().contains(thread_id) ==>
              self.heap_shared_access.dom().contains(
                  self.thread_local_state[thread_id].heap_id)
    }


    #[invariant]
    pub closed spec fn wf_heap_shared_access_requires_inst(&self) -> bool {
        self.my_inst.is_none() ==>
            self.heap_shared_access.dom() =~= Set::empty()
    }

    #[invariant]
    pub closed spec fn wf_heap_shared_access(&self) -> bool {
        forall |heap_id|
            #![trigger self.heap_shared_access.dom().contains(heap_id)]
            #![trigger self.heap_shared_access.index(heap_id)]
            self.heap_shared_access.dom().contains(heap_id)
              ==> self.heap_shared_access[heap_id].wf2(heap_id, self.my_inst.unwrap())
    }

    #[invariant]
    pub closed spec fn inv_thread_of_segment1(&self) -> bool {
        forall |thread_id, segment_id| #![all_triggers] self.thread_local_state.dom().contains(thread_id) && self.thread_local_state[thread_id].segments.dom().contains(segment_id) ==>
            self.thread_of_segment.dom().contains(segment_id)
              && self.thread_of_segment[segment_id] == thread_id
    }

    #[invariant]
    pub closed spec fn inv_thread_of_segment2(&self) -> bool {
        forall |segment_id| #[trigger] self.thread_of_segment.dom().contains(segment_id) ==>
            self.thread_local_state.dom().contains(self.thread_of_segment[segment_id])
              && self.thread_local_state[self.thread_of_segment[segment_id]].segments.dom().contains(segment_id)
    }

    #[invariant]
    pub closed spec fn inv_thread_has_segment_for_page(&self) -> bool {
        forall |thread_id, page_id| self.thread_local_state.dom().contains(thread_id) && #[trigger] self.thread_local_state[thread_id].pages.dom().contains(page_id)
          ==>
            self.thread_local_state[thread_id].segments.dom().contains(page_id.segment_id)
    }

    #[invariant]
    pub closed spec fn inv_thread_of_page1(&self) -> bool {
        forall |thread_id, page_id| self.thread_local_state.dom().contains(thread_id) && #[trigger] self.thread_local_state[thread_id].pages.dom().contains(page_id)
            && self.thread_local_state[thread_id].pages[page_id].offset == 0
          ==>
            self.heap_of_page.dom().contains(page_id)
              && self.thread_local_state[thread_id].segments.dom().contains(page_id.segment_id)
    }

    #[invariant]
    pub closed spec fn inv_thread_of_page2(&self) -> bool {
        forall |page_id| #[trigger] self.heap_of_page.dom().contains(page_id)
            ==> self.thread_of_segment.dom().contains(page_id.segment_id)
              && self.thread_local_state.dom().contains(self.thread_of_segment[page_id.segment_id])
              && self.thread_local_state[self.thread_of_segment[page_id.segment_id]].pages.dom().contains(page_id)
              && self.thread_local_state[self.thread_of_segment[page_id.segment_id]].pages[page_id].offset == 0
    }

    #[invariant]
    pub closed spec fn heap_of_page_is_correct(&self) -> bool {
        forall |page_id|
            #[trigger] self.heap_of_page.dom().contains(page_id) ==>
                //self.heap_shared_access.dom().contains(self.heap_of_page[page_id])
                self.heap_of_page[page_id] ==
                  self.thread_local_state[self.thread_of_segment[page_id.segment_id]].heap_id
    }

    #[invariant]
    pub closed spec fn inv_page_shared_access_dom(&self) -> bool {
        forall |page_id: PageId|
            #![trigger self.page_shared_access.dom().contains(page_id)]
            self.page_shared_access.dom().contains(page_id) <==>
            (self.thread_of_segment.dom().contains(page_id.segment_id)
                && self.thread_local_state[self.thread_of_segment[page_id.segment_id]].pages.dom().contains(page_id)
                && self.thread_local_state[self.thread_of_segment[page_id.segment_id]].pages[page_id].is_enabled)
    }

    #[invariant]
    pub closed spec fn inv_page_shared_access_eq(&self) -> bool {
        forall |page_id: PageId|
            #![trigger self.page_shared_access.dom().contains(page_id)]
            self.page_shared_access.dom().contains(page_id) ==>
              self.page_shared_access[page_id] == self.thread_local_state[self.thread_of_segment[page_id.segment_id]].pages[page_id].shared_access
    }

    #[invariant]
    pub closed spec fn inv_segment_shared_access_dom(&self) -> bool {
        forall |segment_id: SegmentId|
            #![trigger self.segment_shared_access.dom().contains(segment_id)]
            self.segment_shared_access.dom().contains(segment_id) <==>
            (self.thread_of_segment.dom().contains(segment_id)
                && self.thread_local_state[self.thread_of_segment[segment_id]].segments.dom().contains(segment_id)
                && self.thread_local_state[self.thread_of_segment[segment_id]].segments[segment_id].is_enabled)
    }

    #[invariant]
    pub closed spec fn inv_segment_shared_access_eq(&self) -> bool {
        forall |segment_id: SegmentId|
            #![trigger self.segment_shared_access.dom().contains(segment_id)]
            self.segment_shared_access.dom().contains(segment_id) ==>
              self.segment_shared_access[segment_id] == self.thread_local_state[self.thread_of_segment[segment_id]].segments[segment_id].shared_access
    }

    #[invariant]
    pub closed spec fn inv_block_id_valid(&self) -> bool {
        forall |block_id: BlockId| #[trigger] self.block.dom().contains(block_id) ==>
            self.inv_block_id_valid_for_block(block_id)
    }

    pub closed spec fn inv_block_id_valid_for_block(&self, block_id: BlockId) -> bool {
        self.thread_of_segment.dom().contains(block_id.page_id.segment_id)
        && Self::block_properties(
            self.thread_local_state[self.thread_of_segment[block_id.page_id.segment_id]],
            block_id,
            self.block[block_id])
    }

    pub open spec fn block_properties(ts: ThreadState, block_id: BlockId, block_state: BlockState) -> bool {
        let slice_id = block_id.page_id_for_slice();

        ts.pages.dom().contains(block_id.page_id)
        && ts.pages[block_id.page_id].is_enabled
        && ts.pages[block_id.page_id].offset == 0
        && ts.pages[block_id.page_id].block_size == block_id.block_size
        && ts.pages[block_id.page_id].shared_access == block_state.page_shared_access
        && 0 <= block_id.idx <
            ts.pages[block_id.page_id].num_blocks

        && ts.pages.dom().contains(slice_id)
        && ts.pages[slice_id].is_enabled
        && ts.pages[slice_id].shared_access == block_state.page_slice_shared_access

        && slice_id.idx - block_id.page_id.idx ==
            ts.pages[slice_id].offset

        && ts.segments[block_id.page_id.segment_id].is_enabled
        && ts.segments[block_id.page_id.segment_id].shared_access == block_state.segment_shared_access

        && (match block_state.heap_id {
            None => true,
            Some(heap_id) => heap_id == ts.heap_id,
        })
    }

    #[invariant]
    pub closed spec fn inv_block_id_at_idx_uniq(&self) -> bool {
        forall |bid1: BlockId, bid2: BlockId|
            self.block.dom().contains(bid1)
            && self.block.dom().contains(bid2)
            && bid1.page_id == bid2.page_id
            && bid1.idx == bid2.idx
            ==> bid1 == bid2
    }

    #[invariant]
    pub closed spec fn heap_ids_thread_id1(&self) -> bool {
        forall |thread_id| #[trigger] self.thread_local_state.dom().contains(thread_id) ==>
            self.heap_to_thread.dom().contains(self.thread_local_state[thread_id].heap_id)
            && self.heap_to_thread[self.thread_local_state[thread_id].heap_id] == thread_id
    }

    #[invariant]
    pub closed spec fn heap_ids_thread_id2(&self) -> bool {
        forall |heap_id| #[trigger] self.heap_to_thread.dom().contains(heap_id) ==>
            self.thread_local_state.dom().contains(self.heap_to_thread[heap_id])
            && self.thread_local_state[self.heap_to_thread[heap_id]].heap_id == heap_id
    }

    #[invariant]
    pub closed spec fn inv_heap_shared_access(&self) -> bool {
        forall |thread_id| self.thread_local_state.dom().contains(thread_id) ==>
            self.heap_shared_access.dom().contains(self.thread_local_state[thread_id].heap_id)
            && self.heap_shared_access[self.thread_local_state[thread_id].heap_id]
                  == self.thread_local_state[thread_id].heap.shared_access
    }

    #[invariant]
    pub closed spec fn page_implies_segment_enabled(&self) -> bool {
        forall |thread_id: ThreadId, page_id: PageId|
            self.thread_local_state.dom().contains(thread_id)
            && #[trigger] self.thread_local_state[thread_id].pages.dom().contains(page_id)
            ==> self.thread_local_state[thread_id].segments.dom().contains(page_id.segment_id)
                  && self.thread_local_state[thread_id].segments[page_id.segment_id].is_enabled
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    #[inductive(set_inst)]
    fn set_inst_inductive(pre: Self, post: Self, inst: InstanceId) { }

    #[inductive(actor_make_idle)]
    fn actor_make_idle_inductive(pre: Self, post: Self, thread_id: ThreadId) { }

    #[inductive(actor_abandon)]
    fn actor_abandon_inductive(pre: Self, post: Self, thread_id: ThreadId) { }

    #[inductive(set_use_delayed_free)]
    fn set_use_delayed_free_inductive(pre: Self, post: Self, page_id: PageId) { }

    #[inductive(delay_enter_freeing)]
    fn delay_enter_freeing_inductive(pre: Self, post: Self, page_id: PageId, block_id: BlockId) { }

    #[inductive(delay_leave_freeing)]
    fn delay_leave_freeing_inductive(pre: Self, post: Self, page_id: PageId) { }

    #[inductive(delay_lookup_heap)]
    fn delay_lookup_heap_inductive(pre: Self, post: Self, block_id: BlockId) { }

    #[inductive(block_set_heap_id)]
    fn block_set_heap_id_inductive(pre: Self, post: Self, block_id: BlockId) {
        /*match pre.delay_actor[block_id.page_id] {
            DelayFreeingActor::Heap(heap_id, _hsa, _psa) => {
                let thread_id = post.heap_to_thread[heap_id];
                assert(post.heap_to_thread.dom().contains(heap_id));
                assert(thread_id == post.thread_of_segment[block_id.page_id.segment_id]);
                assert(heap_id == post.thread_local_state[thread_id].heap_id);
                assert(heap_id == post.thread_local_state[post.thread_of_segment[block_id.page_id.segment_id]].heap_id);
            }
            _ => { assert(false); }
        }*/
    }

    #[inductive(create_thread_mk_tokens)]
    fn create_thread_mk_tokens_inductive(pre: Self, post: Self, thread_id: ThreadId, thread_state: ThreadState) {
        /*assert forall |tid, segment_id| post.thread_local_state.dom().contains(tid) && #[trigger] post.thread_local_state[tid].segments.dom().contains(segment_id) implies
            post.thread_of_segment.dom().contains(segment_id)
              && post.thread_of_segment[segment_id] == tid
        by {
            if tid == thread_id {
                assert(post.thread_of_segment.dom().contains(segment_id));
                assert(post.thread_of_segment[segment_id] == tid);
            } else {
                assert(post.thread_of_segment.dom().contains(segment_id));
                assert(post.thread_of_segment[segment_id] == tid);
            }
        }*/
    }

    #[inductive(create_segment_mk_tokens)]
    fn create_segment_mk_tokens_inductive(pre: Self, post: Self, thread_id: ThreadId, pre_segment_id: SegmentId, segment_state: SegmentState) { }

    #[inductive(segment_enable)]
    fn segment_enable_inductive(pre: Self, post: Self, thread_id: ThreadId, segment_id: SegmentId, shared_access: SegmentSharedAccess) { }

    #[inductive(create_page_mk_tokens)]
    fn create_page_mk_tokens_inductive(pre: Self, post: Self, thread_id: ThreadId, page_id: PageId, n_slices: nat, block_size: nat, page_map: Map<PageId, PageState>) {

    }

    #[inductive(page_enable)]
    fn page_enable_inductive(pre: Self, post: Self, thread_id: ThreadId, page_id: PageId, n_slices: nat, page_map: Map<PageId, PageState>, psa_map: Map<PageId, PageSharedAccess>) { }

    #[inductive(page_mk_block_tokens)]
    fn page_mk_block_tokens_inductive(pre: Self, post: Self, thread_id: ThreadId, page_id: PageId, old_num_blocks: nat, new_num_blocks: nat, block_size: nat) {
        let ts = pre.thread_local_state[thread_id];
        let ssa = pre.segment_shared_access[page_id.segment_id];
        let block_map = Map::new(
            range_block_ids(old_num_blocks, new_num_blocks, page_id, block_size),
            |block_id: BlockId|
              BlockState {
                  segment_shared_access: ssa,
                  page_shared_access: ts.pages[page_id].shared_access,
                  page_slice_shared_access: ts.pages[block_id.page_id_for_slice()].shared_access,
                  heap_id: None,
              });
        assert(post.block == pre.block.union_prefer_right(block_map));
        assert forall |bid: BlockId| post.block.dom().contains(bid) ==>
            pre.block.dom().contains(bid) || block_map.dom().contains(bid) by {
            if post.block.dom().contains(bid) {
                assert(pre.block.dom().contains(bid) || block_map.dom().contains(bid));
            }
        };
        assert(pre.inv_block_id_valid());
        assert(pre.inv_thread_of_page2());
        assert(pre.inv_segment_shared_access_eq());
        assert(pre.thread_of_segment.dom().contains(page_id.segment_id));
        assert(pre.thread_of_segment[page_id.segment_id] == thread_id);
        assert(pre.segment_shared_access.dom().contains(page_id.segment_id));
        assert(pre.segment_shared_access[page_id.segment_id] ==
            pre.thread_local_state[pre.thread_of_segment[page_id.segment_id]].segments[page_id.segment_id].shared_access);
        assert(ts.segments[page_id.segment_id].shared_access == ssa);
        assert forall |bid: BlockId| post.block.dom().contains(bid) ==>
            post.inv_block_id_valid_for_block(bid) by {
            if post.block.dom().contains(bid) {
                if pre.block.dom().contains(bid) {
                    assert(pre.inv_block_id_valid_for_block(bid));
                    assert(post.inv_block_id_valid_for_block(bid));
                } else {
                    assert(block_map.dom().contains(bid));
                    assert(bid.page_id == page_id);
                    assert(old_num_blocks <= bid.idx < new_num_blocks);
                    assert(bid.block_size == block_size);
                    assert(bid.slice_idx == BlockId::get_slice_idx(page_id, bid.idx, block_size));
                    assert(ts.pages.dom().contains(page_id));
                    assert(ts.pages[page_id].is_enabled);
                    assert(ts.pages[page_id].offset == 0);
                    assert(ts.pages[page_id].block_size == block_size);
                    assert(Self::okay_to_add_block(ts, page_id, bid.idx, block_size));
                    assert(post.block[bid] == block_map[bid]);
                    assert(post.block[bid].segment_shared_access == ssa);
                    assert(post.block[bid].page_shared_access == ts.pages[page_id].shared_access);
                    assert(post.block[bid].page_slice_shared_access == ts.pages[bid.page_id_for_slice()].shared_access);
                    assert(post.block[bid].heap_id == None);
                    assert(post.thread_local_state[thread_id].pages[page_id].num_blocks == new_num_blocks);
                    assert(post.thread_local_state[thread_id].pages[page_id].shared_access == ts.pages[page_id].shared_access);
                    assert(post.thread_local_state[thread_id].pages[page_id].is_enabled);
                    assert(post.thread_local_state[thread_id].pages[page_id].offset == 0);
                    assert(post.thread_local_state[thread_id].pages[page_id].block_size == block_size);
                    assert(post.thread_local_state[thread_id].pages[bid.page_id_for_slice()].is_enabled);
                    assert(post.thread_local_state[thread_id].pages[bid.page_id_for_slice()].shared_access ==
                        ts.pages[bid.page_id_for_slice()].shared_access);
                    assert(ts.pages[bid.page_id_for_slice()].offset ==
                        bid.page_id_for_slice().idx - page_id.idx);
                    assert(post.thread_local_state[thread_id].pages[bid.page_id_for_slice()].offset ==
                        bid.page_id_for_slice().idx - page_id.idx);
                    assert(post.thread_local_state[thread_id].segments[page_id.segment_id].is_enabled);
                    assert(post.thread_local_state[thread_id].segments[page_id.segment_id].shared_access == ssa);
                }
            }
        };
    }

    proof fn block_map_with_len(blocks: Map<BlockId, BlockState>, page_id: PageId, len: int)
        requires
            blocks.len() >= len,
            len >= 0,
            forall |block_id: BlockId| blocks.dom().contains(block_id) ==>
                block_id.page_id == page_id && 0 <= block_id.idx < len,
            forall |bid1: BlockId, bid2: BlockId|
                blocks.dom().contains(bid1) && blocks.dom().contains(bid2)
                && bid1.page_id == bid2.page_id && bid1.idx == bid2.idx
                ==> bid1 == bid2
        ensures
            blocks.len() > len ==> false,
            forall |i| 0 <= i < blocks.len() ==> Self::blocks_has(blocks, page_id, i)
        decreases len,
    {
        if len == 0 {
            if (blocks.len() > len) {
                vstd::set_lib::lemma_set_empty_equivalency_len(blocks.dom());
                let t = choose |t: BlockId| blocks.dom().contains(t);
                assert(blocks.dom().contains(t));
                assert(false);
            }
            assert(forall |i| 0 <= i < blocks.len() ==> Self::blocks_has(blocks, page_id, i));
        } else {
            if Self::blocks_has(blocks, page_id, len - 1) {
                let block_id = choose |block_id: BlockId| blocks.dom().contains(block_id)
                    && block_id.page_id == page_id && block_id.idx == len - 1;
                let blocks0 = blocks.remove(block_id);
                Self::block_map_with_len(blocks0, page_id, len - 1);
                assert forall |i| 0 <= i < blocks.len()
                    implies Self::blocks_has(blocks, page_id, i)
                by {
                    if i < blocks.len() - 1 {
                        assert(Self::blocks_has(blocks0, page_id, i));
                        assert(Self::blocks_has(blocks, page_id, i));
                    } else {
                        assert(Self::blocks_has(blocks, page_id, i));
                    }
                }
            } else {
                Self::block_map_with_len(blocks, page_id, len - 1);
            }
        }
    }

    spec fn blocks_has(blocks: Map<BlockId, BlockState>, page_id: PageId, i: int) -> bool {
        exists |block_id| blocks.dom().contains(block_id) && block_id.page_id == page_id
            && block_id.idx == i
    }

    #[inductive(page_destroy_block_tokens)]
    fn page_destroy_block_tokens_inductive(pre: Self, post: Self, thread_id: ThreadId, page_id: PageId, blocks: Map<BlockId, BlockState>) {
        assert forall |bid: BlockId| post.block.dom().contains(bid) ==> pre.block.dom().contains(bid) by {
            vstd::map::lemma_map_remove_domain(pre.block, bid);
            assert(post.block.dom() =~= pre.block.dom().difference(blocks.dom()));
        };
        assert(pre.inv_block_id_valid());
        assert(blocks.dom() <= pre.block.dom());
        assert(blocks.len() == pre.thread_local_state[thread_id].pages[page_id].num_blocks);
        assert(blocks.len() >= pre.thread_local_state[thread_id].pages[page_id].num_blocks as int);
        assert forall |x: BlockId| blocks.dom().contains(x) ==>
            x.page_id == page_id && 0 <= x.idx < pre.thread_local_state[thread_id].pages[page_id].num_blocks as int by {
            if blocks.dom().contains(x) {
                assert(x.page_id == page_id && 0 <= x.idx < pre.thread_local_state[thread_id].pages[page_id].num_blocks as int);
            }
        };
        assert forall |x: BlockId, y: BlockId|
            blocks.dom().contains(x) && blocks.dom().contains(y)
            && x.page_id == y.page_id && x.idx == y.idx ==> x == y by {
            if blocks.dom().contains(x) && blocks.dom().contains(y)
                && x.page_id == y.page_id && x.idx == y.idx {
                assert(pre.inv_block_id_at_idx_uniq());
                assert(x == y);
            }
        };
        Self::block_map_with_len(blocks, page_id,
            pre.thread_local_state[thread_id].pages[page_id].num_blocks as int);
        assert forall |bid: BlockId| post.block.dom().contains(bid) ==> !blocks.dom().contains(bid) by {
            if post.block.dom().contains(bid) {
                assert(post.block.dom() =~= pre.block.dom().difference(blocks.dom()));
                assert(!blocks.dom().contains(bid));
            }
        };
        assert forall |bid: BlockId| post.block.dom().contains(bid) ==>
            post.inv_block_id_valid_for_block(bid) by {
            if post.block.dom().contains(bid) {
                assert(pre.block.dom().contains(bid));
                assert(pre.inv_block_id_valid_for_block(bid));
                assert(!blocks.dom().contains(bid));
                if bid.page_id == page_id {
                    assert(Self::blocks_has(blocks, page_id, bid.idx as int));
                    let other = choose |x: BlockId| blocks.dom().contains(x)
                        && x.page_id == page_id && x.idx == bid.idx;
                    assert(blocks.dom().contains(other));
                    assert(other.page_id == page_id && other.idx == bid.idx);
                    assert(other == bid);
                    assert(false);
                }
            }
        };
    }

    #[inductive(page_disable)]
    fn page_disable_inductive(pre: Self, post: Self, thread_id: ThreadId, page_id: PageId, n_slices: nat) {
    }

    #[inductive(page_destroy_tokens)]
    fn page_destroy_tokens_inductive(pre: Self, post: Self, thread_id: ThreadId, page_id: PageId, n_slices: nat) {
    }

    #[inductive(block_tokens_distinct)]
    fn block_tokens_distinct_inductive(pre: Self, post: Self, block_id1: BlockId, block_id2: BlockId) { }

    #[inductive(block_in_range)]
    fn block_in_range_inductive(pre: Self, post: Self, thread_id: ThreadId, block_id: BlockId) { }

    /*proof fn page_disable_withdraw_ok(
            &self,
            thread_id: ThreadId,
            page_id: PageId,
            n_slices: nat)
      requires self.invariant(),
            ts.pages.dom().contains(page_id),
            ts.pages[page_id].is_enabled,
            ts.pages[page_id].checked_delay_state,
            ts.pages[page_id].num_blocks == 0,
            page_id.range_from(0, n_slices as int).subset_of(ts.pages.dom()),
      ensures ({
            let psa_map = Map::new(
                |pid: PageId| page_id.range_from(0, n_slices as int).contains(pid),
                |pid: PageId| ts.pages[pid].shared_access,
            );
            forall |pid| psa_map.dom().contains(pid) ==>
                pre.page_shared_access.dom().contains(pid)
      })*/

    #[inductive(page_check_delay_state)]
    fn page_check_delay_state_inductive(pre: Self, post: Self, thread_id: ThreadId, page_id: PageId) { }

    #[inductive(reserve_uniq_identifier)]
    fn reserve_uniq_identifier_inductive(pre: Self, post: Self) {
        let u = heap_get_unused_uniq_field(pre.heap_shared_access.dom() + pre.reserved_uniq);
        let new_id = HeapId { id: 0, uniq: u, provenance: Provenance::null() };
        assert(post.reserved_uniq =~= pre.reserved_uniq + set! { new_id });
        assert(post.heap_shared_access.dom() =~= pre.heap_shared_access.dom());
        assert forall |h: HeapId| #[trigger] post.reserved_uniq.contains(h)
            <==> pre.reserved_uniq.contains(h) || h == new_id by { };
        assert forall |h: HeapId| post.reserved_uniq.contains(h)
            implies pre.reserved_uniq.contains(h) || h == new_id by { };
        assert forall |hid1: HeapId, hid2: HeapId|
            post.reserved_uniq.contains(hid1)
            && post.heap_shared_access.dom().contains(hid2)
            ==> hid1.uniq != hid2.uniq
        by {
            if post.reserved_uniq.contains(hid1) && post.heap_shared_access.dom().contains(hid2) {
                assert(pre.heap_shared_access.dom().contains(hid2));
                assert(post.reserved_uniq.contains(hid1)
                    ==> pre.reserved_uniq.contains(hid1) || hid1 == new_id);
                if pre.reserved_uniq.contains(hid1) {
                    assert(pre.inv_reserved2());
                    assert(hid1.uniq != hid2.uniq);
                } else {
                    assert(hid1 == new_id);
                    assert((pre.heap_shared_access.dom() + pre.reserved_uniq).contains(hid2));
                    lemma_heap_get_unused_uniq_field(pre.heap_shared_access.dom() + pre.reserved_uniq);
                    assert(hid2.uniq != new_id.uniq);
                }
            }
        };
    }


}}

fn main() {}
