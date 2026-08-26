#![feature(core_intrinsics)]
#![feature(allocator_api)]
#![allow(unused_imports)]
#![allow(non_snake_case)]
#![allow(unused_assignments)]
#![allow(unused_macros)]
#![feature(thread_id_value)]
#![verifier::exec_allows_no_decreases_clause]

mod libc {
    pub use core::ffi::c_void;

    pub const PROT_NONE: i32 = 0;
    pub const PROT_READ: i32 = 1;
    pub const PROT_WRITE: i32 = 2;
    pub const MAP_PRIVATE: i32 = 0x02;
    pub const MAP_FAILED: *mut c_void = usize::MAX as *mut c_void;

    #[cfg(target_os = "macos")]
    pub const MAP_ANONYMOUS: i32 = 0x1000;
    #[cfg(not(target_os = "macos"))]
    pub const MAP_ANONYMOUS: i32 = 0x20;

    #[cfg(target_os = "macos")]
    pub const MAP_NORESERVE: i32 = 0;
    #[cfg(not(target_os = "macos"))]
    pub const MAP_NORESERVE: i32 = 0x4000;

    #[cfg(target_os = "macos")]
    pub const CLOCK_MONOTONIC: i32 = 6;
    #[cfg(not(target_os = "macos"))]
    pub const CLOCK_MONOTONIC: i32 = 1;

    #[repr(C)]
    pub struct timespec {
        pub tv_sec: i64,
        pub tv_nsec: i64,
    }

    extern "C" {
        pub fn mmap(
            addr: *mut c_void,
            len: usize,
            prot: i32,
            flags: i32,
            fd: i32,
            offset: isize,
        ) -> *mut c_void;
        pub fn mprotect(addr: *mut c_void, len: usize, prot: i32) -> i32;
        pub fn clock_gettime(clock_id: i32, ts: *mut timespec) -> i32;
    }
}


mod os_mem {
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::set_lib::*;
use crate::libc::{self, MAP_ANONYMOUS, MAP_NORESERVE, MAP_PRIVATE, PROT_NONE, PROT_READ, PROT_WRITE};

verus!{

#[verus::trusted]
pub open spec fn page_size() -> int { 4096 }

#[verus::trusted]
pub fn get_page_size() -> (u: usize)
    ensures u == page_size()
{ 4096 }

#[verus::trusted]
#[verifier(external_body)]
pub tracked struct OsMem {
    no_copy: NoCopy,
}

#[verus::trusted]
pub ghost struct MemProtect {
    pub read: bool,
    pub write: bool,
}

#[verus::trusted]
pub ghost struct OsMemData {
    pub byte_addr: int,
    pub mem_protect: MemProtect,
}

#[verus::trusted]
pub tracked struct MemChunk {
    pub os: Map<int, OsMem>,
    pub points_to: PointsToRaw,
}

#[verus::trusted]
impl MemChunk {
    pub open spec fn wf(&self) -> bool {
        self.wf_os()
    }

    pub open spec fn wf_os(&self) -> bool {
        forall |addr: int|
            #[trigger] self.os.dom().contains(addr)
             ==> self.os[addr]@.byte_addr == addr
    }

    #[verifier::inline]
    pub open spec fn range_os(&self) -> Set<int> {
        self.os.dom()
    }

    pub open spec fn range_os_rw(&self) -> Set<int> {
        self.os.dom().filter(|addr| self.os[addr]@.mem_protect == MemProtect { read: true, write: true })
    }

    pub open spec fn range_os_none(&self) -> Set<int> {
        self.os.dom().filter(|addr| self.os[addr]@.mem_protect == MemProtect { read: false, write: false })
    }

    #[verifier::inline]
    pub open spec fn range_points_to(&self) -> Set<int> {
        self.points_to.dom()
    }

    pub open spec fn has_pointsto_for_all_read_write(&self) -> bool {
        self.range_os_rw() <= self.range_points_to()
    }

    pub open spec fn os_has_range(&self, start: int, len: int) -> bool {
        set_int_range(start, start + len) <= self.range_os()
    }

    pub open spec fn os_exact_range(&self, start: int, len: int) -> bool {
        set_int_range(start, start + len) =~= self.range_os()
    }

    pub open spec fn os_has_range_read_write(&self, start: int, len: int) -> bool {
        set_int_range(start, start + len) <= self.range_os_rw()
    }

    pub open spec fn os_has_range_no_read_write(&self, start: int, len: int) -> bool {
        set_int_range(start, start + len) <= self.range_os_none()
    }

    pub open spec fn has_new_pointsto(&self, the_old: &MemChunk) -> bool {
        self.os.dom() == the_old.os.dom()
        && the_old.points_to.dom().subset_of(self.points_to.dom())
        && (forall |addr: int|
            #[trigger] the_old.os.dom().contains(addr)
              ==> the_old.os[addr]@.mem_protect == MemProtect { read: true, write: true }
              ==> self.os[addr]@.mem_protect == MemProtect { read: true, write: true }
        )
        && (forall |addr: int|
              self.os.dom().contains(addr)
              && self.os[addr]@.mem_protect == MemProtect { read: true, write: true }
              && the_old.os[addr]@.mem_protect != MemProtect { read: true, write: true }
              ==> #[trigger] self.points_to.dom().contains(addr)
        )
    }
}

#[verus::trusted]
impl OsMem {
    pub uninterp spec fn view(self) -> OsMemData;
}

#[verus::trusted]
pub const MAP_FAILED: usize = usize::MAX;



#[verus::trusted]
#[verifier::external_body]
pub fn mmap_prot_none(hint: *mut u8, len: usize) -> (pt: (*mut u8, Tracked<MemChunk>))
    requires
        hint as int % page_size() == 0,
        len as int % page_size() == 0,
    ensures
        pt.0.addr() != MAP_FAILED ==> pt.1@.wf(),
        pt.0.addr() != MAP_FAILED ==> pt.1@.os_exact_range(pt.0 as int, len as int),
        pt.0.addr() != MAP_FAILED ==> pt.1@.os_has_range_no_read_write(pt.0 as int, len as int),
        pt.0.addr() != MAP_FAILED ==> pt.0.addr() + len < usize::MAX,
        pt.0.addr() != MAP_FAILED ==> pt.0@.provenance == pt.1@.points_to.provenance(),
{
    let p = _mmap_prot_none(hint as *mut libc::c_void, len);
    let p = if p == libc::MAP_FAILED { MAP_FAILED as *mut u8 } else { p as *mut u8 };
    (p, Tracked::assume_new())
}

#[verus::trusted]
#[verifier::external_body]
pub fn mmap_prot_read_write(hint: *mut u8, len: usize) -> (pt: (*mut u8, Tracked<MemChunk>))
    requires
        hint as int % page_size() == 0,
        len as int % page_size() == 0,
    ensures
        pt.0.addr() != MAP_FAILED ==> pt.1@.wf(),
        pt.0.addr() != MAP_FAILED ==> pt.1@.os_exact_range(pt.0 as int, len as int),
        pt.0.addr() != MAP_FAILED ==> pt.1@.os_has_range_read_write(pt.0 as int, len as int),
        pt.0.addr() != MAP_FAILED ==> pt.1@.has_pointsto_for_all_read_write(),
        pt.0.addr() != MAP_FAILED ==> pt.0.addr() + len < usize::MAX,
        pt.0.addr() != MAP_FAILED ==> pt.0 as int % page_size() == 0,
        pt.0.addr() != MAP_FAILED ==> pt.0@.provenance == pt.1@.points_to.provenance(),
{
    let p = _mmap_prot_read_write(hint as *mut libc::c_void, len);
    let p = if p == libc::MAP_FAILED { MAP_FAILED as *mut u8 } else { p as *mut u8 };
    (p, Tracked::assume_new())
}

#[verus::trusted]
#[verifier::external_body]
pub fn mprotect_prot_none(addr: *mut u8, len: usize, Tracked(mem): Tracked<&mut MemChunk>)
    requires
        addr as int % page_size() == 0,
        len as int % page_size() == 0,

        old(mem).wf(),
        old(mem).os_exact_range(addr as int, len as int),
        old(mem).has_pointsto_for_all_read_write(),
        old(mem).points_to.provenance() == addr@.provenance,
    ensures
        final(mem).wf(),
        final(mem).os_exact_range(addr as int, len as int),
        final(mem).os_has_range_no_read_write(addr as int, len as int),
        final(mem).points_to.dom() === Set::empty(),
        final(mem).points_to.provenance() == old(mem).points_to.provenance(),
{
    _mprotect_prot_none(addr as *mut libc::c_void, len);
}

#[verus::trusted]
#[verifier::external_body]
pub fn mprotect_prot_read_write(addr: *mut u8, len: usize, Tracked(mem): Tracked<&mut MemChunk>)
    requires
        addr as int % page_size() == 0,
        len as int % page_size() == 0,
        old(mem).wf(),
        old(mem).os_exact_range(addr as int, len as int),
        old(mem).points_to.provenance() == addr@.provenance,
    ensures
        final(mem).wf(),
        final(mem).os_exact_range(addr as int, len as int),
        final(mem).os_has_range_read_write(addr as int, len as int),
        final(mem).has_new_pointsto(&*old(mem)),
        old(mem).has_pointsto_for_all_read_write() ==>
             final(mem).has_pointsto_for_all_read_write(),
        final(mem).points_to.provenance() == old(mem).points_to.provenance(),
{
    _mprotect_prot_read_write(addr as *mut libc::c_void, len);
}


#[verus::trusted]
#[verifier::external]
fn _mmap_prot_read_write(hint_addr: *mut libc::c_void, len: usize) -> *mut libc::c_void {
    unsafe {
        libc::mmap(
            hint_addr,
            len,
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
            -1,
            0)
    }
}

#[verifier::external]
fn _mmap_prot_none(hint_addr: *mut libc::c_void, len: usize) -> *mut libc::c_void {
    unsafe {
        libc::mmap(
            hint_addr,
            len,
            PROT_NONE,
            MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
            -1,
            0)
    }
}

#[verus::trusted]
#[verifier::external]
fn _mprotect_prot_read_write(addr: *mut libc::c_void, len: usize) {
    unsafe {
        let res = libc::mprotect(
            addr as *mut libc::c_void,
            len,
            PROT_READ | PROT_WRITE);
        if res != 0 {
            panic!("mprotect failed");
        }
    }
}

#[verus::trusted]
#[verifier::external]
fn _mprotect_prot_none(addr: *mut libc::c_void, len: usize) {
    unsafe {
        let res = libc::mprotect(
            addr as *mut libc::c_void,
            len,
            PROT_NONE);
        if res != 0 {
            panic!("mprotect failed");
        }
    }
}


#[verus::trusted]
#[verifier::external_type_specification]
pub struct ExTimespec(libc::timespec);

#[verus::trusted]
#[inline(always)]
#[verifier::external_body]
pub fn clock_gettime_monotonic() -> libc::timespec
{
    let mut ts = libc::timespec { tv_sec: 0, tv_nsec: 0 };
    unsafe { libc::clock_gettime(libc::CLOCK_MONOTONIC, &mut ts); }
    ts
}


}
}
mod thread {
#![allow(unused_imports)]

use vstd::prelude::*;

verus!{


#[verus::trusted]
pub struct ThreadId {
    pub thread_id: u64,
}


#[verus::trusted]
#[cfg(verus_keep_ghost)]
#[verifier(external_body)]
pub tracked struct IsThread { }

#[verus::trusted]
#[cfg(verus_keep_ghost)]
impl !Sync for IsThread { }

#[verus::trusted]
#[cfg(verus_keep_ghost)]
impl !Send for IsThread { }

#[cfg(not(verus_keep_ghost))]
#[verifier(external_body)]
#[verus::trusted]
pub tracked struct IsThread { _no_send_sync: core::marker::PhantomData<*const ()> }

#[verus::trusted]
impl IsThread {
    pub uninterp spec fn view(&self) -> ThreadId;


    #[verifier(external_body)]
    pub proof fn agrees(tracked self, tracked other: IsThread)
        ensures self@ == other@,
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    pub proof fn nonzero(tracked self)
        ensures self@.thread_id != 0,
    {
        unimplemented!()
    }
}

#[verus::trusted]
#[verifier(external)]
impl Clone for IsThread {
    #[cfg(verus_keep_ghost)]
    fn clone(&self) -> Self {
        IsThread { }
    }
    #[cfg(not(verus_keep_ghost))]
    fn clone(&self) -> Self {
        IsThread { _no_send_sync: Default::default() }
    }
}

#[verus::trusted]
impl Copy for IsThread { }


#[verus::trusted]
#[cfg(feature = "override_system_allocator")]
#[cfg(target_os = "linux")]
#[verifier::external_body]
pub fn thread_id() -> (res: (ThreadId, Tracked<IsThread>))
    ensures res.1@@ == res.0,
{
    let id_u64: u64 = unsafe { crate::thread_id_helper() };
    let id = ThreadId { thread_id: id_u64 };
    (id, Tracked::assume_new())
}


#[verus::trusted]
#[cfg(not(feature = "override_system_allocator"))]
#[verifier::external_body]
pub fn thread_id() -> (res: (ThreadId, Tracked<IsThread>))
    ensures res.1@@ == res.0,
{
    let id: std::thread::ThreadId = std::thread::current().id();
    let id = ThreadId { thread_id: id.as_u64().into() };
    (id, Tracked::assume_new())
}



#[verus::trusted]
#[verifier::external_body]
pub proof fn ghost_thread_id() -> (tracked res: IsThread)
{
    unimplemented!();
}

#[verus::trusted]
#[verifier::external_fn_specification]
pub fn ex_yield_now() {
    std::thread::yield_now()
}

}
}


mod tokens {
#![allow(unused_imports)]

use verus_state_machines_macros::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use crate::config::SLICE_SIZE;



verus!{

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

    pub idx: nat,

    pub slice_idx: nat,

    pub block_size: nat,
}

impl PageId {
    pub open spec fn range_from(&self, lo: int, hi: int) -> Set<PageId> {
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
        (page_id.idx + (crate::layout::start_offset(block_size as int) + idx * block_size) / (SLICE_SIZE as int)) as nat
    }

    pub open spec fn slice_idx_is_right(&self) -> bool {
        self.slice_idx == BlockId::get_slice_idx(self.page_id, self.idx, self.block_size)
    }
}


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


pub ghost struct PageState {
    pub offset: int,


    pub block_size: nat,
    pub num_blocks: nat,

    pub shared_access: PageSharedAccess,
    pub is_enabled: bool,
}

pub ghost struct SegmentState {

    pub shared_access: SegmentSharedAccess,
    pub is_enabled: bool,
}

pub ghost struct BlockState {
    pub segment_shared_access: SegmentSharedAccess,
    pub page_shared_access: PageSharedAccess,
    pub page_slice_shared_access: PageSharedAccess,

    pub heap_id: Option<HeapId>,
}


pub ghost struct HeapState {

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



use crate::types::SegmentSharedAccess;
use crate::types::SegmentLocalAccess;

use crate::types::PageSharedAccess;
use crate::types::PageLocalAccess;

use crate::types::HeapSharedAccess;
use crate::types::HeapLocalAccess;


pub ghost enum Actor {
    Idle,
    Abandoned,
}

pub ghost enum DelayFreeingActor {
    HeapUnknown,
    Heap(HeapId, HeapSharedAccess, PageSharedAccess),
}

pub type ThreadId = crate::thread::ThreadId;

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

#[verifier::external_body]
proof fn segment_u_max_not_in(s: Set<SegmentId>)
    ensures forall |id: SegmentId| s.contains(id) ==> id.uniq < segment_u_max(s) + 1,
    decreases s.len(),
{
    unimplemented!()
}

pub open spec fn segment_get_unused_uniq_field(s: Set<SegmentId>) -> int {
    segment_u_max(s) + 1
}

#[verifier::external_body]
pub proof fn lemma_segment_get_unused_uniq_field(s: Set<SegmentId>)
    ensures forall |id: SegmentId| s.contains(id) ==> id.uniq != segment_get_unused_uniq_field(s)
{
    unimplemented!()
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

#[verifier::external_body]
proof fn heap_u_max_not_in(s: Set<HeapId>)
    ensures forall |id: HeapId| s.contains(id) ==> id.uniq < heap_u_max(s) + 1,
    decreases s.len(),
{
    unimplemented!()
}

pub open spec fn heap_get_unused_uniq_field(s: Set<HeapId>) -> int {
    heap_u_max(s) + 1
}

#[verifier::external_body]
pub proof fn lemma_heap_get_unused_uniq_field(s: Set<HeapId>)
    ensures forall |id: HeapId| s.contains(id) ==> id.uniq != heap_get_unused_uniq_field(s)
{
    unimplemented!()
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

        #[sharding(bool)] pub right_to_set_inst: bool,
        #[sharding(persistent_option)] pub my_inst: Option<InstanceId>,

        #[sharding(map)] pub thread_local_state: Map<ThreadId, ThreadState>,
        #[sharding(set)] pub right_to_use_thread: Set<ThreadId>,


        #[sharding(map)] pub block: Map<BlockId, BlockState>,


        #[sharding(map)] pub thread_of_segment: Map<SegmentId, ThreadId>,
        #[sharding(map)] pub delay: Map<PageId, DelayState>,
        #[sharding(map)] pub heap_of_page: Map<PageId, HeapId>,


        #[sharding(map)] pub actor: Map<ThreadId, Actor>,
        #[sharding(map)] pub delay_actor: Map<PageId, DelayFreeingActor>,


        #[sharding(storage_map)] pub segment_shared_access: Map<SegmentId, SegmentSharedAccess>,

        #[sharding(storage_map)] pub page_shared_access: Map<PageId, PageSharedAccess>,

        #[sharding(storage_map)] pub heap_shared_access: Map<HeapId, HeapSharedAccess>,

        #[sharding(set)] pub reserved_uniq: Set<HeapId>,

        #[sharding(map)] pub thread_checked_state: Map<ThreadId, ThreadCheckedState>,



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
                by { assert(pre.segment_shared_access.dom().contains(segment_id)); };
        }
    }



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

            let new_pages = ts.pages.union_prefer_right(page_map);
            let ts2 = ThreadState { pages: new_pages, .. ts };

            add thread_local_state += [ thread_id => ts2 ];



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
                false
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
    }

    #[inductive(create_thread_mk_tokens)]
    fn create_thread_mk_tokens_inductive(pre: Self, post: Self, thread_id: ThreadId, thread_state: ThreadState) {
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
        let ts1 = pre.thread_local_state[thread_id];
        let ts2 = post.thread_local_state[thread_id];
        assert forall |block_id: BlockId| #[trigger] post.block.dom().contains(block_id)
            implies post.inv_block_id_valid_for_block(block_id)
        by {
            if post.block.dom().contains(block_id)
              && !pre.block.dom().contains(block_id)
            {
                assert(Self::okay_to_add_block(ts1, page_id, block_id.idx, block_size));
            }
            assert(post.segment_shared_access.dom().contains(block_id.page_id.segment_id));
            assert(post.inv_block_id_valid_for_block(block_id));
        }
    }

    #[verifier::external_body]
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
        unimplemented!()
    }

    spec fn blocks_has(blocks: Map<BlockId, BlockState>, page_id: PageId, i: int) -> bool {
        exists |block_id| blocks.dom().contains(block_id) && block_id.page_id == page_id
            && block_id.idx == i
    }

    #[inductive(page_destroy_block_tokens)]
    fn page_destroy_block_tokens_inductive(pre: Self, post: Self, thread_id: ThreadId, page_id: PageId, blocks: Map<BlockId, BlockState>) {
        let ts = pre.thread_local_state[thread_id];
        assert(forall |block_id: BlockId| blocks.dom().contains(block_id) ==>
            pre.block.dom().contains(block_id));

        Self::block_map_with_len(blocks, page_id, ts.pages[page_id].num_blocks as int);
        assert forall |block_id: BlockId| #[trigger] post.block.dom().contains(block_id)
            implies post.inv_block_id_valid_for_block(block_id)
        by {
            if block_id.page_id == page_id {
                assert(Self::blocks_has(blocks, page_id, block_id.idx as int));
                assert(post.inv_block_id_valid_for_block(block_id));
            } else {
                assert(post.inv_block_id_valid_for_block(block_id));
            }
        }
    }

    #[inductive(page_disable)]
    fn page_disable_inductive(pre: Self, post: Self, thread_id: ThreadId, page_id: PageId, n_slices: nat) {
        assert forall |pid: PageId| #[trigger] post.delay_actor.dom().contains(pid)
            implies post.inv_delay_actor_for_page(pid)
        by {
            if pid == page_id {
                assert(post.inv_delay_actor_for_page(pid));
            } else if page_id.range_from(0, n_slices as int).contains(pid) {
                assert(post.inv_delay_actor_for_page(pid));
            } else {
                assert(post.inv_delay_actor_for_page(pid));
            }
        }


    }

    #[inductive(page_destroy_tokens)]
    fn page_destroy_tokens_inductive(pre: Self, post: Self, thread_id: ThreadId, page_id: PageId, n_slices: nat) {
        assert(page_id.range_from(0, n_slices as int).contains(page_id));
        assert forall |block_id: BlockId| #[trigger] post.block.dom().contains(block_id)
            implies post.inv_block_id_valid_for_block(block_id)
        by {
            if block_id.page_id == page_id {
                assert(post.inv_block_id_valid_for_block(block_id));
            } else if page_id.range_from(0, n_slices as int).contains(block_id.page_id) {
                assert(post.inv_block_id_valid_for_block(block_id));
            } else {
                assert(post.inv_block_id_valid_for_block(block_id));
            }
        }
        let ts = pre.thread_local_state[thread_id];
        assert(page_id.range_from(0, n_slices as int).contains(page_id));
        assert(!ts.pages[page_id].is_enabled);
        assert(!pre.delay_actor.dom().contains(page_id));
    }

    #[inductive(block_tokens_distinct)]
    fn block_tokens_distinct_inductive(pre: Self, post: Self, block_id1: BlockId, block_id2: BlockId) { }

    #[inductive(block_in_range)]
    fn block_in_range_inductive(pre: Self, post: Self, thread_id: ThreadId, block_id: BlockId) { }


    #[inductive(page_check_delay_state)]
    fn page_check_delay_state_inductive(pre: Self, post: Self, thread_id: ThreadId, page_id: PageId) { }

    #[inductive(reserve_uniq_identifier)]
    fn reserve_uniq_identifier_inductive(pre: Self, post: Self) {
        lemma_heap_get_unused_uniq_field(pre.heap_shared_access.dom() + pre.reserved_uniq);
        let u = heap_get_unused_uniq_field(pre.heap_shared_access.dom() + pre.reserved_uniq);
        assert forall |hid1: HeapId, hid2: HeapId|
            post.reserved_uniq.contains(hid1)
            && post.heap_shared_access.dom().contains(hid2)
            implies hid1.uniq != hid2.uniq
        by {
            if hid1.uniq == u {
                assert((pre.heap_shared_access.dom() + pre.reserved_uniq).contains(hid2));
                assert(hid1.uniq != hid2.uniq);
            } else {
                assert(hid1.uniq != hid2.uniq);
            }
        }
    }


}}
}
mod types {
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::modes::*;
use vstd::*;
use vstd::cell::pcell::*;
use vstd::cell::pcell;
use vstd::atomic_ghost::*;
use vstd::shared::Shared;
use verus_state_machines_macros::*;

use crate::config::*;
use crate::tokens::{Mim, PageId, ThreadId, SegmentId, HeapId, PageState, HeapState, SegmentState, TldId};
use crate::linked_list::{LL, ThreadLLSimple, ThreadLLWithDelayBits};
use crate::layout::{is_page_ptr, is_page_ptr_opt, is_heap_ptr, is_tld_ptr, block_start_at, is_segment_ptr};
use crate::page_organization::*;
use crate::os_mem::MemChunk;
use crate::commit_mask::CommitMask;
use crate::bin_sizes::{valid_bin_idx, size_of_bin, smallest_bin_fitting_size};
use crate::arena::{ArenaId, MemId};

verus!{


#[repr(C)]
pub struct PageInner {
    pub flags0: u8,

    pub capacity: u16,
    pub reserved: u16,

    pub flags1: u8,
    pub flags2: u8,

    pub free: LL,

    pub used: u32,

    pub xblock_size: u32,
    pub local_free: LL,
}

impl PageInner {
    pub open spec fn wf(&self, page_id: PageId, page_state: PageState, mim_instance: Mim::Instance) -> bool {
        &&& page_state.block_size == self.xblock_size as nat

        &&& self.free.wf()
        &&& self.free.fixed_page()
        &&& self.free.page_id() == page_id
        &&& self.free.block_size() == page_state.block_size
        &&& self.free.instance() == mim_instance
        &&& self.free.heap_id().is_none()

        &&& self.local_free.wf()
        &&& self.local_free.fixed_page()
        &&& self.local_free.page_id() == page_id
        &&& self.local_free.block_size() == page_state.block_size
        &&& self.local_free.instance() == mim_instance
        &&& self.local_free.heap_id().is_none()

        &&& self.used + self.free.len() + self.local_free.len() == page_state.num_blocks

        &&& self.local_free.fixed_page()
        &&& self.free.fixed_page()

        &&& self.local_free.block_size() == page_state.block_size
        &&& self.free.block_size() == page_state.block_size

        &&& self.capacity <= self.reserved
        &&& self.capacity == page_state.num_blocks

        &&& self.xblock_size > 0
    }

    pub open spec fn zeroed(&self) -> bool {
        &&& self.capacity == 0
        &&& self.reserved == 0
        &&& self.free.wf() && self.free.len() == 0
        &&& self.used == 0
        &&& self.xblock_size == 0
        &&& self.local_free.wf() && self.local_free.len() == 0
    }

    pub open spec fn zeroed_except_block_size(&self) -> bool {
        &&& self.capacity == 0
        &&& self.reserved == 0
        &&& self.free.wf() && self.free.len() == 0
        &&& self.used == 0
        &&& self.local_free.wf() && self.local_free.len() == 0
    }
}

tokenized_state_machine!{ BoolAgree {
    fields {
        #[sharding(variable)] pub x: bool,
        #[sharding(variable)] pub y: bool,
    }
    init!{
        initialize(b: bool) {
            init x = b;
            init y = b;
        }
    }
    transition!{
        set(b: bool) {
            assert(pre.x == pre.y);
            update x = b;
            update y = b;
        }
    }
    property!{
        agree() {
            assert(pre.x == pre.y);
        }
    }
    #[invariant]
    pub spec fn inv_eq(&self) -> bool {
        self.x == self.y
    }
    #[inductive(initialize)] fn initialize_inductive(post: Self, b: bool) { }
    #[inductive(set)] fn set_inductive(pre: Self, post: Self, b: bool) { }
}}

struct_with_invariants!{
    pub struct AtomicHeapPtr {
        pub atomic: AtomicPtr<Heap, _, (BoolAgree::y, Option<Mim::heap_of_page>), _>,

        pub instance: Ghost<Mim::Instance>,
        pub page_id: Ghost<PageId>,
        pub emp: Tracked<BoolAgree::x>,
        pub emp_inst: Tracked<BoolAgree::Instance>,
    }

    pub open spec fn wf(&self, instance: Mim::Instance, page_id: PageId) -> bool {
        predicate {
            self.instance == instance
            && self.page_id == page_id
            && self.emp@.instance_id() == self.emp_inst@.id()
        }
        invariant
            on atomic
            with (instance, page_id, emp, emp_inst)
            is (v: *mut Heap, all_g: (BoolAgree::y, Option<Mim::heap_of_page>))
        {
            let (is_emp, g_opt) = all_g;
            is_emp.instance_id() == emp_inst@.id()
            && (match g_opt {
                None => is_emp.value(),
                Some(g) => {
                    &&& !is_emp.value()
                    &&& g.instance_id() == instance@.id()
                    &&& g.key() == page_id
                    &&& is_heap_ptr(v, g.value())
                }
            })
        }
    }
}

impl AtomicHeapPtr {
    pub open spec fn is_empty(&self) -> bool { self.emp@.value() }

    pub fn empty() -> (ahp: AtomicHeapPtr)
        ensures ahp.is_empty(),
    {
        let tracked (Tracked(emp_inst), Tracked(emp_x), Tracked(emp_y)) = BoolAgree::Instance::initialize(true);
        let ghost g = (Ghost(arbitrary()), Ghost(arbitrary()), Tracked(emp_x), Tracked(emp_inst));
        AtomicHeapPtr {
            page_id: Ghost(arbitrary()),
            instance: Ghost(arbitrary()),
            emp: Tracked(emp_x),
            emp_inst: Tracked(emp_inst),
            atomic: AtomicPtr::new(Ghost(g), core::ptr::null_mut(), Tracked((emp_y, None))),
        }
    }

    #[inline(always)]
    pub fn disable(&mut self) -> (hop: Tracked<Mim::heap_of_page>)
        requires old(self).wf(old(self).instance@, old(self).page_id@),
            !old(self).is_empty(),
        ensures
            final(self).is_empty(),
            hop@.instance_id() == old(self).instance@.id(),
            hop@.key() == old(self).page_id@,
    {
        let tracked mut heap_of_page;
        atomic_with_ghost!(
            &self.atomic => no_op();
            ghost g => {
                let tracked (mut y, heap_of_page_opt) = g;
                self.emp_inst.borrow().set(true, self.emp.borrow_mut(), &mut y);
                heap_of_page = heap_of_page_opt.tracked_unwrap();
                g = (y, None);
            }
        );
        Tracked(heap_of_page)
    }
}

#[repr(C)]
pub struct Page {
    pub count: PCell<u32>,
    pub offset: u32,

    pub inner: PCell<PageInner>,
    pub xthread_free: ThreadLLWithDelayBits,
    pub xheap: AtomicHeapPtr,
    pub prev: PCell<*mut Page>,
    pub next: PCell<*mut Page>,

    pub padding: usize,
}

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

pub tracked struct PageFullAccess {
    pub tracked s: PageSharedAccess,
    pub tracked l: PageLocalAccess,
}

impl Page {
    pub open spec fn wf(&self, page_id: PageId, block_size: nat, mim_instance: Mim::Instance) -> bool {
        self.xthread_free.wf()
          && !self.xthread_free.is_empty()
          && self.xthread_free.instance == mim_instance
          && self.xthread_free.page_id() == page_id
          && self.xthread_free.block_size() == block_size

          && self.xheap.wf(mim_instance, page_id)
          && !self.xheap.is_empty()
    }

    pub open spec fn wf_secondary(&self, mim_instance: Mim::Instance) -> bool {
        self.xthread_free.wf()
          && self.xthread_free.is_empty()
          && self.xthread_free.instance == mim_instance
    }

    pub open spec fn wf_unused(&self, mim_instance: Mim::Instance) -> bool {
        self.xthread_free.wf()
          && self.xthread_free.is_empty()
          && self.xthread_free.instance == mim_instance
    }
}

pub open spec fn page_differ_only_in_offset(page1: Page, page2: Page) -> bool {
    page2 == Page { offset: page2.offset, .. page1 }
}

pub open spec fn psa_differ_only_in_offset(psa1: PageSharedAccess, psa2: PageSharedAccess) -> bool {
    psa1.points_to.is_init()
    && psa2.points_to.is_init()
    && page_differ_only_in_offset(
        psa1.points_to.value(),
        psa2.points_to.value())
    && psa1.points_to.ptr() == psa2.points_to.ptr()
}

impl PageSharedAccess {
    pub open spec fn wf(&self, page_id: PageId, block_size: nat, mim_instance: Mim::Instance) -> bool {
        &&& is_page_ptr(self.points_to.ptr(), page_id)
        &&& self.points_to.is_init()
        &&& self.points_to.value().wf(page_id, block_size, mim_instance)
        &&& self.exposed.provenance() == self.points_to.ptr()@.provenance
    }

    pub open spec fn wf_secondary(&self, page_id: PageId, block_size: nat, mim_instance: Mim::Instance) -> bool {
        &&& is_page_ptr(self.points_to.ptr(), page_id)
        &&& self.points_to.is_init()
        &&& self.points_to.value().wf_secondary(mim_instance)
        &&& self.exposed.provenance() == self.points_to.ptr()@.provenance
    }

    pub open spec fn wf_unused(&self, page_id: PageId, mim_instance: Mim::Instance) -> bool {
        &&& is_page_ptr(self.points_to.ptr(), page_id)
        &&& self.points_to.is_init()
        &&& self.points_to.value().wf_unused(mim_instance)
        &&& self.exposed.provenance() == self.points_to.ptr()@.provenance
    }
}

pub open spec fn wf_reserved(block_size: int, reserved: int, count: int) -> bool {
    reserved * block_size + crate::layout::start_offset(block_size) <= count * SLICE_SIZE
}

impl PageLocalAccess {
    pub open spec fn wf(&self, page_id: PageId, page_state: PageState, mim_instance: Mim::Instance) -> bool {
        (page_state.offset == 0 ==> page_state.shared_access.wf(page_id, page_state.block_size, mim_instance))
        && (page_state.offset != 0 ==> page_state.shared_access.wf_secondary(page_id, page_state.block_size, mim_instance))
        && page_state.is_enabled

        && match page_state.shared_access.points_to.opt_value() {
            MemContents::Init(page) => {
                &&& self.inner.id() == page.inner.id()
                &&& self.count.id() == page.count.id()
                &&& self.prev.id() == page.prev.id()
                &&& self.next.id() == page.next.id()

                &&& match (self.count.value(), self.inner.value(), self.prev.value(), self.next.value()) {
                    (count, page_inner, prev, next) => {

                        &&& (page_state.offset == 0 ==>
                            page_inner.wf(page_id, page_state, mim_instance)
                            && wf_reserved(page_state.block_size as int,
                                page_inner.reserved as int, count as int)
                        )
                        &&& (page_state.offset != 0 ==> page_inner.zeroed_except_block_size())
                    }
                }
            }
            MemContents::Uninit => false,
        }
    }

    pub open spec fn wf_unused(&self, page_id: PageId, shared_access: PageSharedAccess, popped: Popped, mim_instance: Mim::Instance) -> bool {
        shared_access.wf_unused(page_id, mim_instance)

        && match shared_access.points_to.opt_value() {
            MemContents::Init(page) => {
                &&& self.count.id() == page.count.id()
                &&& self.inner.id() == page.inner.id()
                &&& self.prev.id() == page.prev.id()
                &&& self.next.id() == page.next.id()

                &&& self.inner.value().zeroed_except_block_size()
            }
            MemContents::Uninit => false,
        }
    }
}

impl PageFullAccess {
    pub open spec fn wf_empty_page_global(&self) -> bool {
        &&& self.s.points_to.is_init()
        &&& self.s.points_to.value().inner.id() == self.l.inner.id()
        &&& self.s.exposed.provenance() == self.s.points_to.ptr()@.provenance
        &&& self.l.inner.value().zeroed()
    }
}


#[derive(Clone, Copy)]
pub enum SegmentKind {
    Normal,
    Huge,
}

#[repr(C)]
pub struct SegmentHeaderMain {
    pub memid: usize,
    pub mem_is_pinned: bool,
    pub mem_is_large: bool,
    pub mem_is_committed: bool,
    pub mem_alignment: usize,
    pub mem_align_offset: usize,
    pub allow_decommit: bool,
    pub decommit_expire: i64,
    pub decommit_mask: CommitMask,
    pub commit_mask: CommitMask,
}

#[repr(C)]
pub struct SegmentHeaderMain2 {
    pub next: *mut SegmentHeader,
    pub abandoned: usize,
    pub abandoned_visits: usize,
    pub used: usize,
    pub cookie: usize,
    pub segment_slices: usize,
    pub segment_info_slices: usize,
    pub kind: SegmentKind,
    pub slice_entries: usize,
}

struct_with_invariants!{
    #[repr(C)]
    pub struct SegmentHeader {
        pub main: PCell<SegmentHeaderMain>,
        pub abandoned_next: usize,
        pub main2: PCell<SegmentHeaderMain2>,

        pub thread_id: AtomicU64<_, Mim::thread_of_segment, _>,

        pub instance: Ghost<Mim::Instance>,
        pub segment_id: Ghost<SegmentId>,
    }

    pub open spec fn wf(&self, instance: Mim::Instance, segment_id: SegmentId) -> bool {
        predicate {
            self.instance == instance
            && self.segment_id == segment_id
        }
        invariant
            on thread_id
            with (instance, segment_id)
            is (v: u64, g: Mim::thread_of_segment)
        {
            &&& g.instance_id() == instance@.id()
            &&& g.key() == segment_id
            &&& g.value() == ThreadId { thread_id: v }
        }
    }
}

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


pub struct PageQueue {
    pub first: *mut Page,
    pub last: *mut Page,
    pub block_size: usize,
}

impl Clone for PageQueue {
    fn clone(&self) -> (s: Self)
        ensures s == *self
    {
        PageQueue { first: self.first, last: self.last, block_size: self.block_size }
    }
}
impl Copy for PageQueue { }

#[repr(C)]
pub struct Heap {
    pub tld_ptr: TldPtr,

    pub pages_free_direct: PCell<[*mut Page; 129]>,
    pub pages: PCell<[PageQueue; 75]>,

    pub thread_delayed_free: ThreadLLSimple,
    pub thread_id: ThreadId,
    pub arena_id: ArenaId,
    pub page_count: PCell<usize>,
    pub page_retired_min: PCell<usize>,
    pub page_retired_max: PCell<usize>,
    pub no_reclaim: bool,

    pub page_empty_ptr: *mut Page,
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

impl Heap {
    pub open spec fn wf(&self, heap_id: HeapId, tld_id: TldId, mim_instance: InstanceId) -> bool {
        &&& self.thread_delayed_free.wf()
        &&& self.thread_delayed_free.instance@.id() == mim_instance
        &&& self.thread_delayed_free.heap_id == heap_id
        &&& self.tld_ptr.wf()
        &&& self.tld_ptr.tld_id == tld_id
    }
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

pub open spec fn pages_free_direct_match(pfd_val: *mut Page, p_val: *mut Page, emp: *mut Page) -> bool {
    (p_val as int == 0 ==> pfd_val as int == emp as int)
    && (p_val as int != 0 ==> pfd_val as int == p_val as int)
}

pub open spec fn pages_free_direct_is_correct(pfd: Seq<*mut Page>, pages: Seq<PageQueue>, emp: *mut Page) -> bool {
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
              && self.pages.value()[0].block_size == 8
              && self.pages.value()[BIN_FULL as int].block_size ==
                    8 * (524288 + 2)

              && self.pages_free_direct.value()@.len() == PAGES_DIRECT
              && self.pages.value()@.len() == BIN_FULL + 1
        }
    }
}



pub struct SegmentsTld {
    pub span_queue_headers: [SpanQueueHeader; 32],
    pub count: usize,
    pub peak_count: usize,
    pub current_size: usize,
    pub peak_size: usize,
}

pub struct SpanQueueHeader {
    pub first: *mut Page,
    pub last: *mut Page,
}

impl Clone for SpanQueueHeader {
    fn clone(&self) -> (s: Self)
        ensures s == *self
    {
        SpanQueueHeader { first: self.first, last: self.last }
    }
}
impl Copy for SpanQueueHeader { }

pub struct Tld {
    pub heap_backing: *mut Heap,

    pub segments: SegmentsTld,
}

pub tracked struct Local {
    pub ghost thread_id: ThreadId,

    pub tracked my_inst: Mim::my_inst,
    pub tracked instance: Mim::Instance,
    pub tracked thread_token: Mim::thread_local_state,
    pub tracked checked_token: Mim::thread_checked_state,
    pub tracked is_thread: crate::thread::IsThread,

    pub ghost heap_id: HeapId,
    pub tracked heap: HeapLocalAccess,

    pub ghost tld_id: TldId,
    pub tracked tld: raw_ptr::PointsTo<Tld>,

    pub tracked segments: Map<SegmentId, SegmentLocalAccess>,

    pub tracked pages: Map<PageId, PageLocalAccess>,
    pub ghost psa: Map<PageId, PageSharedAccess>,

    pub tracked unused_pages: Map<PageId, PageSharedAccess>,

    pub ghost page_organization: PageOrg::State,

    pub tracked page_empty_global: Shared<PageFullAccess>,
}

pub open spec fn common_preserves(l1: Local, l2: Local) -> bool {
    l1.heap_id == l2.heap_id
    && l1.tld_id == l2.tld_id
    && l1.instance == l2.instance
}

impl Local {
    pub open(crate) spec fn inst(&self) -> Mim::Instance {
        self.instance
    }

    pub open(crate) spec fn wf(&self) -> bool {
        self.wf_main()
          && self.page_organization.popped == Popped::No
    }

    pub open spec fn wf_basic(&self) -> bool {
        &&& is_tld_ptr(self.tld.ptr(), self.tld_id)

        &&& self.thread_token.instance_id() == self.instance.id()
        &&& self.thread_token.key() == self.thread_id

        &&& self.thread_token.value().segments.dom() == self.segments.dom()

        &&& self.thread_token.value().heap_id == self.heap_id
        &&& self.heap.wf_basic(self.heap_id, self.thread_token.value().heap, self.tld_id, self.instance.id())

        &&& self.thread_token.value().heap.shared_access.points_to.value().page_empty_ptr == self.page_empty_global@.s.points_to.ptr()
        &&& self.page_empty_global@.wf_empty_page_global()
    }

    pub open spec fn wf_main(&self) -> bool {
        &&& is_tld_ptr(self.tld.ptr(), self.tld_id)

        &&& self.thread_token.instance_id() == self.instance.id()
        &&& self.thread_token.key() == self.thread_id
        &&& self.thread_id == self.is_thread@

        &&& self.checked_token.instance_id() == self.instance.id()
        &&& self.checked_token.key() == self.thread_id

        &&& self.my_inst.instance_id() == self.instance.id()
        &&& self.my_inst.value() == self.instance.id()

        &&& self.thread_token.value().segments.dom() == self.segments.dom()

        &&& self.thread_token.value().heap_id == self.heap_id
        &&& self.heap.wf(self.heap_id, self.thread_token.value().heap, self.tld_id, self.instance.id(), self.page_empty_global@.s.points_to.ptr())

        &&& (forall |page_id|
            #[trigger] self.pages.dom().contains(page_id) ==>
              (self.unused_pages.dom().contains(page_id) <==>
                !self.thread_token.value().pages.dom().contains(page_id)))

        &&& self.thread_token.value().pages.dom().subset_of(self.pages.dom())
        &&& (forall |page_id|
            #[trigger] self.pages.dom().contains(page_id) ==>
              self.thread_token.value().pages.dom().contains(page_id) ==>
                self.pages.index(page_id).wf(
                  page_id,
                  self.thread_token.value().pages.index(page_id),
                  self.instance,
                )
            )

        &&& (forall |page_id|
            #[trigger] self.pages.dom().contains(page_id) ==>
              self.unused_pages.dom().contains(page_id) ==>
                self.pages.index(page_id).wf_unused(page_id, self.unused_pages[page_id], self.page_organization.popped, self.instance))

        &&& (forall |segment_id|
            #[trigger] self.segments.dom().contains(segment_id) ==>
              self.segments[segment_id].wf(
                segment_id,
                self.thread_token.value().segments.index(segment_id),
                self.instance,
              )
            )
        &&& (forall |segment_id|
            #[trigger] self.segments.dom().contains(segment_id) ==>
              self.mem_chunk_good(segment_id)
            )

        &&& self.tld.is_init()

        &&& self.page_organization_valid()

        &&& self.page_empty_global@.wf_empty_page_global()
    }

    pub open spec fn page_organization_valid(&self) -> bool
    {
        &&& self.page_organization.invariant()
        &&& self.tld.is_init()

        &&& page_organization_queues_match(self.page_organization.unused_dlist_headers,
                self.tld.value().segments.span_queue_headers@)

        &&& page_organization_used_queues_match(self.page_organization.used_dlist_headers,
                self.heap.pages.value()@)

        &&& page_organization_pages_match(self.page_organization.pages,
                self.pages, self.psa, self.page_organization.popped)

        &&& page_organization_segments_match(self.page_organization.segments, self.segments)

        &&& (forall |page_id: PageId| #[trigger] self.page_organization.pages.dom().contains(page_id) ==>
            (!self.page_organization.pages[page_id].is_used <==> self.unused_pages.dom().contains(page_id)))


        &&& (forall |page_id|
          #[trigger] self.page_organization.pages.dom().contains(page_id)
            ==> self.page_organization.pages[page_id].is_used
            ==> page_organization_matches_token_page(
                    self.page_organization.pages[page_id],
                    self.thread_token.value().pages[page_id]))

        &&& (forall |page_id: PageId| (#[trigger] self.unused_pages.dom().contains(page_id)) ==>
            self.page_organization.pages.dom().contains(page_id))

        &&& (forall |page_id: PageId| #[trigger] self.unused_pages.dom().contains(page_id) ==>
            self.unused_pages[page_id] == self.psa[page_id])

        &&& (forall |page_id: PageId| #[trigger] self.thread_token.value().pages.dom().contains(page_id) ==>
            self.thread_token.value().pages[page_id].shared_access == self.psa[page_id])
    }

    pub open spec fn page_state(&self, page_id: PageId) -> PageState
        recommends self.thread_token.value().pages.dom().contains(page_id)
    {
        self.thread_token.value().pages.index(page_id)
    }

    pub open spec fn page_inner(&self, page_id: PageId) -> PageInner
        recommends
            self.pages.dom().contains(page_id),
    {
        *self.pages.index(page_id).inner.value()
    }



    pub proof fn take_thread_token(tracked &mut self) -> (tracked tt: Mim::thread_local_state)
        ensures
            *final(self) == (Local { thread_token: final(self).thread_token, .. *old(self) }),
            tt == old(self).thread_token,
    {
        let tracked mut t = Mim::thread_local_state::arbitrary();
        tracked_swap(&mut t, &mut self.thread_token);
        t
    }

    pub proof fn take_checked_token(tracked &mut self) -> (tracked tt: Mim::thread_checked_state)
        ensures
            *final(self) == (Local { checked_token: final(self).checked_token, .. *old(self) }),
            tt == old(self).checked_token,
    {
        let tracked mut t = Mim::thread_checked_state::arbitrary();
        tracked_swap(&mut t, &mut self.checked_token);
        t
    }

    pub open spec fn commit_mask(&self, segment_id: SegmentId) -> CommitMask {
        self.segments[segment_id].main.value().commit_mask
    }

    pub open spec fn decommit_mask(&self, segment_id: SegmentId) -> CommitMask {
        self.segments[segment_id].main.value().decommit_mask
    }

    pub open spec fn is_used_primary(&self, page_id: PageId) -> bool {
        self.page_organization.pages.dom().contains(page_id)
          && self.page_organization.pages[page_id].is_used
          && self.page_organization.pages[page_id].offset == Some(0nat)
    }

    pub open spec fn page_reserved(&self, page_id: PageId) -> int {
        self.pages[page_id].inner.value().reserved as int
    }

    pub open spec fn page_count(&self, page_id: PageId) -> int {
        self.pages[page_id].count.value() as int
    }

    pub open spec fn page_capacity(&self, page_id: PageId) -> int {
        self.pages[page_id].inner.value().capacity as int
    }

    pub open spec fn block_size(&self, page_id: PageId) -> int {
        self.pages[page_id].inner.value().xblock_size as int
    }
}

pub open spec fn page_organization_queues_match(
    org_queues: Seq<DlistHeader>,
    queues: Seq<SpanQueueHeader>,
) -> bool {
    org_queues.len() == queues.len()
    && (forall |i: int| 0 <= i < org_queues.len() ==>
        is_page_ptr_opt((#[trigger] queues[i]).first, org_queues[i].first))
    && (forall |i: int| 0 <= i < org_queues.len() ==>
        is_page_ptr_opt((#[trigger] queues[i]).last, org_queues[i].last))
}

pub open spec fn page_organization_used_queues_match(
    org_queues: Seq<DlistHeader>,
    queues: Seq<PageQueue>,
) -> bool {
    org_queues.len() == queues.len()
    && (forall |i: int| 0 <= i < org_queues.len() ==>
        is_page_ptr_opt((#[trigger] queues[i]).first, org_queues[i].first))
    && (forall |i: int| 0 <= i < org_queues.len() ==>
        is_page_ptr_opt((#[trigger] queues[i]).last, org_queues[i].last))
}


pub open spec fn page_organization_pages_match(
    org_pages: Map<PageId, PageData>,
    pages: Map<PageId, PageLocalAccess>,
    psa: Map<PageId, PageSharedAccess>,
    popped: Popped,
) -> bool {
    &&& org_pages.dom() =~= pages.dom()
    &&& org_pages.dom() =~= psa.dom()


    &&& (forall |page_id| #[trigger] org_pages.dom().contains(page_id) ==>
        page_organization_pages_match_data(org_pages[page_id], pages[page_id], psa[page_id], page_id, popped))
}

pub open spec fn page_organization_pages_match_data(
    page_data: PageData,
    pla: PageLocalAccess,
    psa: PageSharedAccess,
    page_id: PageId,
    popped: Popped) -> bool
{
    psa.points_to.is_init() && (
    match (*pla.count.value(), *pla.inner.value(), *pla.prev.value(), *pla.next.value()) {
        (count, inner, prev, next) => {
            &&& (match page_data.count {
                None => true,
                Some(c) => count as int == c
            })
            &&& (match page_data.full {
                None => true,
                Some(b) => inner.in_full() == b,
            })
            &&& (match page_data.offset {
                None => true,
                Some(o) => psa.points_to.value().offset as int ==
                            o * SIZEOF_PAGE_HEADER
            })
            &&& (match page_data.dlist_entry {
                None => true,
                Some(page_queue_data) => {
                    &&& is_page_ptr_opt(prev, page_queue_data.prev)
                    &&& is_page_ptr_opt(next, page_queue_data.next)
                }
            })
            &&& (match page_data.page_header_kind {
                None => {
                    (page_id.idx == 0 ==> {
                      &&& !page_data.is_used
                      &&& (match popped {
                          Popped::SegmentCreating(sid) if sid == page_id.segment_id =>
                              true,
                          _ => inner.xblock_size != 0
                      })
                      &&& (!popped.is_SegmentCreating() ==> inner.xblock_size != 0)
                    })
                    && (page_id.idx != 0 ==> page_data.offset == Some(0nat) ==> (
                        (!(popped.is_Ready() && popped.get_Ready_0() == page_id) &&
                            !(popped.is_VeryUnready() && popped.get_VeryUnready_0() == page_id.segment_id && popped.get_VeryUnready_1() == page_id.idx))
                          ==>
                        (page_data.is_used <==> inner.xblock_size != 0)
                    ))
                }
                Some(PageHeaderKind::Normal(_, bsize)) => {
                    &&& page_id.idx != 0
                    &&& page_data.is_used
                    &&& inner.xblock_size != 0
                    &&& inner.xblock_size == bsize
                    &&& page_data.is_used
                    &&& page_data.offset == Some(0nat)
                }
            })
        }
    })
}

pub open spec fn page_organization_segments_match(
    org_segments: Map<SegmentId, SegmentData>,
    segments: Map<SegmentId, SegmentLocalAccess>,
) -> bool {
    org_segments.dom() =~= segments.dom()
    && (forall |segment_id: SegmentId| segments.dom().contains(segment_id) ==>
        org_segments[segment_id].used == segments[segment_id].main2.value().used)
}

pub open spec fn page_organization_matches_token_page(
    page_data: PageData,
    page_state: PageState) -> bool
{
    page_data.offset.is_some()
    && page_data.offset.unwrap() == page_state.offset
}



pub struct HeapPtr {
    pub heap_ptr: *mut Heap,
    pub heap_id: Ghost<HeapId>,
}

impl Clone for HeapPtr {
    #[inline(always)]
    fn clone(&self) -> (s: Self)
        ensures *self == s
    {
        HeapPtr { heap_ptr: self.heap_ptr, heap_id: Ghost(self.heap_id@) }
    }
}
impl Copy for HeapPtr { }

impl HeapPtr {
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
        is_heap_ptr(self.heap_ptr, self.heap_id@)
    }

    #[verifier(inline)]
    pub open spec fn is_in(&self, local: Local) -> bool {
        local.heap_id == self.heap_id@
    }

    #[inline(always)]
    pub fn get_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (heap: &'a Heap)
        requires
            local.wf_basic(),
            self.wf(),
            self.is_in(*local),
        ensures
            MemContents::Init(*heap) == local.thread_token.value().heap.shared_access.points_to.opt_value(),
    {
        let tracked perm = &local.instance.thread_local_state_guards_heap(
            local.thread_id, &local.thread_token).points_to;
        ptr_ref(self.heap_ptr, Tracked(perm))
    }

    #[inline(always)]
    pub fn get_pages<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (pages: &'a [PageQueue; 75])
        requires
            local.wf_basic(),
            self.wf(),
            self.is_in(*local),
        ensures
            *pages == *local.heap.pages.value()
    {
        self.get_ref(Tracked(local)).pages.borrow(Tracked(&local.heap.pages))
    }

    #[inline(always)]
    pub fn get_page_count<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page_count: usize)
        requires
            local.wf_basic(),
            self.wf(),
            self.is_in(*local),
        ensures
            page_count == *local.heap.page_count.value()
    {
        *self.get_ref(Tracked(local)).page_count.borrow(Tracked(&local.heap.page_count))
    }

    #[inline(always)]
    pub fn set_page_count<'a>(&self, Tracked(local): Tracked<&mut Local>, page_count: usize)
        requires
            old(local).wf_basic(),
            self.wf(),
            self.is_in(*old(local)),
        ensures
            local_page_count_update(*old(local), *final(local)),
    {
        let tracked perm = &local.instance.thread_local_state_guards_heap(
            local.thread_id, &local.thread_token).points_to;
        let heap = ptr_ref(self.heap_ptr, Tracked(perm));
        *heap.page_count.borrow_mut(Tracked(&mut local.heap.page_count)) = page_count;
    }

    #[inline(always)]
    pub fn get_page_retired_min<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page_retired_min: usize)
        requires
            local.wf_basic(),
            self.wf(),
            self.is_in(*local),
        ensures
            page_retired_min == local.heap.page_retired_min.value()
    {
        *self.get_ref(Tracked(local)).page_retired_min.borrow(Tracked(&local.heap.page_retired_min))
    }

    #[inline(always)]
    pub fn set_page_retired_min<'a>(&self, Tracked(local): Tracked<&mut Local>, page_retired_min: usize)
        requires
            old(local).wf_basic(),
            self.wf(),
            self.is_in(*old(local)),
        ensures
            local_page_retired_min_update(*old(local), *final(local)),
    {
        let tracked perm = &local.instance.thread_local_state_guards_heap(
            local.thread_id, &local.thread_token).points_to;
        let heap = ptr_ref(self.heap_ptr, Tracked(perm));
        *heap.page_retired_min.borrow_mut(Tracked(&mut local.heap.page_retired_min)) = page_retired_min;
    }

    #[inline(always)]
    pub fn get_page_retired_max<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page_retired_max: usize)
        requires
            local.wf_basic(),
            self.wf(),
            self.is_in(*local),
        ensures
            page_retired_max == local.heap.page_retired_max.value()
    {
        *self.get_ref(Tracked(local)).page_retired_max.borrow(Tracked(&local.heap.page_retired_max))
    }

    #[inline(always)]
    pub fn set_page_retired_max<'a>(&self, Tracked(local): Tracked<&mut Local>, page_retired_max: usize)
        requires
            old(local).wf_basic(),
            self.wf(),
            self.is_in(*old(local)),
        ensures
            local_page_retired_max_update(*old(local), *final(local)),
    {
        let tracked perm = &local.instance.thread_local_state_guards_heap(
            local.thread_id, &local.thread_token).points_to;
        let heap = ptr_ref(self.heap_ptr, Tracked(perm));
        *heap.page_retired_max.borrow_mut(Tracked(&mut local.heap.page_retired_max)) = page_retired_max;
    }

    #[inline(always)]
    pub fn get_pages_free_direct<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (pages: &'a [*mut Page; 129])
        requires
            local.wf_basic(),
            self.wf(),
            self.is_in(*local),
        ensures
            *pages == local.heap.pages_free_direct.value()
    {
        self.get_ref(Tracked(local)).pages_free_direct.borrow(Tracked(&local.heap.pages_free_direct))
    }

    #[inline(always)]
    pub fn get_arena_id<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (arena_id: ArenaId)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            arena_id
             == local.thread_token.value().heap.shared_access.points_to.value().arena_id,
    {
        self.get_ref(Tracked(local)).arena_id
    }

    #[inline(always)]
    pub fn get_page_empty(&self, Tracked(local): Tracked<&Local>)
        -> (res: (*mut Page, Tracked<Shared<PageFullAccess>>))
    requires
        local.wf_basic(),
        self.wf(),
        self.is_in(*local),
    ensures ({ let (page_ptr, pfa) = res; {
        pfa@@.wf_empty_page_global()
        && pfa@@.s.points_to.ptr() == page_ptr
        && page_ptr.addr() != 0
        && page_ptr == local.page_empty_global@.s.points_to.ptr()
    }})
    {
        let page_ptr = self.get_ref(Tracked(local)).page_empty_ptr;
        let tracked pfa = local.page_empty_global.clone();
        proof { const_facts(); pfa.borrow().s.points_to.is_nonnull(); }
        (page_ptr, Tracked(pfa))
    }
}

pub open spec fn local_page_count_update(loc1: Local, loc2: Local) -> bool {
    &&& loc2 == Local { heap: loc2.heap, .. loc1 }
    &&& loc2.heap == HeapLocalAccess { page_count: loc2.heap.page_count, .. loc1.heap }
    &&& loc1.heap.page_count.id() == loc2.heap.page_count.id()
}

pub open spec fn local_page_retired_min_update(loc1: Local, loc2: Local) -> bool {
    &&& loc2 == Local { heap: loc2.heap, .. loc1 }
    &&& loc2.heap == HeapLocalAccess { page_retired_min: loc2.heap.page_retired_min, .. loc1.heap }
    &&& loc1.heap.page_retired_min.id() == loc2.heap.page_retired_min.id()
}

pub open spec fn local_page_retired_max_update(loc1: Local, loc2: Local) -> bool {
    &&& loc2 == Local { heap: loc2.heap, .. loc1 }
    &&& loc2.heap == HeapLocalAccess { page_retired_max: loc2.heap.page_retired_max, .. loc1.heap }
    &&& loc1.heap.page_retired_max.id() == loc2.heap.page_retired_max.id()
}



pub struct TldPtr {
    pub tld_ptr: *mut Tld,
    pub tld_id: Ghost<TldId>,
}

impl Clone for TldPtr {
    #[inline(always)]
    fn clone(&self) -> (s: Self)
        ensures *self == s
    {
        TldPtr { tld_ptr: self.tld_ptr, tld_id: Ghost(self.tld_id@) }
    }
}
impl Copy for TldPtr { }


impl TldPtr {
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
        is_tld_ptr(self.tld_ptr, self.tld_id@)
    }

    #[verifier(inline)]
    pub open spec fn is_in(&self, local: Local) -> bool {
        local.tld_id == self.tld_id@
    }

    #[inline(always)]
    pub fn get_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (tld: &'a Tld)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            MemContents::Init(*tld) == local.tld.opt_value()
    {
        ptr_ref(self.tld_ptr, Tracked(&local.tld))
    }

    #[inline(always)]
    pub fn get_mut<'a>(&self, Tracked(local): Tracked<&'a mut Local>) -> (tld: &'a mut Tld)
        requires
            local.tld.ptr() == self.tld_ptr,
            local.tld.opt_value().is_init(),
        ensures
            MemContents::Init(*tld) == old(local).tld.opt_value(),
            *final(local) == (Local { tld: final(local).tld, .. *old(local) }),
            final(local).tld.ptr() == old(local).tld.ptr(),
            final(local).tld.opt_value() == MemContents::Init(*final(tld)),
    {
        ptr_mut_ref(self.tld_ptr, Tracked(&mut local.tld))
    }

    #[inline(always)]
    pub fn get_segments_count(&self, Tracked(local): Tracked<&Local>) -> (count: usize)
        requires
            self.wf(), self.is_in(*local), local.wf_main(),
        ensures count == local.tld.value().segments.count,
    {
        self.get_ref(Tracked(local)).segments.count
    }
}

pub struct SegmentPtr {
    pub segment_ptr: *mut SegmentHeader,
    pub segment_id: Ghost<SegmentId>,
}

impl Clone for SegmentPtr {
    #[inline(always)]
    fn clone(&self) -> (s: Self)
        ensures *self == s
    {
        SegmentPtr { segment_ptr: self.segment_ptr, segment_id: Ghost(self.segment_id@) }
    }
}
impl Copy for SegmentPtr { }

impl SegmentPtr {
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
        is_segment_ptr(self.segment_ptr, self.segment_id@)
    }

    #[verifier(inline)]
    pub open spec fn is_in(&self, local: Local) -> bool {
        local.segments.dom().contains(self.segment_id@)
    }

    #[inline(always)]
    pub fn is_null(&self) -> (b: bool)
        ensures b == (self.segment_ptr as int == 0)
    {
        self.segment_ptr.addr() == 0
    }

    #[inline(always)]
    pub fn null() -> (s: Self)
        ensures s.segment_ptr as int == 0
    {
        SegmentPtr { segment_ptr: core::ptr::null_mut(),
            segment_id: Ghost(arbitrary())
        }
    }

    #[inline(always)]
    pub fn get_page_header_ptr(&self, idx: usize) -> (page_ptr: PagePtr)
        requires self.wf(),
            0 <= idx <= SLICES_PER_SEGMENT
        ensures page_ptr.wf(),
            page_ptr.page_id@.segment_id == self.segment_id@,
            page_ptr.page_id@.idx == idx,
    {
        proof { const_facts(); }
        let j = self.segment_ptr.addr() + SIZEOF_SEGMENT_HEADER + idx * SIZEOF_PAGE_HEADER;
        return PagePtr {
            page_ptr: self.segment_ptr.with_addr(j) as *mut Page,
            page_id: Ghost(PageId { segment_id: self.segment_id@, idx: idx as nat }),
        };
    }

    #[inline]
    pub fn get_page_after_end(&self) -> (page_ptr: *mut Page)
        requires self.wf(),
        ensures page_ptr as int == crate::layout::page_header_start(
            PageId { segment_id: self.segment_id@, idx: SLICES_PER_SEGMENT as nat })
    {
        proof { const_facts(); }
        let j = self.segment_ptr.addr()
          + SIZEOF_SEGMENT_HEADER
          + SLICES_PER_SEGMENT as usize * SIZEOF_PAGE_HEADER;
        self.segment_ptr.with_addr(j) as *mut Page
    }

    #[inline(always)]
    pub fn get_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (segment: &'a SegmentHeader)
        requires
            local.thread_token.value().segments.dom().contains(self.segment_id@),
            local.thread_token.value().segments[self.segment_id@].shared_access.points_to.ptr() == self.segment_ptr,
            local.thread_token.value().segments[self.segment_id@].shared_access.points_to.is_init(),
            local.thread_token.value().segments[self.segment_id@].is_enabled,
            local.thread_token.key() == local.thread_id,
            local.thread_token.instance_id() == local.instance.id(),
            self.wf(),
            self.is_in(*local),
        ensures
            MemContents::Init(*segment) == local.thread_token.value().segments.index(self.segment_id@).shared_access.points_to.opt_value(),
    {
        let tracked perm =
            &local.instance.thread_local_state_guards_segment(
                local.thread_id, self.segment_id@, &local.thread_token).points_to;
        ptr_ref(self.segment_ptr, Tracked(perm))
    }

    #[inline(always)]
    pub fn get_main_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (segment_header_main: &'a SegmentHeaderMain)
        requires
            self.wf(), self.is_in(*local),
            local.thread_token.value().segments.dom().contains(self.segment_id@),
            local.thread_token.value().segments[self.segment_id@].shared_access.points_to.ptr() == self.segment_ptr,
            local.thread_token.value().segments.index(self.segment_id@).shared_access.points_to.is_init(),
            local.thread_token.value().segments[self.segment_id@].is_enabled,
            local.thread_token.key() == local.thread_id,
            local.thread_token.instance_id() == local.instance.id(),
            local.thread_token.value().segments.index(self.segment_id@).shared_access.points_to.value().main.id()
                == local.segments[self.segment_id@].main.id(),
            local.segments.dom().contains(self.segment_id@),
        ensures *segment_header_main == local.segments.index(self.segment_id@).main.value()
    {
        let segment = self.get_ref(Tracked(local));
        segment.main.borrow(Tracked(&local.segments.tracked_borrow(self.segment_id@).main))
    }

    #[inline(always)]
    pub fn get_main2_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (segment_header_main2: &'a SegmentHeaderMain2)
        requires local.wf_main(), self.wf(), self.is_in(*local),
        ensures *segment_header_main2 == local.segments.index(self.segment_id@).main2.value()
    {
        let segment = self.get_ref(Tracked(local));
        segment.main2.borrow(Tracked(&local.segments.tracked_borrow(self.segment_id@).main2))
    }

    #[inline(always)]
    pub fn get_commit_mask<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (cm: &'a CommitMask)
        requires self.wf(), self.is_in(*local),
            local.wf_main(),
        ensures cm == local.segments[self.segment_id@].main.value().commit_mask
    {
        &self.get_main_ref(Tracked(local)).commit_mask
    }

    #[inline(always)]
    pub fn get_decommit_mask<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (cm: &'a CommitMask)
        requires self.wf(), self.is_in(*local),
            local.wf_main(),
        ensures cm == local.segments[self.segment_id@].main.value().decommit_mask
    {
        &self.get_main_ref(Tracked(local)).decommit_mask
    }

    #[inline(always)]
    pub fn get_decommit_expire(&self, Tracked(local): Tracked<&Local>) -> (i: i64)
        requires self.wf(), self.is_in(*local),
            local.wf_main(),
        ensures i == local.segments[self.segment_id@].main.value().decommit_expire
    {
        self.get_main_ref(Tracked(local)).decommit_expire
    }


    #[inline(always)]
    pub fn get_allow_decommit(&self, Tracked(local): Tracked<&Local>) -> (b: bool)
        requires self.wf(), self.is_in(*local),
            local.wf_main(),
        ensures b == local.segments[self.segment_id@].main.value().allow_decommit
    {
        self.get_main_ref(Tracked(local)).allow_decommit
    }

    #[inline(always)]
    pub fn get_used(&self, Tracked(local): Tracked<&Local>) -> (used: usize)
        requires self.wf(), self.is_in(*local), local.wf_main(),
        ensures used == local.segments[self.segment_id@].main2.value().used,
    {
        self.get_main2_ref(Tracked(local)).used
    }

    #[inline(always)]
    pub fn get_abandoned(&self, Tracked(local): Tracked<&Local>) -> (abandoned: usize)
        requires self.wf(), self.is_in(*local), local.wf_main(),
        ensures abandoned == local.segments[self.segment_id@].main2.value().abandoned,
    {
        self.get_main2_ref(Tracked(local)).abandoned
    }

    #[inline(always)]
    pub fn get_mem_is_pinned(&self, Tracked(local): Tracked<&Local>) -> (mem_is_pinned: bool)
        requires self.wf(), self.is_in(*local), local.wf_main(),
        ensures mem_is_pinned == local.segments[self.segment_id@].main.value().mem_is_pinned,
    {
        self.get_main_ref(Tracked(local)).mem_is_pinned
    }

    #[inline(always)]
    pub fn is_abandoned(&self, Tracked(local): Tracked<&Local>) -> (is_ab: bool)
        requires self.wf(), self.is_in(*local), local.wf_main(),
    {
        self.get_ref(Tracked(local)).thread_id.load() == 0
    }

    #[inline(always)]
    pub fn get_segment_kind(&self, Tracked(local): Tracked<&Local>) -> (kind: SegmentKind)
        requires self.wf(), self.is_in(*local), local.wf_main(),
        ensures kind == local.segments[self.segment_id@].main2.value().kind,
    {
        self.get_main2_ref(Tracked(local)).kind
    }

    #[inline(always)]
    pub fn is_kind_huge(&self, Tracked(local): Tracked<&Local>) -> (b: bool)
        requires self.wf(), self.is_in(*local), local.wf_main(),
        ensures b == (local.segments[self.segment_id@].main2.value().kind == SegmentKind::Huge)
    {
        let kind = self.get_main2_ref(Tracked(local)).kind;
        matches!(kind, SegmentKind::Huge)
    }
}

pub struct PagePtr {
    pub page_ptr: *mut Page,
    pub page_id: Ghost<PageId>,
}

impl Clone for PagePtr {
    #[inline(always)]
    fn clone(&self) -> (s: Self)
        ensures *self == s
    {
        PagePtr { page_ptr: self.page_ptr, page_id: Ghost(self.page_id@) }
    }
}
impl Copy for PagePtr { }

impl PagePtr {
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
        is_page_ptr(self.page_ptr, self.page_id@)
          && self.page_ptr.addr() != 0
    }

    #[verifier(inline)]
    pub open spec fn is_in(&self, local: Local) -> bool {
        local.pages.dom().contains(self.page_id@)
    }

    pub open spec fn is_empty_global(&self, local: Local) -> bool {
        self.page_ptr == local.page_empty_global@.s.points_to.ptr()
    }

    #[verifier(inline)]
    pub open spec fn is_used_and_primary(&self, local: Local) -> bool {
        local.pages.dom().contains(self.page_id@)
          && local.thread_token.value().pages.dom().contains(self.page_id@)
          && local.thread_token.value().pages[self.page_id@].offset == 0
    }

    #[verifier(inline)]
    pub open spec fn is_in_unused(&self, local: Local) -> bool {
        local.unused_pages.dom().contains(self.page_id@)
    }

    #[verifier(inline)]
    pub open spec fn is_used(&self, local: Local) -> bool {
        local.pages.dom().contains(self.page_id@)
          && local.thread_token.value().pages.dom().contains(self.page_id@)
    }

    #[inline(always)]
    pub fn null() -> (s: Self)
        ensures s.page_ptr == core::ptr::null_mut::<Page>(),
    {
        PagePtr { page_ptr: core::ptr::null_mut(),
            page_id: Ghost(arbitrary())
        }
    }

    #[inline(always)]
    pub fn is_null(&self) -> (b: bool)
        ensures b == (self.page_ptr.addr() == 0)
    {
        self.page_ptr.addr() == 0
    }

    #[inline(always)]
    pub fn get_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page: &'a Page)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            !self.is_in_unused(*local) ==>
              MemContents::Init(*page) == local.thread_token.value().pages.index(self.page_id@)
                                .shared_access.points_to.opt_value(),
            self.is_in_unused(*local) ==>
              MemContents::Init(*page) == local.unused_pages[self.page_id@].points_to.opt_value(),
    {
        let tracked perm = if self.is_in_unused(*local) {
            &local.unused_pages.tracked_borrow(self.page_id@).points_to
        } else {
            &local.instance.thread_local_state_guards_page(
                local.thread_id, self.page_id@, &local.thread_token).points_to
        };

        ptr_ref(self.page_ptr, Tracked(perm))
    }

    #[inline(always)]
    pub fn get_inner_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page_inner: &'a PageInner)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            *page_inner == local.pages.index(self.page_id@).inner.value()
    {
        let page = self.get_ref(Tracked(local));
        page.inner.borrow(Tracked(
            &local.pages.tracked_borrow(self.page_id@).inner
            ))
    }

    #[inline(always)]
    pub fn get_inner_ref_maybe_empty<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page_inner: &'a PageInner)
        requires
            local.wf_main(),
            !self.is_empty_global(*local) ==> (
              self.wf() && self.is_in(*local)
            )
        ensures
            !self.is_empty_global(*local) ==> (
                *page_inner == local.pages.index(self.page_id@).inner.value()
            ),
            self.is_empty_global(*local) ==> (
                *page_inner == local.page_empty_global@.l.inner.value()
            ),
    {
        let tracked perm = if self.is_empty_global(*local) {
            &local.page_empty_global.borrow().s.points_to
        } else if self.is_in_unused(*local) {
            &local.unused_pages.tracked_borrow(self.page_id@).points_to
        } else {
            &local.instance.thread_local_state_guards_page(
                local.thread_id, self.page_id@, &local.thread_token).points_to
        };
        let page = ptr_ref(self.page_ptr, Tracked(perm));
        page.inner.borrow(Tracked(
            if self.is_empty_global(*local) {
                &local.page_empty_global.borrow().l.inner
            } else {
                &local.pages.tracked_borrow(self.page_id@).inner
            }
            ))
    }

    #[inline(always)]
    pub fn get_count<'a>(&self, Tracked(local): Tracked<&Local>) -> (count: u32)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            count == local.pages.index(self.page_id@).count.value()
    {
        let page = self.get_ref(Tracked(local));
        *page.count.borrow(Tracked(
            &local.pages.tracked_borrow(self.page_id@).count
            ))
    }

    #[inline(always)]
    pub fn get_next<'a>(&self, Tracked(local): Tracked<&Local>) -> (next: *mut Page)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            next == local.pages.index(self.page_id@).next.value()
    {
        let page = self.get_ref(Tracked(local));
        *page.next.borrow(Tracked(
            &local.pages.tracked_borrow(self.page_id@).next
            ))
    }

    #[inline(always)]
    pub fn get_prev<'a>(&self, Tracked(local): Tracked<&Local>) -> (prev: *mut Page)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            prev == local.pages.index(self.page_id@).prev.value()
    {
        let page = self.get_ref(Tracked(local));
        *page.prev.borrow(Tracked(
            &local.pages.tracked_borrow(self.page_id@).prev
            ))
    }

    #[inline(always)]
    pub fn add_offset(&self, count: usize) -> (p: Self)
        requires
            self.wf(),
            self.page_id@.idx + count <= SLICES_PER_SEGMENT,
        ensures
            p.wf(),
            p.page_id@.segment_id == self.page_id@.segment_id,
            p.page_id@.idx == self.page_id@.idx + count as int,
            p.page_ptr.addr() != 0,
    {
        proof {
            const_facts();
            assert(SIZEOF_PAGE_HEADER == 80);
        }
        let p = self.page_ptr.addr();
        let q = p + count * SIZEOF_PAGE_HEADER;
        PagePtr {
            page_ptr: self.page_ptr.with_addr(q),
            page_id: Ghost(PageId {
                segment_id: self.page_id@.segment_id,
                idx: (self.page_id@.idx + count) as nat,
            })
        }
    }

    #[inline(always)]
    pub fn sub_offset(&self, count: usize) -> (p: Self)
        requires
            self.wf(),
            self.page_id@.idx >= count,
        ensures
            p.wf(),
            p.page_id@.segment_id == self.page_id@.segment_id,
            p.page_id@.idx == self.page_id@.idx - count as int,
            p.page_ptr.addr() != 0,
    {
        proof {
            const_facts();
            assert(SIZEOF_PAGE_HEADER == 80);
            crate::layout::segment_start_ge0(self.page_id@.segment_id);
        }
        let p = self.page_ptr.addr();
        let q = p - count * SIZEOF_PAGE_HEADER;
        let ghost page_id = PageId {
                segment_id: self.page_id@.segment_id,
                idx: (self.page_id@.idx - count) as nat,
            };
        let q = self.page_ptr.with_addr(q);
        proof {
            crate::layout::is_page_ptr_nonzero(q, page_id);
        }
        PagePtr {
            page_ptr: q,
            page_id: Ghost(page_id)
        }
    }

    #[inline(always)]
    pub fn is_gt_0th_slice(&self, segment: SegmentPtr) -> (res: bool)
        requires self.wf(),
            segment.wf(),
            segment.segment_id@ == self.page_id@.segment_id,
    ensures
        res == (self.page_id@.idx > 0),
    {
        proof { const_facts(); }
        self.page_ptr.addr() > segment.get_page_header_ptr(0).page_ptr.addr()
    }

    #[inline(always)]
    pub fn get_index(&self) -> (idx: usize)
        requires self.wf(),
    ensures
        idx == self.page_id@.idx,
    {
        proof { const_facts(); }
        let segment = SegmentPtr::ptr_segment(*self);
        (self.page_ptr.addr() - segment.segment_ptr.addr() - SIZEOF_SEGMENT_HEADER)
            / SIZEOF_PAGE_HEADER
    }

    pub fn slice_start(&self) -> (p: usize)
        requires self.wf(),
        ensures
            p == crate::layout::page_start(self.page_id@),
    {
        proof {
            const_facts();
            assert(SLICE_SIZE as usize == 65536);
        }
        let segment = SegmentPtr::ptr_segment(*self);
        let s = segment.segment_ptr.addr();
        s +
          ((self.page_ptr.addr() - s - SIZEOF_SEGMENT_HEADER) / SIZEOF_PAGE_HEADER)
            * SLICE_SIZE as usize
    }

    #[inline(always)]
    pub fn add_offset_and_check(&self, count: usize, segment: SegmentPtr) -> (res: (Self, bool))
        requires
            self.wf(),
            self.page_id@.idx + count <= SLICES_PER_SEGMENT,
            segment.wf(),
            self.page_id@.segment_id == segment.segment_id@,
        ensures ({ let (p, b) = res; {
            b ==> ({
                &&& p.wf()
                &&& p.page_id@.segment_id == self.page_id@.segment_id
                &&& p.page_id@.idx == self.page_id@.idx + count as int
                &&& p.page_ptr.addr() != 0
            })
            && (b <==> self.page_id@.idx + count < SLICES_PER_SEGMENT)
        }})
    {
        proof {
            const_facts();
            assert(SIZEOF_PAGE_HEADER == 80);
        }
        let p = self.page_ptr.addr();
        let q = p + count * SIZEOF_PAGE_HEADER;
        let page_ptr = PagePtr {
            page_ptr: self.page_ptr.with_addr(q),
            page_id: Ghost(PageId {
                segment_id: self.page_id@.segment_id,
                idx: (self.page_id@.idx + count) as nat,
            })
        };
        let last = segment.get_page_after_end();
        (page_ptr, page_ptr.page_ptr.addr() < last.addr())
    }

    #[inline(always)]
    pub fn get_block_size(&self, Tracked(local): Tracked<&Local>) -> (bsize: u32)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            bsize == local.pages.index(self.page_id@).inner.value().xblock_size
    {
        self.get_inner_ref(Tracked(local)).xblock_size
    }

    #[inline(always)]
    pub fn get_heap(&self, Tracked(local): Tracked<&Local>) -> (heap: HeapPtr)
        requires
            local.wf_main(), self.wf(), self.is_in(*local),
                self.is_used_and_primary(*local),
        ensures heap.wf(), heap.is_in(*local),
    {
        let page_ref = self.get_ref(Tracked(&*local));
        proof {
            assert(page_ref.xheap.wf(local.instance, self.page_id@));
            assert(!page_ref.xheap.is_empty());
            assert(page_ref.xheap.atomic.well_formed());
        }
        let h = atomic_with_ghost!(
            &page_ref.xheap.atomic => load();
            ghost g => {
                page_ref.xheap.emp_inst.borrow().agree(page_ref.xheap.emp.borrow(), &g.0);
                assert(g.0.value() == page_ref.xheap.emp@.value());
                assert(!g.0.value());
                assert(g.1.is_some());
                local.instance.heap_of_page_agree_with_thread_state(
                    self.page_id@,
                    local.thread_token.key(),
                    &local.thread_token,
                    g.1.tracked_borrow(),
                );
                assert(g.1.unwrap().value() == local.heap_id);
            }
        );
        HeapPtr {
            heap_ptr: h,
            heap_id: Ghost(local.heap_id),
        }
    }
}


#[macro_export]
macro_rules! page_get_mut_inner {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::page_get_mut_inner_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! page_get_mut_inner_internal {
    ($ptr:expr, $local:ident, $page_inner:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = $ptr;

            let tracked perm = &$local.instance.thread_local_state_guards_page(
                    $local.thread_id, page_ptr.page_id@, &$local.thread_token).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: mut inner_0, prev: prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_inner = page.inner.borrow_mut(Tracked(&mut inner_0));

            { $body }

            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, PageLocalAccess {
                    inner: inner_0, prev: prev_0, next: next_0, count: count_0
                });
            }
        } }
    }
}

pub use page_get_mut_inner;
pub use page_get_mut_inner_internal;

#[macro_export]
macro_rules! unused_page_get_mut_prev {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::unused_page_get_mut_prev_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! unused_page_get_mut_prev_internal {
    ($ptr:expr, $local:ident, $page_prev:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = ($ptr);
            assert(page_ptr.wf());

            let tracked perm = &$local.unused_pages.tracked_borrow(page_ptr.page_id@).points_to;
            let page = ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: inner_0, prev: mut prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_prev = page.prev.read(Tracked(&mut prev_0));

            { $body }

            page.prev.write(Tracked(&mut prev_0), $page_prev);
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, PageLocalAccess {
                    inner: inner_0, prev: prev_0, next: next_0, count: count_0
                });
            }
        } }
    }
}

pub use unused_page_get_mut_prev;
pub use unused_page_get_mut_prev_internal;

#[macro_export]
macro_rules! unused_page_get_mut_inner {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::unused_page_get_mut_inner_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! unused_page_get_mut_inner_internal {
    ($ptr:expr, $local:ident, $page_inner:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = ($ptr);

            let tracked perm = &$local.unused_pages.tracked_borrow(page_ptr.page_id@).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: mut inner_0, prev: prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_inner = page.inner.borrow_mut(Tracked(&mut inner_0));

            { $body }

            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, PageLocalAccess {
                    inner: inner_0, prev: prev_0, next: next_0, count: count_0
                });
            }
        } }
    }
}

pub use unused_page_get_mut_inner;
pub use unused_page_get_mut_inner_internal;


#[macro_export]
macro_rules! unused_page_get_mut_next {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::unused_page_get_mut_next_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! unused_page_get_mut_next_internal {
    ($ptr:expr, $local:ident, $page_next:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = ($ptr);

            let tracked perm = &$local.unused_pages.tracked_borrow(page_ptr.page_id@).points_to;
            let page = ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: inner_0, prev: prev_0, next: mut next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_next = page.next.read(Tracked(&mut next_0));

            { $body }

            page.next.write(Tracked(&mut next_0), $page_next);
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, PageLocalAccess {
                    inner: inner_0, prev: prev_0, next: next_0, count: count_0
                });
            }
        } }
    }
}

pub use unused_page_get_mut_next;
pub use unused_page_get_mut_next_internal;

#[macro_export]
macro_rules! unused_page_get_mut_count {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::unused_page_get_mut_count_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! unused_page_get_mut_count_internal {
    ($ptr:expr, $local:ident, $page_count:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = ($ptr);

            let tracked perm = &$local.unused_pages.tracked_borrow(page_ptr.page_id@).points_to;
            let page = ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: inner_0, prev: prev_0, next: next_0, count: mut count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_count = page.count.read(Tracked(&mut count_0));

            { $body }

            page.count.write(Tracked(&mut count_0), $page_count);
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, PageLocalAccess {
                    inner: inner_0, prev: prev_0, next: next_0, count: count_0
                });
            }
        } }
    }
}

pub use unused_page_get_mut_count;
pub use unused_page_get_mut_count_internal;


#[macro_export]
macro_rules! unused_page_get_mut {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::unused_page_get_mut_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! unused_page_get_mut_internal {
    ($ptr:expr, $local:ident, $page:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = ($ptr);

            let tracked psa = $local.unused_pages.tracked_remove(page_ptr.page_id@);
            let tracked PageSharedAccess { points_to: mut points_to, exposed } = psa;
            let mut $page = vstd::raw_ptr::ptr_mut_read(page_ptr.page_ptr, Tracked(&mut points_to));

            { $body }

            vstd::raw_ptr::ptr_mut_write(page_ptr.page_ptr, Tracked(&mut points_to), $page);
            proof {
                let tracked psa = PageSharedAccess { points_to: points_to, exposed };
                $local.unused_pages.tracked_insert(page_ptr.page_id@, psa);
            }
        } }
    }
}

pub use unused_page_get_mut;
pub use unused_page_get_mut_internal;


#[macro_export]
macro_rules! used_page_get_mut_prev {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::used_page_get_mut_prev_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! used_page_get_mut_prev_internal {
    ($ptr:expr, $local:ident, $page_prev:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = ($ptr);
            assert(page_ptr.wf());

            let tracked perm = &$local.instance.thread_local_state_guards_page(
                $local.thread_id, page_ptr.page_id@, &$local.thread_token).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: inner_0, prev: mut prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_prev = page.prev.read(Tracked(&mut prev_0));

            { $body }

            page.prev.write(Tracked(&mut prev_0), $page_prev);
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, PageLocalAccess {
                    inner: inner_0, prev: prev_0, next: next_0, count: count_0
                });
            }
        } }
    }
}

pub use used_page_get_mut_prev;
pub use used_page_get_mut_prev_internal;

#[macro_export]
macro_rules! heap_get_pages {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::heap_get_pages_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! heap_get_pages_internal {
    ($ptr:expr, $local:ident, $pages:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let heap_ptr = ($ptr);

            let tracked perm = &$local.instance.thread_local_state_guards_heap(
                $local.thread_id, &$local.thread_token).points_to;
            let heap = vstd::raw_ptr::ptr_ref(heap_ptr.heap_ptr, Tracked(perm));
            let mut $pages = heap.pages.read(Tracked(&mut $local.heap.pages));

            { $body }

            heap.pages.write(Tracked(&mut $local.heap.pages), $pages);
        } }
    }
}

pub use heap_get_pages;
pub use heap_get_pages_internal;

#[macro_export]
macro_rules! heap_get_pages_free_direct {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::heap_get_pages_free_direct_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! heap_get_pages_free_direct_internal {
    ($ptr:expr, $local:ident, $pages_free_direct:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let heap_ptr = ($ptr);

            let tracked perm = &$local.instance.thread_local_state_guards_heap(
                $local.thread_id, &$local.thread_token).points_to;
            let heap = vstd::raw_ptr::ptr_ref(heap_ptr.heap_ptr, Tracked(perm));
            let mut $pages_free_direct = heap.pages_free_direct.read(Tracked(&mut $local.heap.pages_free_direct));

            { $body }

            let mut $pages_free_direct = heap.pages_free_direct.write(Tracked(&mut $local.heap.pages_free_direct), $pages_free_direct);
        } }
    }
}

pub use heap_get_pages_free_direct;
pub use heap_get_pages_free_direct_internal;



#[macro_export]
macro_rules! used_page_get_mut_next {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::used_page_get_mut_next_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! used_page_get_mut_next_internal {
    ($ptr:expr, $local:ident, $page_next:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = ($ptr);
            assert(page_ptr.wf());

            let tracked perm = &$local.instance.thread_local_state_guards_page(
                $local.thread_id, page_ptr.page_id@, &$local.thread_token).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: inner_0, prev: prev_0, next: mut next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_next = page.next.read(Tracked(&mut next_0));

            { $body }

            page.next.write(Tracked(&mut next_0), $page_next);
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, PageLocalAccess {
                    inner: inner_0, prev: prev_0, next: next_0, count: count_0
                });
            }
        } }
    }
}

pub use used_page_get_mut_next;
pub use used_page_get_mut_next_internal;

#[verus::trusted]
#[verifier::external_body]
pub fn print_hex(s: &'static str, u: usize) {
    println!("{:} {:x}", s, u);
}

#[verus::trusted]
#[cfg(feature = "override_system_allocator")]
#[verifier::external_body]
pub fn todo()
    ensures false
{
    std::process::abort();
}

#[verus::trusted]
#[cfg(not(feature = "override_system_allocator"))]
#[verifier::external_body]
pub fn todo()
    ensures false
{
    panic!("todo");
}

#[macro_export]
macro_rules! segment_get_mut_main {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::segment_get_mut_main_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! segment_get_mut_main_internal {
    ($ptr:expr, $local:ident, $segment_main:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let segment_ptr = $ptr;

            let tracked perm = &$local.instance.thread_local_state_guards_segment(
                    $local.thread_id, segment_ptr.segment_id@, &$local.thread_token).points_to;
            let segment = vstd::raw_ptr::ptr_ref(segment_ptr.segment_ptr, Tracked(perm));

            let tracked SegmentLocalAccess { main: mut main_0, mem: mem_0, main2: main2_0 } =
                $local.segments.tracked_remove(segment_ptr.segment_id@);
            let mut $segment_main = segment.main.borrow_mut(Tracked(&mut main_0));

            { $body }

            proof {
                $local.segments.tracked_insert(segment_ptr.segment_id@, SegmentLocalAccess {
                    main: main_0, mem: mem_0, main2: main2_0,
                });
            }
        } }
    }
}

pub use segment_get_mut_main;
pub use segment_get_mut_main_internal;

#[macro_export]
macro_rules! segment_get_mut_main2 {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::segment_get_mut_main2_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! segment_get_mut_main2_internal {
    ($ptr:expr, $local:ident, $segment_main2:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let segment_ptr = $ptr;

            let tracked perm = &$local.instance.thread_local_state_guards_segment(
                    $local.thread_id, segment_ptr.segment_id@, &$local.thread_token).points_to;
            let segment = vstd::raw_ptr::ptr_ref(segment_ptr.segment_ptr, Tracked(perm));

            let tracked SegmentLocalAccess { main: main_0, mem: mem_0, main2: mut main2_0 } =
                $local.segments.tracked_remove(segment_ptr.segment_id@);
            let mut $segment_main2 = segment.main2.borrow_mut(Tracked(&mut main2_0));

            { $body }

            proof {
                $local.segments.tracked_insert(segment_ptr.segment_id@, SegmentLocalAccess {
                    main: main_0, mem: mem_0, main2: main2_0,
                });
            }
        } }
    }
}

pub use segment_get_mut_main2;
pub use segment_get_mut_main2_internal;

#[macro_export]
macro_rules! segment_get_mut_local {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::segment_get_mut_local_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! segment_get_mut_local_internal {
    ($ptr:expr, $local:ident, $segment_local:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let segment_ptr = $ptr;

            let tracked perm = &$local.instance.thread_local_state_guards_segment(
                    $local.thread_id, segment_ptr.segment_id@, &$local.thread_token).points_to;
            let segment = vstd::raw_ptr::ptr_ref(segment_ptr.segment_ptr, Tracked(perm));

            let tracked mut $segment_local =
                $local.segments.tracked_remove(segment_ptr.segment_id@);

            { $body }

            proof {
                $local.segments.tracked_insert(segment_ptr.segment_id@, $segment_local);
            }
        } }
    }
}

pub use segment_get_mut_local;
pub use segment_get_mut_local_internal;


}
}
mod flags {
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::modes::*;
use vstd::*;
use vstd::cell::*;

use crate::types::*;

verus!{

pub closed spec fn flags0_is_reset(u: u8) -> bool { u & 1 != 0 }
pub closed spec fn flags0_is_committed(u: u8) -> bool { u & 2 != 0 }
pub closed spec fn flags0_is_zero_init(u: u8) -> bool { u & 4 != 0 }

pub closed spec fn flags1_in_full(u: u8) -> bool { u & 1 != 0 }
pub closed spec fn flags1_has_aligned(u: u8) -> bool { u & 2 != 0 }

pub closed spec fn flags2_is_zero(u: u8) -> bool { u & 1 != 0 }
pub closed spec fn flags2_retire_expire(u: u8) -> int { (u >> 1u8) as int }

impl PageInner {
    pub open spec fn is_reset(&self) -> bool { flags0_is_reset(self.flags0) }
    pub open spec fn is_committed(&self) -> bool { flags0_is_committed(self.flags0) }
    pub open spec fn is_zero_init(&self) -> bool { flags0_is_zero_init(self.flags0) }

    pub open spec fn in_full(&self) -> bool { flags1_in_full(self.flags1) }
    pub open spec fn has_aligned(&self) -> bool { flags1_has_aligned(self.flags1) }

    pub open spec fn is_zero(&self) -> bool { flags2_is_zero(self.flags2) }
    pub open spec fn retire_expire(&self) -> int { flags2_retire_expire(self.flags2) }


    #[inline(always)]
    pub fn get_is_reset(&self) -> (b: bool)
        ensures b == self.is_reset()
    {
        (self.flags0 & 1) != 0
    }

    #[inline(always)]
    pub fn get_is_committed(&self) -> (b: bool)
        ensures b == self.is_committed()
    {
        (self.flags0 & 2) != 0
    }

    #[inline(always)]
    pub fn get_is_zero_init(&self) -> (b: bool)
        ensures b == self.is_zero_init()
    {
        (self.flags0 & 4) != 0
    }

    #[inline(always)]
    pub fn get_in_full(&self) -> (b: bool)
        ensures b == self.in_full()
    {
        (self.flags1 & 1) != 0
    }

    #[inline(always)]
    pub fn get_has_aligned(&self) -> (b: bool)
        ensures b == self.has_aligned()
    {
        (self.flags1 & 2) != 0
    }

    #[inline(always)]
    pub fn get_is_zero(&self) -> (b: bool)
        ensures b == self.is_zero()
    {
        (self.flags2 & 1) != 0
    }

    #[inline(always)]
    pub fn get_retire_expire(&self) -> (u: u8)
        ensures u == self.retire_expire(),
            u <= 127,
    {
        let x = self.flags2 >> 1u8;
        proof {
            assert(x == (self.flags2 >> 1u8));
            let y = self.flags2;
            assert((y >> 1u8) <= 127) by(bit_vector);
        }
        x
    }

    #[inline(always)]
    pub fn not_full_nor_aligned(&self) -> (b: bool)
        ensures b ==> (!self.in_full() && !self.has_aligned())
    {
        proof {
            let x = self.flags1;
            assert(x == 0 ==> (x & 1u8 == 0u8) && (x & 2u8 == 0u8)) by(bit_vector);
        }
        self.flags1 == 0
    }


    #[inline(always)]
    pub fn set_retire_expire(&mut self, u: u8)
        requires u <= 127,
        ensures
            *final(self) == (PageInner { flags2: final(self).flags2, .. *old(self) }),
            final(self).is_zero() == old(self).is_zero(),
            final(self).retire_expire() == u,
    {
        proof {
            let x = self.flags2;
            assert(((x & 1) | (u << 1)) & 1 == (x & 1)) by(bit_vector);
            assert(((x & 1) | (u << 1)) >> 1 == u) by(bit_vector)
                requires u <= 127;

        }
        self.flags2 = (self.flags2 & 1) | (u << 1u8);
    }

    #[inline(always)]
    pub fn set_is_reset(&mut self, b: bool)
        ensures *final(self) == (PageInner { flags0: final(self).flags0, .. *old(self) }),
            final(self).is_reset() == b,
            final(self).is_committed() == old(self).is_committed(),
            final(self).is_zero_init() == old(self).is_zero_init(),
    {
        proof {
            let y = (if b { 1 } else { 0 });
            let x = self.flags0;
            assert(y == 1 || y == 0 ==> ((x & !1) | y) & 2 == x & 2) by(bit_vector);
            assert(y == 1 || y == 0 ==> ((x & !1) | y) & 4 == x & 4) by(bit_vector);
            assert(y == 1 || y == 0 ==> ((x & !1) | y) & 1 == y) by(bit_vector);
        }
        self.flags0 = (self.flags0 & !1) | (if b { 1 } else { 0 })
    }

    #[inline(always)]
    pub fn set_is_committed(&mut self, b: bool)
        ensures *final(self) == (PageInner { flags0: final(self).flags0, .. *old(self) }),
            final(self).is_reset() == old(self).is_reset(),
            final(self).is_committed() == b,
            final(self).is_zero_init() == old(self).is_zero_init(),
    {
        proof {
            let y: u8 = (if b { 1 } else { 0 });
            let x = self.flags0;
            assert(y == 1 || y == 0 ==> ((x & !2) | (y << 1)) & 1 == x & 1) by(bit_vector);
            assert(y == 1 || y == 0 ==> ((x & !2) | (y << 1)) & 4 == x & 4) by(bit_vector);
            assert(y == 1 || y == 0 ==> (((x & !2) | (y << 1)) & 2 == 0 <==> y == 0)) by(bit_vector);
        }
        self.flags0 = (self.flags0 & !2) | ((if b { 1 } else { 0 }) << 1u8)

    }

    #[inline(always)]
    pub fn set_is_zero_init(&mut self, b: bool)
        ensures *final(self) == (PageInner { flags0: final(self).flags0, .. *old(self) }),
            final(self).is_reset() == old(self).is_reset(),
            final(self).is_committed() == old(self).is_committed(),
            final(self).is_zero_init() == b,
    {
        proof {
            let y: u8 = (if b { 1 } else { 0 });
            let x = self.flags0;
            assert(y == 1 || y == 0 ==> ((x & !4) | (y << 2)) & 1 == x & 1) by(bit_vector);
            assert(y == 1 || y == 0 ==> ((x & !4) | (y << 2)) & 2 == x & 2) by(bit_vector);
            assert(y == 1 || y == 0 ==> (((x & !4) | (y << 2)) & 4 == 0 <==> y == 0)) by(bit_vector);
        }
        self.flags0 = (self.flags0 & !4) | ((if b { 1 } else { 0 }) << 2u8)

    }

    #[inline(always)]
    pub fn set_in_full(&mut self, b: bool)
        ensures *final(self) == (PageInner { flags1: final(self).flags1, .. *old(self) }),
            final(self).has_aligned() == old(self).has_aligned(),
            final(self).in_full() == b,
    {
        proof {
            let y = (if b { 1 } else { 0 });
            let x = self.flags1;
            assert(y == 1 || y == 0 ==> ((x & !1) | y) & 2 == x & 2) by(bit_vector);
            assert(y == 1 || y == 0 ==> ((x & !1) | y) & 1 == y) by(bit_vector);
        }
        self.flags1 = (self.flags1 & !1) | (if b { 1 } else { 0 })
    }

    #[inline(always)]
    pub fn set_has_aligned(&mut self, b: bool)
        ensures *final(self) == (PageInner { flags1: final(self).flags1, .. *old(self) }),
            final(self).has_aligned() == b,
            final(self).in_full() == old(self).in_full(),
    {
        proof {
            let y: u8 = (if b { 1 } else { 0 });
            let x = self.flags1;
            assert(y == 1 || y == 0 ==> ((x & !2) | (y << 1)) & 1 == x & 1) by(bit_vector);
            assert(y == 1 || y == 0 ==> (((x & !2) | (y << 1)) & 2 == 0 <==> y == 0)) by(bit_vector);
        }
        self.flags1 = (self.flags1 & !2) | ((if b { 1 } else { 0 }) << 1u8);
    }

}

}
}
mod layout {
#![allow(unused_imports)]

use verus_state_machines_macros::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::layout::*;

use crate::types::{SegmentHeader, Page, PagePtr, SegmentPtr, todo, Heap, Tld};
use crate::tokens::{PageId, SegmentId, BlockId, HeapId, TldId};
use crate::config::*;


verus!{

pub open spec fn is_page_ptr(ptr: *mut Page, page_id: PageId) -> bool {
    ptr as int == page_header_start(page_id)
        && 0 <= page_id.idx <= SLICES_PER_SEGMENT
        && segment_start(page_id.segment_id) + SEGMENT_SIZE < usize::MAX
        && ptr@.provenance == page_id.segment_id.provenance
}

pub open spec fn is_segment_ptr(ptr: *mut SegmentHeader, segment_id: SegmentId) -> bool {
    ptr as int == segment_start(segment_id)
      && ptr as int + SEGMENT_SIZE < usize::MAX
      && ptr@.provenance == segment_id.provenance
}

pub open spec fn is_heap_ptr(ptr: *mut Heap, heap_id: HeapId) -> bool {
    heap_id.id == ptr.addr() && ptr@.provenance == heap_id.provenance
}

pub open spec fn is_tld_ptr(ptr: *mut Tld, tld_id: TldId) -> bool {
    tld_id.id == ptr.addr() && ptr@.provenance == tld_id.provenance
}

pub closed spec fn segment_start(segment_id: SegmentId) -> int {
    segment_id.id * (SEGMENT_SIZE as int)
}

pub open spec fn page_header_start(page_id: PageId) -> int {
    segment_start(page_id.segment_id) + SIZEOF_SEGMENT_HEADER + page_id.idx * SIZEOF_PAGE_HEADER
}

pub open spec fn page_start(page_id: PageId) -> int {
    segment_start(page_id.segment_id) + SLICE_SIZE * page_id.idx
}

pub closed spec fn start_offset(block_size: int) -> int {
    if block_size >= INTPTR_SIZE as int && block_size <= 1024 {
        3 * MAX_ALIGN_GUARANTEE
    } else {
        0
    }
}

pub open spec fn block_start_at(page_id: PageId, block_size: int, block_idx: int) -> int {
    page_start(page_id)
         + start_offset(block_size)
         + block_idx * block_size
}

pub closed spec fn block_start(block_id: BlockId) -> int {
    block_start_at(block_id.page_id, block_id.block_size as int, block_id.idx as int)
}

pub open spec fn is_block_ptr(ptr: *mut u8, block_id: BlockId) -> bool {
    &&& ptr@.provenance == block_id.page_id.segment_id.provenance
    &&& is_block_ptr1(ptr as int, block_id)
}

#[verifier::opaque]
pub open spec fn is_block_ptr1(ptr: int, block_id: BlockId) -> bool {
    &&& segment_start(block_id.page_id.segment_id) < ptr
        <= segment_start(block_id.page_id.segment_id) + (SEGMENT_SIZE as int)
        < usize::MAX

    &&& 0 <= block_id.slice_idx <= SLICES_PER_SEGMENT

    &&& segment_start(block_id.page_id.segment_id) + (block_id.slice_idx * SLICE_SIZE)
        <= ptr
        < segment_start(block_id.page_id.segment_id) + (block_id.slice_idx * SLICE_SIZE)
              + SLICE_SIZE

    &&& ptr == block_start(block_id)

    &&& 0 <= block_id.page_id.segment_id.id

    &&& block_id.block_size >= size_of::<crate::linked_list::Node>()
    &&& block_id.block_size % size_of::<crate::linked_list::Node>() == 0
}

pub open spec fn is_page_ptr_opt(pptr: *mut Page, opt_page_id: Option<PageId>) -> bool {
    match opt_page_id {
        Some(page_id) => is_page_ptr(pptr, page_id) && pptr.addr() != 0,
        None => pptr.addr() == 0,
    }
}

#[verifier::external_body]
pub proof fn block_size_ge_word()
    ensures forall |p, block_id| is_block_ptr(p, block_id) ==>
        block_id.block_size >= size_of::<crate::linked_list::Node>()
{
    unimplemented!()
}

#[verifier::spinoff_prover]
#[verifier::external_body]
pub proof fn block_ptr_aligned_to_word()
    ensures forall |p, block_id| is_block_ptr(p, block_id) ==>
        p as int % align_of::<crate::linked_list::Node>() as int == 0
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn block_start_at_diff(page_id: PageId, block_size: nat,
  block_idx1: nat, block_idx2: nat)
    ensures block_start_at(page_id, block_size as int, block_idx2 as int) ==
        block_start_at(page_id, block_size as int, block_idx1 as int) + (block_idx2 - block_idx1) * block_size
{
    unimplemented!()
}







pub fn calculate_segment_ptr_from_block(ptr: *mut u8, Ghost(block_id): Ghost<BlockId>) -> (res: *mut SegmentHeader)
    requires is_block_ptr(ptr, block_id),
    ensures is_segment_ptr(res, block_id.page_id.segment_id),
{
    let block_p = ptr.addr();

    proof {
        reveal(is_block_ptr1);
        const_facts();
        assert(block_p > 0);



        let id = block_id.page_id.segment_id.id as usize;
        assert(id == block_id.page_id.segment_id.id);
        assert(id < 0x7fffffffff);
        assert(
            sub(block_p, 1) & (!0x1ffffffusize) == mul(id, 0x2000000)) by(bit_vector)
          requires
            mul(id, 0x2000000) < block_p <= add(mul(id, 0x2000000), 0x2000000),
            id < 0x7fffffffffusize;

        assert(mul(id, 0x2000000) == id * 0x2000000);
        assert(add(mul(id, 0x2000000), 0x2000000) == id * 0x2000000 + 0x2000000);
    }

    let segment_p = (block_p - 1) & (!((SEGMENT_SIZE - 1) as usize));



    ptr.with_addr(segment_p) as *mut SegmentHeader
}



pub fn calculate_slice_page_ptr_from_block(block_ptr: *mut u8, segment_ptr: *mut SegmentHeader, Ghost(block_id): Ghost<BlockId>) -> (page_ptr: *mut Page)
    requires
        is_block_ptr(block_ptr, block_id),
        is_segment_ptr(segment_ptr, block_id.page_id.segment_id),
    ensures is_page_ptr(page_ptr, block_id.page_id_for_slice())
{
    let b = block_ptr.addr();
    let s = segment_ptr.addr();
    proof {
        reveal(is_block_ptr1);
        const_facts();
        assert(b - s <= SEGMENT_SIZE);
    }
    let q = (b - s) / SLICE_SIZE as usize;
    proof {
        assert((b - s) / SLICE_SIZE as int <= SLICES_PER_SEGMENT) by(nonlinear_arith)
          requires SLICES_PER_SEGMENT == SEGMENT_SIZE as int / SLICE_SIZE as int,
            b - s <= SEGMENT_SIZE as int,
            SLICE_SIZE > 0;
    }
    let h = s + SIZEOF_SEGMENT_HEADER + q * SIZEOF_PAGE_HEADER;
    block_ptr.with_addr(h) as *mut Page
}

#[inline(always)]
pub fn calculate_page_ptr_subtract_offset(
    page_ptr: *mut Page, offset: u32, Ghost(page_id): Ghost<PageId>, Ghost(target_page_id): Ghost<PageId>) -> (result: *mut Page)
    requires
        is_page_ptr(page_ptr, page_id),
        page_id.segment_id == target_page_id.segment_id,
        offset == (page_id.idx - target_page_id.idx) * SIZEOF_PAGE_HEADER,
    ensures
        is_page_ptr(result, target_page_id),
{
    proof {
        segment_start_ge0(page_id.segment_id);
    }

    let p = page_ptr.addr();
    let q = p - offset as usize;
    page_ptr.with_addr(q)
}



pub fn calculate_page_start(page_ptr: PagePtr, block_size: usize) -> (addr: usize)
    requires block_size > 0, page_ptr.wf(),
    ensures addr == block_start_at(page_ptr.page_id@, block_size as int, 0)
{
    let segment_ptr = SegmentPtr::ptr_segment(page_ptr);
    segment_page_start_from_slice(segment_ptr, page_ptr, block_size)
}

pub fn calculate_page_block_at(
    page_start: usize,
    block_size: usize,
    idx: usize,
    Ghost(page_id): Ghost<PageId>
) -> (p: usize)
    requires page_start == block_start_at(page_id, block_size as int, 0),
        block_start_at(page_id, block_size as int, 0)
            + idx as int * block_size as int <= segment_start(page_id.segment_id) + SEGMENT_SIZE,
        segment_start(page_id.segment_id) + SEGMENT_SIZE < usize::MAX,
    ensures
        p == block_start_at(page_id, block_size as int, idx as int),
        p == page_start + idx as int * block_size as int
{
    proof {
        const_facts();
        assert(block_size * idx >= 0) by(nonlinear_arith)
            requires block_size >= 0, idx >= 0;
        assert(block_size * idx == idx * block_size) by(nonlinear_arith);
    }
    let p = page_start + block_size * idx;
    return p;
}

#[verifier::external_body]
pub proof fn mk_segment_id(p: *mut SegmentHeader) -> (id: SegmentId)
    requires p as int >= 0,
        p as int % SEGMENT_SIZE as int == 0,
        ((p as int + SEGMENT_SIZE as int) < usize::MAX),
    ensures is_segment_ptr(p, id),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn segment_id_divis(sp: SegmentPtr)
    requires sp.wf(),
    ensures sp.segment_ptr as int % SEGMENT_SIZE as int == 0,
{
    unimplemented!()
}

pub fn segment_page_start_from_slice(
    segment_ptr: SegmentPtr,
    slice: PagePtr,
    xblock_size: usize)
  -> (res: usize)
    requires
        segment_ptr.wf(), slice.wf(), slice.page_id@.segment_id == segment_ptr.segment_id@
    ensures ({ let start_offset = res; {
        &&& xblock_size == 0 ==>
            start_offset == segment_start(segment_ptr.segment_id@)
                + slice.page_id@.idx * SLICE_SIZE
        &&& xblock_size > 0 ==>
            start_offset == block_start_at(slice.page_id@, xblock_size as int, 0)
    }})
{
    proof { const_facts(); }

    let idxx = slice.page_ptr.addr() - (segment_ptr.segment_ptr.addr() + SIZEOF_SEGMENT_HEADER);
    let idx = idxx / SIZEOF_PAGE_HEADER;

    let start_offset = if xblock_size >= INTPTR_SIZE as usize && xblock_size <= 1024 {
        3 * MAX_ALIGN_GUARANTEE
    } else {
        0
    };

    segment_ptr.segment_ptr.addr() + (idx * SLICE_SIZE as usize) + start_offset
}

#[verifier::external_body]
proof fn bitand_with_mask_gives_rounding(x: usize, y: usize)
    requires y != 0, y & sub(y, 1) == 0,
    ensures x & !sub(y, 1) == (x / y) * y,
    decreases y,
{
    unimplemented!()
}

#[verifier::spinoff_prover]
#[verifier::external_body]
proof fn two_mul_with_bit0(x1: int, y1: int)
    requires y1 != 0,
    ensures (2 * x1) / (2 * y1) == x1 / y1
{
    unimplemented!()
}

#[verifier::spinoff_prover]
#[verifier::external_body]
proof fn two_mul_with_bit1(x1: int, y1: int)
    requires y1 != 0,
    ensures (2 * x1 + 1) / (2 * y1) == x1 / y1
{
    unimplemented!()
}


#[verifier::spinoff_prover]
#[inline]
pub fn align_down(x: usize, y: usize) -> (res: usize)
    requires y != 0,
    ensures
        res == (x as int / y as int) * y,
        res <= x < res + y,
        res % y == 0,
        (res / y * y) == res,
{
    let mask = y - 1;

    proof {
        assert(0 <= (x / y) * y <= x) by(nonlinear_arith)
            requires y > 0, x >= 0;

        if y & mask == 0usize {
            bitand_with_mask_gives_rounding(x, y);
            assert((x & !mask) == (x / y) * y);
            assert((x & !mask) == (x as int / y as int) * y);
        }

        assert((x as int / y as int) == (x / y) as int);

        assert(x / y * y + x % y == x) by(nonlinear_arith) requires y != 0;
        assert(0 <= x % y < y);
        let t = x / y;
        mul_mod_right(t as int, y as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(t as int * y as int, y as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(y as int, (t as int * y as int) / y as int);
    }

    if ((y & mask) == 0) {
        x & !mask
    } else {
        (x / y) * y
    }
}

#[inline]
pub fn align_up(x: usize, y: usize) -> (res: usize)
    requires y != 0,
        x + y - 1 <= usize::MAX,
    ensures
        res == ((x + y - 1) / y as int) * y,
        x <= res <= x + y - 1,
        res % y == 0,
        (res / y * y) == res,
{
    let mask = y - 1;

    proof {
        if y & mask == 0 {
            bitand_with_mask_gives_rounding((x + y - 1) as usize, y);
            assert(((x + mask) as usize) & !mask == ((x + y - 1) / y as int) * y);
        }

        let z = x + mask;
        assert(z / y as int * y + z % y as int == z) by(nonlinear_arith) requires y != 0;

        let t = (x + y - 1) / y as int;
        mul_mod_right(t, y as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(t * y as int, y as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(y as int, (t * y as int) / y as int);
    }

    if ((y & mask) == 0) {
        (x + mask) & !mask
    } else {
        ((x + mask) / y) * y
    }
}

#[verifier::external_body]
pub proof fn mod_trans(a: int, b: int, c: int)
    requires b != 0, c != 0, a % b == 0, b % c == 0,
    ensures a % c == 0
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn mod_mul(a: int, b: int, c: int)
    requires b % c == 0, c != 0
    ensures (a * b) % c == 0,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn mul_mod_right(a: int, b: int)
    requires b != 0,
    ensures (a * b) % b == 0,
{
    unimplemented!()
}


impl SegmentPtr {
    #[inline]
    pub fn ptr_segment(page_ptr: PagePtr) -> (segment_ptr: SegmentPtr)
        requires page_ptr.wf(),
        ensures segment_ptr.wf(),
            segment_ptr.segment_id == page_ptr.page_id@.segment_id,
    {
        proof {
            const_facts();
            let p = page_ptr.page_ptr as int;
            let sid = page_ptr.page_id@.segment_id;
            assert((p / SEGMENT_SIZE as int) * SEGMENT_SIZE as int == segment_start(sid));
        }

        let p = page_ptr.page_ptr.addr();
        let s = (p / SEGMENT_SIZE as usize) * SEGMENT_SIZE as usize;
        SegmentPtr {
            segment_ptr: page_ptr.page_ptr.with_addr(s) as *mut SegmentHeader,
            segment_id: Ghost(page_ptr.page_id@.segment_id),
        }
    }
}

#[verifier::external_body]
pub proof fn is_page_ptr_nonzero(ptr: *mut Page, page_id: PageId)
    requires is_page_ptr(ptr, page_id),
    ensures ptr as int != 0,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn is_block_ptr_mult4(ptr: *mut u8, block_id: BlockId)
    requires is_block_ptr(ptr, block_id),
    ensures ptr as int % 4 == 0,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn segment_start_mult_commit_size(segment_id: SegmentId)
    ensures segment_start(segment_id) % COMMIT_SIZE as int == 0,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn segment_start_mult8(segment_id: SegmentId)
    ensures segment_start(segment_id) % 8 == 0,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn segment_start_ge0(segment_id: SegmentId)
    ensures segment_start(segment_id) >= 0,
{
    unimplemented!()
}

pub fn calculate_start_offset(block_size: usize) -> (res: u32)
    ensures res == start_offset(block_size as int),
{
    if block_size >= 8 && block_size <= 1024 {
        3 * MAX_ALIGN_GUARANTEE as u32
    } else {
        0
    }
}

#[verifier::external_body]
pub proof fn start_offset_le_slice_size(block_size: int)
    ensures 0 <= start_offset(block_size) <= SLICE_SIZE,
        start_offset(block_size) == 0 || start_offset(block_size) == 3 * MAX_ALIGN_GUARANTEE,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn segment_start_eq(sid: SegmentId, sid2: SegmentId)
    requires sid.id == sid2.id,
    ensures segment_start(sid) == segment_start(sid2)
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn get_block_start_from_is_block_ptr(ptr: *mut u8, block_id: BlockId)
    requires is_block_ptr(ptr, block_id),
    ensures ptr as int == block_start(block_id),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn get_block_start_defn(block_id: BlockId)
    ensures block_start(block_id)
      == block_start_at(block_id.page_id, block_id.block_size as int, block_id.idx as int),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn sub_distribute(a: int, b: int, c: int)
    ensures a * c - b * c == (a - b) * c,
{
    unimplemented!()
}

}
}
mod config {
use vstd::prelude::*;

verus!{


pub const INTPTR_SHIFT: u64 = 3;
pub const INTPTR_SIZE: u64 = 8;
global size_of usize == 8;

pub const SLICE_SHIFT: u64 = 13 + INTPTR_SHIFT;

pub const SLICE_SIZE: u64 = 65536;

pub const SEGMENT_SHIFT: u64 = 9 + SLICE_SHIFT;

pub const SEGMENT_SIZE: u64 = (1 << SEGMENT_SHIFT);

pub const SEGMENT_ALIGN: u64 = SEGMENT_SIZE;

pub const SLICES_PER_SEGMENT: u64 = (SEGMENT_SIZE / SLICE_SIZE);

pub const BIN_HUGE: u64 = 73;

pub const BIN_FULL: u64 = BIN_HUGE + 1;

pub const SMALL_PAGE_SHIFT: u64 = SLICE_SHIFT;
pub const MEDIUM_PAGE_SHIFT: u64 = 3 + SMALL_PAGE_SHIFT;

pub const SMALL_PAGE_SIZE: u64 = 1u64 << SMALL_PAGE_SHIFT;
pub const MEDIUM_PAGE_SIZE: u64 = 1u64 << MEDIUM_PAGE_SHIFT;

pub const SMALL_OBJ_SIZE_MAX: u64 = (SMALL_PAGE_SIZE / 4);
pub const MEDIUM_OBJ_SIZE_MAX: u64 = MEDIUM_PAGE_SIZE / 4;
pub const MEDIUM_OBJ_WSIZE_MAX: u64 = MEDIUM_OBJ_SIZE_MAX / (usize::BITS as u64 / 8);
pub const LARGE_OBJ_SIZE_MAX: u64 = (SEGMENT_SIZE / 2);

pub const MAX_ALLOC_SIZE: usize = isize::MAX as usize;

pub const SMALL_WSIZE_MAX: usize = 128;
pub const PAGES_DIRECT: usize = SMALL_WSIZE_MAX + 1;
pub const SMALL_SIZE_MAX: usize = SMALL_WSIZE_MAX * INTPTR_SIZE as usize;

pub const MAX_ALIGN_SIZE: usize = 16;
pub const MAX_ALIGN_GUARANTEE: usize = 8 * MAX_ALIGN_SIZE;

pub const SEGMENT_BIN_MAX: usize = 31;

pub const ALIGNMENT_MAX: u64 = (SEGMENT_SIZE / 2);

pub const SIZEOF_SEGMENT_HEADER: usize = 264;
pub const SIZEOF_PAGE_HEADER: usize = 80;
pub const SIZEOF_HEAP: usize = 2904;
pub const SIZEOF_TLD: usize = 552;

use crate::types::*;
global layout SegmentHeader is size == 264, align == 8;
global layout Page is size == 80, align == 8;
global layout Heap is size == 2904, align == 8;
global layout Tld is size == 552, align == 8;



pub const COMMIT_SIZE: u64 = SLICE_SIZE;
pub const COMMIT_MASK_BITS: u64 = SLICES_PER_SEGMENT;
pub const COMMIT_MASK_FIELD_COUNT: u64 = COMMIT_MASK_BITS / (usize::BITS as u64);


pub const HUGE_BLOCK_SIZE: u32 = 0x80000000;


#[verifier::external_body]
pub proof fn const_facts()
    ensures SLICE_SIZE == 65536,
        SEGMENT_SIZE == 33554432,
        SLICES_PER_SEGMENT == 512,
        SMALL_PAGE_SIZE == 65536,
        MEDIUM_PAGE_SIZE == 524288,

        SMALL_OBJ_SIZE_MAX == 16384,
        MEDIUM_OBJ_SIZE_MAX == 131072,
        MEDIUM_OBJ_WSIZE_MAX == 16384,
        SMALL_SIZE_MAX == 1024,
        LARGE_OBJ_SIZE_MAX == 16777216,

        COMMIT_MASK_FIELD_COUNT == 8,

        vstd::layout::size_of::<SegmentHeader>() == SIZEOF_SEGMENT_HEADER,
        vstd::layout::size_of::<Page>() == SIZEOF_PAGE_HEADER,
        vstd::layout::size_of::<Heap>() == SIZEOF_HEAP,
        vstd::layout::size_of::<Tld>() == SIZEOF_TLD,

        vstd::layout::align_of::<SegmentHeader>() == 8,
        vstd::layout::align_of::<Page>() == 8,
        vstd::layout::align_of::<Heap>() == 8,
        vstd::layout::align_of::<Tld>() == 8,
{
    unimplemented!()
}

use crate::types::todo;
pub fn option_eager_commit_delay() -> i64 { 1 }
pub fn option_eager_commit() -> bool { true }
pub fn option_allow_decommit() -> bool { true }
pub fn option_page_reset() -> bool { false }


pub fn option_decommit_delay() -> i64 { 25 }
pub fn option_decommit_extend_delay() -> i64 { 1 }


}
}
mod bin_sizes {
use vstd::prelude::*;
use vstd::assert_by_contradiction;
use vstd::calc;
use vstd::std_specs::bits::u64_leading_zeros;
use crate::config::*;





verus!{














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

        ((usize::BITS / 8) * (inner + 5) * pow2(group + 1)) as nat
    }
}

#[verifier::external_body]
proof fn mod8(x:int, y:int) by (nonlinear_arith)
    requires x == 8 * y,
    ensures  x % 8 == 0,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn size_of_bin_mult_word_size(bin_idx: int)
    ensures size_of_bin(bin_idx) % 8 == 0
{
    unimplemented!()
}

pub open spec fn smallest_bin_fitting_size(size: int) -> int {
    let bytes_per_word = (usize::BITS / 8) as int;
    let wsize = (size + bytes_per_word - 1) / bytes_per_word;
    if wsize <= 1 {
        1
    } else if wsize <= 8 {
        wsize
    } else if wsize > 524288 {
        BIN_HUGE as int
    } else {
        let w = (wsize - 1) as u64;
        let lz = u64_leading_zeros(w);
        let b = (usize::BITS - 1 - lz) as u8;
        let shifted = (w >> (b - 2) as u64) as u8;
        let bin_idx = ((b * 4) + (shifted & 0x03)) - 3;
        bin_idx
    }
}

pub open spec fn pfd_lower(bin_idx: int) -> nat
    recommends valid_bin_idx(bin_idx)
{
    if bin_idx == 1 {
        0
    } else {
        size_of_bin(bin_idx - 1) / INTPTR_SIZE as nat + 1
    }
}

pub open spec fn pfd_upper(bin_idx: int) -> nat
    recommends valid_bin_idx(bin_idx)
{
    size_of_bin(bin_idx) / INTPTR_SIZE as nat
}

#[verifier::external_body]
pub proof fn lemma_bin_sizes_constants()
    ensures
        size_of_bin(1) == 8, size_of_bin(1) / 8 == 1,
        size_of_bin(2) == 16, size_of_bin(2) / 8 == 2,
        size_of_bin(3) == 24, size_of_bin(3) / 8 == 3,
        size_of_bin(4) == 32, size_of_bin(4) / 8 == 4,
        size_of_bin(5) == 40, size_of_bin(5) / 8 == 5,
        size_of_bin(6) == 48, size_of_bin(6) / 8 == 6,
        size_of_bin(7) == 56, size_of_bin(7) / 8 == 7,
        size_of_bin(8) == 64, size_of_bin(8) / 8 == 8,
        size_of_bin(9) == 80, size_of_bin(9) / 8 == 10,
        size_of_bin(10) == 96, size_of_bin(10) / 8 == 12,
        size_of_bin(11) == 112, size_of_bin(11) / 8 == 14,
        size_of_bin(12) == 128, size_of_bin(12) / 8 == 16,
        size_of_bin(13) == 160, size_of_bin(13) / 8 == 20,
        size_of_bin(14) == 192, size_of_bin(14) / 8 == 24,
        size_of_bin(15) == 224, size_of_bin(15) / 8 == 28,
        size_of_bin(16) == 256, size_of_bin(16) / 8 == 32,
        size_of_bin(17) == 320, size_of_bin(17) / 8 == 40,
        size_of_bin(18) == 384, size_of_bin(18) / 8 == 48,
        size_of_bin(19) == 448, size_of_bin(19) / 8 == 56,
        size_of_bin(20) == 512, size_of_bin(20) / 8 == 64,
        size_of_bin(21) == 640, size_of_bin(21) / 8 == 80,
        size_of_bin(22) == 768, size_of_bin(22) / 8 == 96,
        size_of_bin(23) == 896, size_of_bin(23) / 8 == 112,
        size_of_bin(24) == 1024, size_of_bin(24) / 8 == 128,
        size_of_bin(25) == 1280, size_of_bin(25) / 8 == 160,
        size_of_bin(26) == 1536, size_of_bin(26) / 8 == 192,
        size_of_bin(27) == 1792, size_of_bin(27) / 8 == 224,
        size_of_bin(28) == 2048, size_of_bin(28) / 8 == 256,
        size_of_bin(29) == 2560, size_of_bin(29) / 8 == 320,
        size_of_bin(30) == 3072, size_of_bin(30) / 8 == 384,
        size_of_bin(31) == 3584, size_of_bin(31) / 8 == 448,
        size_of_bin(32) == 4096, size_of_bin(32) / 8 == 512,
        size_of_bin(33) == 5120, size_of_bin(33) / 8 == 640,
        size_of_bin(34) == 6144, size_of_bin(34) / 8 == 768,
        size_of_bin(35) == 7168, size_of_bin(35) / 8 == 896,
        size_of_bin(36) == 8192, size_of_bin(36) / 8 == 1024,
        size_of_bin(37) == 10240, size_of_bin(37) / 8 == 1280,
        size_of_bin(38) == 12288, size_of_bin(38) / 8 == 1536,
        size_of_bin(39) == 14336, size_of_bin(39) / 8 == 1792,
        size_of_bin(40) == 16384, size_of_bin(40) / 8 == 2048,
        size_of_bin(41) == 20480, size_of_bin(41) / 8 == 2560,
        size_of_bin(42) == 24576, size_of_bin(42) / 8 == 3072,
        size_of_bin(43) == 28672, size_of_bin(43) / 8 == 3584,
        size_of_bin(44) == 32768, size_of_bin(44) / 8 == 4096,
        size_of_bin(45) == 40960, size_of_bin(45) / 8 == 5120,
        size_of_bin(46) == 49152, size_of_bin(46) / 8 == 6144,
        size_of_bin(47) == 57344, size_of_bin(47) / 8 == 7168,
        size_of_bin(48) == 65536, size_of_bin(48) / 8 == 8192,
        size_of_bin(49) == 81920, size_of_bin(49) / 8 == 10240,
        size_of_bin(50) == 98304, size_of_bin(50) / 8 == 12288,
        size_of_bin(51) == 114688, size_of_bin(51) / 8 == 14336,
        size_of_bin(52) == 131072, size_of_bin(52) / 8 == 16384,
        size_of_bin(53) == 163840, size_of_bin(53) / 8 == 20480,
        size_of_bin(54) == 196608, size_of_bin(54) / 8 == 24576,
        size_of_bin(55) == 229376, size_of_bin(55) / 8 == 28672,
        size_of_bin(56) == 262144, size_of_bin(56) / 8 == 32768,
        size_of_bin(57) == 327680, size_of_bin(57) / 8 == 40960,
        size_of_bin(58) == 393216, size_of_bin(58) / 8 == 49152,
        size_of_bin(59) == 458752, size_of_bin(59) / 8 == 57344,
        size_of_bin(60) == 524288, size_of_bin(60) / 8 == 65536,
        size_of_bin(61) == 655360, size_of_bin(61) / 8 == 81920,
        size_of_bin(62) == 786432, size_of_bin(62) / 8 == 98304,
        size_of_bin(63) == 917504, size_of_bin(63) / 8 == 114688,
        size_of_bin(64) == 1048576, size_of_bin(64) / 8 == 131072,
        size_of_bin(65) == 1310720, size_of_bin(65) / 8 == 163840,
        size_of_bin(66) == 1572864, size_of_bin(66) / 8 == 196608,
        size_of_bin(67) == 1835008, size_of_bin(67) / 8 == 229376,
        size_of_bin(68) == 2097152, size_of_bin(68) / 8 == 262144,
        size_of_bin(69) == 2621440, size_of_bin(69) / 8 == 327680,
        size_of_bin(70) == 3145728, size_of_bin(70) / 8 == 393216,
        size_of_bin(71) == 3670016, size_of_bin(71) / 8 == 458752,
        size_of_bin(72) == 4194304, size_of_bin(72) / 8 == 524288,
        size_of_bin(73) == 4194312, size_of_bin(73) / 8 == 524289,
{
    unimplemented!()
}


spec fn property_idx_out_of_range_has_different_bin_size(bin_idx: int, wsize:int) -> bool
{
    valid_bin_idx(bin_idx) &&
    !(pfd_lower(bin_idx) <= wsize <= pfd_upper(bin_idx)) &&
    0 <= wsize <= 128
    ==>
    smallest_bin_fitting_size(wsize * INTPTR_SIZE) != bin_idx
}

spec fn check_idx_out_of_range_has_different_bin_size(bin_idx: int, wsize_start:int, wsize_end:int) -> bool
    decreases wsize_end - wsize_start,
{
   if wsize_start >= wsize_end {
       true
   } else {
          property_idx_out_of_range_has_different_bin_size(bin_idx, wsize_start)
       && check_idx_out_of_range_has_different_bin_size(bin_idx, wsize_start + 1, wsize_end)
   }
}

#[verifier::external_body]
proof fn result_idx_out_of_range_has_different_bin_size(bin_idx: int, wsize_start:int, wsize_end:int)
    ensures
        check_idx_out_of_range_has_different_bin_size(bin_idx, wsize_start, wsize_end) ==>
            (forall |wsize| wsize_start <= wsize < wsize_end ==>
                 property_idx_out_of_range_has_different_bin_size(bin_idx, wsize)),
    decreases wsize_end - wsize_start,
{
    unimplemented!()
}

spec fn check2_idx_out_of_range_has_different_bin_size(bin_idx_start: int, bin_idx_end: int, wsize_start:int, wsize_end:int) -> bool
    decreases bin_idx_end - bin_idx_start,
{
    if bin_idx_start >= bin_idx_end {
        true
    } else {
        check_idx_out_of_range_has_different_bin_size(bin_idx_start, wsize_start, wsize_end)
        && check2_idx_out_of_range_has_different_bin_size(bin_idx_start + 1, bin_idx_end, wsize_start, wsize_end)
    }
}

#[verifier::external_body]
proof fn result2_idx_out_of_range_has_different_bin_size(bin_idx_start: int, bin_idx_end: int, wsize_start:int, wsize_end:int)
    ensures
        check2_idx_out_of_range_has_different_bin_size(bin_idx_start, bin_idx_end, wsize_start, wsize_end) ==>
            (forall |bin_idx,wsize| bin_idx_start <= bin_idx < bin_idx_end && wsize_start <= wsize < wsize_end ==>
                     property_idx_out_of_range_has_different_bin_size(bin_idx, wsize)),
    decreases bin_idx_end - bin_idx_start,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn different_bin_size(bin_idx1: int, bin_idx2: int)
    requires
        valid_bin_idx(bin_idx1),
        valid_bin_idx(bin_idx2),
        bin_idx1 != bin_idx2,
    ensures
        size_of_bin(bin_idx1) != size_of_bin(bin_idx2)
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn idx_out_of_range_has_different_bin_size(bin_idx: int, wsize: int)
    requires
        valid_bin_idx(bin_idx),
        !(pfd_lower(bin_idx) <= wsize <= pfd_upper(bin_idx)),
        0 <= wsize <= 128,
    ensures
        smallest_bin_fitting_size(wsize * INTPTR_SIZE) != bin_idx
{
    unimplemented!()
}


#[verifier::external_body]
proof fn div2(x: u64, y:int) by (nonlinear_arith)
    requires y > 0,
    ensures x as int / (y * 2) == (x as int / y) / 2,
{
    unimplemented!()
}

#[verifier::external_body]
proof fn lemma_div_is_ordered(x: int, y: int, z: int) by (nonlinear_arith)
    requires
        x <= y,
        0 < z,
    ensures x / z <= y / z
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn lemma_div_by_multiple(b: int, d: int) by (nonlinear_arith)
    requires
        0 <= b,
        0 < d,
    ensures
        (b * d) / d == b
{
    unimplemented!()
}

#[verifier::external_body]
proof fn mul_assoc(x: nat, y: nat, z: nat) by (nonlinear_arith)
    ensures (x * y) * z == y * (x * z)
{
    unimplemented!()
}

#[verifier::external_body]
proof fn mul_ordering(x: nat, y: nat, z: nat) by (nonlinear_arith)
    requires
        0 < x && 1 < y && 0 < z,
        x * y == z,
    ensures
        x < z,
{
    unimplemented!()
}

#[verifier::external_body]
proof fn pow2_positive(e:int)
    ensures pow2(e) > 0,
    decreases e,
{
    unimplemented!()
}

#[verifier::external_body]
proof fn pow2_adds(e1:nat, e2:nat)
    ensures
        pow2(e1 as int) * pow2(e2 as int) == pow2((e1 + e2) as int),
    decreases e1,
{
    unimplemented!()
}

#[verifier::external_body]
proof fn pow2_subtracts(e1:nat, e2:nat)
    requires e1 <= e2,
    ensures
        pow2(e2 as int) / pow2(e1 as int) == pow2((e2 - e1) as int),
{
    unimplemented!()
}

#[verifier::external_body]
proof fn pow2_properties()
    ensures
        forall |e:int| pow2(e) > 0,
        forall |e:int| e > 0 ==> #[trigger] pow2(e) / 2 == pow2(e - 1),
        forall |e1, e2| 0 <= e1 < e2 ==> pow2(e1) < pow2(e2),
        forall |e1, e2| 0 <= e1 && 0 <= e2 ==> pow2(e1) * pow2(e2) == #[trigger] pow2(e1 + e2),
        forall |e1, e2| 0 <= e1 <= e2 ==> pow2(e2) / pow2(e1) == #[trigger] pow2(e2 - e1),
{
    unimplemented!()
}

#[verifier::external_body]
proof fn shift_is_div(x:u64, shift:u64)
    requires 0 <= shift < 64,
    ensures x >> shift == x as nat / pow2(shift as int),
    decreases shift,
{
    unimplemented!()
}


#[verifier::external_body]
proof fn leading_zeros_powers_of_2(i: u64, exp: nat)
    requires
        i == pow2(exp as int),
        exp < 64
    ensures
        u64_leading_zeros(i) == 64 - exp - 1,
    decreases i,
{
    unimplemented!()
}

#[verifier::external_body]
proof fn leading_zeros_between_powers_of_2(i: u64, exp: nat)
    requires
        pow2(exp as int) <= i < pow2((exp + 1) as int),
        1 <= exp < 64
    ensures
        u64_leading_zeros(i) == 64 - exp - 1,
    decreases exp,
{
    unimplemented!()
}

#[verifier::external_body]
proof fn log2(i:u64) -> (e:nat)
    requires i >= 1,
    ensures pow2(e as int) <= i < pow2((e+1) as int),
    decreases i,
{
    unimplemented!()
}


spec fn property_idx_in_range_has_bin_size(bin_idx: int, wsize:int) -> bool
{
    valid_bin_idx(bin_idx) &&
    (pfd_lower(bin_idx) <= wsize <= pfd_upper(bin_idx))
    ==>
    smallest_bin_fitting_size(wsize * INTPTR_SIZE) == bin_idx
}

spec fn check_idx_in_range_has_bin_size(bin_idx: int, wsize_start:int, wsize_end:int) -> bool
    decreases wsize_end - wsize_start,
{
   if wsize_start >= wsize_end {
       true
   } else {
          property_idx_in_range_has_bin_size(bin_idx, wsize_start)
       && check_idx_in_range_has_bin_size(bin_idx, wsize_start + 1, wsize_end)
   }
}

#[verifier::external_body]
proof fn result_idx_in_range_has_bin_size(bin_idx: int, wsize_start:int, wsize_end:int)
    ensures
        check_idx_in_range_has_bin_size(bin_idx, wsize_start, wsize_end) ==>
            (forall |wsize| wsize_start <= wsize < wsize_end ==>
                 property_idx_in_range_has_bin_size(bin_idx, wsize)),
    decreases wsize_end - wsize_start,
{
    unimplemented!()
}

spec fn check2_idx_in_range_has_bin_size(bin_idx_start: int, bin_idx_end: int, wsize_start:int, wsize_end:int) -> bool
    decreases bin_idx_end - bin_idx_start,
{
    if bin_idx_start >= bin_idx_end {
        true
    } else {
        check_idx_in_range_has_bin_size(bin_idx_start, wsize_start, wsize_end)
        && check2_idx_in_range_has_bin_size(bin_idx_start + 1, bin_idx_end, wsize_start, wsize_end)
    }
}

#[verifier::external_body]
proof fn result2_idx_in_range_has_bin_size(bin_idx_start: int, bin_idx_end: int, wsize_start:int, wsize_end:int)
    ensures
        check2_idx_in_range_has_bin_size(bin_idx_start, bin_idx_end, wsize_start, wsize_end) ==>
            (forall |bin_idx,wsize| bin_idx_start <= bin_idx < bin_idx_end && wsize_start <= wsize < wsize_end ==>
                     property_idx_in_range_has_bin_size(bin_idx, wsize)),
    decreases bin_idx_end - bin_idx_start,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn idx_in_range_has_bin_size(bin_idx: int, wsize: int)
    requires
        valid_bin_idx(bin_idx),
        (pfd_lower(bin_idx) <= wsize <= pfd_upper(bin_idx)),
        wsize <= 128,
    ensures
        smallest_bin_fitting_size(wsize * INTPTR_SIZE) == bin_idx
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn pfd_lower_le_upper(bin_idx: int)
    requires valid_bin_idx(bin_idx),
    ensures pfd_lower(bin_idx) <= pfd_upper(bin_idx)
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn size_of_bin_bounds(b: int)
    requires valid_bin_idx(b),
    ensures size_of_bin(b) >= INTPTR_SIZE,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn size_of_bin_bounds_not_huge(b: int)
    requires valid_bin_idx(b), b != BIN_HUGE,
    ensures 8 <= size_of_bin(b) <= 4194304
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn out_of_small_range(bin_idx: int)
    requires valid_bin_idx(bin_idx),
        size_of_bin(bin_idx) > SMALL_SIZE_MAX,
    ensures
        pfd_lower(bin_idx) >= PAGES_DIRECT,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn size_le_8_implies_idx_eq_1(bin_idx: int)
    requires valid_bin_idx(bin_idx), size_of_bin(bin_idx) / 8 <= 1,
    ensures bin_idx == 1,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn size_gt_8_implies_idx_gt_1(bin_idx: int)
    requires valid_bin_idx(bin_idx), size_of_bin(bin_idx) / 8 > 1,
    ensures bin_idx > 1,
{
    unimplemented!()
}


pub open spec fn pow2(i: int) -> nat
    decreases i
{
    if i <= 0 {
        1
    } else {
        pow2(i - 1) * 2
    }
}

spec fn property_bounds_for_smallest_bitting_size(size:int) -> bool
{
    valid_bin_idx(smallest_bin_fitting_size(size)) &&
    size_of_bin(smallest_bin_fitting_size(size)) >= size
}

spec fn check_bounds_for_smallest_bitting_size(size_start:int, size_end:int) -> bool
    decreases size_end - size_start,
{
   if size_start >= size_end {
       true
   } else {
          property_bounds_for_smallest_bitting_size(size_start)
       && check_bounds_for_smallest_bitting_size(size_start + 1, size_end)
   }
}

#[verifier::external_body]
proof fn result_bounds_for_smallest_bitting_size(size_start:int, size_end:int)
    ensures
        check_bounds_for_smallest_bitting_size(size_start, size_end) ==>
            (forall |size| size_start <= size < size_end ==>
                 property_bounds_for_smallest_bitting_size(size)),
    decreases size_end - size_start,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn bounds_for_smallest_bin_fitting_size(size: int)
    requires 0 <= size <= 128 * 8,
    ensures
        valid_bin_idx(smallest_bin_fitting_size(size)),
        size_of_bin(smallest_bin_fitting_size(size)) >= size,
{
    unimplemented!()
}

spec fn property_smallest_bin_fitting_size_size_of_bin(bin_idx:int) -> bool
{
    smallest_bin_fitting_size(size_of_bin(bin_idx) as int) == bin_idx
}

spec fn check_smallest_bin_fitting_size_size_of_bin(bin_idx_start:int, bin_idx_end:int) -> bool
    decreases bin_idx_end - bin_idx_start,
{
   if bin_idx_start >= bin_idx_end {
       true
   } else {
          property_smallest_bin_fitting_size_size_of_bin(bin_idx_start)
       && check_smallest_bin_fitting_size_size_of_bin(bin_idx_start + 1, bin_idx_end)
   }
}

#[verifier::external_body]
proof fn result_smallest_bin_fitting_size_size_of_bin(bin_idx_start:int, bin_idx_end:int)
    ensures
        check_smallest_bin_fitting_size_size_of_bin(bin_idx_start, bin_idx_end) ==>
            (forall |bin_idx| bin_idx_start <= bin_idx < bin_idx_end ==>
                 property_smallest_bin_fitting_size_size_of_bin(bin_idx)),
    decreases bin_idx_end - bin_idx_start,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn smallest_bin_fitting_size_size_of_bin(bin_idx: int)
    requires valid_bin_idx(bin_idx),
    ensures smallest_bin_fitting_size(size_of_bin(bin_idx) as int) == bin_idx,
{
    unimplemented!()
}

#[verifier::external_body]
proof fn leading_zeros_monotonic(w:u64)
    ensures
       forall |x:u64| x < w ==> u64_leading_zeros(w) <= u64_leading_zeros(x),
    decreases w,
{
    unimplemented!()
}

#[verifier::external_body]
proof fn leading_zeros_between(lo:u64, mid:u64, hi:u64)
    requires lo <= mid < hi,
    ensures u64_leading_zeros(lo) >= u64_leading_zeros(mid) >= u64_leading_zeros(hi),
{
    unimplemented!()
}

spec fn property_bin(size:int) -> bool
{
    131072 >= size_of_bin(smallest_bin_fitting_size(size)) >= size
}

spec fn check_bin(size_start:int, size_end:int) -> bool
    decreases size_end - size_start + 8,
{
   if size_start >= size_end {
       true
   } else {
          property_bin(size_start)
       && check_bin(size_start + 8, size_end)
   }
}

spec fn id(i:int) -> bool { true }

#[verifier::spinoff_prover]
#[verifier::external_body]
proof fn result_bin(size_start:int, size_end:int)
    requires size_start % 8 == 0,
    ensures
        check_bin(size_start, size_end) ==>
            (forall |size: int| size_start <= size < size_end && size % 8 == 0 ==>
                 #[trigger] id(size) && property_bin(size)),
    decreases size_end - size_start + 8,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn bin_size_result(size: usize)
    requires
        size <= 131072,
        valid_bin_idx(smallest_bin_fitting_size(size as int)),
    ensures
        131072 >= size_of_bin(smallest_bin_fitting_size(size as int) as int) >= size,
    decreases 8 - ((size + 7) % 8)
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn bin_size_result_mul8(size: usize)
    requires
        size % 8 == 0,
        size <= 131072,
        valid_bin_idx(smallest_bin_fitting_size(size as int)),
    ensures
        131072 >= size_of_bin(smallest_bin_fitting_size(size as int) as int) >= size,
{
    unimplemented!()
}

#[verifier::external_body]
pub fn bin(size: usize) -> (bin_idx: u8)
    requires
        size <= MAX_ALLOC_SIZE,
        size <= 131072,
    ensures
        valid_bin_idx(bin_idx as int),
        size_of_bin(bin_idx as int) >= size,
        bin_idx == smallest_bin_fitting_size(size as int),
{
   unimplemented!()
}


pub open spec fn valid_sbin_idx(sbin_idx: int) -> bool {
    0 <= sbin_idx <= SEGMENT_BIN_MAX
}

pub closed spec fn size_of_sbin(sbin_idx: int) -> nat
    recommends valid_sbin_idx(sbin_idx)
{
    if 0 <= sbin_idx <= 7 {
        sbin_idx as nat
    } else if sbin_idx == 8 {
        10
    } else {
        let group = (sbin_idx - 8) / 4;
        let inner = (sbin_idx - 8) % 4;

        ((inner + 5) * pow2(group + 1)) as nat
    }
}

pub open spec fn smallest_sbin_fitting_size(i: int) -> int
{
    if i <= 8 {
        i
    } else {
        let w = (i - 1) as u64;
        let lz = u64_leading_zeros(w);
        let b = (usize::BITS - 1 - lz) as u8;
        let sbin_idx = ((b << 2u8) as u64 | ((w >> (b as u64 - 2) as u64) & 0x03)) - 4;
        sbin_idx
    }
}

spec fn property_sbin_idx_smallest_sbin_fitting_size(size:int) -> bool
{
    valid_sbin_idx(smallest_sbin_fitting_size(size))
}

spec fn check_sbin_idx_smallest_sbin_fitting_size(size_start:int, size_end:int) -> bool
    decreases size_end - size_start,
{
   if size_start >= size_end {
       true
   } else {
          property_sbin_idx_smallest_sbin_fitting_size(size_start)
       && check_sbin_idx_smallest_sbin_fitting_size(size_start + 1, size_end)
   }
}

#[verifier::external_body]
proof fn result_sbin_idx_smallest_sbin_fitting_size(size_start:int, size_end:int)
    ensures
        check_sbin_idx_smallest_sbin_fitting_size(size_start, size_end) ==>
            (forall |size| size_start <= size < size_end ==>
                 property_sbin_idx_smallest_sbin_fitting_size(size)),
    decreases size_end - size_start,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn valid_sbin_idx_smallest_sbin_fitting_size(i: int)
    requires 0 <= i <= SLICES_PER_SEGMENT
    ensures valid_sbin_idx(smallest_sbin_fitting_size(i)),
{
    unimplemented!()
}

spec fn property_sbin_bounds(size:int) -> bool
{
    let lz = u64_leading_zeros(size as u64);
    let b = (63 - lz) as u8;
    (b  >= 2) &&
    (((b << 2u8) as u64 | ((size as u64 >> (b as u64 - 2) as u64) & 0x03)) >= 4)
}

spec fn check_sbin_bounds(size_start:int, size_end:int) -> bool
    decreases size_end - size_start,
{
   if size_start >= size_end {
       true
   } else {
          property_sbin_bounds(size_start)
       && check_sbin_bounds(size_start + 1, size_end)
   }
}

#[verifier::external_body]
proof fn result_sbin_bounds(size_start:int, size_end:int)
    ensures
        check_sbin_bounds(size_start, size_end) ==>
            (forall |size| size_start <= size < size_end ==>
                 property_sbin_bounds(size)),
    decreases size_end - size_start,
{
    unimplemented!()
}

spec fn property_sbin(slice_count:int) -> bool
{
    let sbin_idx = smallest_sbin_fitting_size(slice_count as int);
    valid_sbin_idx(sbin_idx as int) &&
    size_of_sbin(sbin_idx as int) >= slice_count
}

spec fn check_sbin(size_start:int, size_end:int) -> bool
    decreases size_end - size_start,
{
   if size_start >= size_end {
       true
   } else {
          property_sbin(size_start)
       && check_sbin(size_start + 1, size_end)
   }
}

#[verifier::external_body]
proof fn result_sbin(size_start:int, size_end:int)
    ensures
        check_sbin(size_start, size_end) ==>
            (forall |size| size_start <= size < size_end ==>
                 property_sbin(size)),
    decreases size_end - size_start,
{
    unimplemented!()
}

#[verifier::external_body]
pub fn slice_bin(slice_count: usize) -> (sbin_idx: usize)
    requires slice_count <= SLICES_PER_SEGMENT
    ensures
        valid_sbin_idx(sbin_idx as int),
        size_of_sbin(sbin_idx as int) >= slice_count,
        sbin_idx == smallest_sbin_fitting_size(slice_count as int),
{
   unimplemented!()
}
}
}
mod dealloc_token {
#![allow(unused_imports)]
use vstd::raw_ptr::*;
use crate::tokens::{Mim, BlockId, DelayState};
use crate::types::*;
use crate::layout::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus!{

pub tracked struct MimDealloc {
    pub(crate) tracked padding: PointsToRaw,

    pub(crate) ghost _size: int,

    pub(crate) tracked inner: MimDeallocInner,
}

pub tracked struct MimDeallocInner {
    pub tracked mim_instance: Mim::Instance,
    pub tracked mim_block: Mim::block,

    pub ghost ptr: *mut u8,
}

pub open spec fn valid_block_token(block: Mim::block, instance: Mim::Instance) -> bool {
    &&& block.key().wf()
    &&& block.instance_id() == instance.id()



    &&& is_segment_ptr(
        block.value().segment_shared_access.points_to.ptr(),
        block.key().page_id.segment_id)
    &&& block.value().segment_shared_access.points_to.is_init()
    &&& block.value().segment_shared_access.points_to.value()
        .wf(instance, block.key().page_id.segment_id)


    &&& is_page_ptr(
        block.value().page_slice_shared_access.points_to.ptr(),
        block.key().page_id_for_slice())
    &&& block.value().page_slice_shared_access.points_to.is_init()
    &&& block.value().page_slice_shared_access.points_to.value().offset as int
          == (block.key().slice_idx - block.key().page_id.idx) * crate::config::SIZEOF_PAGE_HEADER


    &&& block.value().page_shared_access.wf(
        block.key().page_id,
        block.key().block_size,
        instance)
}

impl MimDeallocInner {
    #[verifier(inline)]
    pub open spec fn block_id(&self) -> BlockId {
        self.mim_block.key()
    }

    pub open spec fn wf(&self) -> bool {
        &&& valid_block_token(self.mim_block, self.mim_instance)
        &&& is_block_ptr(self.ptr, self.block_id())
    }

    #[verifier::external_body]
    pub(crate) proof fn into_user(tracked self, tracked points_to_raw: PointsToRaw, sz: int)
        -> (tracked res: (MimDealloc, PointsToRaw))

        requires
            self.wf(),
            points_to_raw.is_range(self.ptr as int, self.block_id().block_size as int),
            points_to_raw.provenance() == self.ptr@.provenance,
            0 <= sz <= self.block_id().block_size,
        ensures ({
            let (md, points_to_raw) = res;
            points_to_raw.is_range(self.ptr as int, sz)
            && points_to_raw.provenance() == self.ptr@.provenance
            && md.size() == sz
            && md.block_id() == self.block_id()
            && md.ptr() == self.ptr
            && md.inst() == self.mim_instance
        })
    {
        unimplemented!()
    }
}

impl MimDealloc {
    pub closed spec fn block_id(&self) -> BlockId {
        self.inner.block_id()
    }

    pub closed spec fn ptr(&self) -> *mut u8 {
        self.inner.ptr
    }

    pub closed spec fn inst(&self) -> Mim::Instance {
        self.inner.mim_instance
    }

    pub closed spec fn size(&self) -> int {
        self._size
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.inner.wf()
          && self.block_id().block_size - self._size >= 0
          && self._size >= 0
          && self.padding.is_range(self.inner.ptr as int + self._size,
              self.block_id().block_size - self._size)
          && self.padding.provenance() == self.inner.ptr@.provenance
    }

    #[verifier::external_body]
    pub(crate) proof fn into_internal(tracked self, tracked points_to_raw: PointsToRaw)
        -> (tracked res: (MimDeallocInner, PointsToRaw))

        requires
            points_to_raw.is_range(self.ptr() as int, self.size()),
            points_to_raw.provenance() == self.ptr()@.provenance
        ensures ({
            let (md, points_to_raw_full) = res;
            md.wf()
            && points_to_raw_full.is_range(self.ptr() as int, self.block_id().block_size as int)
            && points_to_raw_full.provenance() == points_to_raw.provenance()
            && self.ptr() == md.ptr
            && self.block_id().block_size == md.mim_block.key().block_size
            && md.mim_instance == self.inst()
        })
    {
        unimplemented!()
    }
}


}
}
mod page_organization {
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::*;
use verus_state_machines_macros::*;

use crate::tokens::{PageId, SegmentId, TldId};
use crate::config::*;
use crate::bin_sizes::{valid_sbin_idx, smallest_sbin_fitting_size, smallest_bin_fitting_size, valid_bin_idx, size_of_bin};

verus!{

pub ghost struct DlistHeader {
    pub first: Option<PageId>,
    pub last: Option<PageId>,
}

pub ghost struct DlistEntry {
    pub prev: Option<PageId>,
    pub next: Option<PageId>,
}

#[is_variant]
pub ghost enum PageHeaderKind {
    Normal(int, int),
}

pub ghost struct PageData {
    pub dlist_entry: Option<DlistEntry>,
    pub count: Option<nat>,
    pub offset: Option<nat>,

    pub is_used: bool,
    pub full: Option<bool>,
    pub page_header_kind: Option<PageHeaderKind>,
}

pub ghost struct SegmentData {
    pub used: int,
}

#[is_variant]
pub ghost enum Popped {
    No,
    Ready(PageId, bool),
    Used(PageId, bool),

    SegmentCreating(SegmentId),
    VeryUnready(SegmentId, int, int, bool),

    SegmentFreeing(SegmentId, int),

    ExtraCount(SegmentId),
}

pub open spec fn page_id_range(segment_id: SegmentId, lo: nat, hi: nat) -> Set<PageId> {
    vstd::contrib::set_build!{ PageId { segment_id, idx }: PageId | idx: nat in lo..hi }
}

state_machine!{ PageOrg {
    fields {
        pub unused_dlist_headers: Seq<DlistHeader>,
        pub used_dlist_headers: Seq<DlistHeader>,
        pub pages: Map<PageId, PageData>,
        pub segments: Map<SegmentId, SegmentData>,

        pub popped: Popped,

        pub unused_lists: Seq<Seq<PageId>>,
        pub used_lists: Seq<Seq<PageId>>,
    }

    #[invariant]
    pub open spec fn public_invariant(&self) -> bool {
        &&& self.unused_dlist_headers.len() == SEGMENT_BIN_MAX + 1
        &&& self.used_dlist_headers.len() == BIN_FULL + 1
        &&& (forall |page_id| #[trigger] self.pages.dom().contains(page_id) ==>
              self.segments.dom().contains(page_id.segment_id))
    }

    #[invariant]
    pub closed spec fn ll_basics(&self) -> bool {
        &&& self.unused_lists.len() == SEGMENT_BIN_MAX + 1
        &&& self.used_lists.len() == BIN_FULL + 1
    }

    #[invariant]
    pub closed spec fn page_id_domain(&self) -> bool {
        forall |pid| #[trigger] self.pages.dom().contains(pid) <==> (
            self.segments.dom().contains(pid.segment_id)
              && 0 <= pid.idx <= SLICES_PER_SEGMENT
        )
    }

    #[invariant]
    pub closed spec fn count_off0(&self) -> bool {
        forall |pid: PageId|
            #[trigger] self.pages.dom().contains(pid) ==>
            (self.pages[pid].count.is_some() <==> self.pages[pid].offset == Some(0nat))
    }

    #[invariant]
    pub closed spec fn end_is_unused(&self) -> bool {
        forall |pid: PageId|
            self.pages.dom().contains(pid) && pid.idx == SLICES_PER_SEGMENT ==>
              !self.pages[pid].is_used
              && self.pages[pid].offset.is_none()
    }

    #[invariant]
    pub closed spec fn count_is_right(&self) -> bool {
        forall |sid| #[trigger] self.segments.dom().contains(sid) ==>
            self.segments[sid].used == self.ucount(sid) + self.popped_ec(sid)
    }

    #[invariant]
    pub closed spec fn popped_basics(&self) -> bool {
        match self.popped {
            Popped::No => true,
            Popped::Ready(page_id, _) => {
                self.pages.dom().contains(page_id)
                  && self.pages[page_id].is_used == false
                  && is_unused_header(self.pages[page_id])
                  && page_id.idx != 0
                  && self.pages[page_id].count.is_some()
                  && page_id.idx + self.pages[page_id].count.unwrap() <= SLICES_PER_SEGMENT
                  && !is_in_lls(page_id, self.unused_lists)
            }
            Popped::Used(page_id, _) => {
                self.pages.dom().contains(page_id)
                  && self.pages[page_id].is_used == true
                  && is_used_header(self.pages[page_id])
                  && page_id.idx != 0
                  && self.pages[page_id].count.is_some()
                  && page_id.idx + self.pages[page_id].count.unwrap() <= SLICES_PER_SEGMENT
            }
            Popped::SegmentCreating(segment_id) => {
                self.segments.dom().contains(segment_id)
            }
            Popped::SegmentFreeing(segment_id, idx) => {
                self.segments.dom().contains(segment_id)
                    && 0 < idx <= SLICES_PER_SEGMENT
                    && self.seg_free_prefix(segment_id, idx)
                    && self.segments[segment_id].used == 0
                    && (forall |page_id: PageId| page_id.segment_id == segment_id &&
                        0 <= page_id.idx < idx &&
                        #[trigger] self.pages.dom().contains(page_id) ==>
                            self.pages[page_id].is_used == false)
            }
            Popped::VeryUnready(segment_id, start, count, _) => {
                let page_id = PageId { segment_id, idx: start as nat };
                self.pages.dom().contains(page_id)
                  && self.pages[page_id].is_used == false
                  && self.good_range_very_unready(PageId { segment_id, idx: start as nat })

                  && self.segments.dom().contains(segment_id)
                  && 1 <= start < start + count <= SLICES_PER_SEGMENT
            }
            Popped::ExtraCount(segment_id) => {
                self.segments.dom().contains(segment_id)
            }
        }
    }

    #[invariant]
    pub closed spec fn data_for_used_header(&self) -> bool {
        forall |page_id: PageId| #[trigger] self.pages.dom().contains(page_id)
            ==> is_used_header(self.pages[page_id])
            ==> self.pages[page_id].count.is_some()
                && self.pages[page_id].count.unwrap() > 0
                && self.pages[page_id].offset == Some(0nat)
    }

    #[invariant]
    pub closed spec fn inv_segment_creating(&self) -> bool {
        match self.popped {
            Popped::SegmentCreating(segment_id) => {
                forall |pid: PageId|
                  pid.segment_id == segment_id
                    && self.pages.dom().contains(pid) ==>
                        !(#[trigger] self.pages[pid]).is_used
                        && self.pages[pid].offset.is_none()
                        && self.pages[pid].count.is_none()
                        && self.pages[pid].page_header_kind.is_none()
                        && self.pages[pid].dlist_entry.is_none()
                        && self.pages[pid].full.is_none()
            }
            _ => true,
        }
    }

    #[invariant]
    pub closed spec fn inv_very_unready(&self) -> bool {
        match self.popped {
            Popped::VeryUnready(segment_id, start, count, _) => {
                forall |pid: PageId|
                  pid.segment_id == segment_id
                    && start <= pid.idx < start + count ==>
                        !(#[trigger] self.pages[pid]).is_used
                        && self.pages[pid].offset.is_none()
                        && self.pages[pid].count.is_none()
                        && self.pages[pid].page_header_kind.is_none()
                        && self.pages[pid].dlist_entry.is_none()
                        && self.pages[pid].full.is_none()
            }
            _ => true,
        }
    }

    #[invariant]
    pub closed spec fn inv_ready(&self) -> bool {
        match self.popped {
            Popped::Ready(page_id, _) => {
                forall |pid: PageId|
                    pid.segment_id == page_id.segment_id
                      && page_id.idx <= pid.idx < page_id.idx + self.pages[page_id].count.unwrap()
                    ==>
                        self.pages.dom().contains(pid) ==>
                        !(#[trigger] self.pages[pid]).is_used
                        && self.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
                        && (self.pages[pid].count.is_some() <==> pid == page_id)
                        && self.pages[pid].page_header_kind.is_none()
                        && self.pages[pid].dlist_entry.is_none()
                        && self.pages[pid].full.is_none()
            }
            _ => true,
        }
    }

    #[invariant]
    pub closed spec fn inv_used(&self) -> bool {
        match self.popped {
            Popped::Used(page_id, _) => {
                forall |pid: PageId|
                    #![trigger self.pages.index(pid)]
                    #![trigger self.pages.dom().contains(pid)]
                    pid.segment_id == page_id.segment_id
                      && page_id.idx <= pid.idx < page_id.idx + self.pages[page_id].count.unwrap()
                    ==>
                        self.pages.dom().contains(pid)
                        && self.pages[pid].is_used
                        && self.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
                        && (self.pages[pid].count.is_some() <==> pid == page_id)
                        && (self.pages[pid].page_header_kind.is_some() <==> pid == page_id)
                        && self.pages[pid].dlist_entry.is_none()
                        && self.pages[pid].full.is_none()
            }
            _ => true,
        }
    }

    #[invariant]
    pub closed spec fn data_for_unused_header(&self) -> bool {
        forall |page_id: PageId| #[trigger] self.pages.dom().contains(page_id)
            ==> is_unused_header(self.pages[page_id])
            ==> self.pages[page_id].count.is_some()
                && self.pages[page_id].count.unwrap() > 0
                && self.pages[page_id].offset == Some(0nat)
    }

    #[invariant]
    pub closed spec fn ll_inv_valid_unused(&self) -> bool {
        forall |i| 0 <= i < self.unused_lists.len() ==> valid_ll(self.pages, self.unused_dlist_headers[i], self.unused_lists[i])
    }


    #[invariant]
    pub closed spec fn ll_inv_valid_used(&self) -> bool {
        forall |i| 0 <= i < self.used_lists.len() ==> valid_ll(self.pages, self.used_dlist_headers[i], self.used_lists[i])
    }

    #[invariant]
    pub closed spec fn ll_inv_valid_unused2(&self) -> bool {
        forall |i| #![trigger self.unused_lists.index(i)] 0 <= i < self.unused_lists.len() ==>
          forall |j| #![trigger self.unused_lists.index(i).index(j)] 0 <= j < self.unused_lists[i].len() ==>
              self.pages.dom().contains(#[trigger] self.unused_lists[i][j])
              && is_unused_header(self.pages[self.unused_lists[i][j]])
              && self.unused_lists[i][j].idx != 0
              && self.pages[self.unused_lists[i][j]].count.is_some()
              && i == smallest_sbin_fitting_size(
                  self.pages[self.unused_lists[i][j]].count.unwrap() as int)
    }

    #[invariant]
    pub closed spec fn ll_inv_valid_used2(&self) -> bool {
        forall |i| #![trigger self.used_lists.index(i)] 0 <= i < self.used_lists.len() ==>
          forall |j| #![trigger self.used_lists.index(i).index(j)] 0 <= j < self.used_lists[i].len() ==>
              self.pages.dom().contains(#[trigger] self.used_lists[i][j])
              && is_used_header(self.pages[self.used_lists[i][j]])
              && self.used_lists[i][j].idx != 0
              && self.pages[self.used_lists[i][j]].full.is_some()
              && (self.pages[self.used_lists[i][j]].full.unwrap() <==> i == BIN_FULL)
              && (match self.pages[self.used_lists[i][j]].page_header_kind {
                  None => false,
                  Some(PageHeaderKind::Normal(bin, bsize)) =>
                      valid_bin_idx(bin)
                        && bsize == crate::bin_sizes::size_of_bin(bin)
                        && (i != BIN_FULL ==> i == bin)
                        && bsize <= MEDIUM_OBJ_SIZE_MAX,
              })
    }

    #[invariant]
    #[verifier::opaque]
    pub closed spec fn ll_inv_exists_in_some_list(&self) -> bool {
        forall |page_id: PageId| #[trigger] self.pages.dom().contains(page_id)
            && self.pages[page_id].offset == Some(0nat)
            && page_id.idx != 0
            && !self.expect_out_of_lists(page_id)
                ==> is_in_lls(page_id, self.used_lists) || is_in_lls(page_id, self.unused_lists)
    }


    #[invariant]
    pub closed spec fn attached_ranges(&self) -> bool {
        forall |segment_id| #[trigger] self.segments.dom().contains(segment_id) ==>
            self.attached_ranges_segment(segment_id)
    }

    pub closed spec fn attached_ranges_segment(&self, segment_id: SegmentId) -> bool {
        match self.popped {
            Popped::SegmentCreating(sid) if sid == segment_id => true,
            Popped::SegmentFreeing(sid, idx) if sid == segment_id && idx > 0 => self.attached_rec(segment_id, idx, false),
            _ => self.attached_rec0(segment_id, self.popped_for_seg(segment_id))
        }
    }

    pub closed spec fn seg_free_prefix(&self, segment_id: SegmentId, idx: int) -> bool {
        forall |pid: PageId|
            #![trigger self.pages.dom().contains(pid)]
            #![trigger self.pages.index(pid)]
            pid.segment_id == segment_id && 0 <= pid.idx < idx ==>
            self.pages.dom().contains(pid)
            && self.pages[pid].dlist_entry.is_none()
            && self.pages[pid].count.is_none()
            && self.pages[pid].offset.is_none()
            && self.pages[pid].is_used == false
            && self.pages[pid].full.is_none()
            && self.pages[pid].page_header_kind.is_none()
    }

    pub closed spec fn attached_rec0(&self, segment_id: SegmentId, sp: bool) -> bool {
        self.good_range0(segment_id)
          && self.attached_rec(segment_id, self.pages[PageId { segment_id, idx: 0 }].count.unwrap() as int, sp)
    }

    #[verifier::opaque]
    pub closed spec fn attached_rec(&self, segment_id: SegmentId, idx: int, sp: bool) -> bool
        decreases SLICES_PER_SEGMENT - idx
    {
        if idx == SLICES_PER_SEGMENT {
          !sp
        } else if idx > SLICES_PER_SEGMENT {
          false
        } else if Self::is_the_popped(segment_id, idx, self.popped) {
          sp
            && self.popped_len() > 0
            && idx + self.popped_len() <= SLICES_PER_SEGMENT
            && self.attached_rec(segment_id, idx + self.popped_len(), false)
        } else {
          let page_id = PageId { segment_id, idx: idx as nat };
               (self.pages[page_id].is_used ==> self.good_range_used(page_id))
            && (!self.pages[page_id].is_used ==> self.good_range_unused(page_id))
            && self.pages[page_id].count.unwrap() > 0
            && idx + self.pages[page_id].count.unwrap() <= SLICES_PER_SEGMENT
            && self.attached_rec(segment_id, idx + self.pages[page_id].count.unwrap(), sp)
        }
    }

    pub closed spec fn popped_ranges_match(pre: Self, post: Self) -> bool {
        Self::is_any_the_popped(pre.popped) == Self::is_any_the_popped(post.popped)
          && (Self::is_any_the_popped(pre.popped) ==>
              pre.popped_len() == post.popped_len()
                && Self::page_id_of_popped(pre.popped) == Self::page_id_of_popped(post.popped)
          )
    }

    pub closed spec fn popped_ranges_match_for_sid(pre: Self, post: Self, sid: SegmentId) -> bool {
        pre.popped_for_seg(sid) == post.popped_for_seg(sid)
          && (pre.popped_for_seg(sid) ==>
              pre.popped_len() == post.popped_len()
                && Self::page_id_of_popped(pre.popped) == Self::page_id_of_popped(post.popped)
          )
    }


    pub closed spec fn popped_for_seg(&self, segment_id: SegmentId) -> bool {
        match self.popped {
            Popped::No => false,
            Popped::Ready(page_id, _)
                | Popped::Used(page_id, _)
                => page_id.segment_id == segment_id,
            Popped::SegmentCreating(_) => false,
            Popped::SegmentFreeing(_, _) => false,
            Popped::VeryUnready(sid, _, _, _) => sid == segment_id,
            Popped::ExtraCount(_) => false,
        }
    }

    pub closed spec fn is_any_the_popped(popped: Popped) -> bool {
        match popped {
            Popped::No => false,
            Popped::Ready(page_id, _)
                | Popped::Used(page_id, _)
                => true,
            Popped::SegmentCreating(_) => false,
            Popped::SegmentFreeing(_, _) => false,
            Popped::VeryUnready(sid, i, _, _) => true,
            Popped::ExtraCount(_) => false,
        }
    }

    pub closed spec fn is_the_popped(segment_id: SegmentId, idx: int, popped: Popped) -> bool {
        match popped {
            Popped::No => false,
            Popped::Ready(page_id, _)
                | Popped::Used(page_id, _)
                => page_id.segment_id == segment_id && page_id.idx == idx,
            Popped::SegmentCreating(_) => false,
            Popped::SegmentFreeing(_, _) => false,
            Popped::VeryUnready(sid, i, _, _) => sid == segment_id && i == idx,
            Popped::ExtraCount(_) => false,
        }
    }

    pub closed spec fn popped_len(&self) -> int {
        match self.popped {
            Popped::No => arbitrary(),
            Popped::Ready(page_id, _)
                | Popped::Used(page_id, _)
                => self.pages[page_id].count.unwrap() as int,
            Popped::SegmentCreating(_) => arbitrary(),
            Popped::SegmentFreeing(_, _) => arbitrary(),
            Popped::VeryUnready(sid, i, count, _) => count,
            Popped::ExtraCount(_) => arbitrary(),
        }
    }


    pub open spec fn valid_unused_page(&self, page_id: PageId, sbin_idx: int, list_idx: int) -> bool {
        self.pages.dom().contains(page_id)
          && self.pages[page_id].is_used == false
          && (match self.pages[page_id].count {
              Some(count) => 0 <= count <= SLICES_PER_SEGMENT,
              None => false,
          })
          && self.pages[page_id].dlist_entry.is_some()
          && 0 <= sbin_idx <= SEGMENT_BIN_MAX
          && 0 <= list_idx < self.unused_lists[sbin_idx].len()
          && self.unused_lists[sbin_idx][list_idx] == page_id
    }

    #[verifier::external_body]
    pub proof fn first_is_in(&self, sbin_idx: int)
        requires self.invariant(), self.popped.is_No(),
            0 <= sbin_idx <= SEGMENT_BIN_MAX,
        ensures
            match self.unused_dlist_headers[sbin_idx].first {
                Some(page_id) => self.valid_unused_page(page_id, sbin_idx, 0),
                None => true,
            }
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn next_is_in(&self, page_id: PageId, sbin_idx: int, list_idx: int)
        requires self.invariant(), self.popped.is_No(),
            self.valid_unused_page(page_id, sbin_idx, list_idx)
        ensures
            match self.pages[page_id].dlist_entry.unwrap().next {
                Some(page_id) => self.valid_unused_page(page_id, sbin_idx, list_idx + 1),
                None => true,
            }
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn segment_freeing_is_in(&self) -> (list_idx: int)
        requires self.invariant(),
            self.popped.is_SegmentFreeing(),
            self.popped.get_SegmentFreeing_1() < SLICES_PER_SEGMENT,
        ensures (match self.popped {
            Popped::SegmentFreeing(segment_id, idx) => { idx >= 0 && {
                let page_id = PageId { segment_id, idx: idx as nat };
                let count = self.pages[page_id].count.unwrap();
                let sbin_idx = smallest_sbin_fitting_size(count as int);
                self.valid_unused_page(page_id, sbin_idx, list_idx)
            }}
            _ => false,
        }),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn marked_full_is_in(&self, page_id: PageId) -> (list_idx: int)
        requires self.invariant(),
            self.pages.dom().contains(page_id),
            self.popped.is_No(),
            self.pages[page_id].offset == Some(0nat),
            self.pages[page_id].full != Some(false),
            self.pages[page_id].is_used,
        ensures
            self.valid_used_page(page_id, BIN_FULL as int, list_idx),
            (match self.pages[page_id].page_header_kind {
                Some(PageHeaderKind::Normal(bin, size)) =>
                  size == size_of_bin(bin)
                  && bin == smallest_bin_fitting_size(size)
                  && size <= MEDIUM_OBJ_SIZE_MAX,
                None => false,
            }),

    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn marked_unfull_is_in(&self, page_id: PageId) -> (list_idx: int)
        requires self.invariant(),
            self.pages.dom().contains(page_id),
            self.popped.is_No(),
            self.pages[page_id].offset == Some(0nat),
            self.pages[page_id].full != Some(true),
            self.pages[page_id].is_used,
        ensures
            (match self.pages[page_id].page_header_kind {
                Some(PageHeaderKind::Normal(bin, size)) =>
                  size == size_of_bin(bin)
                  && self.valid_used_page(page_id, bin, list_idx)
                  && bin == smallest_bin_fitting_size(size)
                  && size <= MEDIUM_OBJ_SIZE_MAX,
                None => false,
            }),
    {
        unimplemented!()
    }

    #[verifier::opaque]
    pub closed spec fn get_list_idx(lists: Seq<Seq<PageId>>, pid: PageId) -> (int, int) {
        let (i, j): (int, int) = choose |i: int, j: int|
            0 <= i < lists.len()
            && 0 <= j < lists[i].len()
            && lists[i][j] == pid;
        (i, j)
    }

    #[verifier::external_body]
    proof fn unused_is_in_sbin(&self, page_id: PageId)
        requires self.invariant(),
            self.pages.dom().contains(page_id),
            self.popped.is_VeryUnready() || self.popped.is_SegmentFreeing(),
            self.pages[page_id].offset == Some(0nat),
            !self.pages[page_id].is_used,
            page_id.idx != 0,
        ensures ({
            let sbin_idx = smallest_sbin_fitting_size(self.pages[page_id].count.unwrap() as int);
            let list_idx = Self::get_list_idx(self.unused_lists, page_id).1;
            self.valid_unused_page(page_id, sbin_idx, list_idx)
        })
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn get_count_bound_very_unready(&self)
        requires self.invariant(), self.popped.is_VeryUnready(),
        ensures
            0 < self.popped.get_VeryUnready_1(),
            self.popped.get_VeryUnready_1() +
                self.popped.get_VeryUnready_2() <= SLICES_PER_SEGMENT,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn lemma_range_disjoint_very_unready(&self, page_id: PageId)
        requires self.invariant(), self.popped.is_VeryUnready(),
            self.pages.dom().contains(page_id),
            self.pages[page_id].offset == Some(0nat),
            self.pages[page_id].is_used,
            page_id.segment_id == self.popped.get_VeryUnready_0(),
        ensures
            match self.popped {
                Popped::VeryUnready(_, idx, p_count, _) => {
                    match self.pages[page_id].count {
                        Some(count) => page_id.idx + count <= idx || idx + p_count <= page_id.idx,
                        None => false,
                    }
                }
                _ => false,
            }
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn lemma_range_disjoint_used2(&self, page_id1: PageId, page_id2: PageId)
        requires self.invariant(),
            self.pages.dom().contains(page_id1),
            self.pages[page_id1].offset == Some(0nat),
            self.pages[page_id1].is_used,
            self.pages.dom().contains(page_id2),
            self.pages[page_id2].offset == Some(0nat),
            self.pages[page_id2].is_used,
            page_id1 != page_id2,
            page_id1.segment_id == page_id2.segment_id,
        ensures
            match (self.pages[page_id1].count, self.pages[page_id2].count) {
                (Some(count1), Some(count2)) => {
                    page_id1.idx + count1 <= page_id2.idx
                      || page_id2.idx + count2 <= page_id1.idx
                }
                _ => false,
            }
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn used_offset0_has_count(&self, page_id: PageId)
        requires self.invariant(), self.pages.dom().contains(page_id),
            self.pages[page_id].is_used,
            self.pages[page_id].offset == Some(0nat),
            page_id.idx != 0,
        ensures
            self.pages[page_id].count.is_some()
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn get_offset_for_something_in_used_range(&self, page_id: PageId, slice_id: PageId)
        requires self.invariant(),
            self.pages.dom().contains(page_id),
            self.pages[page_id].is_used,
            self.pages[page_id].offset == Some(0nat),
            slice_id.segment_id == page_id.segment_id,
            page_id.idx <= slice_id.idx < page_id.idx + self.pages[page_id].count.unwrap(),
        ensures
            self.pages.dom().contains(slice_id),
            self.pages[slice_id].is_used,
            self.pages[slice_id].offset == Some((slice_id.idx - page_id.idx) as nat)
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn get_count_bound(&self, page_id: PageId)
        requires self.invariant(), self.pages.dom().contains(page_id),
        ensures
            (match self.pages[page_id].count {
                None => true,
                Some(count) => page_id.idx + count <= SLICES_PER_SEGMENT
            }),
    {
        unimplemented!()
    }

    pub open spec fn valid_used_page(&self, page_id: PageId, bin_idx: int, list_idx: int) -> bool {
        self.pages.dom().contains(page_id)
          && self.pages[page_id].is_used == true
          && self.pages[page_id].dlist_entry.is_some()
          && self.pages[page_id].offset == Some(0nat)
          && (crate::bin_sizes::valid_bin_idx(bin_idx) || bin_idx == BIN_FULL)
          && 0 <= list_idx < self.used_lists[bin_idx].len()
          && self.used_lists[bin_idx][list_idx] == page_id
          && (match self.pages[page_id].page_header_kind {
              None => false,
              Some(PageHeaderKind::Normal(bin, bsize)) =>
                  valid_bin_idx(bin)
                  && size_of_bin(bin) == bsize
                  && (bin_idx != BIN_FULL ==> bin_idx == bin)
          })
    }

    #[verifier::external_body]
    pub proof fn used_first_is_in(&self, bin_idx: int)
        requires self.invariant(), !self.popped.is_Ready(),
            0 <= bin_idx <= BIN_HUGE,
        ensures
            match self.used_dlist_headers[bin_idx].first {
                Some(page_id) => self.valid_used_page(page_id, bin_idx, 0),
                None => true,
            }
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn used_next_is_in(&self, page_id: PageId, bin_idx: int, list_idx: int)
        requires self.invariant(),
            self.valid_used_page(page_id, bin_idx, list_idx)
        ensures
            match self.pages[page_id].dlist_entry.unwrap().next {
                Some(page_id) => self.valid_used_page(page_id, bin_idx, list_idx + 1),
                None => true,
            }
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn rec_valid_page_after(&self, idx: int, sp: bool)
        requires self.invariant(),
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    start + len < SLICES_PER_SEGMENT
                }
                _ => false,
            },
            self.attached_rec(self.popped.get_VeryUnready_0(), idx, sp),
            !sp ==>
                idx >= Self::page_id_of_popped(self.popped).idx + self.popped_len(),
            idx >= 0,
        ensures
            sp ==> match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    let page_id = PageId { segment_id: sid, idx: (start + len) as nat };
                    self.pages.dom().contains(page_id)
                      && self.pages[page_id].offset == Some(0nat)
                }
                _ => false,
            },
            sp ==>
                idx <= Self::page_id_of_popped(self.popped).idx,
        decreases SLICES_PER_SEGMENT - idx
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn valid_page_after(&self)
        requires self.invariant(),
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    start + len < SLICES_PER_SEGMENT
                }
                _ => false,
            }
        ensures
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    let page_id = PageId { segment_id: sid, idx: (start + len) as nat };
                    self.pages.dom().contains(page_id)
                      && self.pages[page_id].offset == Some(0nat)
                }
                _ => false,
            }
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn rec_valid_page_before(&self, idx: int, sp: bool)
        requires self.invariant(),
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    start > 0
                }
                _ => false,
            },
            self.attached_rec(self.popped.get_VeryUnready_0(), idx, sp),
            !sp ==>
                idx >= Self::page_id_of_popped(self.popped).idx + self.popped_len(),
            idx >= 0,
        ensures
            idx < Self::page_id_of_popped(self.popped).idx ==> (
                match self.popped {
                    Popped::VeryUnready(sid, start, len, _) => {
                        let last_id = PageId { segment_id: sid, idx: (start - 1) as nat };
                        let offset = self.pages[last_id].offset.unwrap();
                        let page_id = PageId { segment_id: sid, idx: (last_id.idx - offset) as nat };
                        self.pages.dom().contains(last_id)
                        && last_id.idx - offset >= 0
                        && self.pages[last_id].offset.is_some()
                        && self.pages.dom().contains(page_id)
                        && self.pages[page_id].offset == Some(0nat)
                        && self.pages[page_id].count == Some(offset + 1)
                    }
                    _ => false,
                }),
            sp ==>
                idx <= Self::page_id_of_popped(self.popped).idx,
        decreases SLICES_PER_SEGMENT - idx
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn valid_page_before(&self)
        requires self.invariant(),
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    start > 0
                }
                _ => false,
            }
        ensures
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    let last_id = PageId { segment_id: sid, idx: (start - 1) as nat };
                    let offset = self.pages[last_id].offset.unwrap();
                    let page_id = PageId { segment_id: sid, idx: (last_id.idx - offset) as nat };
                    self.pages.dom().contains(last_id)
                    && last_id.idx - offset >= 0
                    && self.pages[last_id].offset.is_some()
                    && self.pages.dom().contains(page_id)
                    && self.pages[page_id].offset == Some(0nat)
                    && self.pages[page_id].count == Some(offset + 1)
                }
                _ => false,
            }
    {
        unimplemented!()
    }

    init!{
        initialize() {
            init unused_dlist_headers = Seq::new((SEGMENT_BIN_MAX + 1) as nat,
                |i| DlistHeader { first: None, last: None });
            init used_dlist_headers = Seq::new((BIN_FULL + 1) as nat,
                |i| DlistHeader { first: None, last: None });
            init pages = Map::empty();
            init segments = Map::empty();
            init popped = Popped::No;

            init unused_lists = Seq::new((SEGMENT_BIN_MAX + 1) as nat, |i| Seq::empty());
            init used_lists = Seq::new((BIN_FULL + 1) as nat, |i| Seq::empty());
        }
    }

    transition!{
        take_page_from_unused_queue(page_id: PageId, sbin_idx: int, list_idx: int) {
            require pre.valid_unused_page(page_id, sbin_idx, list_idx);
            require pre.popped == Popped::No
                || pre.popped == Popped::SegmentFreeing(page_id.segment_id, page_id.idx as int);

            assert let Some(dlist_entry) = pre.pages[page_id].dlist_entry;
            assert pre.pages[page_id].is_used == false;

            update pages[page_id] = PageData {
                dlist_entry: None,
                count: None,
                offset: None,
                .. pre.pages[page_id]
            };

            match dlist_entry.prev {
                Some(prev_page_id) => {
                    assert prev_page_id != page_id
                      && pre.pages.dom().contains(prev_page_id)
                      && pre.pages[prev_page_id].dlist_entry.is_some()
                      && pre.pages[prev_page_id].is_used == false

                      by { pre.unused_ll_stuff(sbin_idx, list_idx); };

                    update pages[prev_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            next: dlist_entry.next,
                            .. pre.pages[prev_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[prev_page_id]
                    };
                }
                Option::None => { }
            }

            match dlist_entry.next {
                Some(next_page_id) => {
                    assert next_page_id != page_id
                      && pre.pages.dom().contains(next_page_id)
                      && pre.pages[next_page_id].dlist_entry.is_some()
                      && pre.pages[next_page_id].is_used == false

                      by { pre.unused_ll_stuff(sbin_idx, list_idx); };

                    update pages[next_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            prev: dlist_entry.prev,
                            .. pre.pages[next_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[next_page_id]
                    };
                }
                Option::None => { }
            }

            if dlist_entry.prev.is_none() && dlist_entry.next.is_none() {
                update unused_dlist_headers[sbin_idx] = DlistHeader {
                    first: dlist_entry.next,
                    last: dlist_entry.prev,
                };
            } else if dlist_entry.prev.is_none() {
                update unused_dlist_headers[sbin_idx] = DlistHeader {
                    first: dlist_entry.next,
                    .. pre.unused_dlist_headers[sbin_idx]
                };
            } else if dlist_entry.next.is_none() {
                update unused_dlist_headers[sbin_idx] = DlistHeader {
                    last: dlist_entry.prev,
                    .. pre.unused_dlist_headers[sbin_idx]
                };
            }

            assert dlist_entry.prev.is_some() && dlist_entry.next.is_some() ==>
                dlist_entry.prev.unwrap() != dlist_entry.next.unwrap()

                by { pre.unused_ll_stuff(sbin_idx, list_idx); };

            assert let Some(count) = pre.pages[page_id].count;

            assert count >= 1;
            let last_id = PageId { idx: (page_id.idx + count - 1) as nat, ..page_id };
            if last_id != page_id {
                update pages[last_id] = PageData {
                    offset: None,
                    .. pre.pages[last_id]
                };
                assert(pre.pages.dom().contains(last_id))
                    by { pre.get_count_bound(page_id); };

                assert(pre.pages[last_id].is_used == false
                      && pre.pages[last_id].page_header_kind.is_none())

                    by { pre.lemma_range_not_used(page_id);
                        assert(pre.pages.dom().contains(last_id));
                    };
            }
            assert dlist_entry.prev != Some(last_id)
                && dlist_entry.next != Some(last_id)
              by { pre.unused_ll_stuff(sbin_idx, list_idx); pre.lemma_range_not_used(page_id); };

            match pre.popped {
                Popped::No => {
                    update popped = Popped::VeryUnready(page_id.segment_id, page_id.idx as int, count as int, false);
                }
                Popped::SegmentFreeing(sid, i) => {
                    update popped = Popped::SegmentFreeing(sid, i + count);
                }
                _ => { }
            }

            update unused_lists[sbin_idx] = pre.unused_lists[sbin_idx].remove(list_idx);
        }
    }

    transition!{
        split_page(page_id: PageId, current_count: int, target_count: int, sbin_idx: int) {
            require pre.popped == Popped::VeryUnready(page_id.segment_id, page_id.idx as int, current_count, false);
            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].count.is_none();
            require !pre.pages[page_id].is_used;

            require 1 <= target_count < current_count;
            require 0 <= sbin_idx <= SEGMENT_BIN_MAX;
            require sbin_idx == smallest_sbin_fitting_size(current_count - target_count);


            let next_page_id = PageId { idx: (page_id.idx + target_count) as nat, .. page_id };
            let last_page_id = PageId { idx: (page_id.idx + current_count - 1) as nat, .. page_id };
            assert pre.pages.dom().contains(next_page_id)
                && pre.pages.dom().contains(last_page_id)
                && pre.pages[next_page_id].is_used == false
                && pre.pages[last_page_id].is_used == false;

            update pages[next_page_id] = PageData {
                count: Some((current_count - target_count) as nat),
                offset: Some(0),
                dlist_entry: Some(DlistEntry {
                    prev: None,
                    next: pre.unused_dlist_headers[sbin_idx].first,
                }),
                .. pre.pages[next_page_id]
            };

            if current_count - target_count > 1 {
                update pages[last_page_id] = PageData {
                    count: None,
                    offset: Some((current_count - target_count - 1) as nat),
                    .. pre.pages[last_page_id]
                };
            }

            update unused_dlist_headers[sbin_idx] = DlistHeader {
                first: Some(next_page_id),
                last:
                    if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                        pre.unused_dlist_headers[sbin_idx].last
                    } else {
                        Some(next_page_id)
                    },
            };
            if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                let first_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                assert pre.pages.dom().contains(first_id)          by { pre.first_last_ll_stuff_unused(sbin_idx); };
                assert !pre.pages[first_id].is_used                by { pre.first_last_ll_stuff_unused(sbin_idx); };
                assert pre.pages[first_id].dlist_entry.is_some()   by { pre.first_last_ll_stuff_unused(sbin_idx); };
                assert first_id != page_id                         by { pre.first_last_ll_stuff_unused(sbin_idx); };
                assert first_id != next_page_id                    by { pre.first_last_ll_stuff_unused(sbin_idx);                                                        };
                assert first_id != last_page_id                    by { pre.first_last_ll_stuff_unused(sbin_idx);                                                        };
                update pages[first_id] = PageData {
                    dlist_entry: Some(DlistEntry {
                        prev: Some(next_page_id),
                        .. pre.pages[first_id].dlist_entry.unwrap()
                    }),
                    .. pre.pages[first_id]
                };
            }

            update popped = Popped::VeryUnready(page_id.segment_id, page_id.idx as int, target_count, false);
            update unused_lists = Self::insert_front(pre.unused_lists, sbin_idx, next_page_id);
        }
    }

    transition!{
        create_segment(segment_id: SegmentId) {
            require pre.popped == Popped::No;
            require !pre.segments.dom().contains(segment_id);

            let new_pages = Map::new(
                page_id_range(segment_id, 0, SLICES_PER_SEGMENT as nat + 1),
                |page_id: PageId| PageData {
                    dlist_entry: None,
                    count: None,
                    offset: None,
                    is_used: false,
                    page_header_kind: None,
                    full: None,
                });

            update segments = pre.segments.insert(segment_id, SegmentData { used: 0 });
            update pages = pre.pages.union_prefer_right(new_pages);
            update popped = Popped::SegmentCreating(segment_id);
        }
    }

    transition!{
        allocate_popped() {
            require let Popped::VeryUnready(segment_id, idx, count, fals) = pre.popped;
            require fals == false;
            assert idx >= 0;
            let page_id = PageId { segment_id, idx: idx as nat };
            assert pre.pages.dom().contains(page_id);
            assert count > 0;
            assert count + page_id.idx <= SLICES_PER_SEGMENT;

            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages.dom().contains(pid)
                );
            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> !pre.pages[pid].is_used
                );

            let changed_pages = Map::new(
                page_id_range(page_id.segment_id, page_id.idx, page_id.idx + count as nat),
                |pid: PageId| PageData {
                    count: if pid == page_id { Some(count as nat) } else { pre.pages[pid].count },
                    offset: Some((pid.idx - page_id.idx) as nat),
                    dlist_entry: pre.pages[pid].dlist_entry,
                    is_used: false,
                    page_header_kind: None,
                    full: None,
                }
            );

            let new_pages = pre.pages.union_prefer_right(changed_pages);
            assert pre.pages.dom() =~= new_pages.dom();

            assert pre.segments[page_id.segment_id].used <= SLICES_PER_SEGMENT + 1
                by { pre.lemma_used_bound(page_id.segment_id); };
            update segments[page_id.segment_id] = SegmentData {
                used: pre.segments[page_id.segment_id].used + 1,
            };

            update pages = new_pages;
            update popped = Popped::Ready(page_id, true);
        }
    }

    transition!{
        forget_about_first_page(count: int) {
            require 1 <= count < SLICES_PER_SEGMENT;
            require let Popped::SegmentCreating(segment_id) = pre.popped;
            assert pre.segments.dom().contains(segment_id);

            assert (forall |pid: PageId| pid.segment_id == segment_id &&
                    0 <= pid.idx < count
                    ==> pre.pages.dom().contains(pid)
                );
            assert (forall |pid: PageId| pid.segment_id == segment_id &&
                    0 <= pid.idx < count
                    ==> !pre.pages[pid].is_used
                );

            let page_id = PageId { segment_id, idx: 0 };
            assert pre.pages.dom().contains(page_id);
            assert count + page_id.idx <= SLICES_PER_SEGMENT;
            let changed_pages = Map::new(
                page_id_range(segment_id, 0, count as nat),
                |pid: PageId| PageData {
                    count: if pid == page_id { Some(count as nat) } else { pre.pages[pid].count },
                    offset: Some((pid.idx - page_id.idx) as nat),
                    dlist_entry: pre.pages[pid].dlist_entry,
                    is_used: false,
                    page_header_kind: None,
                    full: None,
                }
            );

            let new_pages = pre.pages.union_prefer_right(changed_pages);
            assert pre.pages.dom() =~= new_pages.dom();
            update pages = new_pages;

            assert pre.segments[page_id.segment_id].used <= SLICES_PER_SEGMENT + 1
                by { pre.lemma_used_bound(page_id.segment_id); };
            update segments[page_id.segment_id] = SegmentData {
                used: pre.segments[page_id.segment_id].used + 1,
            };

            update popped = Popped::VeryUnready(segment_id, count, SLICES_PER_SEGMENT - count, true);
        }
    }

    transition!{
        forget_about_first_page2() {
            require let Popped::VeryUnready(segment_id, start, count, tru) = pre.popped;
            require tru == true;

            assert pre.segments[segment_id].used >= 1;
            update segments[segment_id] = SegmentData {
                used: pre.segments[segment_id].used - 1,
            };

            update popped = Popped::VeryUnready(segment_id, start, count, false);
        }
    }

    transition!{
        clear_ec() {
            require let Popped::ExtraCount(segment_id) = pre.popped;

            assert pre.segments[segment_id].used >= 1;
            update segments[segment_id] = SegmentData {
                used: pre.segments[segment_id].used - 1,
            };

            update popped = Popped::No;
        }
    }


    transition!{
        free_to_unused_queue(sbin_idx: int) {
            require valid_sbin_idx(sbin_idx);
            require let Popped::VeryUnready(segment_id, start, count, ec) = pre.popped;
            assert pre.segments.dom().contains(segment_id);
            assert 1 <= start < start + count <= SLICES_PER_SEGMENT;

            require sbin_idx == smallest_sbin_fitting_size(count);

            let first_page = PageId { segment_id, idx: start as nat };
            let last_page = PageId { segment_id, idx: (first_page.idx + count - 1) as nat };

            assert pre.pages.dom().contains(first_page);
            assert !pre.pages[first_page].is_used;
            assert pre.pages.dom().contains(last_page);
            assert !pre.pages[last_page].is_used;

            assert pre.pages[first_page].count.is_none();
            assert pre.pages[first_page].offset.is_none();
            assert pre.pages[last_page].offset.is_none();

            update pages[first_page] = PageData {
                dlist_entry: Some(DlistEntry {
                    prev: None,
                    next: pre.unused_dlist_headers[sbin_idx].first,
                }),
                count: Some(count as nat),
                offset: Some(0),
                is_used: false,
                page_header_kind: None,
                full: None,
            };

            if count > 1 {
                assert last_page != first_page;
                update pages[last_page] = PageData {
                    offset: Some((count - 1) as nat),
                    .. pre.pages[last_page]
                };
            }

            update unused_dlist_headers[sbin_idx] = DlistHeader {
                first: Some(first_page),
                last: if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                    pre.unused_dlist_headers[sbin_idx].last
                } else {
                    Some(first_page)
                },
            };

            if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                let queue_first_page_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                assert queue_first_page_id != first_page;
                assert queue_first_page_id != last_page;
                assert pre.pages.dom().contains(queue_first_page_id);
                assert !pre.pages[queue_first_page_id].is_used;
                assert pre.pages[queue_first_page_id].dlist_entry.is_some()
                    by { pre.first_last_ll_stuff_unused(sbin_idx); };

                update pages[queue_first_page_id] = PageData {
                    dlist_entry: Some(DlistEntry {
                        prev: Some(first_page),
                        .. pre.pages[queue_first_page_id].dlist_entry.unwrap()
                    }),
                    .. pre.pages[queue_first_page_id]
                };
            }

            update popped = if ec { Popped::ExtraCount(segment_id) } else { Popped::No };
            update unused_lists = Self::insert_front(pre.unused_lists, sbin_idx, first_page);
        }
    }


    transition!{
        set_range_to_used(page_header_kind: PageHeaderKind) {
            require let Popped::Ready(page_id, b) = pre.popped;
            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].count.is_some();
            let count = pre.pages[page_id].count.unwrap();
            assert count > 0;
            assert pre.pages[page_id].offset == Some(0nat);
            assert page_id.idx != 0;

            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages.dom().contains(pid)
                );
            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> !pre.pages[pid].is_used
                );
            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages[pid].offset.is_some()
                        && pre.pages[pid].offset.unwrap() == pid.idx - page_id.idx
                );

            let changed_pages = Map::new(
                page_id_range(page_id.segment_id, page_id.idx, page_id.idx + count),
                |pid: PageId| PageData {
                    is_used: true,
                    page_header_kind: if pid == page_id { Some(page_header_kind) } else { None },
                    .. pre.pages[pid]
                }
            );

            let new_pages = pre.pages.union_prefer_right(changed_pages);
            assert pre.pages.dom() =~= new_pages.dom();

            update pages = new_pages;
            update popped = Popped::Used(page_id, b);
        }
    }

    transition!{
        set_range_to_not_used() {
            require let Popped::Used(page_id, b) = pre.popped;
            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].count.is_some();
            let count = pre.pages[page_id].count.unwrap();
            assert count > 0;
            assert pre.pages[page_id].offset == Some(0nat);
            assert pre.pages[page_id].full.is_none();

            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages.dom().contains(pid)
                );
            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages[pid].is_used
                );
            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages[pid].offset.is_some()
                        && pre.pages[pid].offset.unwrap() == pid.idx - page_id.idx
                );

            let changed_pages = Map::new(
                page_id_range(page_id.segment_id, page_id.idx, page_id.idx + count),
                |pid: PageId| PageData {
                    is_used: false,
                    page_header_kind: None,
                    offset: None,
                    count: None,
                    .. pre.pages[pid]
                }
            );

            let new_pages = pre.pages.union_prefer_right(changed_pages);
            assert pre.pages.dom() =~= new_pages.dom();

            update pages = new_pages;
            update popped = Popped::VeryUnready(page_id.segment_id, page_id.idx as int, count as int, b);
        }
    }

    transition!{
        into_used_list(bin_idx: int) {
            require valid_bin_idx(bin_idx) || bin_idx == BIN_FULL;
            require let Popped::Used(page_id, tru) = pre.popped;
            require tru == true;

            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].page_header_kind.is_some();
            match pre.pages[page_id].page_header_kind.unwrap() {
                PageHeaderKind::Normal(i, bsize) => {
                    require((bin_idx != BIN_FULL ==> bin_idx == i)
                        && valid_bin_idx(i)
                        && bsize == crate::bin_sizes::size_of_bin(i)
                        && bsize <= MEDIUM_OBJ_SIZE_MAX);
                }
            }

            update used_dlist_headers[bin_idx] = DlistHeader {
                first: Some(page_id),
                last:
                    if pre.used_dlist_headers[bin_idx].first.is_some() {
                        pre.used_dlist_headers[bin_idx].last
                    } else {
                        Some(page_id)
                    },
            };
            if pre.used_dlist_headers[bin_idx].first.is_some() {
                let first_id = pre.used_dlist_headers[bin_idx].first.unwrap();
                assert pre.pages.dom().contains(first_id);
                assert pre.pages[first_id].is_used;
                assert pre.pages[first_id].dlist_entry.is_some()
                    by { pre.first_last_ll_stuff_used(bin_idx); };
                assert first_id != page_id;
                update pages[first_id] = PageData {
                    dlist_entry: Some(DlistEntry {
                        prev: Some(page_id),
                        .. pre.pages[first_id].dlist_entry.unwrap()
                    }),
                    .. pre.pages[first_id]
                };
            }

            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].is_used;
            assert pre.pages[page_id].offset == Some(0nat);
            assert pre.pages[page_id].dlist_entry.is_none();

            update pages[page_id] = PageData {
                dlist_entry: Some(DlistEntry {
                    prev: None,
                    next: pre.used_dlist_headers[bin_idx].first,
                }),
                full: Some(bin_idx == BIN_FULL),
                .. pre.pages[page_id]
            };

            update popped = Popped::No;
            update used_lists = Self::insert_front(pre.used_lists, bin_idx, page_id);
        }
    }

    transition!{
        into_used_list_back(bin_idx: int) {
            require valid_bin_idx(bin_idx) || bin_idx == BIN_FULL;
            require let Popped::Used(page_id, tru) = pre.popped;
            require tru == true;

            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].page_header_kind.is_some();
            match pre.pages[page_id].page_header_kind.unwrap() {
                PageHeaderKind::Normal(i, bsize) => {
                    require((bin_idx != BIN_FULL ==> bin_idx == i)
                        && valid_bin_idx(i)
                        && bsize == crate::bin_sizes::size_of_bin(i)
                        && bsize <= MEDIUM_OBJ_SIZE_MAX);
                }
            }

            assert pre.used_dlist_headers[bin_idx].last.is_some()
                <==> pre.used_dlist_headers[bin_idx].first.is_some()

                by { pre.first_last_ll_stuff_used(bin_idx); };

            update used_dlist_headers[bin_idx] = DlistHeader {
                first:
                    if pre.used_dlist_headers[bin_idx].last.is_some() {
                        pre.used_dlist_headers[bin_idx].first
                    } else {
                        Some(page_id)
                    },
                last: Some(page_id),
            };
            if pre.used_dlist_headers[bin_idx].last.is_some() {
                let last_id = pre.used_dlist_headers[bin_idx].last.unwrap();
                assert pre.pages.dom().contains(last_id)
                    && pre.pages[last_id].is_used
                    && pre.pages[last_id].dlist_entry.is_some()
                    && last_id != page_id

                    by { pre.first_last_ll_stuff_used(bin_idx); };

                update pages[last_id] = PageData {
                    dlist_entry: Some(DlistEntry {
                        next: Some(page_id),
                        .. pre.pages[last_id].dlist_entry.unwrap()
                    }),
                    .. pre.pages[last_id]
                };
            }

            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].is_used;
            assert pre.pages[page_id].offset == Some(0nat);
            assert pre.pages[page_id].dlist_entry.is_none();

            update pages[page_id] = PageData {
                dlist_entry: Some(DlistEntry {
                    prev: pre.used_dlist_headers[bin_idx].last,
                    next: None,
                }),
                full: Some(bin_idx == BIN_FULL),
                .. pre.pages[page_id]
            };

            update popped = Popped::No;
            update used_lists = Self::insert_back(pre.used_lists, bin_idx, page_id);
        }
    }

    transition!{
        out_of_used_list(page_id: PageId, bin_idx: int, list_idx: int) {
            require pre.popped == Popped::No;
            require pre.valid_used_page(page_id, bin_idx, list_idx);

            assert pre.pages[page_id].dlist_entry.is_some();
            let prev_page_id_opt = pre.pages[page_id].dlist_entry.unwrap().prev;
            let next_page_id_opt = pre.pages[page_id].dlist_entry.unwrap().next;

            assert prev_page_id_opt != Some(page_id)
                && next_page_id_opt != Some(page_id)
                && prev_page_id_opt.is_some() ==> prev_page_id_opt != next_page_id_opt

                by { pre.used_ll_stuff(bin_idx, list_idx); };

            match prev_page_id_opt {
                Option::Some(prev_page_id) => {
                    assert pre.pages.dom().contains(prev_page_id)
                        && pre.pages[prev_page_id].dlist_entry.is_some()
                        && pre.pages[prev_page_id].is_used

                      by { pre.used_ll_stuff(bin_idx, list_idx); };

                    update pages[prev_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            next: next_page_id_opt,
                            .. pre.pages[prev_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[prev_page_id]
                    };
                }
                Option::None => { }
            }

            match next_page_id_opt {
                Option::Some(next_page_id) => {
                    assert pre.pages.dom().contains(next_page_id)
                        && pre.pages[next_page_id].dlist_entry.is_some()
                        && pre.pages[next_page_id].is_used

                      by { pre.used_ll_stuff(bin_idx, list_idx); };

                    update pages[next_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            prev: prev_page_id_opt,
                            .. pre.pages[next_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[next_page_id]
                    };
                }
                Option::None => { }
            }

            update used_dlist_headers[bin_idx] = DlistHeader {
                first: if prev_page_id_opt.is_some() {
                    pre.used_dlist_headers[bin_idx].first
                } else {
                    next_page_id_opt
                },
                last: if next_page_id_opt.is_some() {
                    pre.used_dlist_headers[bin_idx].last
                } else {
                    prev_page_id_opt
                }
            };

            update pages[page_id] = PageData {
                full: None,
                dlist_entry: None,
                .. pre.pages[page_id]
            };

            update popped = Popped::Used(page_id, true);
            update used_lists[bin_idx] = pre.used_lists[bin_idx].remove(list_idx);
        }
    }

    transition!{
        segment_freeing_start(segment_id: SegmentId) {
            require let Popped::No = pre.popped;
            require pre.segments.dom().contains(segment_id);
            require pre.segments[segment_id].used == 0;

            let page_id = PageId { segment_id, idx: 0 };
            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].count.is_some();
            let count = pre.pages[page_id].count.unwrap();
            assert 1 <= count <= SLICES_PER_SEGMENT;

            let last_id = PageId { segment_id, idx: (count - 1) as nat };

            let new_page_map = Map::<PageId, PageData>::new(
                page_id_range(segment_id, 0, count),
                |page_id: PageId| PageData {
                    dlist_entry: None,
                    count: None,
                    offset: None,
                    is_used: false,
                    full: None,
                    page_header_kind: None,
                }
            );

            update pages = pre.pages.union_prefer_right(new_page_map);

            update popped = Popped::SegmentFreeing(segment_id, count as int);
        }
    }

    transition!{
        segment_freeing_finish() {
            require let Popped::SegmentFreeing(segment_id, idx) = pre.popped;
            require idx == SLICES_PER_SEGMENT;
            assert pre.segments.dom().contains(segment_id);
            update segments = pre.segments.remove(segment_id);
            update popped = Popped::No;

            let keys = page_id_range(segment_id, 0, SLICES_PER_SEGMENT as nat + 1);
            update pages = pre.pages.remove_keys(keys);
        }
    }


    transition!{
        merge_with_after() {
            require let Popped::VeryUnready(segment_id, cur_start, cur_count, b) = pre.popped;

            require cur_start + cur_count < SLICES_PER_SEGMENT;
            let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
            assert pre.pages.dom().contains(page_id);
            require !pre.pages[page_id].is_used;
            assert pre.pages[page_id].count.is_some()
                by { pre.get_stuff_after(); };
            let n_count = pre.pages[page_id].count.unwrap();
            assert cur_count + n_count <= SLICES_PER_SEGMENT
                by { pre.get_stuff_after(); };


            assert pre.pages[page_id].dlist_entry.is_some()
                by { pre.get_stuff_after(); };

            assert let Some(dlist_entry) = pre.pages[page_id].dlist_entry;

            update pages[page_id] = PageData {
              offset: None,
              count: None,
              dlist_entry: None,
              .. pre.pages[page_id]
            };
            let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };
            assert pre.pages.dom().contains(final_id)      by { pre.get_stuff_after(); };
            update pages[final_id] = PageData {
              offset: None,
              count: None,
              dlist_entry: None,
              .. pre.pages[final_id]
            };
            assert !pre.pages[final_id].is_used

                    by { pre.lemma_range_not_used(page_id);
                        assert(pre.pages.dom().contains(final_id)); };

            match dlist_entry.prev {
                Some(prev_page_id) => {
                    assert prev_page_id != page_id
                        && pre.pages.dom().contains(prev_page_id)
                        && pre.pages[prev_page_id].dlist_entry.is_some()
                        && pre.pages[prev_page_id].is_used == false

                    by { let (i, j) = pre.get_stuff_after(); pre.unused_ll_stuff(i, j); };

                    update pages[prev_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            next: dlist_entry.next,
                            .. pre.pages[prev_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[prev_page_id]
                    };
                }
                Option::None => { }
            }

            match dlist_entry.next {
                Some(next_page_id) => {
                    assert next_page_id != page_id
                        && pre.pages.dom().contains(next_page_id)
                        && pre.pages[next_page_id].dlist_entry.is_some()
                        && pre.pages[next_page_id].is_used == false

                    by { let (i, j) = pre.get_stuff_after(); pre.unused_ll_stuff(i, j); };

                    update pages[next_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            prev: dlist_entry.prev,
                            .. pre.pages[next_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[next_page_id]
                    };
                }
                Option::None => { }
            }

            let sbin_idx = smallest_sbin_fitting_size(n_count as int);
            assert 0 <= sbin_idx <= SEGMENT_BIN_MAX
                by { crate::bin_sizes::valid_sbin_idx_smallest_sbin_fitting_size(n_count as int); };

            update unused_dlist_headers[sbin_idx] = DlistHeader {
                first: if dlist_entry.prev.is_none() {
                    dlist_entry.next
                } else {
                    pre.unused_dlist_headers[sbin_idx].first
                },
                last: if dlist_entry.next.is_none() {
                    dlist_entry.prev
                } else {
                    pre.unused_dlist_headers[sbin_idx].last
                }
            };

            assert dlist_entry.prev.is_some() && dlist_entry.next.is_some() ==>
                dlist_entry.prev.unwrap() != dlist_entry.next.unwrap()

                by { let (i, j) = pre.get_stuff_after(); pre.unused_ll_stuff(i, j); };

            update popped = Popped::VeryUnready(segment_id, cur_start, (cur_count + n_count) as int, b);

            let list_idx = Self::get_list_idx(pre.unused_lists, page_id).1;
            update unused_lists[sbin_idx] = pre.unused_lists[sbin_idx].remove(list_idx);
        }
    }

    transition!{
        merge_with_before() {
            require let Popped::VeryUnready(segment_id, cur_start, cur_count, b) = pre.popped;

            require cur_start > 1;
            let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
            assert pre.pages[last_id].offset.is_some()    by { pre.get_stuff_before(); };
            let offset = pre.pages[last_id].offset.unwrap();
            require last_id.idx - offset > 0;
            let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
            require !pre.pages[page_id].is_used;
            assert !pre.pages[last_id].is_used            by { pre.get_stuff_before(); };

            assert pre.pages[page_id].count.is_some()     by { pre.get_stuff_before(); };
            let p_count = pre.pages[page_id].count.unwrap();
            assert cur_count + p_count <= SLICES_PER_SEGMENT
                by { pre.get_stuff_before(); };

            assert pre.pages.dom().contains(PageId { segment_id, idx: cur_start as nat });
            assert pre.pages[PageId { segment_id, idx: cur_start as nat }].offset.is_none();
            assert pre.pages[PageId { segment_id, idx: cur_start as nat }].is_used == false;

            assert pre.pages[page_id].dlist_entry.is_some()
                by { pre.get_stuff_before(); };

            assert let Some(dlist_entry) = pre.pages[page_id].dlist_entry;

            update pages[page_id] = PageData {
              offset: None,
              count: None,
              dlist_entry: None,
              .. pre.pages[page_id]
            };
            assert pre.pages.dom().contains(last_id)      by { pre.get_stuff_after(); };
            update pages[last_id] = PageData {
              offset: None,
              count: None,
              dlist_entry: None,
              .. pre.pages[last_id]
            };

            match dlist_entry.prev {
                Some(prev_page_id) => {
                    assert prev_page_id != page_id
                        && pre.pages.dom().contains(prev_page_id)
                        && pre.pages[prev_page_id].dlist_entry.is_some()
                        && pre.pages[prev_page_id].is_used == false
                        && prev_page_id != last_id
                        by { let (i, j) = pre.get_stuff_before(); pre.unused_ll_stuff(i, j); };

                    update pages[prev_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            next: dlist_entry.next,
                            .. pre.pages[prev_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[prev_page_id]
                    };
                }
                Option::None => { }
            }

            match dlist_entry.next {
                Some(next_page_id) => {
                    assert next_page_id != page_id
                        && pre.pages.dom().contains(next_page_id)
                        && pre.pages[next_page_id].dlist_entry.is_some()
                        && pre.pages[next_page_id].is_used == false
                        && next_page_id != last_id
                        by { let (i, j) = pre.get_stuff_before(); pre.unused_ll_stuff(i, j); };

                    update pages[next_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            prev: dlist_entry.prev,
                            .. pre.pages[next_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[next_page_id]
                    };
                }
                Option::None => { }
            }

            let sbin_idx = smallest_sbin_fitting_size(p_count as int);

            assert 0 <= sbin_idx <= SEGMENT_BIN_MAX
                by { crate::bin_sizes::valid_sbin_idx_smallest_sbin_fitting_size(p_count as int); };

            update unused_dlist_headers[sbin_idx] = DlistHeader {
                first: if dlist_entry.prev.is_none() {
                    dlist_entry.next
                } else {
                    pre.unused_dlist_headers[sbin_idx].first
                },
                last: if dlist_entry.next.is_none() {
                    dlist_entry.prev
                } else {
                    pre.unused_dlist_headers[sbin_idx].last
                }
            };

            assert dlist_entry.prev.is_some() && dlist_entry.next.is_some() ==>
                dlist_entry.prev.unwrap() != dlist_entry.next.unwrap()

                by { let (i, j) = pre.get_stuff_before(); pre.unused_ll_stuff(i, j); };

            update popped = Popped::VeryUnready(segment_id,
                  page_id.idx as int, (cur_count + p_count) as int, b);

            let list_idx = Self::get_list_idx(pre.unused_lists, page_id).1;
            update unused_lists[sbin_idx] = pre.unused_lists[sbin_idx].remove(list_idx);
        }
    }

    #[inductive(take_page_from_unused_queue)]
    #[verifier::spinoff_prover]
    fn take_page_from_unused_queue_inductive(pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int) {
        pre.unused_ll_stuff(sbin_idx, list_idx);
        pre.lemma_range_not_used(page_id);

        assert(post.popped_basics());

        Self::ucount_preserve_all(pre, post);
        assert(post.count_is_right());
        Self::unchanged_used_ll(pre, post);

        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();


        Self::take_page_from_unused_queue_ll_inv_valid_unused(pre, post, page_id, sbin_idx, list_idx);
        Self::take_page_from_unused_queue_inductive_attached_ranges(pre, post, page_id, sbin_idx, list_idx);
        Self::take_page_from_unused_queue_inductive_unusedinv2(pre, post, page_id, sbin_idx, list_idx);
        Self::ll_inv_exists_take_page_from_unused_queue(pre, post, page_id, sbin_idx, list_idx);
    }

    #[verifier::spinoff_prover]
    #[verifier::external_body]
    pub proof fn take_page_from_unused_queue_ll_inv_valid_unused(pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int)
        requires pre.invariant(),
            State::take_page_from_unused_queue_strong(pre, post, page_id, sbin_idx, list_idx),
        ensures
            post.ll_inv_valid_unused()
    {
        unimplemented!()
    }

    #[verifier::spinoff_prover]
    #[verifier::external_body]
    pub proof fn take_page_from_unused_queue_inductive_attached_ranges(
        pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int
    )
        requires pre.invariant(),
          State::take_page_from_unused_queue_strong(pre, post, page_id, sbin_idx, list_idx),
        ensures post.attached_ranges()
    {
        unimplemented!()
    }

    #[verifier::spinoff_prover]
    #[verifier::external_body]
    pub proof fn take_page_from_unused_queue_inductive_unusedinv2(
        pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int
    )
        requires pre.invariant(),
          State::take_page_from_unused_queue_strong(pre, post, page_id, sbin_idx, list_idx),
        ensures post.ll_inv_valid_unused2()
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ll_inv_exists_take_page_from_unused_queue(pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int)
      requires
          0 <= sbin_idx < pre.unused_lists.len(),
          0 <= list_idx < pre.unused_lists[sbin_idx].len(),
          pre.ll_inv_exists_in_some_list(),
          State::take_page_from_unused_queue_strong(pre, post, page_id, sbin_idx, list_idx),
      ensures
          post.ll_inv_exists_in_some_list(),
    {
        unimplemented!()
    }

    #[verifier::spinoff_prover]
    #[verifier::external_body]
    pub proof fn rec_take_page_from_unused_queue(pre: Self, post: Self, pid: PageId, sbin_idx: int, list_idx: int, idx: int)
      requires pre.invariant(),
          State::take_page_from_unused_queue_strong(pre, post, pid, sbin_idx, list_idx),
          pre.attached_rec(pid.segment_id, idx, false),
          pre.popped.is_No(),
          idx >= 0,
          pid.idx < SLICES_PER_SEGMENT,
      ensures
          post.attached_rec(pid.segment_id, idx, idx <= pid.idx)
      decreases SLICES_PER_SEGMENT - idx
    {
        unimplemented!()
    }

    #[inductive(split_page)]
    fn split_page_inductive(pre: Self, post: Self, page_id: PageId, current_count: int, target_count: int, sbin_idx: int) {
       admit()
    }

    #[verifier::external_body]
    pub proof fn rec_split_page(pre: Self, post: Self, pid: PageId, current_count: int, target_count: int, sbin_idx: int, idx: int, sp: bool)
      requires pre.invariant(),
          State::split_page_strong(pre, post, pid, current_count, target_count, sbin_idx),
          pre.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp)
      ensures
          post.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp)
      decreases SLICES_PER_SEGMENT - idx
    {
        unimplemented!()
    }


    #[inductive(allocate_popped)]
    fn allocate_popped_inductive(pre: Self, post: Self) {
        Self::ucount_preserve_all(pre, post);
        Self::unchanged_used_ll(pre, post);
        Self::unchanged_unused_ll(pre, post);
        assert(post.inv_ready());

        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
        }

        Self::attached_ranges_all(pre, post);
    }

    #[inductive(set_range_to_used)]
    fn set_range_to_used_inductive(pre: Self, post: Self, page_header_kind: PageHeaderKind) {
        let page_id = post.popped.get_Used_0();
        let segment_id = page_id.segment_id;
        Self::unchanged_used_ll(pre, post);
        Self::unchanged_unused_ll(pre, post);
        Self::ucount_inc1(pre, post, page_id);
        Self::ucount_preserve_except(pre, post, segment_id);

        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
        }
        Self::attached_ranges_all(pre, post);

        assert forall |i: int, j: int| 0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len() implies post.unused_lists[i][j] != page_id
        by {
            assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
            assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
        }
    }

    #[inductive(set_range_to_not_used)]
    fn set_range_to_not_used_inductive(pre: Self, post: Self) {
        let page_id = pre.popped.get_Used_0();
        let segment_id = page_id.segment_id;

        Self::unchanged_used_ll(pre, post);
        Self::unchanged_unused_ll(pre, post);
        Self::ucount_dec1(pre, post, page_id);
        Self::ucount_preserve_except(pre, post, segment_id);

        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
        }
        Self::attached_ranges_all(pre, post);

        assert forall |i: int, j: int| 0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len() implies post.unused_lists[i][j] != page_id
        by {
            assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
            assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
        }
    }

    #[inductive(into_used_list)]
    fn into_used_list_inductive(pre: Self, post: Self, bin_idx: int) {
        admit()
    }

    #[verifier::external_body]
    pub proof fn rec_into_used_list(pre: Self, post: Self, bin_idx: int, idx: int, sp: bool)
      requires pre.invariant(),
          State::into_used_list_strong(pre, post, bin_idx)
            || State::into_used_list_back_strong(pre, post, bin_idx),
          pre.attached_rec(pre.popped.get_Used_0().segment_id, idx, sp)
      ensures
          post.attached_rec(pre.popped.get_Used_0().segment_id, idx, false)
      decreases SLICES_PER_SEGMENT - idx
    {
        unimplemented!()
    }


    #[inductive(create_segment)]
    fn create_segment_inductive(pre: Self, post: Self, segment_id: SegmentId) {
        Self::ucount_preserve_all(pre, post);
        post.ucount_eq0(segment_id);

        Self::unchanged_used_ll(pre, post);
        Self::unchanged_unused_ll(pre, post);

        assert(post.attached_ranges()) by {
            reveal_with_fuel(State::attached_rec);
            assert(post.attached_ranges_segment(segment_id));
            Self::attached_ranges_except(pre, post, segment_id);
        }

        reveal(State::ll_inv_exists_in_some_list);
    }

    #[inductive(forget_about_first_page)]
    fn forget_about_first_page_inductive(pre: Self, post: Self, count: int) {
        let segment_id = pre.popped.get_SegmentCreating_0();
        let page_id = PageId { segment_id, idx: count as nat };
        assert(post.good_range_very_unready(page_id));
        assert(post.popped_basics());
        Self::ucount_preserve_all(pre, post);
        assert(post.count_is_right());
        Self::unchanged_used_ll(pre, post);
        Self::unchanged_unused_ll(pre, post);
        assert(post.attached_ranges()) by {
            reveal_with_fuel(State::attached_rec);
            let page_id = PageId { segment_id, idx: 0 };
            assert(post.good_range0(segment_id));
            assert(post.popped_for_seg(segment_id));

            assert(count + post.popped_len() == SLICES_PER_SEGMENT);

            assert(post.attached_rec(segment_id, SLICES_PER_SEGMENT as int, false));
            assert(post.attached_rec(segment_id, count, true));
            assert(post.attached_rec0(segment_id, true));
            assert(post.attached_ranges_segment(segment_id));

            Self::attached_ranges_except(pre, post, segment_id);
        }

        reveal(State::ll_inv_exists_in_some_list);
    }

    #[inductive(free_to_unused_queue)]
    fn free_to_unused_queue_inductive(pre: Self, post: Self, sbin_idx: int) {
       admit()
    }

    #[verifier::spinoff_prover]
    #[verifier::external_body]
    pub proof fn rec_free_to_unused_queue(pre: Self, post: Self, sbin_idx: int, idx: int, sp: bool)
      requires pre.invariant(),
          State::free_to_unused_queue_strong(pre, post, sbin_idx),
          pre.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp)
      ensures
          post.attached_rec(pre.popped.get_VeryUnready_0(), idx, false)
      decreases SLICES_PER_SEGMENT - idx
    {
        unimplemented!()
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
        reveal(State::ll_inv_exists_in_some_list);
    }

    #[inductive(out_of_used_list)]
    fn out_of_used_list_inductive(pre: Self, post: Self, page_id: PageId, bin_idx: int, list_idx: int) {
       admit()
    }

    #[verifier::external_body]
    proof fn out_of_used_list_inductive_ll_inv_valid_used2(pre: Self, post: Self, page_id: PageId, bin_idx: int, list_idx: int)
        requires pre.invariant(),
          State::out_of_used_list_strong(pre, post, page_id, bin_idx, list_idx)
        ensures
          post.ll_inv_valid_used2(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn out_of_used_list_inductive_ll_inv_exists_in_some_list(pre: Self, post: Self, page_id: PageId, bin_idx: int, list_idx: int)
        requires pre.invariant(),
          State::out_of_used_list_strong(pre, post, page_id, bin_idx, list_idx)
        ensures
          post.ll_inv_exists_in_some_list(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn out_of_used_list_inductive_attached_ranges(pre: Self, post: Self, page_id: PageId, bin_idx: int, list_idx: int)
        requires pre.invariant(),
          State::out_of_used_list_strong(pre, post, page_id, bin_idx, list_idx)
        ensures
          post.attached_ranges(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn rec_out_of_used_list(pre: Self, post: Self, pid: PageId, bin_idx: int, list_idx: int, idx: int)
      requires pre.invariant(),
          State::out_of_used_list_strong(pre, post, pid, bin_idx, list_idx),
          pre.attached_rec(pid.segment_id, idx, false),
          idx >= 0,
          pid.idx < SLICES_PER_SEGMENT,
      ensures
          post.attached_rec(pid.segment_id, idx, idx <= pid.idx)
      decreases SLICES_PER_SEGMENT - idx
    {
        unimplemented!()
    }

    #[inductive(merge_with_after)]
    fn merge_with_after_inductive(pre: Self, post: Self) {
       admit()
    }

    #[verifier::external_body]
    pub proof fn merge_with_after_ll_inv_valid_unused(pre: Self, post: Self)
        requires pre.invariant(),
            State::merge_with_after_strong(pre, post),
        ensures
            post.ll_inv_valid_unused()
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn sp_true_implies_le(&self, idx: int)
      requires self.invariant(),
          self.popped.is_VeryUnready(),
          self.attached_rec(self.popped.get_VeryUnready_0(), idx, true),
          idx >= 0,
      ensures
          idx <= self.popped.get_VeryUnready_1()
      decreases SLICES_PER_SEGMENT - idx
    {
        unimplemented!()
    }

    #[verifier::spinoff_prover]
    #[verifier::external_body]
    pub proof fn rec_merge_with_after(pre: Self, post: Self, idx: int, sp: bool)
      requires pre.invariant(),
          State::merge_with_after_strong(pre, post),
          pre.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp),
          idx >= 0,
          !sp ==> idx >= pre.popped.get_VeryUnready_1() + post.popped_len(),
      ensures
          post.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp)
      decreases SLICES_PER_SEGMENT - idx
    {
        unimplemented!()
    }

    #[verifier::spinoff_prover]
    #[verifier::external_body]
    pub proof fn rec_merge_with_before(pre: Self, post: Self, idx: int, sp: bool)
      requires pre.invariant(),
          State::merge_with_before_strong(pre, post),
          pre.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp),
          idx >= 0,
          idx != pre.popped.get_VeryUnready_1(),
          !sp ==> idx >= pre.popped.get_VeryUnready_1() + pre.popped_len(),
      ensures
          post.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp)
      decreases SLICES_PER_SEGMENT - idx
    {
        unimplemented!()
    }


    #[verifier::external_body]
    pub proof fn ll_inv_exists_merge_with_after(pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int)
      requires
          0 <= sbin_idx < pre.unused_lists.len(),
          0 <= list_idx < pre.unused_lists[sbin_idx].len(),
          pre.ll_inv_exists_in_some_list(),
          post.pages[page_id].offset.is_none(),
          State::merge_with_after_strong(pre, post),
          ({
              let segment_id = pre.popped.get_VeryUnready_0();
              let cur_start = pre.popped.get_VeryUnready_1();
              let cur_count = pre.popped.get_VeryUnready_2();
              let cur_id = PageId { segment_id, idx: cur_start as nat };
              let n_count = pre.pages[page_id].count.unwrap();
              page_id == PageId { segment_id, idx: (cur_start + cur_count) as nat }
               && sbin_idx == smallest_sbin_fitting_size(n_count as int)
               && list_idx == Self::get_list_idx(pre.unused_lists, page_id).1
          }),
          page_id == pre.unused_lists[sbin_idx][list_idx],
      ensures
          post.ll_inv_exists_in_some_list(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ll_inv_exists_merge_with_before(pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int)
      requires
          0 <= sbin_idx < pre.unused_lists.len(),
          0 <= list_idx < pre.unused_lists[sbin_idx].len(),
          pre.ll_inv_exists_in_some_list(),
          post.pages[page_id].offset.is_none(),
          State::merge_with_before_strong(pre, post),
          ({
              let segment_id = pre.popped.get_VeryUnready_0();
              let cur_start = pre.popped.get_VeryUnready_1();
              let cur_count = pre.popped.get_VeryUnready_2();
              let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
              let offset = pre.pages[last_id].offset.unwrap();
              let p_count = pre.pages[page_id].count.unwrap();
              page_id == PageId { segment_id, idx: (last_id.idx - offset) as nat }
               && sbin_idx == smallest_sbin_fitting_size(p_count as int)
               && list_idx == Self::get_list_idx(pre.unused_lists, page_id).1
          }),
          page_id == pre.unused_lists[sbin_idx][list_idx],
      ensures
          post.ll_inv_exists_in_some_list(),
    {
        unimplemented!()
    }



    #[inductive(merge_with_before)]
    fn merge_with_before_inductive(pre: Self, post: Self) {
       admit()
    }

    #[verifier::spinoff_prover]
    #[verifier::external_body]
    pub proof fn merge_with_before_ll_inv_valid_unused(pre: Self, post: Self)
        requires pre.invariant(),
            State::merge_with_before_strong(pre, post),
        ensures
            post.ll_inv_valid_unused()
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn merge_with_before_inductive_attached_ranges(
        pre: Self, post: Self,
    )
        requires pre.invariant(),
          State::merge_with_before_strong(pre, post),
        ensures post.attached_ranges()
    {
        unimplemented!()
    }

    #[inductive(segment_freeing_start)]
    fn segment_freeing_start_inductive(pre: Self, post: Self, segment_id: SegmentId) {
        Self::ucount_preserve_all(pre, post);
        assert(post.popped_basics());
        Self::unchanged_unused_ll(pre, post);
        Self::unchanged_used_ll(pre, post);

        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
        }

        assert(post.attached_ranges()) by {
            Self::attached_ranges_except(pre, post, segment_id);
            reveal(State::attached_rec);
            let page_id = PageId { segment_id, idx: 0 };
            Self::attached_rec_same(pre, post, segment_id,
                pre.pages[page_id].count.unwrap() as int,
                false);
        }
    }

    #[inductive(segment_freeing_finish)]
    fn segment_freeing_finish_inductive(pre: Self, post: Self) {
        Self::ucount_preserve_all(pre, post);
        Self::unchanged_used_ll(pre, post);
        let segment_id = pre.popped.get_SegmentFreeing_0();
        Self::attached_ranges_except(pre, post, segment_id);
        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
        }

        assert forall |i| 0 <= i < post.unused_lists.len()
            implies valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            let ll = post.unused_lists[i];
            assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
            by {
                assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
            }
        }
    }

    #[inductive(into_used_list_back)]
    fn into_used_list_back_inductive(pre: Self, post: Self, bin_idx: int) {
       admit()
    }

    #[verifier::external_body]
    pub proof fn preserved_by_into_used_list_back(pre: Self, post: Self,
        bin_idx: int, other_page_id: PageId, other_bin_idx: int, other_list_idx: int)
        requires Self::into_used_list_back(pre, post, bin_idx),
            pre.invariant(),
            pre.valid_used_page(other_page_id, other_bin_idx, other_list_idx)
        ensures
            post.valid_used_page(other_page_id, other_bin_idx, other_list_idx)
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn preserved_by_out_of_used_list(pre: Self, post: Self,
        page_id: PageId, bin_idx: int, list_idx: int,
        next_page_id: PageId)
        requires Self::out_of_used_list(pre, post, page_id, bin_idx, list_idx),
            pre.invariant(),
            pre.valid_used_page(next_page_id, bin_idx, list_idx + 1)
        ensures
            post.valid_used_page(next_page_id, bin_idx, list_idx)
    {
        unimplemented!()
    }

    #[inductive(forget_about_first_page2)]
    fn forget_about_first_page2_inductive(pre: Self, post: Self) {
        Self::ucount_preserve_all(pre, post);
        Self::attached_ranges_all(pre, post);
        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
        }
    }

    #[inductive(clear_ec)]
    fn clear_ec_inductive(pre: Self, post: Self) {
        Self::ucount_preserve_all(pre, post);
        Self::attached_ranges_all(pre, post);
        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
        }
    }

    #[verifier::external_body]
    pub proof fn used_ll_stuff(&self, i: int, j: int)
        requires self.invariant(),
            0 <= i < self.used_lists.len(),
            0 <= j < self.used_lists[i].len(),
        ensures
            self.pages.dom().contains(self.used_lists[i][j]),
            self.pages[self.used_lists[i][j]].is_used == true,
            self.pages[self.used_lists[i][j]].count.is_some(),
            self.pages[self.used_lists[i][j]].dlist_entry.is_some(),
            self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev != Some(self.used_lists[i][j]),
            self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next != Some(self.used_lists[i][j]),
            self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.is_some() ==>
                self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev != self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next,

            self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.is_some() ==>
                self.pages.dom().contains(self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.unwrap())
                && self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.unwrap()].dlist_entry.is_some()
                && self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.unwrap()].is_used == true,
            self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.is_some() ==>
                self.pages.dom().contains(self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.unwrap())
                && self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.unwrap()].dlist_entry.is_some()
                && self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.unwrap()].is_used == true,

    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn unused_ll_stuff(&self, i: int, j: int)
        requires self.invariant(),
            0 <= i < self.unused_lists.len(),
            0 <= j < self.unused_lists[i].len(),
        ensures
            self.pages.dom().contains(self.unused_lists[i][j]),
            self.pages[self.unused_lists[i][j]].is_used == false,
            self.pages[self.unused_lists[i][j]].count.is_some(),
            self.pages[self.unused_lists[i][j]].dlist_entry.is_some(),
            self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev != Some(self.unused_lists[i][j]),
            self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next != Some(self.unused_lists[i][j]),
            self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.is_some() ==>
                self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev != self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next,

            self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.is_some() ==>
                self.pages.dom().contains(self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.unwrap())
                && self.pages[self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.unwrap()].dlist_entry.is_some()
                && self.pages[self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.unwrap()].is_used == false,
            self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next.is_some() ==>
                self.pages.dom().contains(self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next.unwrap())
                && self.pages[self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next.unwrap()].dlist_entry.is_some()
                && self.pages[self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next.unwrap()].is_used == false,
    {
        unimplemented!()
    }

    pub closed spec fn page_id_of_popped(p: Popped) -> PageId {
        match p {
            Popped::Ready(page_id, _) => page_id,
            Popped::Used(page_id, _) => page_id,
            Popped::VeryUnready(segment_id, idx, _, _) => PageId { segment_id, idx: idx as nat },
            _ => arbitrary(),
        }
    }

    pub closed spec fn popped_page_id(&self) -> PageId {
        Self::page_id_of_popped(self.popped)
    }

    pub closed spec fn expect_out_of_lists(&self, pid: PageId) -> bool {
        match self.popped {
            Popped::No => false,
            Popped::ExtraCount(_) => false,
            Popped::Ready(page_id, _) => pid == page_id,
            Popped::Used(page_id, _) => pid == page_id,
            Popped::SegmentCreating(segment_id) => false,
            Popped::SegmentFreeing(segment_id, idx) => pid.segment_id == segment_id && pid.idx < idx,
            Popped::VeryUnready(segment_id, start, _, _) => false,
        }
    }

    pub closed spec fn ec_of_popped(p: Popped, segment_id: SegmentId) -> int {
        match p {
            Popped::No => 0,
            Popped::Ready(p, b) => if p.segment_id == segment_id && b { 1 } else { 0 },
            Popped::Used(p, b) => if p.segment_id == segment_id {
                if b { 0 } else { -1 }
              } else { 0 }
            Popped::SegmentCreating(_) => 0,
            Popped::VeryUnready(sid, _, _, b) => if segment_id == sid && b { 1 } else { 0 },
            Popped::SegmentFreeing(_, _) => 0,
            Popped::ExtraCount(sid) => if segment_id == sid { 1 } else { 0 },
        }
    }

    pub closed spec fn popped_ec(&self, segment_id: SegmentId) -> int {
        Self::ec_of_popped(self.popped, segment_id)
    }

    #[verifier::opaque]
    pub closed spec fn ucount(&self, segment_id: SegmentId) -> nat {
        self.ucount_sum(segment_id, SLICES_PER_SEGMENT as int)
    }

    pub closed spec fn ucount_sum(&self, segment_id: SegmentId, idx: int) -> nat
        decreases idx
    {
        if idx <= 0 {
            0
        } else {
            self.ucount_sum(segment_id, idx - 1)
              + self.one_count(PageId { segment_id, idx: (idx - 1) as nat })
        }
    }

    #[verifier::external_body]
    pub proof fn first_last_ll_stuff_unused(&self, i: int)
        requires self.invariant(),
            0 <= i < self.unused_lists.len(),
        ensures
            (self.popped.is_Ready())
              ==>
                self.unused_dlist_headers[i].first != Some(self.popped_page_id())
                && self.unused_dlist_headers[i].last != Some(self.popped_page_id()),
            (match self.unused_dlist_headers[i].first {
                Some(first_id) => self.pages.dom().contains(first_id)
                  && is_unused_header(self.pages[first_id])
                  && self.pages[first_id].dlist_entry.is_some(),
                None => true,
            }),
            (match self.unused_dlist_headers[i].last {
                Some(last_id) => self.pages.dom().contains(last_id)
                  && is_unused_header(self.pages[last_id])
                  && self.pages[last_id].dlist_entry.is_some(),
                None => true,
            }),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn first_last_ll_stuff_used(&self, i: int)
        requires self.invariant(),
            0 <= i < self.used_lists.len(),
        ensures
            (self.popped.is_Ready())
              ==>
                self.used_dlist_headers[i].first != Some(self.popped_page_id())
                && self.used_dlist_headers[i].last != Some(self.popped_page_id()),
            self.used_dlist_headers[i].first.is_some() <==>
                self.used_dlist_headers[i].last.is_some(),
            (match self.used_dlist_headers[i].first {
                Some(first_id) => self.pages.dom().contains(first_id)
                  && is_used_header(self.pages[first_id])
                  && self.pages[first_id].dlist_entry.is_some(),
                None => true,
            }),
            (match self.used_dlist_headers[i].last {
                Some(last_id) => self.pages.dom().contains(last_id)
                  && is_used_header(self.pages[last_id])
                  && self.pages[last_id].dlist_entry.is_some(),
                None => true,
            }),
    {
        unimplemented!()
    }


    #[verifier::external_body]
    pub proof fn lemma_range_not_used(&self, page_id: PageId)
        requires self.invariant(), self.pages.dom().contains(page_id),
            is_unused_header(self.pages[page_id]),
            page_id.idx != 0,
            match self.popped {
                Popped::Ready(pid, _) => pid != page_id,
                _ => true,
            }
        ensures
            self.pages[page_id].count.is_some(),
            self.good_range_unused(page_id),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn lemma_range_used(&self, page_id: PageId)
        requires self.invariant(), self.pages.dom().contains(page_id),
            is_used_header(self.pages[page_id]),
            match self.popped {
                Popped::Used(pid, _) => pid != page_id,
                _ => true,
            },
        ensures
            self.pages[page_id].count.is_some(),
            self.good_range_used(page_id),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn rec_lemma_range_used(&self, page_id: PageId, idx: int, sp: bool)
        requires self.invariant(), self.pages.dom().contains(page_id),
            is_used_header(self.pages[page_id]),
            page_id.idx != SLICES_PER_SEGMENT,
            0 <= idx <= page_id.idx,
            match self.popped {
                Popped::Used(pid, _) => pid != page_id,
                _ => true,
            },
            self.attached_rec(page_id.segment_id, idx, sp),
        ensures
            self.pages[page_id].count.is_some(),
            self.good_range_used(page_id),
        decreases SLICES_PER_SEGMENT - idx
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn rec_lemma_range_not_used(&self, page_id: PageId, idx: int, sp: bool)
        requires self.invariant(), self.pages.dom().contains(page_id),
            is_unused_header(self.pages[page_id]),
            0 <= idx <= page_id.idx,
            page_id.idx != SLICES_PER_SEGMENT,
            match self.popped {
                Popped::Ready(pid, _) => pid != page_id,
                _ => true,
            },
            self.attached_rec(page_id.segment_id, idx, sp)
        ensures
            self.pages[page_id].count.is_some(),
            self.good_range_unused(page_id),
        decreases SLICES_PER_SEGMENT - idx
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn get_stuff_after(&self) -> (r: (int, int))
        requires self.invariant(),
        ensures
          match self.popped {
              Popped::VeryUnready(segment_id, cur_start, cur_count, _) => {
                  let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
                  page_id.idx < SLICES_PER_SEGMENT ==> (
                      self.pages.dom().contains(page_id)
                      && (!self.pages[page_id].is_used ==> self.good_range_unused(page_id)
                          && self.pages[page_id].dlist_entry.is_some()
                          && 0 <= r.0 < self.unused_lists.len()
                          && 0 <= r.1 < self.unused_lists[r.0].len()
                          && self.unused_lists[r.0][r.1] == page_id
                      )
                  )
              }
              _ => true,
          },
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn get_stuff_before(&self) -> (r: (int, int))
        requires self.invariant(),
        ensures
          match self.popped {
              Popped::VeryUnready(segment_id, cur_start, cur_count, _) => {
                  cur_start >= 1 && ({
                    let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
                      self.pages.dom().contains(last_id)
                      && self.pages[last_id].offset.is_some()
                      && cur_start - 1 - self.pages[last_id].offset.unwrap() >= 0
                      && ({
                        let page_id = PageId { segment_id, idx: (cur_start - 1 - self.pages[last_id].offset.unwrap()) as nat };
                        self.pages.dom().contains(page_id)
                          && (!self.pages[page_id].is_used && page_id.idx != 0 ==> self.good_range_unused(page_id)
                              && self.pages[page_id].dlist_entry.is_some()
                              && 0 <= r.0 < self.unused_lists.len()
                              && 0 <= r.1 < self.unused_lists[r.0].len()
                              && self.unused_lists[r.0][r.1] == page_id
                              && self.pages[page_id].count.unwrap()
                                  == self.pages[last_id].offset.unwrap() + 1
                          )
                      })
                  })
              }
              _ => true,
          },
    {
        unimplemented!()
    }


    pub closed spec fn good_range_very_unready(&self, page_id: PageId) -> bool
    {
        &&& self.pages.dom().contains(page_id)
        &&& self.pages[page_id].offset.is_none()
        &&& self.pages[page_id].count.is_none()
        &&& ({ let count = self.popped.get_VeryUnready_2();
            page_id.idx + count <= SLICES_PER_SEGMENT
            && (forall |pid| #![trigger self.pages.dom().contains(pid)]
                #![trigger self.pages.index(pid)]
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count ==>
                self.pages.dom().contains(pid)
                && self.pages[pid].is_used == false
                && self.pages[pid].full.is_none()
                && self.pages[pid].page_header_kind.is_none()
                && self.pages[pid].count.is_none()
                && self.pages[pid].dlist_entry.is_none()
                && self.pages[pid].offset.is_none()
           )
        })
    }

    pub closed spec fn good_range0(&self, segment_id: SegmentId) -> bool
    {
        let page_id = PageId { segment_id, idx: 0 }; {
        &&& self.pages.dom().contains(page_id)
        &&& self.pages[page_id].offset == Some(0nat)
        &&& self.pages[page_id].count.is_some()
        &&& ({ let count = self.pages[page_id].count.unwrap();
            page_id.idx + count <= SLICES_PER_SEGMENT
            && (forall |pid| #![trigger self.pages.dom().contains(pid)]
                #![trigger self.pages.index(pid)]
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count ==>
                self.pages.dom().contains(pid)
                && self.pages[pid].is_used == false
                && self.pages[pid].full.is_none()
                && self.pages[pid].page_header_kind.is_none()
                && (self.pages[pid].count.is_some() <==> pid == page_id)
                && self.pages[pid].dlist_entry.is_none()
                && self.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
            )
        })
        }
    }

    pub closed spec fn good_range_unused(&self, page_id: PageId) -> bool
    {
        &&& self.pages.dom().contains(page_id)
        &&& self.pages[page_id].offset == Some(0nat)
        &&& self.pages[page_id].count.is_some()
        &&& ({ let count = self.pages[page_id].count.unwrap();
            page_id.idx + count <= SLICES_PER_SEGMENT
            && (forall |pid| #![trigger self.pages.dom().contains(pid)]
                #![trigger self.pages.index(pid)]
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count ==>
                self.pages.dom().contains(pid)
                && self.pages[pid].is_used == false
                && self.pages[pid].full.is_none()
                && self.pages[pid].page_header_kind.is_none()
                && (self.pages[pid].count.is_some() <==> pid == page_id)
                && (self.pages[pid].dlist_entry.is_some() <==> pid == page_id)
                && self.pages[pid].offset == (if pid == page_id || pid == (PageId { segment_id: page_id.segment_id, idx: (page_id.idx + self.pages[page_id].count.unwrap() - 1) as nat }) {
                            Some((pid.idx - page_id.idx) as nat)
                        } else {
                            None
                        })
            )
        })
    }

    pub closed spec fn good_range_used(&self, page_id: PageId) -> bool
    {
        &&& self.pages.dom().contains(page_id)
        &&& self.pages[page_id].offset == Some(0nat)
        &&& self.pages[page_id].count.is_some()
        &&& ({ let count = self.pages[page_id].count.unwrap();
            page_id.idx + count <= SLICES_PER_SEGMENT
            && (forall |pid| #![trigger self.pages.dom().contains(pid)]
                #![trigger self.pages.index(pid)]
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count ==>
                self.pages.dom().contains(pid)
                && self.pages[pid].is_used == true
                && self.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
                && (self.pages[pid].page_header_kind.is_some() <==> pid == page_id)
                && (self.pages[pid].dlist_entry.is_some() <==> pid == page_id)
                && (self.pages[pid].full.is_some() <==> pid == page_id)
            )
        })
    }

    #[verifier::external_body]
    pub proof fn lemma_used_bound(&self, segment_id: SegmentId)
        requires self.segments.dom().contains(segment_id),
            self.invariant(),
        ensures self.segments[segment_id].used <= SLICES_PER_SEGMENT + 1,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ucount_sum_le(&self, segment_id: SegmentId, idx: int)
        requires idx >= 0,
        ensures self.ucount_sum(segment_id, idx) <= idx
        decreases idx,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ucount_preserve_except(pre: Self, post: Self, esid: SegmentId)
        requires
          forall |pid: PageId| #![all_triggers] pid.segment_id != esid ==>
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> pre.pages[pid] == post.pages[pid]),
        ensures
          forall |sid: SegmentId| sid != esid ==> pre.ucount(sid) == post.ucount(sid)
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ucount_preserve_all(pre: Self, post: Self)
        requires
          forall |pid: PageId|
            pre.does_count(pid) <==> post.does_count(pid),
        ensures
          forall |sid: SegmentId| pre.ucount(sid) == post.ucount(sid)
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ucount_sum_preserve(pre: Self, post: Self, segment_id: SegmentId, idx: int)
        requires
            idx >= 0,
            (forall |pid: PageId| #![all_triggers] pid.segment_id == segment_id ==>
              (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
              && (pre.pages.dom().contains(pid) ==> pre.pages[pid] == post.pages[pid])
            ) || (
              forall |pid: PageId|
                pre.does_count(pid) <==> post.does_count(pid)
            ),
        ensures
            pre.ucount_sum(segment_id, idx) == post.ucount_sum(segment_id, idx)
        decreases idx,
    {
        unimplemented!()
    }

    pub closed spec fn one_count(&self, page_id: PageId) -> nat {
        if self.does_count(page_id) { 1 } else { 0 }
    }

    pub closed spec fn does_count(&self, page_id: PageId) -> bool {
        self.pages.dom().contains(page_id)
          && page_id.idx != 0
          && self.pages[page_id].is_used
          && self.pages[page_id].offset == Some(0nat)
    }

    #[verifier::external_body]
    pub proof fn ucount_inc1(pre: Self, post: Self, page_id: PageId)
        requires
            0 <= page_id.idx < SLICES_PER_SEGMENT,
            forall |pid: PageId| pid != page_id ==>
              (pre.does_count(pid) <==> post.does_count(pid)),
            !pre.does_count(page_id),
            post.does_count(page_id),
        ensures
            post.ucount(page_id.segment_id) == pre.ucount(page_id.segment_id) + 1
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ucount_sum_inc1(pre: Self, post: Self, page_id: PageId, idx: int)
        requires
            idx >= 0,
            forall |pid: PageId| pid != page_id ==>
                (pre.does_count(pid) <==> post.does_count(pid)),
            !pre.does_count(page_id),
            post.does_count(page_id),
        ensures
            pre.ucount_sum(page_id.segment_id, idx) + (if page_id.idx < idx { 1int } else { 0 }) == post.ucount_sum(page_id.segment_id, idx)
        decreases idx,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ucount_dec1(pre: Self, post: Self, page_id: PageId)
        requires
            0 <= page_id.idx < SLICES_PER_SEGMENT,
            forall |pid: PageId| pid != page_id ==>
              (pre.does_count(pid) <==> post.does_count(pid)),
            pre.does_count(page_id),
            !post.does_count(page_id),
        ensures
            post.ucount(page_id.segment_id) == pre.ucount(page_id.segment_id) - 1
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ucount_sum_dec1(pre: Self, post: Self, page_id: PageId, idx: int)
        requires
            idx >= 0,
            forall |pid: PageId| pid != page_id ==>
                (pre.does_count(pid) <==> post.does_count(pid)),
            pre.does_count(page_id),
            !post.does_count(page_id),
        ensures
            pre.ucount_sum(page_id.segment_id, idx) - (if page_id.idx < idx { 1int } else { 0 }) == post.ucount_sum(page_id.segment_id, idx)
        decreases idx,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ucount_eq0(&self, sid: SegmentId)
        requires
          forall |pid: PageId| pid.segment_id == sid ==>
              !self.does_count(pid)
        ensures
            self.ucount(sid) == 0
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ucount_sum_eq0(&self, sid: SegmentId, idx: int)
        requires
            idx >= 0,
            forall |pid: PageId| pid.segment_id == sid ==> !self.does_count(pid)
        ensures
            self.ucount_sum(sid, idx) == 0
        decreases idx,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ucount_eq0_inverse(&self, page_id: PageId)
        requires self.ucount(page_id.segment_id) == 0,
            0 <= page_id.idx < SLICES_PER_SEGMENT,
        ensures
            !self.does_count(page_id)
    {
        unimplemented!()
    }

    #[verifier::spinoff_prover]
    #[verifier::external_body]
    pub proof fn ucount_sum_eq0_inverse(&self, page_id: PageId, idx: int)
        requires self.ucount_sum(page_id.segment_id, idx) == 0,
            0 <= page_id.idx < idx,
        ensures
            !self.does_count(page_id)
        decreases idx,
    {
        unimplemented!()
    }


    #[verifier::external_body]
    pub proof fn attached_ranges_except(pre: Self, post: Self, esid: SegmentId)
        requires
          pre.invariant(),
          forall |sid: SegmentId| sid != esid && post.segments.dom().contains(sid) ==> pre.segments.dom().contains(sid),
          forall |pid: PageId| pid.segment_id != esid ==>
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> {
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& (pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some())
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              }),
          pre.if_popped_or_other_then_for(esid),
          post.if_popped_or_other_then_for(esid),
          match post.popped {
              Popped::VeryUnready(_, i, _, _) => i >= 0,
              _ => true,
          },
        ensures
          forall |sid: SegmentId| sid != esid && #[trigger] post.segments.dom().contains(sid) ==> post.attached_ranges_segment(sid)
    {
        unimplemented!()
    }

    pub open spec fn in_popped_range(&self, pid: PageId) -> bool {
        match self.popped {
            Popped::No | Popped::ExtraCount(_)
              | Popped::SegmentFreeing(..)
              | Popped::SegmentCreating(..) => false,
            Popped::VeryUnready(segment_id, idx, count, _) =>
                pid.segment_id == segment_id && idx <= pid.idx < idx + count,
            Popped::Ready(page_id, _)
              | Popped::Used(page_id, _) => {
                  pid.segment_id == page_id.segment_id
                    && page_id.idx <= pid.idx < page_id.idx + self.pages[page_id].count.unwrap()
            }
        }
    }

    #[verifier::external_body]
    pub proof fn attached_ranges_all(pre: Self, post: Self)
        requires
          pre.invariant(),
          Self::popped_ranges_match(pre, post),
          !pre.popped.is_SegmentFreeing(),
          !pre.popped.is_SegmentCreating(),
          !post.popped.is_SegmentFreeing(),
          pre.segments.dom() =~= post.segments.dom(),
          match post.popped {
              Popped::VeryUnready(_, i, _, _) => i >= 0,
              _ => true,
          },
          forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid)
                && !pre.in_popped_range(pid)
            ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              }),
        ensures
          forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) ==> post.attached_ranges_segment(sid)
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn attached_rec_same(
        pre: State, post: State,
        segment_id: SegmentId, idx: int, sp: bool
    )
        requires
          pre.invariant(),
          pre.attached_rec(segment_id, idx, sp),
          Self::popped_ranges_match_for_sid(pre, post, segment_id),
          match pre.popped {
              Popped::VeryUnready(_, i, _, _) => i >= 0,
              _ => true,
          },
          match post.popped {
              Popped::VeryUnready(_, i, _, _) => i >= 0,
              _ => true,
          },
          forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            pid.segment_id == segment_id ==>
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> (
                (!pre.in_popped_range(pid) && pid.idx >= idx ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              }))),

          !sp ==> pre.popped_for_seg(segment_id) ==>
              idx >= Self::page_id_of_popped(pre.popped).idx + pre.popped_len(),
          idx >= 0,

        ensures post.attached_rec(segment_id, idx, sp),
          sp ==> pre.popped_for_seg(segment_id) ==>
              idx <= Self::page_id_of_popped(pre.popped).idx

        decreases SLICES_PER_SEGMENT - idx
    {
        unimplemented!()
    }

    pub closed spec fn if_popped_or_other_then_for(&self, segment_id: SegmentId) -> bool {
        match self.popped {
            Popped::No => true,
            Popped::Ready(page_id, _)
                | Popped::Used(page_id, _)
                => page_id.segment_id == segment_id,
            Popped::SegmentCreating(sid) => sid == segment_id,
            Popped::SegmentFreeing(sid, _) => sid == segment_id,
            Popped::VeryUnready(sid, _, _, _) => sid == segment_id,
            Popped::ExtraCount(_) => true,
        }
    }

    #[verifier::external_body]
    pub proof fn unchanged_used_ll(pre: Self, post: Self)
        requires pre.invariant(),
          pre.used_lists == post.used_lists,
          pre.used_dlist_headers == post.used_dlist_headers,
          forall |page_id: PageId|
            pre.pages.dom().contains(page_id)
              && pre.pages[page_id].is_used
              ==> post.pages.dom().contains(page_id)
                && post.pages[page_id].dlist_entry == pre.pages[page_id].dlist_entry
        ensures
          post.ll_inv_valid_used()
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn unchanged_unused_ll(pre: Self, post: Self)
        requires pre.invariant(),
          pre.unused_lists == post.unused_lists,
          pre.unused_dlist_headers == post.unused_dlist_headers,
          forall |page_id: PageId|
            pre.pages.dom().contains(page_id)
              && !pre.pages[page_id].is_used
              ==> post.pages.dom().contains(page_id)
                && post.pages[page_id].dlist_entry == pre.pages[page_id].dlist_entry
        ensures
          post.ll_inv_valid_unused()
    {
        unimplemented!()
    }

    pub closed spec fn insert_front(ll: Seq<Seq<PageId>>, i: int, page_id: PageId) -> Seq<Seq<PageId>> {
        ll.update(i, ll[i].insert(0, page_id))
    }

    pub closed spec fn insert_back(ll: Seq<Seq<PageId>>, i: int, page_id: PageId) -> Seq<Seq<PageId>> {
        ll.update(i, ll[i].push(page_id))
    }

    #[verifier::external_body]
    pub proof fn good_range_disjoint_very_unready(&self, page_id: PageId)
        requires self.invariant(),
            self.good_range_unused(page_id) || self.good_range_used(page_id),
        ensures (match self.popped {
            Popped::VeryUnready(sid, idx, count, _) => {
                sid != page_id.segment_id
                  || idx + count <= page_id.idx
                  || idx >= page_id.idx + self.pages[page_id].count.unwrap()
            }
            _ => true,
        })
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn rec_grd(&self, segment_id: SegmentId, idx: int, page_id: PageId)
        requires self.invariant(),
            self.good_range_unused(page_id),
            (match self.popped {
                Popped::VeryUnready(sid, idx, count, _) => {
                    sid == page_id.segment_id
                      && !(idx + count <= page_id.idx)
                      && !(idx >= page_id.idx + self.pages[page_id].count.unwrap())
                }
                _ => false,
            }),
            self.attached_rec(segment_id, idx, true),
            0 <= idx <= page_id.idx,
            page_id.segment_id == segment_id,
        ensures
            false
        decreases SLICES_PER_SEGMENT - idx
    {
        unimplemented!()
    }




    #[verifier::external_body]
    pub proof fn ll_unused_distinct(&self, i1: int, j1: int, i2: int, j2: int)
      requires self.invariant(),
        0 <= i1 < self.unused_lists.len(),
        0 <= j1 < self.unused_lists[i1].len(),
        0 <= i2 < self.unused_lists.len(),
        0 <= j2 < self.unused_lists[i2].len(),
        i1 != i2 || j1 != j2,
      ensures
        self.unused_lists[i1][j1] != self.unused_lists[i2][j2],
      decreases j1
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ll_used_distinct(&self, i1: int, j1: int, i2: int, j2: int)
      requires self.invariant(),
        0 <= i1 < self.used_lists.len(),
        0 <= j1 < self.used_lists[i1].len(),
        0 <= i2 < self.used_lists.len(),
        0 <= j2 < self.used_lists[i2].len(),
        i1 != i2 || j1 != j2,
      ensures
        self.used_lists[i1][j1] != self.used_lists[i2][j2],
      decreases j1
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ll_mono_back(lls1: Seq<Seq<PageId>>, sbin_idx: int, first_page: PageId)
    requires 0 <= sbin_idx < lls1.len()
    ensures ({
        let lls2 = Self::insert_back(lls1, sbin_idx, first_page);
        forall |pid| is_in_lls(pid, lls1) ==> is_in_lls(pid, lls2)
    })
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ll_mono(lls1: Seq<Seq<PageId>>, sbin_idx: int, first_page: PageId)
    requires 0 <= sbin_idx < lls1.len()
    ensures ({
        let lls2 = Self::insert_front(lls1, sbin_idx, first_page);
        forall |pid| is_in_lls(pid, lls1) ==> is_in_lls(pid, lls2)
    })
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn ll_remove(lls1: Seq<Seq<PageId>>, lls2: Seq<Seq<PageId>>, sbin_idx: int, list_idx: int)
    requires 0 <= sbin_idx < lls1.len(),
        0 <= list_idx < lls1[sbin_idx].len(),
        lls2 =~~= lls1.update(sbin_idx, lls1[sbin_idx].remove(list_idx)),
    ensures
        forall |pid| pid != lls1[sbin_idx][list_idx] ==>
            #[trigger] is_in_lls(pid, lls1) ==> is_in_lls(pid, lls2),
    {
        unimplemented!()
    }
}}

pub open spec fn is_header(pd: PageData) -> bool {
    pd.offset == Some(0nat)
}

pub open spec fn is_unused_header(pd: PageData) -> bool {
    pd.offset == Some(0nat) && !pd.is_used
}

pub open spec fn is_used_header(pd: PageData) -> bool {
    pd.offset == Some(0nat) && pd.is_used
}

pub open spec fn get_next(ll: Seq<PageId>, j: int) -> Option<PageId> {
    if j == ll.len() - 1 {
        None
    } else {
        Some(ll[j + 1])
    }
}

pub open spec fn get_prev(ll: Seq<PageId>, j: int) -> Option<PageId> {
    if j == 0 {
        None
    } else {
        Some(ll[j - 1])
    }
}

pub open spec fn valid_ll_i(pages: Map<PageId, PageData>, ll: Seq<PageId>, j: int) -> bool {
    0 <= j < ll.len()
      && pages.dom().contains(ll[j])
      && pages[ll[j]].dlist_entry.is_some()
      && pages[ll[j]].dlist_entry.unwrap().prev == get_prev(ll, j)
      && pages[ll[j]].dlist_entry.unwrap().next == get_next(ll, j)
}

pub open spec fn valid_ll(pages: Map<PageId, PageData>, header: DlistHeader, ll: Seq<PageId>) -> bool {
    &&& (match header.first {
        Some(first_id) => ll.len() != 0 && ll[0] == first_id,
        None => ll.len() == 0,
    })
    &&& (match header.last {
        Some(last_id) => ll.len() != 0 && ll[ll.len() - 1] == last_id,
        None => ll.len() == 0,
    })
    &&& (forall |j| 0 <= j < ll.len() ==> valid_ll_i(pages, ll, j))
}

pub open spec fn is_in_lls(page_id: PageId, s: Seq<Seq<PageId>>) -> bool {
    exists |i: int, j: int|
        0 <= i < s.len()
        && 0 <= j < s[i].len()
        && s[i][j] == page_id
}

}
}
mod os_mem_util {
use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::raw_ptr::*;
use vstd::modes::*;

use crate::os_mem::*;
use crate::layout::*;
use crate::tokens::*;
use crate::config::*;
use crate::page_organization::*;
use crate::types::*;

verus!{

impl MemChunk {
    #[verifier::external_body]
    pub proof fn empty() -> (tracked mc: MemChunk)
    {
        unimplemented!()
    }

    #[verifier::inline]
    pub open spec fn pointsto_has_range(&self, start: int, len: int) -> bool {
        set_int_range(start, start + len) <= self.range_points_to()
    }

    pub open spec fn os_rw_bytes(&self) -> Set<int> {
        self.range_os_rw()
    }

    pub open spec fn committed_pointsto_has_range(&self, start: int, len: int) -> bool {
        self.pointsto_has_range(start, len) && self.os_has_range_read_write(start, len)
    }

    #[verifier::external_body]
    pub proof fn split(
        tracked &mut self,
        start: int,
        len: int
    ) -> (tracked t: Self)
        ensures
            t.points_to.dom() == old(self).points_to.dom().intersect(set_int_range(start, start + len)),
            t.os == old(self).os.restrict(set_int_range(start, start + len)),
            final(self).points_to.dom() == old(self).points_to.dom().difference(set_int_range(start, start + len)),
            final(self).os == old(self).os.remove_keys(set_int_range(start, start + len)),
            final(self).points_to.provenance() == old(self).points_to.provenance(),
            final(self).points_to.provenance() == t.points_to.provenance(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn join(
        tracked &mut self,
        tracked t: Self,
    )
        requires
            old(self).points_to.provenance() == t.points_to.provenance(),
        ensures
            final(self).points_to.dom() == old(self).points_to.dom().union(t.points_to.dom()),
            final(self).os == old(self).os.union_prefer_right(t.os),
            final(self).points_to.provenance() == old(self).points_to.provenance(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn os_restrict(
        tracked &mut self,
        start: int,
        len: int
    )
        requires old(self).os_has_range(start, len),
        ensures final(self).points_to == old(self).points_to,
            final(self).os == old(self).os.restrict(set_int_range(start, start + len))
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn take_points_to_set(
        tracked &mut self,
        s: Set<int>,
    ) -> (tracked points_to: PointsToRaw)
        requires
            s <= old(self).points_to.dom()
        ensures
            final(self).os == old(self).os,
            final(self).points_to.dom() == old(self).points_to.dom().difference(s),
            points_to.dom() == s,
            final(self).points_to.provenance() == old(self).points_to.provenance(),
            points_to.provenance() == old(self).points_to.provenance(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn take_points_to_range(
        tracked &mut self,
        start: int,
        len: int
    ) -> (tracked points_to: PointsToRaw)
        requires
            len >= 0,
            old(self).pointsto_has_range(start, len),
        ensures
            final(self).os == old(self).os,
            final(self).points_to.dom() == old(self).points_to.dom().difference(set_int_range(start, start+len)),
            final(self).points_to.provenance() == old(self).points_to.provenance(),
            points_to.is_range(start, len),
            points_to.provenance() == old(self).points_to.provenance(),

    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn give_points_to_range(
        tracked &mut self,
        tracked points_to: PointsToRaw,
    )
        requires
            old(self).wf(),
            old(self).points_to.provenance() == points_to.provenance()
        ensures
            final(self).wf(),
            final(self).os == old(self).os,
            final(self).points_to.dom() == old(self).points_to.dom() + points_to.dom(),
            final(self).points_to.provenance() == points_to.provenance(),
    {
        unimplemented!()
    }
}

pub open spec fn segment_info_range(segment_id: SegmentId) -> Set<int> {
    set_int_range(segment_start(segment_id),
        segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + SIZEOF_PAGE_HEADER * (SLICES_PER_SEGMENT + 1)
    )
}

pub open spec fn mem_chunk_good1(
    mem: MemChunk,
    segment_id: SegmentId,
    commit_bytes: Set<int>,
    decommit_bytes: Set<int>,
    pages_range_total: Set<int>,
    pages_used_total: Set<int>,
) -> bool {
    &&& mem.wf()
    &&& mem.os_exact_range(segment_start(segment_id), SEGMENT_SIZE as int)
    &&& mem.points_to.provenance() == segment_id.provenance

    &&& commit_bytes.subset_of(mem.os_rw_bytes())

    &&& decommit_bytes <= commit_bytes
    &&& segment_info_range(segment_id) <= commit_bytes - decommit_bytes
    &&& pages_used_total <= commit_bytes - decommit_bytes

    &&& mem.os_rw_bytes() <=
          mem.points_to.dom()
            + segment_info_range(segment_id)
            + pages_range_total
}

impl Local {
    spec fn segment_page_range(&self, segment_id: SegmentId, page_id: PageId) -> Set<int> {
        if page_id.segment_id == segment_id && self.is_used_primary(page_id) {
            set_int_range(
                page_start(page_id) + start_offset(self.block_size(page_id)),
                page_start(page_id) + start_offset(self.block_size(page_id))
                    + self.page_capacity(page_id) * self.block_size(page_id)
            )
        } else {
            Set::empty()
        }
    }

    pub closed spec fn segment_pages_range_total(&self, segment_id: SegmentId) -> Set<int> {
        self.page_organization.pages.dom().map(
            |page_id| self.segment_page_range(segment_id, page_id)
        ).flatten()
    }

    #[verifier::external_body]
    proof fn get_page_id_of_addr_in_segment_pages_range_total(
        self,
        segment_id: SegmentId,
        addr: int
    ) -> (page_id: PageId)
        requires
            self.segment_pages_range_total(segment_id).contains(addr),
        ensures
            self.page_organization.pages.dom().contains(page_id),
            self.segment_page_range(segment_id, page_id).contains(addr),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn lemma_establish_segment_pages_range_total_contains(
        self,
        segment_id: SegmentId,
        page_id: PageId,
        addr: int
    )
        requires
            self.segment_page_range(segment_id, page_id).contains(addr),
            self.page_organization.pages.dom().contains(page_id),
        ensures
            self.segment_pages_range_total(segment_id).contains(addr),
    {
        unimplemented!()
    }

    spec fn segment_page_used(&self, segment_id: SegmentId, page_id: PageId) -> Set<int> {
        if page_id.segment_id == segment_id && self.is_used_primary(page_id) {
            set_int_range(
                page_start(page_id),
                page_start(page_id) + self.page_count(page_id) * SLICE_SIZE
            )
        } else {
            Set::empty()
        }
    }

    pub closed spec fn segment_pages_used_total(&self, segment_id: SegmentId) -> Set<int> {
        self.page_organization.pages.dom().map(
            |page_id| self.segment_page_used(segment_id, page_id)
        ).flatten()
    }

    #[verifier::external_body]
    proof fn get_page_id_of_addr_in_segment_pages_used_total(
        self,
        segment_id: SegmentId,
        addr: int
    ) -> (page_id: PageId)
        requires
            self.segment_pages_used_total(segment_id).contains(addr),
        ensures
            self.page_organization.pages.dom().contains(page_id),
            self.segment_page_used(segment_id, page_id).contains(addr),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn lemma_establish_segment_pages_used_total_contains(
        self,
        segment_id: SegmentId,
        page_id: PageId,
        addr: int
    )
        requires
            self.segment_page_used(segment_id, page_id).contains(addr),
            self.page_organization.pages.dom().contains(page_id),
        ensures
            self.segment_pages_used_total(segment_id).contains(addr),
    {
        unimplemented!()
    }



    pub open spec fn mem_chunk_good(&self, segment_id: SegmentId) -> bool {
        self.segments.dom().contains(segment_id)
        && mem_chunk_good1(
            self.segments[segment_id].mem,
            segment_id,
            self.commit_mask(segment_id).bytes(segment_id),
            self.decommit_mask(segment_id).bytes(segment_id),
            self.segment_pages_range_total(segment_id),
            self.segment_pages_used_total(segment_id),
        )
    }
}

#[verifier::external_body]
pub proof fn range_total_le_used_total(local: Local, sid: SegmentId)
    requires
        local.wf_main(),
        local.segments.dom().contains(sid),
    ensures
        local.segment_pages_range_total(sid)
            <= local.segment_pages_used_total(sid)
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn decommit_subset_of_pointsto(local: Local, sid: SegmentId)
    requires
        local.wf_main(),
        local.segments.dom().contains(sid),
        local.mem_chunk_good(sid),
    ensures
        local.decommit_mask(sid).bytes(sid) <=
            local.segments[sid].mem.points_to.dom()
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn very_unready_range_okay_to_decommit(local: Local)
    requires
        local.wf_main(),
        local.page_organization.popped.is_VeryUnready(),
    ensures
        (match local.page_organization.popped {
            Popped::VeryUnready(segment_id, idx, count, _) => {
                set_int_range(
                    segment_start(segment_id) + idx * SLICE_SIZE,
                    segment_start(segment_id) + idx * SLICE_SIZE + count * SLICE_SIZE,
                ).disjoint(
                    segment_info_range(segment_id)
                        + local.segment_pages_used_total(segment_id)
                )
            }
            _ => false,
        }),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_good(local1: Local, local2: Local)
    requires
        local1.segments.dom() == local2.segments.dom(),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.decommit_mask(sid).bytes(sid) == local1.decommit_mask(sid).bytes(sid),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.segments[sid].mem == local1.segments[sid].mem,
        forall |page_id| local1.is_used_primary(page_id) ==>
              local2.is_used_primary(page_id)
              && local1.page_capacity(page_id) <= local2.page_capacity(page_id)
              && local1.page_reserved(page_id) <= local2.page_reserved(page_id)
              && local1.page_count(page_id) == local2.page_count(page_id)
              && local1.block_size(page_id) == local2.block_size(page_id),
        forall |page_id: PageId| #[trigger] local2.is_used_primary(page_id) ==>
              local1.is_used_primary(page_id),

    ensures forall |sid| #[trigger] local1.segments.dom().contains(sid) ==>
        local1.mem_chunk_good(sid) ==> local2.mem_chunk_good(sid),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_good_except(local1: Local, local2: Local, esegment_id: SegmentId)
    requires
        local1.segments.dom().subset_of(local2.segments.dom()),
        forall |sid| sid != esegment_id ==> #[trigger] local1.segments.dom().contains(sid) ==> local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        forall |sid| sid != esegment_id ==> #[trigger] local1.segments.dom().contains(sid) ==> local2.decommit_mask(sid).bytes(sid) == local1.decommit_mask(sid).bytes(sid),
        forall |sid| sid != esegment_id ==> #[trigger] local1.segments.dom().contains(sid) ==> local2.segments[sid].mem == local1.segments[sid].mem,
        forall |page_id: PageId| page_id.segment_id != esegment_id && #[trigger] local1.is_used_primary(page_id) ==>
              local2.is_used_primary(page_id)
              && local1.page_capacity(page_id) <= local2.page_capacity(page_id)
              && local1.page_reserved(page_id) <= local2.page_reserved(page_id)
              && local1.page_count(page_id) == local2.page_count(page_id)
              && local1.block_size(page_id) == local2.block_size(page_id),

        forall |page_id: PageId| page_id.segment_id != esegment_id && #[trigger] local2.is_used_primary(page_id) ==>
              local1.is_used_primary(page_id),

    ensures forall |sid| sid != esegment_id ==> #[trigger] local1.segments.dom().contains(sid) ==>
        local1.mem_chunk_good(sid) ==> local2.mem_chunk_good(sid),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn empty_segment_pages_used_total(local1: Local, sid: SegmentId)
    requires
        forall |pid: PageId| pid.segment_id == sid ==> !local1.is_used_primary(pid),
    ensures
        local1.segment_pages_used_total(sid) =~= Set::empty(),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn preserves_segment_pages_used_total(local1: Local, local2: Local, sid: SegmentId)
    requires
        forall |page_id: PageId| page_id.segment_id == sid && #[trigger] local2.is_used_primary(page_id) ==>
              local1.is_used_primary(page_id)
              && local1.page_count(page_id) == local2.page_count(page_id),
    ensures local2.segment_pages_used_total(sid) <=
        local1.segment_pages_used_total(sid),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn preserve_totals(local1: Local, local2: Local, sid: SegmentId)
    requires
        forall |page_id: PageId| page_id.segment_id == sid && #[trigger] local2.is_used_primary(page_id) ==>
              local1.is_used_primary(page_id)
              && local1.page_count(page_id) == local2.page_count(page_id)
              && local1.page_capacity(page_id) == local2.page_capacity(page_id)
              && local1.block_size(page_id) == local2.block_size(page_id),
        forall |page_id: PageId| page_id.segment_id == sid && #[trigger] local1.is_used_primary(page_id) ==>
              local2.is_used_primary(page_id)
    ensures
        local2.segment_pages_used_total(sid) =~= local1.segment_pages_used_total(sid),
        local2.segment_pages_range_total(sid) =~= local1.segment_pages_range_total(sid),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_good_on_commit(local1: Local, local2: Local, sid: SegmentId)
    requires
        local1.segments.dom().contains(sid),
        local2.segments.dom().contains(sid),
        local1.mem_chunk_good(sid),
        local2.page_organization == local1.page_organization,
        local2.pages == local1.pages,
        local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        local2.decommit_mask(sid).bytes(sid) == local1.decommit_mask(sid).bytes(sid),
        local2.segments[sid].mem.wf(),
        local2.segments[sid].mem.has_new_pointsto(&local1.segments[sid].mem),
        local2.segments[sid].mem.points_to.provenance() == local1.segments[sid].mem.points_to.provenance(),
    ensures local2.mem_chunk_good(sid),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_good_on_decommit(local1: Local, local2: Local, sid: SegmentId)
    requires
        local1.segments.dom().contains(sid),
        local2.segments.dom().contains(sid),
        local1.mem_chunk_good(sid),
        local2.page_organization == local1.page_organization,
        local2.pages == local1.pages,
        local2.segments[sid].mem.wf(),
        local2.segments[sid].mem.points_to.provenance() == local1.segments[sid].mem.points_to.provenance(),

        local2.decommit_mask(sid).bytes(sid) <= local1.decommit_mask(sid).bytes(sid),
        local2.commit_mask(sid).bytes(sid) =~=
            local1.commit_mask(sid).bytes(sid) -
              (local1.decommit_mask(sid).bytes(sid) - local2.decommit_mask(sid).bytes(sid)),

        local2.segments[sid].mem.os_rw_bytes() <= local1.segments[sid].mem.os_rw_bytes(),
        local2.segments[sid].mem.points_to.dom() =~=
            local1.segments[sid].mem.points_to.dom() -
              (local1.segments[sid].mem.os_rw_bytes() - local2.segments[sid].mem.os_rw_bytes()),

        (local1.segments[sid].mem.os_rw_bytes() - local2.segments[sid].mem.os_rw_bytes())
          <= (local1.decommit_mask(sid).bytes(sid) - local2.decommit_mask(sid).bytes(sid)),


        local2.segments[sid].mem.os.dom() =~= local1.segments[sid].mem.os.dom(),
    ensures local2.mem_chunk_good(sid),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_good_on_commit_with_mask_set(local1: Local, local2: Local, sid: SegmentId)
    requires
        local1.segments.dom().contains(sid),
        local2.segments.dom().contains(sid),
        local1.mem_chunk_good(sid),
        local2.page_organization == local1.page_organization,
        local2.pages == local1.pages,
        local2.segments[sid].mem.wf(),
        local2.segments[sid].mem.has_new_pointsto(&local1.segments[sid].mem),
        local2.segments[sid].mem.points_to.provenance() == sid.provenance,

        local2.decommit_mask(sid).bytes(sid).subset_of( local1.decommit_mask(sid).bytes(sid) ),
        local1.commit_mask(sid).bytes(sid).subset_of( local2.commit_mask(sid).bytes(sid) ),

        local2.decommit_mask(sid).bytes(sid).disjoint(
            local2.commit_mask(sid).bytes(sid) - local1.commit_mask(sid).bytes(sid)),

        (local1.segments[sid].mem.os_rw_bytes() + (
            local2.commit_mask(sid).bytes(sid) - local1.commit_mask(sid).bytes(sid)))
          .subset_of(local2.segments[sid].mem.os_rw_bytes())
    ensures local2.mem_chunk_good(sid),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_good_on_transfer_to_capacity(local1: Local, local2: Local, page_id: PageId)
    requires
        local1.segments.dom().contains(page_id.segment_id),
        local2.segments.dom().contains(page_id.segment_id),
        local1.mem_chunk_good(page_id.segment_id),
        local2.page_organization == local1.page_organization,
        local1.pages.dom().contains(page_id),
        local2.pages.dom().contains(page_id),
        local2.commit_mask(page_id.segment_id).bytes(page_id.segment_id) == local1.commit_mask(page_id.segment_id).bytes(page_id.segment_id),
        local2.decommit_mask(page_id.segment_id).bytes(page_id.segment_id) == local1.decommit_mask(page_id.segment_id).bytes(page_id.segment_id),
        local2.segments[page_id.segment_id].mem.wf(),
        local2.segments[page_id.segment_id].mem.points_to.provenance() == page_id.segment_id.provenance,

        local1.is_used_primary(page_id),
        forall |page_id| #[trigger] local1.is_used_primary(page_id) ==>
              local2.is_used_primary(page_id)
              && local1.page_capacity(page_id) <= local2.page_capacity(page_id)
              && local1.block_size(page_id) == local2.block_size(page_id)
              && local1.page_count(page_id) == local2.page_count(page_id),

        forall |page_id| local2.is_used_primary(page_id) ==>
              local1.is_used_primary(page_id),

        local2.segments[page_id.segment_id].mem.os
          == local1.segments[page_id.segment_id].mem.os,
        ({ let sr = set_int_range(
                page_start(page_id)
                    + start_offset(local1.block_size(page_id))
                    + local1.page_capacity(page_id) * local1.block_size(page_id),
                page_start(page_id)
                    + start_offset(local1.block_size(page_id))
                    + local2.page_capacity(page_id) * local1.block_size(page_id),
            );
          local2.segments[page_id.segment_id].mem.points_to.dom() =~=
              local1.segments[page_id.segment_id].mem.points_to.dom() - sr
        }),
    ensures local2.mem_chunk_good(page_id.segment_id),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_good_on_transfer_back(local1: Local, local2: Local, page_id: PageId)
    requires
        local1.segments.dom().contains(page_id.segment_id),
        local2.segments.dom().contains(page_id.segment_id),
        local1.mem_chunk_good(page_id.segment_id),

        local1.pages.dom().contains(page_id),
        local2.pages.dom().contains(page_id),
        local2.commit_mask(page_id.segment_id).bytes(page_id.segment_id) == local1.commit_mask(page_id.segment_id).bytes(page_id.segment_id),
        local2.decommit_mask(page_id.segment_id).bytes(page_id.segment_id) == local1.decommit_mask(page_id.segment_id).bytes(page_id.segment_id),
        local2.segments[page_id.segment_id].mem.wf(),
        local2.segments[page_id.segment_id].mem.points_to.provenance() == page_id.segment_id.provenance,

        local1.is_used_primary(page_id),
        forall |pid| #[trigger] local1.is_used_primary(pid) && pid != page_id ==>
              local2.is_used_primary(pid)
              && local1.page_capacity(pid) <= local2.page_capacity(pid)
              && local1.block_size(pid) == local2.block_size(pid)
              && local1.page_count(pid) == local2.page_count(pid),

        forall |pid| #[trigger] local2.is_used_primary(pid) ==>
              local1.is_used_primary(pid),
        !local2.is_used_primary(page_id),

        local2.segments[page_id.segment_id].mem.os
          == local1.segments[page_id.segment_id].mem.os,
        local2.segments[page_id.segment_id].mem.points_to.dom() =~=
            local1.segments[page_id.segment_id].mem.points_to.dom() +
            set_int_range(
                page_start(page_id)
                    + start_offset(local1.block_size(page_id)),
                page_start(page_id)
                    + start_offset(local1.block_size(page_id))
                    + local1.page_capacity(page_id) * local1.block_size(page_id),
            )
    ensures local2.mem_chunk_good(page_id.segment_id),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_on_set_used(local1: Local, local2: Local, page_id: PageId)
    requires
        local1.mem_chunk_good(page_id.segment_id),
        local1.segments.dom() == local2.segments.dom(),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.decommit_mask(sid).bytes(sid) == local1.decommit_mask(sid).bytes(sid),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.segments[sid].mem == local1.segments[sid].mem,
        forall |pid| local1.is_used_primary(pid) ==>
              local2.is_used_primary(pid)
              && local1.page_capacity(pid) <= local2.page_capacity(pid)
              && local1.page_reserved(pid) <= local2.page_reserved(pid)
              && local1.page_count(pid) == local2.page_count(pid)
              && local1.block_size(pid) == local2.block_size(pid),
        forall |pid: PageId| #[trigger] local2.is_used_primary(pid) && page_id != pid ==>
              local1.is_used_primary(pid),
        page_init_is_committed(page_id, local2),
    ensures local2.mem_chunk_good(page_id.segment_id),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn segment_mem_has_reserved_range(local: Local, page_id: PageId, new_cap: int)
    requires
        local.wf_main(),
        local.is_used_primary(page_id),
        local.page_capacity(page_id) <= new_cap <= local.page_reserved(page_id),
    ensures ({ let blocksize = local.block_size(page_id);
        local.segments[page_id.segment_id].mem.pointsto_has_range(
            block_start_at(page_id, blocksize, local.page_capacity(page_id)),
            (new_cap - local.page_capacity(page_id)) * blocksize)
    })
{
    unimplemented!()
}


pub open spec fn page_init_is_committed(page_id: PageId, local: Local) -> bool {
    let count = local.page_organization.pages[page_id].count.unwrap() as int;
    let start = page_start(page_id);
    let len = count * SLICE_SIZE;
    let cm = local.segments[page_id.segment_id].main.value().commit_mask@;

    set_int_range(start, start + len) <=
        local.commit_mask(page_id.segment_id).bytes(page_id.segment_id)
        - local.decommit_mask(page_id.segment_id).bytes(page_id.segment_id)
    && count == local.page_count(page_id)
}

}
}


mod pigeonhole {
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::assert_by_contradiction;

verus!{

#[verifier::external_body]
proof fn singleton_set_unique_elt<T>(s: Set<T>, a:T, b:T)
    requires
        s.len() == 1,
        s.contains(a),
        s.contains(b),
    ensures
        a == b,
{
    unimplemented!()
}

#[verifier::external_body]
proof fn set_mismatch(s1:Set<nat>, s2:Set<nat>, missing:nat)
    requires
        s1.len() == s2.len(),
        forall |elt| s2.contains(elt) ==> s1.contains(elt),
        s1.contains(missing),
        !s2.contains(missing),
    ensures
        false,
    decreases s1.len(),
{
    unimplemented!()
}


pub open spec fn set_nat_range(lo: nat, hi: nat) -> Set<nat> {
    Set::range(lo, hi)
}

#[verifier::external_body]
pub proof fn lemma_nat_range(lo: nat, hi: nat)
    requires
        lo <= hi,
    ensures
        set_nat_range(lo, hi).len() == hi - lo,
    decreases
        hi - lo,
{
    unimplemented!()
}


#[verifier::external_body]
proof fn nat_set_size(s:Set<nat>, bound:nat)
    requires
        forall |i: nat| (0 <= i < bound <==> s.contains(i)),
    ensures
        s.len() == bound,
{
    unimplemented!()
}



#[verifier::external_body]
pub proof fn pigeonhole_missing_idx_implies_double_helper(
    m: Map<nat, nat>,
    missing: nat,
    len: nat,
    prev_vals: Set<nat>,
    k: nat,
) -> (dup2: nat)
    requires
        len >= 2,
        forall |i: nat| (0 <= i < len <==> m.dom().contains(i)),
        forall |i: nat| (#[trigger] m.dom().contains(i) ==> (
            0 <= m[i] < len && m[i] != missing
        )),
        0 <= missing < len,
        0 <= k < len,
        prev_vals.len() == k,
        forall |elt| #[trigger] prev_vals.contains(elt) ==> exists |j| 0 <= j < k && m[j] == elt,
    ensures
        m.dom().contains(dup2),
        exists |dup1| #![auto] dup1 != dup2 && m.dom().contains(dup1) && 0 <= dup1 < len && m[dup1] == m[dup2],
    decreases len - k,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn pigeonhole_missing_idx_implies_double(
    m: Map<nat, nat>,
    missing: nat,
    len: nat,
) -> (r: (nat, nat))
    requires
        forall |i: nat| (0 <= i < len <==> m.dom().contains(i)),
        forall |i: nat| (#[trigger] m.dom().contains(i) ==> (
            0 <= m[i] < len && m[i] != missing
        )),
        0 <= missing < len,
    ensures ({ let (i, j) = r;
        i != j
          && m.dom().contains(i)
          && m.dom().contains(j)
          && m[i] == m[j]
    })
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn pigeonhole_too_many_elements_implies_double(
    m: Map<nat, nat>,
    len: nat,
) -> (r: (nat, nat))
    requires
        forall |i: nat| (0 <= i < len + 1 <==> m.dom().contains(i)),
        forall |i: nat| #[trigger] m.dom().contains(i) ==> 0 <= m[i] < len,
    ensures ({ let (i, j) = r;
        i != j
          && m.dom().contains(i)
          && m.dom().contains(j)
          && m[i] == m[j]
    })
{
    unimplemented!()
}

}
}


mod linked_list {
#![allow(unused_imports)]

use verus_state_machines_macros::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::modes::*;
use vstd::*;
use vstd::set_lib::*;
use vstd::layout::*;
use vstd::atomic_ghost::*;

use crate::tokens::{Mim, BlockId, PageId, DelayState, HeapId};
use crate::layout::{is_block_ptr, block_size_ge_word, block_ptr_aligned_to_word, block_start_at, block_start, is_block_ptr1};
use crate::types::*;
use crate::config::INTPTR_SIZE;
use core::intrinsics::unlikely;

verus!{


#[repr(C)]
#[derive(Copy)]
pub struct Node {
    pub ptr: *mut Node,
}

impl Clone for Node {
    fn clone(&self) -> Node {
        Node { ptr: self.ptr }
    }
}

global layout Node is size == 8, align == 8;

#[verifier::external_body]
pub proof fn size_of_node()
    ensures size_of::<Node>() == 8
        && align_of::<Node>() == 8
{
    unimplemented!()
}

pub ghost struct LLData {
    ghost fixed_page: bool,
    ghost block_size: nat,
    ghost page_id: PageId,
    ghost heap_id: Option<HeapId>,

    ghost instance: Mim::Instance,
    ghost len: nat,
}

pub struct LL {
    first: *mut Node,

    data: Ghost<LLData>,

    perms: Tracked<Map<nat, (PointsTo<Node>, PointsToRaw, Mim::block, IsExposed)>>,
}

pub tracked struct LLGhostStateToReconvene {
    pub ghost block_size: nat,
    pub ghost page_id: PageId,
    pub ghost instance: Mim::Instance,

    pub tracked map: Map<nat, (PointsToRaw, Mim::block)>,
}

impl LL {
    pub closed spec fn next_ptr(&self, i: nat) -> *mut Node {
        if i == 0 {
            core::ptr::null_mut()
        } else {
            self.perms@.index((i - 1) as nat).0.ptr()
        }
    }

    pub closed spec fn valid_node(&self, i: nat, next_ptr: *mut Node) -> bool {
        0 <= i < self.data@.len ==> (
            self.perms@.dom().contains(i) && {
                  let (perm, padding, block_token, is_exposed) = self.perms@.index(i);

                  perm.is_init()
                  && perm.value().ptr.addr() == next_ptr.addr()

                  && block_token.key().block_size - size_of::<Node>() >= 0
                  && padding.is_range(perm.ptr().addr() + size_of::<Node>(),
                      block_token.key().block_size - size_of::<Node>())
                  && padding.provenance() == perm.ptr()@.provenance
                  && is_exposed.provenance() == padding.provenance()

                  && block_token.instance_id() == self.data@.instance.id()
                  && is_block_ptr(perm.ptr() as *mut u8, block_token.key())

                  && (self.data@.fixed_page ==> (
                      block_token.key().page_id == self.data@.page_id
                      && block_token.key().block_size == self.data@.block_size
                  ))

                  && (match self.data@.heap_id {
                      Some(heap_id) => block_token.value().heap_id == Some(heap_id),
                      None => true,
                  })
            }
        )
    }

    pub closed spec fn wf(&self) -> bool {
        &&& (forall |i: nat| self.perms@.dom().contains(i) ==> 0 <= i < self.data@.len)
        &&& self.first.addr() == self.next_ptr(self.data@.len).addr()
        &&& (forall |i: nat| self.valid_node(i, #[trigger] self.next_ptr(i)))
    }

    pub closed spec fn len(&self) -> nat {
        self.data@.len
    }

    pub closed spec fn page_id(&self) -> PageId {
        self.data@.page_id
    }

    pub closed spec fn block_size(&self) -> nat {
        self.data@.block_size
    }

    pub closed spec fn fixed_page(&self) -> bool {
        self.data@.fixed_page
    }

    pub closed spec fn instance(&self) -> Mim::Instance {
        self.data@.instance
    }

    pub closed spec fn heap_id(&self) -> Option<HeapId> {
        self.data@.heap_id
    }

    pub closed spec fn ptr(&self) -> *mut Node {
        self.first
    }


    #[inline(always)]
    pub fn insert_block(&mut self, ptr: *mut u8, Tracked(points_to_raw): Tracked<PointsToRaw>, Tracked(block_token): Tracked<Mim::block>)
        requires old(self).wf(),
            points_to_raw.is_range(ptr as int, block_token.key().block_size as int),
            points_to_raw.provenance() == ptr@.provenance,
            block_token.instance_id() == old(self).instance().id(),
            is_block_ptr(ptr, block_token.key()),
            old(self).fixed_page() ==> (
                block_token.key().page_id == old(self).page_id()
                && block_token.key().block_size == old(self).block_size()
            ),
            old(self).heap_id().is_none(),
        ensures
            final(self).wf(),
            final(self).block_size() == old(self).block_size(),
            final(self).len() == old(self).len() + 1,
            final(self).instance() == old(self).instance(),
            final(self).page_id() == old(self).page_id(),
            final(self).fixed_page() == old(self).fixed_page(),
            final(self).heap_id() == old(self).heap_id(),
    {
        let tracked mut mem1;
        let tracked mut mem2;
        vstd::layout::layout_for_type_is_valid::<Node>();
        proof {
            block_size_ge_word();
            block_ptr_aligned_to_word();

            let tracked (m1, m2) = points_to_raw.split(set_int_range(ptr as int, ptr as int + size_of::<Node>() as int));
            mem1 = m1.into_typed::<Node>(ptr.addr());
            mem2 = m2;
        }

        let ptr = ptr as *mut Node;
        ptr_mut_write(ptr, Tracked(&mut mem1), Node { ptr: self.first });
        self.first = ptr;
        let Tracked(is_exposed) = expose_provenance(ptr);

        proof {
            let tracked tuple = (mem1, mem2, block_token, is_exposed);
            self.perms.borrow_mut().tracked_insert(self.data@.len, tuple);
            self.data@.len = self.data@.len + 1;

            let ghost len = self.data@.len;

            assert forall |i: nat| self.perms@.dom().contains(i) implies 0 <= i < self.data@.len
            by {
                if i + 1 < len {
                    assert(old(self).perms@.dom().contains(i));
                }
            }

            assert forall |i: nat| #[trigger] self.valid_node(i, self.next_ptr(i))
            by {
                assert(old(self).valid_node(i, old(self).next_ptr(i)));
                if i > 0 {
                    let j = (i - 1) as nat;
                    assert(old(self).valid_node(j, old(self).next_ptr(j)));
                }
            }
        }
    }


    #[verifier::external_body]
    pub proof fn ghost_insert_block(
        tracked self_: &mut Tracked<LL>,
        tracked ptr: *mut Node,
        tracked points_to_ptr: PointsTo<Node>,
        tracked points_to_raw: PointsToRaw,
        tracked block_token: Mim::block,
        tracked is_exposed: IsExposed,
     )
        requires old(self_).wf(),
            block_token.instance_id() == old(self_).instance().id(),
            is_block_ptr(ptr as *mut u8, block_token.key()),

            points_to_ptr.ptr() == ptr,
            points_to_ptr.is_init(),
            points_to_ptr.value().ptr.addr() == old(self_).ptr().addr(),

            points_to_raw.is_range(
                ptr as int + size_of::<Node>(),
                block_token.key().block_size - size_of::<Node>()),
            points_to_raw.provenance() == is_exposed.provenance(),
            points_to_raw.provenance() == ptr@.provenance,
            block_token.key().block_size - size_of::<Node>() >= 0,

            old(self_).fixed_page() ==> (
                block_token.key().page_id == old(self_).page_id()
                && block_token.key().block_size == old(self_).block_size()
            ),
            (match old(self_).heap_id() {
                Some(heap_id) => block_token.value().heap_id == Some(heap_id),
                None => true,
            }),
        ensures
            final(self_).wf(),
            final(self_).block_size() == old(self_).block_size(),
            final(self_).len() == old(self_).len() + 1,
            final(self_).instance() == old(self_).instance(),
            final(self_).page_id() == old(self_).page_id(),
            final(self_).fixed_page() == old(self_).fixed_page(),
            final(self_).heap_id() == old(self_).heap_id(),
            final(self_).ptr() == ptr
    {
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn is_empty_iff_null(tracked &self)
        requires self.wf(),
        ensures self.len() == 0 <==> self.first.addr() == 0
    {
        unimplemented!()
    }

    #[inline(always)]
    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b <==> (self.len() == 0)
    {
        proof {
            self.is_empty_iff_null();
        }
        self.first.addr() == 0
    }

    #[inline(always)]
    pub fn pop_block(&mut self) -> (x: (*mut u8, Tracked<PointsToRaw>, Tracked<Mim::block>))
        requires old(self).wf(),
            old(self).len() != 0,
        ensures ({
            let (ptr, points_to, block_token) = x;
            {
                &&& final(self).wf()
                &&& final(self).block_size() == old(self).block_size()
                &&& final(self).len() + 1 == old(self).len()
                &&& final(self).instance() == old(self).instance()
                &&& final(self).page_id() == old(self).page_id()
                &&& final(self).fixed_page() == old(self).fixed_page()
                &&& final(self).heap_id() == old(self).heap_id()

                &&& points_to@.is_range(ptr as int, block_token@.key().block_size as int)
                &&& points_to@.provenance() == ptr@.provenance

                &&& block_token@.instance_id() == old(self).instance().id()
                &&& is_block_ptr(ptr, block_token@.key())

                &&& (final(self).fixed_page() ==> (
                    block_token@.key().page_id == final(self).page_id()
                    && block_token@.key().block_size == final(self).block_size()
                ))
                &&& (match final(self).heap_id() {
                    Some(heap_id) => block_token@.value().heap_id == Some(heap_id),
                    None => true,
                })
            }
        })
    {
        proof {
            let i = (self.data@.len - 1) as nat;
            assert(self.valid_node(i, self.next_ptr(i)));
        }
        let tracked (mut points_to_node, points_to_raw, block, is_exposed) = self.perms.borrow_mut().tracked_remove((self.data@.len - 1) as nat);

        let ptr: *mut Node = with_exposed_provenance(self.first.addr(), Tracked(is_exposed));
        let node = ptr_mut_read(ptr, Tracked(&mut points_to_node));
        self.first = node.ptr;

        let tracked points_to_raw = points_to_node.into_raw().join(points_to_raw);
        let ptru = ptr as *mut u8;

        proof {
            self.data@.len = (self.data@.len - 1) as nat;
            assert forall |i: nat| self.valid_node(i, #[trigger] self.next_ptr(i))
            by {
                assert(old(self).valid_node(i, old(self).next_ptr(i)));
                if i > 0 {
                    let j = (i - 1) as nat;
                    assert(old(self).valid_node(j, old(self).next_ptr(j)));
                }
            }
            let j = self.data@.len;
            assert(old(self).valid_node(j, old(self).next_ptr(j)));
            assert(old(self).valid_node((j-1) as nat, old(self).next_ptr((j-1) as nat)));
            assert((forall |i: nat| self.perms@.dom().contains(i) ==> 0 <= i < self.data@.len));
            assert(self.wf());
        }

        assert(block.key().block_size >= size_of::<Node>());

        return (ptru, Tracked(points_to_raw), Tracked(block))
    }


    #[inline(always)]
    pub fn block_write_ptr(ptr: *mut Node, Tracked(perm): Tracked<PointsToRaw>, next: *mut Node)
        -> (res: (Tracked<PointsTo<Node>>, Tracked<PointsToRaw>))
        requires
            perm.contains_range(ptr as int, size_of::<Node>() as int),
            perm.provenance() == ptr@.provenance,
            ptr as int % align_of::<crate::linked_list::Node>() as int == 0,
        ensures ({
            let points_to = res.0@;
            let points_to_raw = res.1@;

            points_to.ptr() == ptr
              && points_to.opt_value() == MemContents::Init(Node { ptr: next })

              && points_to_raw.dom() == perm.dom().difference(set_int_range(ptr as int, ptr as int + size_of::<Node>()))
              && points_to_raw.provenance() == ptr@.provenance
        }),
    {
        let tracked (points_to, rest) = perm.split(set_int_range(ptr as int, ptr as int + size_of::<Node>()));

        vstd::layout::layout_for_type_is_valid::<Node>();
        let tracked mut points_to_node = points_to.into_typed::<Node>(ptr.addr());
        ptr_mut_write(ptr, Tracked(&mut points_to_node), Node { ptr: next });
        (Tracked(points_to_node), Tracked(rest))
    }

    #[inline(always)]
    pub fn new(Ghost(page_id): Ghost<PageId>,
        Ghost(fixed_page): Ghost<bool>,
        Ghost(instance): Ghost<Mim::Instance>,
        Ghost(block_size): Ghost<nat>,
        Ghost(heap_id): Ghost<Option<HeapId>>,
    ) -> (ll: LL)
        ensures ll.wf(),
            ll.page_id() == page_id,
            ll.fixed_page() == fixed_page,
            ll.instance() == instance,
            ll.block_size() == block_size,
            ll.heap_id() == heap_id,
            ll.len() == 0,
    {
        LL {
            first: core::ptr::null_mut(),
            data: Ghost(LLData {
                fixed_page, block_size, page_id, instance, len: 0, heap_id,
            }),
            perms: Tracked(Map::tracked_empty()),
        }
    }

    #[inline(always)]
    pub fn empty() -> (ll: LL)
        ensures ll.wf(),
            ll.len() == 0,
    {
        LL::new(Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()))
    }


    #[inline(always)]
    pub fn set_ghost_data(
        &mut self,
        Ghost(page_id): Ghost<PageId>,
        Ghost(fixed_page): Ghost<bool>,
        Ghost(instance): Ghost<Mim::Instance>,
        Ghost(block_size): Ghost<nat>,
        Ghost(heap_id): Ghost<Option<HeapId>>,
    )
        requires old(self).wf(), old(self).len() == 0,
        ensures
            final(self).wf(),
            final(self).page_id() == page_id,
            final(self).fixed_page() == fixed_page,
            final(self).instance() == instance,
            final(self).block_size() == block_size,
            final(self).heap_id() == heap_id,
            final(self).len() == 0,
    {
        proof {
            self.data@.fixed_page = fixed_page;
            self.data@.block_size = block_size;
            self.data@.page_id = page_id;
            self.data@.instance = instance;
            self.data@.heap_id = heap_id;
        }
    }



    #[inline(always)]
    pub fn append(&mut self, other: &mut LL) -> (other_len: u32)
        requires
            old(self).wf() && old(other).wf(),
            old(self).page_id() == old(other).page_id(),
            old(self).block_size() == old(other).block_size(),
            old(self).fixed_page() == old(other).fixed_page(),
            old(self).instance() == old(other).instance(),
            old(self).heap_id().is_none(),
            old(other).heap_id().is_none(),
            old(other).len() < u32::MAX,
        ensures
            final(self).wf() && final(other).wf(),
            final(self).page_id() == old(self).page_id(),
            final(self).block_size() == old(self).block_size(),
            final(self).fixed_page() == old(self).fixed_page(),
            final(self).instance() == old(self).instance(),
            final(self).heap_id() == old(self).heap_id(),
            final(other).page_id() == old(other).page_id(),
            final(other).block_size() == old(other).block_size(),
            final(other).fixed_page() == old(other).fixed_page(),
            final(other).instance() == old(other).instance(),
            final(other).heap_id() == old(other).heap_id(),

            final(self).len() == old(self).len() + old(other).len(),
            final(other).len() == 0,

            other_len as int == old(other).len(),
    {
        proof {
            other.is_empty_iff_null();
        }
        if other.first.addr() == 0 {
            return 0;
        }

        let mut count = 1;
        let mut p = other.first;
        loop
            invariant
                1 <= count <= other.len(),
                other.len() < u32::MAX,
                other.wf(),
                p.addr() == other.perms@[(other.len() - count) as nat].0.ptr().addr(),
            ensures
                count == other.len(),
                p == other.perms@[0].0.ptr(),
        {
            proof {
                let ghost i = (other.len() - count) as nat;
                let ghost j = (i - 1) as nat;
                assert(other.valid_node(i, other.next_ptr(i)));
                assert(other.valid_node(j, other.next_ptr(j)));
                if i != 0 {
                    other.perms.borrow().tracked_borrow(j).0.is_nonnull();
                }
            }

            p = with_exposed_provenance(p.addr(),
                Tracked(other.perms.borrow().tracked_borrow((other.len() - count) as nat).3));

            let next = *ptr_ref(p, Tracked(&other.perms.borrow().tracked_borrow((other.len() - count) as nat).0));
            if next.ptr.addr() != 0 {
                count += 1;
                p = next.ptr;
            } else {
                break;
            }
        }

        let ghost old_other = *other;
        let ghost old_self = *self;

        assert(other.valid_node(0, other.next_ptr(0)));
        let tracked mut perm = other.perms.borrow_mut().tracked_remove(0);
        let tracked (mut a, b, c, exposed) = perm;
        let _ = ptr_mut_read(p, Tracked(&mut a));
        ptr_mut_write(p, Tracked(&mut a), Node { ptr: self.first });

        proof {
            other.perms.borrow_mut().tracked_insert(0, (a, b, c, exposed));

            let other_len = other.data@.len;
            let self_len = self.data@.len;
            self.data@.len = self.data@.len + other.data@.len;
            other.data@.len = 0;

            let tracked mut other_map = Map::tracked_empty();
            tracked_swap(other.perms.borrow_mut(), &mut other_map);

            let tracked mut self_map = Map::tracked_empty();
            tracked_swap(self.perms.borrow_mut(), &mut self_map);

            let key_map = Map::<nat, nat>::new(
                    Set::range(self_len, self_len + other_len),
                    |i: nat| (i - self_len) as nat,
                );
            assert forall|j| key_map.dom().contains(j) implies other_map.dom().contains(key_map.index(j))
            by {
                let r = (j - self_len) as nat;
                assert(old_other.valid_node(r, old_other.next_ptr(r)));
            }

            other_map.tracked_map_keys_in_place(key_map);
            other_map.tracked_union_prefer_right(self_map);
            self.perms@ = other_map;
        }

        self.first = other.first;
        other.first = core::ptr::null_mut();

        proof {
            assert forall |i: nat| self.valid_node(i, #[trigger] self.next_ptr(i))
            by {
                assert(old_self.valid_node(i, old_self.next_ptr(i)));
                assert(old_self.valid_node((i-1) as nat, old_self.next_ptr((i-1) as nat)));
                let k = (i - old_self.data@.len) as nat;
                let k1 = (k - 1) as nat;
                assert(old_other.valid_node(k, old_other.next_ptr(k)));
                assert(old_other.valid_node(k1, old_other.next_ptr(k1)));

                if i < old_self.data@.len {
                    assert(self.valid_node(i, self.next_ptr(i)));
                } else if i < self.data@.len {
                    assert(self.valid_node(i, self.next_ptr(i)));
                } else {
                    assert(self.valid_node(i, self.next_ptr(i)));
                }
            }
        }

        return count;
    }


    #[inline(always)]
    pub fn prepend_contiguous_blocks(
        &mut self,
        start: *mut u8,
        last: *mut u8,
        bsize: usize,

        Ghost(cap): Ghost<nat>,
        Ghost(extend): Ghost<nat>,

        Tracked(points_to_raw_r): Tracked<&mut PointsToRaw>,
        Tracked(tokens): Tracked<&mut Map<int, Mim::block>>,
    )
        requires
            old(self).wf(),
            old(self).fixed_page(),
            old(self).block_size() == bsize as nat,
            old(self).heap_id().is_none(),
            INTPTR_SIZE <= bsize,
            start as int % INTPTR_SIZE as int == 0,
            bsize as int % INTPTR_SIZE as int == 0,

            old(points_to_raw_r).is_range(start as int, extend as int * bsize as int),
            old(points_to_raw_r).provenance() == start@.provenance,
            start@.provenance == old(self).page_id().segment_id.provenance,
            start as int + extend * bsize <= usize::MAX,

            start as int ==
                block_start_at(old(self).page_id(), old(self).block_size() as int, cap as int),

            extend >= 1,
            last as int == start as int + ((extend as int - 1) * bsize as int),

            (forall |i: int| cap <= i < cap + extend ==> old(tokens).dom().contains(i)),
            (forall |i: int| cap <= i < cap + extend ==> old(tokens).index(i).instance_id() == old(self).instance().id()),
            (forall |i: int| cap <= i < cap + extend ==> old(tokens).index(i).key().page_id == old(self).page_id()),
            (forall |i: int| cap <= i < cap + extend ==> old(tokens).index(i).key().idx == i),
            (forall |i: int| cap <= i < cap + extend ==> old(tokens).index(i).key().block_size == bsize),
            (forall |i: int| cap <= i < cap + extend ==> is_block_ptr1(
                block_start(old(tokens).index(i).key()),
                old(tokens).index(i).key())
            )
        ensures
            final(self).wf(),
            final(self).page_id() == old(self).page_id(),
            final(self).block_size() == old(self).block_size(),
            final(self).fixed_page() == old(self).fixed_page(),
            final(self).instance() == old(self).instance(),
            final(self).heap_id() == old(self).heap_id(),

            final(self).len() == old(self).len() + extend,

            *final(tokens) == old(tokens).remove_keys(
                set_int_range(cap as int, cap as int + extend)),
    {

        let tracked mut points_to_raw = PointsToRaw::empty(start@.provenance);
        let tracked mut new_map: Map<nat, (PointsTo<Node>, PointsToRaw, Mim::block, IsExposed)> = Map::tracked_empty();
        proof {
            tracked_swap(&mut points_to_raw, points_to_raw_r);
        }

        let mut block = start.addr();
        let Tracked(exposed) = expose_provenance(start);
        let ghost mut i: int = 0;
        let ghost tokens_snap = *tokens;
        while block < last.addr()
            invariant 0 <= i < extend,
              start as int + extend * bsize <= usize::MAX,
              block == start as int + i * bsize,
              last as int == start.addr() + (extend - 1) * bsize,
              points_to_raw.is_range(block as int, (extend - i) * bsize),
              points_to_raw.provenance() == start@.provenance,
              start@.provenance == self.data@.page_id.segment_id.provenance,
              start@.provenance == exposed.provenance(),
              INTPTR_SIZE as int <= bsize,
              block as int % INTPTR_SIZE as int == 0,
              bsize as int % INTPTR_SIZE as int == 0,
              *tokens =~= tokens_snap.remove_keys(
                  set_int_range(cap as int, cap as int + i)),

              forall |j| #![trigger tokens.dom().contains(j)]
                  #![trigger tokens.index(j)]
                cap + i <= j < cap + extend ==>
                  tokens.dom().contains(j) && tokens[j] == tokens_snap[j],
              forall |j| (self.data@.len + extend - i <= j < self.data@.len + extend)
                    <==> #[trigger] new_map.dom().contains(j),
              *old(self) == *self,
              forall |j|
                  #![trigger new_map.dom().contains(j)]
                  #![trigger new_map.index(j)]
                ((self.data@.len + extend - i <= j < self.data@.len + extend)
                    ==> { let k = self.data@.len + extend - 1 - j; {
                      &&& new_map[j].2 == tokens_snap[cap + k]
                      &&& new_map[j].0.ptr() as int == start as int + k * bsize
                      &&& new_map[j].0.ptr()@.provenance == start@.provenance
                      &&& new_map[j].0.is_init()
                      &&& new_map[j].0.value().ptr as int == start.addr() + (k+1) * bsize
                      &&& new_map[j].0.value().ptr@.provenance == start@.provenance
                      &&& new_map[j].1.is_range(
                         start.addr() + k * bsize + size_of::<Node>(),
                         bsize - size_of::<Node>())
                      &&& new_map[j].1.provenance() == start@.provenance
                      &&& new_map[j].3.provenance() == start@.provenance
                }})
        {
            proof {
                assert(i < extend);
                assert((i + 1) * bsize == i * bsize + bsize) by(nonlinear_arith);
                assert((extend - i) * bsize == (extend - (i + 1)) * bsize + bsize)
                    by(nonlinear_arith);
                assert(bsize <= (extend - i) * bsize)
                    by(nonlinear_arith) requires bsize >= 0, extend - i >= 1;
                assert(i * bsize + bsize <= extend * bsize)
                    by(nonlinear_arith) requires bsize >= 0, extend - i >= 1;
                assert(block + bsize <= start as int + extend * bsize);
                assert(size_of::<Node>() == 8);
            }

            let next: *mut Node = start.with_addr(block + bsize) as *mut Node;

            let tracked (points_to, rest) = points_to_raw.split(set_int_range(block as int, block as int + bsize as int));
            let tracked (points_to1, points_to2) = points_to.split(set_int_range(block as int, block as int + size_of::<Node>() as int));
            vstd::layout::layout_for_type_is_valid::<Node>();
            let tracked mut points_to_node = points_to1.into_typed::<Node>(block);

            let block_ptr = next.with_addr(block);
            ptr_mut_write(block_ptr, Tracked(&mut points_to_node), Node { ptr: next });

            block = next.addr();

            proof {
                points_to_raw = rest;
                let ghost old_tokens = *tokens;
                let tracked block = tokens.tracked_remove(cap + i);
                let ghost the_key = (self.data@.len + extend - 1 - i) as nat;
                new_map.tracked_insert(
                    (self.data@.len + extend - 1 - i) as nat,
                    (points_to_node, points_to2, block, exposed));
                i = i + 1;

            }
        }

        assert((i + 1) * bsize == i * bsize + bsize) by(nonlinear_arith);
        assert((extend - i) * bsize == (extend - (i + 1)) * bsize + bsize) by(nonlinear_arith);
        assert(bsize <= (extend - i) * bsize)
            by(nonlinear_arith) requires bsize >= 0, extend - i >= 1;
        assert(i * bsize + bsize <= extend * bsize)
            by(nonlinear_arith) requires bsize >= 0, extend - i >= 1;
        assert(block + bsize <= start as int + extend * bsize);
        assert(i == extend - 1) by {
            if i < extend - 1 {
                assert(i * bsize < (extend as int - 1) * bsize)
                  by(nonlinear_arith) requires bsize > 0, i < extend as int - 1;
                assert(false);
            }
        }

        let tracked (points_to, rest) = points_to_raw.split(set_int_range(block as int, block as int + bsize as int));
        let tracked (points_to1, points_to2) = points_to.split(set_int_range(block as int, block as int + size_of::<Node>() as int));
        proof { points_to_raw = rest; }
        vstd::layout::layout_for_type_is_valid::<Node>();
        let tracked mut points_to_node = points_to1.into_typed::<Node>(block);

        let block_ptr = start.with_addr(block) as *mut Node;
        ptr_mut_write(block_ptr, Tracked(&mut points_to_node), Node { ptr: self.first });

        self.first = start as *mut Node;

        proof {
            let tracked block = tokens.tracked_remove(cap + i);
            let ghost the_key = (self.data@.len + extend - 1 - i) as nat;
            new_map.tracked_insert(
                (self.data@.len + extend - 1 - i) as nat,
                (points_to_node, points_to2, block, exposed));

            let old_len = self.data@.len;
            self.data@.len = self.data@.len + extend;
            self.perms.borrow_mut().tracked_union_prefer_right(new_map);

            assert(*tokens == tokens_snap.remove_keys(
                set_int_range(cap as int, cap as int + extend)));
            assert forall |j: nat| self.valid_node(j, #[trigger] self.next_ptr(j))
            by {
                let (perm, padding, block_token, exposed) = self.perms@.index(j);
                if j < old_len {
                    assert(old(self).valid_node(j, old(self).next_ptr(j)));
                    assert(!new_map.dom().contains(j));
                    assert(self.perms@.index(j) == old(self).perms@.index(j));

                    if j > 0 {
                        assert(old(self).valid_node((j-1) as nat, old(self).next_ptr((j-1) as nat)));
                        assert(self.perms@.index((j-1) as nat) == old(self).perms@.index((j-1) as nat));
                        assert(self.perms@.index((j - 1) as nat)
                            == old(self).perms@.index((j - 1) as nat));
                    }
                    assert(old(self).next_ptr(j) == self.next_ptr(j));




                    assert(self.valid_node(j, self.next_ptr(j)));
                } else if j < self.data@.len {
                    let (perm, padding, block_token, exposed) = self.perms@.index(j);
                    let next_ptr = self.next_ptr(j);

                    assert(block_token.key().block_size == bsize);
                    assert(is_block_ptr(perm.ptr() as *mut u8, block_token.key())) by {
                        let block_id = block_token.key();
                        crate::layout::get_block_start_defn(block_id);
                        let k = old_len + extend - 1 - j;
                        crate::layout::block_start_at_diff(block_id.page_id, bsize as nat, cap as nat, (cap + k) as nat);


                    }

                    if j == old_len {
                        if j > 0 {
                            assert(old(self).valid_node((j-1) as nat, old(self).next_ptr((j-1) as nat)));
                            assert(self.perms@.index((j-1) as nat) == old(self).perms@.index((j-1) as nat));
                            assert(self.perms@.index((j - 1) as nat)
                                == old(self).perms@.index((j - 1) as nat));
                        }
                        assert(perm.value().ptr.addr() == next_ptr.addr());
                    } else {
                        assert(perm.value().ptr.addr() == next_ptr.addr());
                    }

                    assert(self.valid_node(j, self.next_ptr(j)));
                }
            }
            assert(self.wf());
        }
    }

    pub fn make_empty(&mut self) -> (llgstr: Tracked<LLGhostStateToReconvene>)
        requires old(self).wf(),
            old(self).fixed_page(),
        ensures
            llgstr_wf(llgstr@),
            llgstr@.block_size == old(self).block_size(),
            llgstr@.page_id == old(self).page_id(),
            llgstr@.instance == old(self).instance(),
            llgstr@.map.len() == old(self).len(),
            final(self).wf(),
            final(self).len() == 0,
    {
        proof {
            assert(forall |i: nat| #[trigger] self.perms@.dom().contains(i) ==>
                self.valid_node(i, self.next_ptr(i)));
        }

        self.first = core::ptr::null_mut();

        let ghost block_size = self.block_size();
        let ghost page_id = self.page_id();
        let ghost instance = self.instance();
        let tracked map;
        proof {

            let len = self.data@.len;
            self.data@.len = 0;
            let tracked mut m = Map::tracked_empty();
            tracked_swap(&mut m, self.perms.borrow_mut());

            assert forall |i: nat| (#[trigger] m.dom().contains(i) <==> 0 <= i < len)
            by {
                if 0 <= i < len {
                    assert(old(self).valid_node(i, old(self).next_ptr(i)));
                    assert(m.dom().contains(i));
                }
            }

            map = Self::convene_pt_map(m, len, instance, page_id, block_size);
        }
        Tracked(LLGhostStateToReconvene {
            map: map,
            block_size,
            page_id,
            instance,
        })
    }

    pub proof fn convene_pt_map(
        tracked m: Map<nat, (PointsTo<Node>, PointsToRaw, Mim::block, IsExposed)>,
        len: nat,
        instance: Mim::Instance,
        page_id: PageId,
        block_size: nat,
    ) -> (tracked m2: Map<nat, (PointsToRaw, Mim::block)>)
        requires
            forall |i: nat| (#[trigger] m.dom().contains(i) <==> 0 <= i < len)
              && (m.dom().contains(i) ==> ({
                  let (perm, padding, block_token, exposed) = m[i];
                    perm.is_init()
                    && block_token.key().block_size - size_of::<Node>() >= 0
                    && padding.is_range(perm.ptr() as int + size_of::<Node>(),
                        block_token.key().block_size - size_of::<Node>())
                    && padding.provenance() == page_id.segment_id.provenance
                    && padding.provenance() == exposed.provenance()
                    && block_token.instance_id() == instance.id()
                    && is_block_ptr(perm.ptr() as *mut u8, block_token.key())
                    && block_token.key().page_id == page_id
                    && block_token.key().block_size == block_size
              }))
        ensures
            m2.len() == len,
            forall |i: nat| (#[trigger] m2.dom().contains(i) <==> 0 <= i < len)
              && (m2.dom().contains(i) ==> ({
                  let (padding, block_token) = m2[i];
                    && block_token.key().block_size - size_of::<Node>() >= 0
                    && padding.is_range(
                        block_start(block_token.key()),
                        block_token.key().block_size as int)
                    && padding.provenance() == page_id.segment_id.provenance
                    && block_token.instance_id() == instance.id()
                    && block_token.key().page_id == page_id
                    && block_token.key().block_size == block_size
              })),
        decreases len,
    {
        if len == 0 {
            let tracked m = Map::tracked_empty();
            assert(m.dom() =~= Set::empty());
            assert(m.len() == 0);
            m
        } else {
            let i = (len - 1) as nat;
            let tracked mut m = m;
            assert(m.dom().contains(i));
            let tracked (mut perm, padding, block_token, exposed) = m.tracked_remove(i);
            let tracked mut m2 = Self::convene_pt_map(m, i, instance, page_id, block_size);
            crate::layout::get_block_start_from_is_block_ptr(perm.ptr() as *mut u8, block_token.key());
            perm.leak_contents();
            let tracked mut permraw = perm.into_raw();
            let tracked ptraw = permraw.join(padding);
            let mj = m2;
            m2.tracked_insert(i, (ptraw, block_token));
            assert(mj.dom().contains(i) == false);
            assert(m2.dom() =~= mj.dom().insert(i));
            assert(m2.dom().len() == mj.dom().len() + 1);
            assert(m2.len() == len);
            m2
        }
    }

    pub proof fn reconvene_state(
        tracked inst: Mim::Instance,
        tracked ts: &Mim::thread_local_state,
        tracked llgstr1: LLGhostStateToReconvene,
        tracked llgstr2: LLGhostStateToReconvene,
        n_blocks: int,
    ) -> (tracked res: (PointsToRaw, Map<BlockId, Mim::block>))
        requires
            llgstr_wf(llgstr1),
            llgstr_wf(llgstr2),
            llgstr1.block_size == llgstr2.block_size,
            llgstr1.page_id == llgstr2.page_id,
            llgstr1.instance == inst,
            llgstr2.instance == inst,
            ts.instance_id() == inst.id(),
            n_blocks >= 0,
            llgstr1.map.len() + llgstr2.map.len() == n_blocks,
            ts.value().pages.dom().contains(llgstr1.page_id),
            ts.value().pages[llgstr1.page_id].num_blocks == n_blocks,
        ensures ({ let (points_to, map) = res; {
            &&& map.len() == n_blocks
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    block_id.page_id == llgstr1.page_id)
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    map[block_id].key() == block_id)
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    map[block_id].instance_id() == inst.id())

            &&& points_to.is_range(block_start_at(llgstr1.page_id, llgstr1.block_size as int, 0), n_blocks * llgstr1.block_size)
            &&& points_to.provenance() == llgstr1.page_id.segment_id.provenance
        }})
    {
        let tracked llgstr = Self::llgstr_merge(llgstr1, llgstr2);
        let idxmap = Map::<nat, nat>::new(
            llgstr.map.dom(),
            |p| llgstr.map[p].1.key().idx);
        if exists |p| llgstr.map.dom().contains(p) && !(0 <= idxmap[p] < n_blocks) {
            let p = choose |p| llgstr.map.dom().contains(p) && !(0 <= idxmap[p] < n_blocks);
            let tracked LLGhostStateToReconvene { map: mut map, .. } = llgstr;
            assert(map.dom().contains(p));
            let tracked (_, block_p) = map.tracked_remove(p);
            assert(block_p.instance_id() == inst.id());
            inst.block_in_range(ts.key(), block_p.key(), ts, &block_p);
            assert(false);
            proof_from_false()
        } else if exists |i| 0 <= i < n_blocks && !has_idx(llgstr.map, i) {
            let i = choose |i| 0 <= i < n_blocks && !has_idx(llgstr.map, i);
            let (p, q) = crate::pigeonhole::pigeonhole_missing_idx_implies_double(idxmap, i, llgstr.map.len());
            let tracked LLGhostStateToReconvene { map: mut map, .. } = llgstr;
            let tracked (_, block_p) = map.tracked_remove(p);
            let tracked (_, block_q) = map.tracked_remove(q);
            inst.block_tokens_distinct(block_p.key(), block_q.key(), block_p, block_q);
            assert(false);
            proof_from_false()
        } else {
            let tracked LLGhostStateToReconvene { map, .. } = llgstr;
            Self::reconvene_rec(map, map.len(), llgstr.instance, llgstr.page_id, llgstr.block_size)
        }
    }

    #[verifier::external_body]
    pub proof fn llgstr_merge(
        tracked llgstr1: LLGhostStateToReconvene,
        tracked llgstr2: LLGhostStateToReconvene,
    ) -> (tracked llgstr: LLGhostStateToReconvene)
        requires
            llgstr_wf(llgstr1),
            llgstr_wf(llgstr2),
            llgstr1.block_size == llgstr2.block_size,
            llgstr1.page_id == llgstr2.page_id,
            llgstr1.instance == llgstr2.instance,
        ensures
            llgstr_wf(llgstr),
            llgstr.block_size == llgstr2.block_size,
            llgstr.page_id == llgstr2.page_id,
            llgstr.instance == llgstr2.instance,
            llgstr.map.len() == llgstr1.map.len() + llgstr2.map.len(),
    {
        unimplemented!()
    }

    pub proof fn reconvene_rec(
        tracked m: Map<nat, (PointsToRaw, Mim::block)>,
        len: nat,
        instance: Mim::Instance,
        page_id: PageId,
        block_size: nat,
    ) -> (tracked res: (PointsToRaw, Map<BlockId, Mim::block>))
        requires
            forall |j: nat| 0 <= j < len ==> #[trigger] has_idx(m, j),
            forall |i: nat|
                  (m.dom().contains(i) ==> ({
                      let (padding, block_token) = m[i];
                        && block_token.key().block_size - size_of::<Node>() >= 0
                        && padding.is_range(
                            block_start(block_token.key()),
                            block_token.key().block_size as int)
                        && padding.provenance() == page_id.segment_id.provenance
                        && block_token.instance_id() == instance.id()
                        && block_token.key().page_id == page_id
                        && block_token.key().block_size == block_size
                  })),
        ensures ({ let (points_to, map) = res; {
            &&& map.len() == len
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    block_id.page_id == page_id)
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    map[block_id].key() == block_id)
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    map[block_id].instance_id() == instance.id())
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    0 <= block_id.idx < len)
            &&& points_to.is_range(block_start_at(page_id, block_size as int, 0), (len * block_size) as int)
            &&& points_to.provenance() == page_id.segment_id.provenance
        }})
        decreases len,
    {
        if len == 0 {
            (PointsToRaw::empty(page_id.segment_id.provenance), Map::tracked_empty())
        } else {
            let j = (len - 1) as nat;
            assert(has_idx(m, j));
            let i = choose |i: nat| m.dom().contains(i) && m[i].1.key().idx == j;
            let old_m = m;
            let tracked mut m = m;
            let tracked (ptraw, block) = m.tracked_remove(i);
            assert forall |k: nat| 0 <= k < (len - 1) as nat implies has_idx(m, k) by {
                assert(has_idx(old_m, k));
                let p = choose |p: nat| old_m.dom().contains(p) && old_m[p].1.key().idx == k;
                assert(m.dom().contains(p) && m[p].1.key().idx == k);
            }
            let tracked (ptraw1, mut blocks) = Self::reconvene_rec(m, (len - 1) as nat, instance, page_id, block_size);

            let tracked ptraw2 = ptraw1.join(ptraw);
            let old_blocks = blocks;
            blocks.tracked_insert(block.key(), block);

            assert(block.key().idx == len - 1);
            assert(old_blocks.dom().contains(block.key()) == false);
            assert(blocks.dom() =~= old_blocks.dom().insert(block.key()));
            assert(blocks.dom().len() == len);

            assert((len - 1) * block_size + block_size == len * block_size) by(nonlinear_arith);
            crate::layout::get_block_start_defn(block.key());

            (ptraw2, blocks)
        }
    }
}

pub closed spec fn has_idx(map: Map<nat, (PointsToRaw, Mim::block)>, i: nat) -> bool {
    exists |p: nat| map.dom().contains(p) && map[p].1.key().idx == i
}

pub open spec fn set_nat_range(lo: nat, hi: nat) -> Set<nat> {
    Set::range(lo, hi)
}

#[verifier::external_body]
pub proof fn lemma_nat_range(lo: nat, hi: nat)
    requires
        lo <= hi,
    ensures
        set_nat_range(lo, hi).len() == hi - lo,
    decreases
        hi - lo,
{
    unimplemented!()
}

pub closed spec fn llgstr_wf(llgstr: LLGhostStateToReconvene) -> bool {
    let len = llgstr.map.len();
    let map = llgstr.map;
    let block_size = llgstr.block_size;
    let page_id = llgstr.page_id;
    let instance = llgstr.instance;

    forall |i: nat| (#[trigger] map.dom().contains(i) <==> 0 <= i < len)
        && (map.dom().contains(i) ==> ({
            let (padding, block_token) = map[i];
              && block_token.key().block_size - size_of::<Node>() >= 0
              && padding.is_range(
                  block_start(block_token.key()),
                  block_token.key().block_size as int)
              && padding.provenance() == page_id.segment_id.provenance
              && block_token.instance_id() == instance.id()
              && block_token.key().page_id == page_id
              && block_token.key().block_size == block_size
        }))
}

#[verifier::external_body]
pub proof fn bound_on_2_lists(
    tracked instance: Mim::Instance,
    tracked thread_token: &Mim::thread_local_state,
    tracked ll1: &mut LL,
    tracked ll2: &mut LL,
)
    requires thread_token.instance_id() == instance.id(),
        old(ll1).wf(), old(ll2).wf(),
        old(ll1).fixed_page(),
        old(ll2).fixed_page(),
        old(ll1).instance() == instance,
        old(ll2).instance() == instance,
        old(ll1).page_id() == old(ll2).page_id(),
        old(ll1).block_size() == old(ll2).block_size(),
        thread_token.value().pages.dom().contains(old(ll1).page_id()),
    ensures *final(ll1) == *old(ll1), *final(ll2) == *old(ll2),
        final(ll1).len() + final(ll2).len() <= thread_token.value().pages[final(ll1).page_id()].num_blocks,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn bound_on_1_lists(
    tracked instance: Mim::Instance,
    tracked thread_token: &Mim::thread_local_state,
    tracked ll1: &mut LL,
)
    requires thread_token.instance_id() == instance.id(),
        old(ll1).wf(),
        old(ll1).fixed_page(),
        old(ll1).instance() == instance,
        thread_token.value().pages.dom().contains(old(ll1).page_id()),
    ensures *final(ll1) == *old(ll1),
        final(ll1).len() <= thread_token.value().pages[final(ll1).page_id()].num_blocks,
{
    unimplemented!()
}



struct_with_invariants!{
    pub struct ThreadLLSimple {
        pub instance: Ghost<Mim::Instance>,
        pub heap_id: Ghost<HeapId>,

        pub atomic: AtomicPtr<Node, _, Tracked<LL>, _>,
    }

    pub closed spec fn wf(&self) -> bool {
        invariant
            on atomic
            with (instance, heap_id)
            is (v: *mut Node, ll: Tracked<LL>)
        {

            ll.wf()
            && ll.instance() == instance
            && !ll.fixed_page()
            && ll.heap_id() == Some(heap_id@)


            && v == ll.ptr()
        }
    }
}

impl ThreadLLSimple {
    #[inline(always)]
    pub fn empty(Ghost(instance): Ghost<Mim::Instance>, Ghost(heap_id): Ghost<HeapId>) -> (s: Self)
        ensures s.wf(),
            s.instance@ == instance,
            s.heap_id@ == heap_id,
    {
        let p: *mut Node = core::ptr::null_mut();
        Self {
            instance: Ghost(instance),
            heap_id: Ghost(heap_id),
            atomic: AtomicPtr::new(Ghost((Ghost(instance), Ghost(heap_id))), core::ptr::null_mut(), Tracked(Tracked(LL { first: p, data: Ghost(LLData { fixed_page: false, block_size: arbitrary(), page_id: arbitrary(), instance, len: 0, heap_id: Some(heap_id), }), perms: Tracked(Map::tracked_empty()), })),),
        }
    }


    #[inline(always)]
    pub fn atomic_insert_block(&self, ptr: *mut Node,
        Tracked(points_to_raw): Tracked<PointsToRaw>,
        Tracked(block_token): Tracked<Mim::block>,
    )
        requires self.wf(),
            points_to_raw.is_range(ptr as int, block_token.key().block_size as int),
            points_to_raw.provenance() == ptr@.provenance,
            block_token.instance_id() == self.instance@.id(),
            block_token.value().heap_id == Some(self.heap_id@),
            is_block_ptr(ptr as *mut u8, block_token.key()),
    {
        let tracked mut points_to_raw = points_to_raw;
        let tracked mut block_token_opt = Some(block_token);

        let Tracked(exposed) = expose_provenance(ptr);

        loop
            invariant_except_break
                block_token_opt == Some(block_token),

                self.wf(),
                points_to_raw.is_range(ptr as int, block_token.key().block_size as int),
                points_to_raw.provenance() == ptr@.provenance,
                exposed.provenance() == ptr@.provenance,

                block_token.instance_id() == self.instance@.id(),
                block_token.value().heap_id == Some(self.heap_id@),
                is_block_ptr(ptr as *mut u8, block_token.key()),
        {
            let next_ptr = atomic_with_ghost!(
                &self.atomic => load(); ghost g => { });

            proof {
                block_size_ge_word();
                block_ptr_aligned_to_word();
            }

            let (Tracked(ptr_mem0), Tracked(raw_mem0)) = LL::block_write_ptr(ptr, Tracked(points_to_raw), next_ptr);

            let cas_result = atomic_with_ghost!(
                &self.atomic => compare_exchange_weak(next_ptr, ptr);
                returning cas_result;
                ghost ghost_ll =>
            {
                let tracked mut ptr_mem = ptr_mem0;
                let tracked raw_mem = raw_mem0;

                let ghost ok = cas_result.is_ok();

                if ok {
                    let tracked block_token = block_token_opt.tracked_unwrap();
                    LL::ghost_insert_block(&mut ghost_ll, ptr, ptr_mem, raw_mem, block_token, exposed);
                    block_token_opt = None;

                    points_to_raw = PointsToRaw::empty(ptr@.provenance);
                } else {
                    ptr_mem.leak_contents();
                    points_to_raw = ptr_mem.into_raw().join(raw_mem);
                }
            });

            match cas_result {
                Result::Ok(_) => { break; }
                _ => { }
            }
        }
    }

    #[inline(always)]
    pub fn take(&self) -> (ll: LL)
        requires self.wf()
        ensures
            ll.wf(),
            ll.instance() == self.instance,
            ll.heap_id() == Some(self.heap_id@),
    {
        let res = self.atomic.load();
        if res.addr() == 0 {
            return LL::new(Ghost(arbitrary()), Ghost(arbitrary()),
                Ghost(self.instance@), Ghost(arbitrary()), Ghost(Some(self.heap_id@)));
        }

        let tracked ll: LL;
        let p = core::ptr::null_mut::<Node>();
        let res = atomic_with_ghost!(
            &self.atomic => swap(core::ptr::null_mut());
            ghost g => {
                ll = g.get();
                let mut data = ll.data@;
                data.len = 0;
                let tracked new_ll = LL {
                    first: p,
                    data: Ghost(data),
                    perms: Tracked(Map::tracked_empty()),
                };
                g = Tracked(new_ll);
            }
        );
        let new_ll = LL {
            first: res,
            data: Ghost(ll.data@),
            perms: Tracked(ll.perms.get()),
        };

        assert(forall |i: nat| ll.valid_node(i, ll.next_ptr(i))
            ==> new_ll.valid_node(i, new_ll.next_ptr(i)));

        new_ll
    }
}

pub struct BlockSizePageId {
    pub block_size: nat,
    pub page_id: PageId,
}

tokenized_state_machine!{ StuffAgree {
    fields {
        #[sharding(variable)] pub x: Option<BlockSizePageId>,
        #[sharding(variable)] pub y: Option<BlockSizePageId>,
    }
    init!{
        initialize(b: Option<BlockSizePageId>) {
            init x = b;
            init y = b;
        }
    }
    transition!{
        set(b: Option<BlockSizePageId>) {
            assert(pre.x == pre.y);
            update x = b;
            update y = b;
        }
    }
    property!{
        agree() {
            assert(pre.x == pre.y);
        }
    }
    #[invariant]
    pub spec fn inv_eq(&self) -> bool {
        self.x == self.y
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, b: Option<BlockSizePageId>) { }

    #[inductive(set)]
    fn set_inductive(pre: Self, post: Self, b: Option<BlockSizePageId>) { }
}}


struct_with_invariants!{
    pub struct ThreadLLWithDelayBits {
        pub instance: Tracked<Mim::Instance>,



        pub atomic: AtomicPtr<Node, _, (StuffAgree::y, Option<(Mim::delay, LL)>), _>,

        pub emp: Tracked<StuffAgree::x>,
        pub emp_inst: Tracked<StuffAgree::Instance>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            self.emp@.instance_id() == self.emp_inst@.id()
        }
        invariant
            on atomic
            with (instance, emp_inst)
            is (v: *mut Node, all_g: (StuffAgree::y, Option<(Mim::delay, LL)>))
        {
            let (is_emp, g_opt) = all_g;
            is_emp.instance_id() == emp_inst@.id()
            && (match (g_opt, is_emp.value()) {
                (None, None) => {
                    v == core::ptr::null_mut::<Node>()
                }
                (Some(g), Some(stuff)) => {
                    let (delay_token, ll) = g;
                    let page_id = stuff.page_id;
                    let block_size = stuff.block_size;


                    ll.wf()
                    && ll.block_size() == block_size
                    && ll.instance() == instance@
                    && ll.page_id() == page_id
                    && ll.fixed_page()
                    && ll.heap_id().is_none()


                    && delay_token.instance_id() == instance@.id()
                    && delay_token.key() == page_id


                    && v as int == ll.ptr() as int + delay_token.value().to_int()

                    && ll.ptr() as int % 4 == 0

                }
                _ => false,
            })
        }
    }
}

impl ThreadLLWithDelayBits {
    pub open spec fn is_empty(&self) -> bool {
        self.emp@.value().is_none()
    }

    pub open spec fn block_size(&self) -> nat {
        self.emp@.value().unwrap().block_size
    }

    pub open spec fn page_id(&self) -> PageId {
        self.emp@.value().unwrap().page_id
    }

    pub fn empty(Tracked(instance): Tracked<Mim::Instance>) -> (ll: ThreadLLWithDelayBits)
        ensures ll.is_empty(),
            ll.wf(),
            ll.instance == instance,
    {
        let tracked (Tracked(emp_inst), Tracked(emp_x), Tracked(emp_y)) = StuffAgree::Instance::initialize(None);
        let emp = Tracked(emp_x);
        let emp_inst = Tracked(emp_inst);
        ThreadLLWithDelayBits {
            instance: Tracked(instance),
            atomic: AtomicPtr::new(Ghost((Tracked(instance), emp_inst)), core::ptr::null_mut(), Tracked((emp_y, None))),
            emp,
            emp_inst,
        }
    }

    #[inline(always)]
    pub fn enable(&mut self,
        Ghost(block_size): Ghost<nat>,
        Ghost(page_id): Ghost<PageId>,
        Tracked(instance): Tracked<Mim::Instance>,
        Tracked(delay_token): Tracked<Mim::delay>,
    )
        requires old(self).is_empty(),
            old(self).wf(),
            old(self).instance == instance,
            delay_token.instance_id() == instance.id(),
            delay_token.key() == page_id,
            delay_token.value() == DelayState::UseDelayedFree,
        ensures
            final(self).wf(),
            !final(self).is_empty(),
            final(self).block_size() == block_size,
            final(self).page_id() == page_id,
            final(self).instance == instance,
    {
        let p = core::ptr::null_mut::<Node>();
        let ghost data = LLData {
            fixed_page: true, block_size, page_id, instance, len: 0, heap_id: None,
        };
        let tracked new_ll = LL {
            first: p,
            data: Ghost(data),
            perms: Tracked(Map::tracked_empty()),
        };
        atomic_with_ghost!(
            &self.atomic => no_op();
            update old_v -> v;
            ghost g => {
                let tracked (mut y, g_opt) = g;
                let bspi = BlockSizePageId { block_size, page_id };
                self.emp_inst.borrow().set(Some(bspi), self.emp.borrow_mut(), &mut y);
                g = (y, Some((delay_token, new_ll)));








            }
        );
    }

    #[inline(always)]
    pub fn disable(&mut self) -> (delay: Tracked<Mim::delay>)
        requires !old(self).is_empty(),
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).is_empty(),
            final(self).instance == old(self).instance,
            delay@.instance_id() == old(self).instance@.id(),
            delay@.key() == old(self).page_id(),
    {
        let mut tmp = Self::empty(Tracked(self.instance.borrow().clone()));
        core::mem::swap(&mut *self, &mut tmp);

        let ThreadLLWithDelayBits { instance: Tracked(instance),
            atomic: ato,
            emp: Tracked(emp), emp_inst: Tracked(emp_inst) } = tmp;
        let (v, Tracked(g)) = ato.into_inner();
        let tracked (y, g_opt) = g;
        proof {
            emp_inst.agree(&emp, &y);
        }
        Tracked(g_opt.tracked_unwrap().0)
    }






    #[inline(always)]
    pub fn check_is_good(
        &self,
        Tracked(thread_tok): Tracked<&Mim::thread_local_state>,
        Tracked(tok): Tracked<Mim::thread_checked_state>,
    ) -> (new_tok: Tracked<Mim::thread_checked_state>)
        requires self.wf(), !self.is_empty(),
            thread_tok.instance_id() == self.instance@.id(),
            thread_tok.value().pages.dom().contains(self.page_id()),
            thread_tok.value().pages[self.page_id()].num_blocks == 0,
            tok.instance_id() == self.instance@.id(),
            tok.key() == thread_tok.key(),
        ensures
            new_tok@.instance_id() == tok.instance_id(),
            new_tok@.key() == tok.key(),
            new_tok@.value() == (crate::tokens::ThreadCheckedState {
                pages: tok.value().pages.insert(self.page_id()),
            }),
    {
        let tracked mut tok0 = tok;
        loop
            invariant self.wf(), !self.is_empty(),
                thread_tok.instance_id() == self.instance@.id(),
                thread_tok.value().pages.dom().contains(self.page_id()),
                thread_tok.value().pages[self.page_id()].num_blocks == 0,
                tok.instance_id() == self.instance@.id(),
                tok.key() == thread_tok.key(),
                tok0 == tok,
        {
            let ghost mut the_ptr;
            let ghost mut the_delay;
            let tfree = atomic_with_ghost!(&self.atomic => load(); ghost g => {
                self.emp_inst.borrow().agree(self.emp.borrow(), &g.0);
                the_ptr = g.1.unwrap().1.ptr();
                the_delay = g.1.unwrap().0.value();

                if the_delay != DelayState::Freeing {
                    let tracked new_tok = self.instance.borrow().page_check_delay_state(
                        tok0.key(),
                        self.page_id(),
                        thread_tok,
                        &g.1.tracked_borrow().0,
                        tok0);
                    tok0 = new_tok;
                }
            });

            let old_delay = masked_ptr_delay_get_delay(tfree, Ghost(the_delay), Ghost(the_ptr));
            if unlikely(old_delay == 1) {
                atomic_yield();
            } else {
                return Tracked(tok0);
            }
        }
    }

    #[inline(always)]
    pub fn try_use_delayed_free(
        &self,
        delay: usize,
        override_never: bool,
    ) -> (b: bool)
        requires self.wf(), !self.is_empty(),
            !override_never && delay == 0,
    {
        let mut yield_count = 0;
        loop
            invariant self.wf(), !self.is_empty(), !override_never, delay == 0,
        {
            let ghost mut the_ptr;
            let ghost mut the_delay;
            let tfree = atomic_with_ghost!(&self.atomic => load(); ghost g => {
                self.emp_inst.borrow().agree(self.emp.borrow(), &g.0);
                the_ptr = g.1.unwrap().1.ptr();
                the_delay = g.1.unwrap().0.value();
            });

            let tfreex = masked_ptr_delay_set_delay(tfree, delay, Ghost(the_delay), Ghost(the_ptr));
            let old_delay = masked_ptr_delay_get_delay(tfree, Ghost(the_delay), Ghost(the_ptr));
            if unlikely(old_delay == 1) {
                if yield_count >= 4 {
                    return false;
                }
                yield_count += 1;
                atomic_yield();
            } else if delay == old_delay {
                return true;
            } else if !override_never && old_delay == 3 {
                return true;
            }

            if old_delay != 1 {
                let res = atomic_with_ghost!(
                    &self.atomic => compare_exchange_weak(tfree, tfreex);
                    returning cas_result;
                    ghost g => {
                        self.emp_inst.borrow().agree(self.emp.borrow(), &g.0);
                        if cas_result.is_ok() {
                            let tracked (emp_token, pair_opt) = g;
                            let tracked pair = pair_opt.tracked_unwrap();
                            let tracked (delay_token, ghost_ll) = pair;
                            let tracked dt = self.instance.borrow().set_use_delayed_free(self.page_id(), delay_token);
                            g = (emp_token, Some((dt, ghost_ll)));
                        }
                    }
                );

                if res.is_ok() {
                    return true;
                }
            }
        }
    }

    #[inline(always)]
    pub fn take(&self) -> (ll: LL)
        requires self.wf(), !self.is_empty(),
        ensures
            ll.wf(),
            ll.page_id() == self.page_id(),
            ll.block_size() == self.block_size(),
            ll.instance() == self.instance,
            ll.heap_id().is_none(),
            ll.fixed_page(),
    {
        let tracked ll: LL;
        let p = core::ptr::null_mut::<Node>();
        let res = atomic_with_ghost!(
            &self.atomic => fetch_and(3);
            update old_v -> new_v;
            ghost g => {
                assert(old_v@.addr & 3 == new_v@.addr);
                assert(old_v@.provenance == new_v@.provenance);

                self.emp_inst.borrow().agree(self.emp.borrow(), &g.0);
                let tracked (emp_token, pair_opt) = g;
                let tracked pair = pair_opt.tracked_unwrap();
                let tracked (delay, _ll) = pair;
                ll = _ll;
                let mut data = ll.data@;
                data.len = 0;
                let tracked new_ll = LL {
                    first: p,
                    data: Ghost(data),
                    perms: Tracked(Map::tracked_empty()),
                };
                g = (emp_token, Some((delay, new_ll)));

                let x = ll.first as usize;
                let y = delay.value().to_int() as usize;
                assert(add(x, y) & 3usize == y) by(bit_vector)
                    requires x % 4 == 0usize, 0usize <= y < 4usize;
                assert(add(x, y) & !3 == x) by(bit_vector)
                    requires x % 4 == 0usize, 0usize <= y < 4usize;

            }
        );
        let ret_ll = LL {
            first: res.with_addr(res.addr() & !3),
            data: Ghost(ll.data@),
            perms: Tracked(ll.perms.get()),
        };
        proof {
            assert forall |i: nat| ret_ll.valid_node(i, #[trigger] ret_ll.next_ptr(i))
            by {
                assert(ll.valid_node(i, ll.next_ptr(i)));
            }
        }
        ret_ll
    }
}

#[inline(always)]
pub fn masked_ptr_delay_get_is_use_delayed(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (b: bool)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0,
  ensures b <==> (expected_delay == DelayState::UseDelayedFree)
{
    v.addr() % 4 == 0
}

#[inline(always)]
pub fn masked_ptr_delay_get_delay(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (d: usize)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0,
  ensures d == expected_delay.to_int()
{
    v.addr() % 4
}

#[inline(always)]
pub fn masked_ptr_delay_get_ptr(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (ptr: *mut Node)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0
  ensures ptr.addr() == expected_ptr.addr(),
{
    proof {
        let v = v.addr();
        assert((v & !3) == sub(v, (v % 4))) by(bit_vector);
    }
    v.with_addr(v.addr() & !3)
}

#[inline(always)]
pub fn masked_ptr_delay_set_ptr(v: *mut Node, new_ptr: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (v2: *mut Node)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0,
      new_ptr as int % 4 == 0,
  ensures v2 as int == new_ptr as int + expected_delay.to_int(), v2@.provenance == new_ptr@.provenance,
{
    proof {
        let v = v as usize;
        assert((v & 3) == (v % 4)) by(bit_vector);
        let u = new_ptr as usize;
        assert(u % 4 == 0usize ==> ((v&3) | u) == add(v&3, u)) by(bit_vector);
    }
    new_ptr.with_addr((v.addr() & 3) | new_ptr.addr())
}

#[inline(always)]
pub fn masked_ptr_delay_set_freeing(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (v2: *mut Node)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0,
  ensures v2 as int == expected_ptr as int + DelayState::Freeing.to_int(), v2@.provenance == v@.provenance,
{
    proof {
        let v = v as usize;
        assert(((v & !3) | 1) == add(sub(v, (v % 4)), 1)) by(bit_vector);
    }
    v.with_addr((v.addr() & !3) | 1)
}

#[inline(always)]
pub fn masked_ptr_delay_set_delay(v: *mut Node, new_delay: usize,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (v2: *mut Node)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0, new_delay <= 3,
  ensures v2 as int == expected_ptr as int + new_delay,
      v2@.provenance == v@.provenance,
{
    proof {
        let v = v.addr();
        assert(((v & !3) | new_delay) == add(sub(v, (v % 4)), new_delay)) by(bit_vector)
            requires new_delay <= 3usize;
    }
    v.with_addr((v.addr() & !3) | new_delay)
}











#[inline(always)]
fn atomic_yield() {
    std::thread::yield_now();
}

}
}
mod bitmap {
#![allow(unused_imports)]

use verus_state_machines_macros::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::set_lib::*;

verus!{










































}
}
mod commit_mask {
use vstd::prelude::*;
use crate::config::*;
use crate::tokens::*;
use crate::layout::*;
use crate::types::*;
use vstd::contrib::set_build;
use vstd::set_lib::set_int_range;

verus!{

#[verifier::external_body]
proof fn lemma_map_distribute<S,T>(s1: Set<S>, s2: Set<S>, f: spec_fn(S) -> T)
    ensures s1.union(s2).map(f) == s1.map(f).union(s2.map(f))
{
    unimplemented!()
}

#[verifier::external_body]
proof fn lemma_map_distribute_auto<S,T>()
    ensures forall|s1: Set<S>, s2: Set<S>, f: spec_fn(S) -> T| s1.union(s2).map(f) == #[trigger] s1.map(f).union(s2.map(f))
{
    unimplemented!()
}

spec fn mod64(x: usize) -> usize { x % 64 }
spec fn div64(x: usize) -> usize { x / 64 }

#[verifier::opaque]
spec fn is_bit_set(a: usize, b: usize) -> bool {
    a & (1usize << b) == (1usize << b)
}

#[allow(unused_macros)]
macro_rules! is_bit_set {
    ($a:expr, $b:expr) => {
        $a & (1u64 << $b) == (1u64 << $b)
    }
}

#[verifier::external_body]
proof fn lemma_bitmask_to_is_bit_set(n: usize, o: usize)
    requires
        n < 64,
        o <= 64 - n,
    ensures ({
        let m = sub(1usize << n, 1) << o;
        &&& forall|j: usize| j < o           ==> !is_bit_set(m, j)
        &&& forall|j: usize| o <= j < o + n  ==> is_bit_set(m, j)
        &&& forall|j: usize| o + n <= j < 64 ==> !is_bit_set(m, j)
    })
{
    unimplemented!()
}

#[verifier::external_body]
proof fn lemma_obtain_bit_index_3_aux(a: u64, b: u64, hi: u64) -> (i: u64)
    requires
        a & b != b,
        hi <= 64,
        a >> hi == 0,
        b >> hi == 0,
    ensures
        i < hi,
        !is_bit_set!(a, i),
        is_bit_set!(b, i),
    decreases hi
{
    unimplemented!()
}

#[verifier::external_body]
proof fn lemma_obtain_bit_index_3(a: usize, b: usize) -> (i: usize)
    requires a & b != b
    ensures
        i < 64,
        !is_bit_set(a, i),
        is_bit_set(b, i),
{
    unimplemented!()
}

#[verifier::external_body]
proof fn lemma_obtain_bit_index_2(a: usize) -> (b: usize)
    requires a != !0usize
    ensures
        b < 64,
        !is_bit_set(a, b)
{
    unimplemented!()
}

#[verifier::external_body]
proof fn lemma_obtain_bit_index_1_aux(a: u64, hi: u64) -> (i: u64)
    requires
        a != 0,
        hi <= 64,
        a >> hi == 0,
    ensures
        i < hi,
        is_bit_set!(a, i),
    decreases hi
{
    unimplemented!()
}

#[verifier::external_body]
proof fn lemma_obtain_bit_index_1(a: usize) -> (b: usize)
    requires a != 0
    ensures
        b < 64,
        is_bit_set(a, b)
{
    unimplemented!()
}

#[verifier::external_body]
proof fn lemma_is_bit_set()
    ensures
        forall|j: usize| j < 64 ==> !(#[trigger] is_bit_set(0, j)),
        forall|j: usize| is_bit_set(!0usize, j),
        forall|a: usize, b: usize, j: usize| #[trigger] is_bit_set(a | b, j)  <==> is_bit_set(a, j) || is_bit_set(b, j),
        forall|a: usize, b: usize, j: usize| j < 64 ==> (#[trigger] is_bit_set(a & !b, j) <==> is_bit_set(a, j) && !is_bit_set(b, j)),
        forall|a: usize, b: usize, j: usize| #[trigger] is_bit_set(a & b, j)  <==> is_bit_set(a, j) && is_bit_set(b, j),
        forall|a: usize, b: usize, j: usize| j < 64 ==> (a & b == 0) ==> !(#[trigger] is_bit_set(a, j) && #[trigger] is_bit_set(b, j)),
{
    unimplemented!()
}

pub struct CommitMask {
    mask: [usize; 8],
}

spec fn set_8_64() -> Set<(int, usize)> {
    set_build!{ (x, y): (int, usize) | x: int in 0..8, y: usize in 0..64 }
}

impl CommitMask {
    pub closed spec fn view(&self) -> Set<int> {
        set_8_64()
            .filter(|t: (int, usize)| is_bit_set(self.mask[t.0], t.1))
            .map(|t: (int, usize)| t.0 * 64 + t.1)
    }

    #[verifier::external_body]
    proof fn lemma_view(&self)
        ensures
        (forall|i: int| self@.contains(i) ==> {
            let a = i / usize::BITS as int;
            let b = (i % usize::BITS as int) as usize;
            &&& a * 64 + b == i
            &&& is_bit_set(self.mask[a], b)
        }),
        forall|a: int, b: usize| 0 <= a < 8 && b < 64 && is_bit_set(self.mask[a], b)
            ==> #[trigger] self@.contains(a * 64 + b),
    {
        unimplemented!()
    }

    #[verifier::opaque]
    pub open spec fn bytes(&self, segment_id: SegmentId) -> Set<int> {
        let start = segment_start(segment_id);
        self@.map_flatten_by(
            |i: int| Set::range(start + i * COMMIT_SIZE, start + (i + 1) * COMMIT_SIZE),
            |addr: int| (addr - start) / COMMIT_SIZE as int,
        )
    }

    pub fn empty() -> (cm: CommitMask)
        ensures cm@ == Set::<int>::empty()
    {
        let res = CommitMask { mask: [ 0, 0, 0, 0, 0, 0, 0, 0 ] };
        proof {
            lemma_is_bit_set();
            res.lemma_view();
            assert(res@ =~= Set::<int>::empty());
        }
        res
    }

    pub fn all_set(&self, other: &CommitMask) -> (res: bool)
        ensures res == other@.subset_of(self@)
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| #![auto] 0 <= j < i ==> self.mask[j] & other.mask[j] == other.mask[j]
        {
            if self.mask[i] & other.mask[i] != other.mask[i] {
                proof {
                    self.lemma_view();
                    other.lemma_view();
                    lemma_is_bit_set();
                    let j = lemma_obtain_bit_index_3(self.mask[i as int], other.mask[i as int]);
                    assert(!self@.contains(i * 64 + j) && other@.contains(i * 64 + j));
                }
                return false;
            }
            i = i + 1;
        }
        proof {
            lemma_is_bit_set();
            self.lemma_view();
            other.lemma_view();
        }
        return true;
    }

    pub fn any_set(&self, other: &CommitMask) -> (res: bool)
        ensures res == !self@.disjoint(other@)
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| #![auto] 0 <= j < i ==> self.mask[j] & other.mask[j] == 0
        {
            if self.mask[i] & other.mask[i] != 0 {
                proof {
                    self.lemma_view();
                    other.lemma_view();
                    lemma_is_bit_set();
                    let j = lemma_obtain_bit_index_1(self.mask[i as int] & other.mask[i as int]);
                    assert(self@.contains(i * 64 + j) && other@.contains(i * 64 + j));
                }
                return true;
            }
            i += 1;
        }
        proof {
            lemma_is_bit_set();
            self.lemma_view();
            other.lemma_view();
            assert(self@.disjoint(other@));
        }
        return false;
    }

    pub fn create_intersect(&self, other: &CommitMask, res: &mut CommitMask)
        ensures final(res)@ == self@.intersect(other@)
    {
        let mut i = 0;
        while i < 8
            invariant
                forall|j: int| 0 <= j < i ==> #[trigger] res.mask[j] == self.mask[j] & other.mask[j],
        {
            res.mask[i] = self.mask[i] & other.mask[i];
            i += 1;
        }
        proof {
            self.lemma_view();
            other.lemma_view();
            res.lemma_view();
            lemma_is_bit_set();
            assert(res@ =~= self@.intersect(other@));
        }
    }

    pub fn clear(&mut self, other: &CommitMask)
        ensures final(self)@ == old(self)@.difference(other@)
    {
        let mut i = 0;
        while i < 8
            invariant
                forall|j: int| 0 <= j < i ==> #[trigger] self.mask[j] == old(self).mask[j] & !other.mask[j],
                forall|j: int| i <= j < 8 ==> #[trigger] self.mask[j] == old(self).mask[j]
        {
            let m = self.mask[i];
            self.mask[i] = m & !other.mask[i];
            i += 1;
        }
        proof {
            old(self).lemma_view();
            other.lemma_view();
            self.lemma_view();
            lemma_is_bit_set();
            assert(self@ =~= old(self)@.difference(other@));
        }
    }

    pub fn set(&mut self, other: &CommitMask)
        ensures final(self)@ == old(self)@.union(other@)
    {
        let mut i = 0;
        while i < 8
            invariant
                forall|j: int| 0 <= j < i ==> #[trigger] self.mask[j] == old(self).mask[j] | other.mask[j],
                forall|j: int| i <= j < 8 ==> #[trigger] self.mask[j] == old(self).mask[j]
        {
            let m = self.mask[i];
            self.mask[i] = m | other.mask[i];
            i += 1;
        }
        proof {
            old(self).lemma_view();
            other.lemma_view();
            self.lemma_view();
            lemma_is_bit_set();
            assert(self@ =~= old(self)@.union(other@));
        }
    }

    #[verifier::external_body]
    proof fn lemma_change_one_entry(&self, other: &Self, i: int)
        requires
            0 <= i < 8,
            self.mask[i] == 0,
            forall|j: int| 0 <= j < i ==> other.mask[j] == self.mask[j],
            forall|j: int| i < j < 8 ==> other.mask[j] == self.mask[j],
        ensures
            other@ == self@.union(Set::range(0, 64).filter(|b: usize| is_bit_set(other.mask[i], b)).map(|b: usize| 64 * i + b)),
    {
        unimplemented!()
    }

    pub fn create(&mut self, idx: usize, count: usize)
        requires
            idx + count <= COMMIT_MASK_BITS,
            old(self)@ == Set::<int>::empty(),
        ensures final(self)@ == Set::range(idx as int, idx + count),
    {
        proof {
            const_facts();
            lemma_is_bit_set();
            self.lemma_view();
            assert forall|i: int| 0 <= i < 8 implies self.mask[i] == 0 by {
                if self.mask[i] != 0 {
                    let j = lemma_obtain_bit_index_1(self.mask[i]);
                    assert(self@.contains(i * 64 + j));
                }
            }
        }
        if count == COMMIT_MASK_BITS as usize {
            self.create_full();
        } else if count == 0 {
            assert(self@ =~= Set::range(idx as int, idx + count));
        } else {
            let mut i = idx / usize::BITS as usize;
            let mut ofs: usize = idx % usize::BITS as usize;
            let mut bitcount = count;
            assert(Set::range(idx as int, idx + (count - bitcount)) =~= Set::empty());
            while bitcount > 0
                invariant
                    self@ == Set::range(idx as int, idx + (count - bitcount)),
                    ofs == if count == bitcount { idx % 64 } else { 0 },
                    bitcount > 0 ==> 64 * i + ofs == idx + (count - bitcount),
                    idx + count <= 512,
                    forall|j: int| i <= j < 8 ==> self.mask[j] == 0,
                    bitcount <= count,
            {
                assert(i < 8) by (nonlinear_arith)
                    requires
                        idx + (count - bitcount) < 512,
                        i == (idx + (count - bitcount)) / 64;
                let avail = usize::BITS as usize - ofs;
                let c = if bitcount > avail { avail } else { bitcount };
                let mask = if c >= usize::BITS as usize {
                    !0usize
                } else {
                    assert((1usize << c) > 0usize) by (bit_vector) requires c < 64usize;
                    ((1usize << c) - 1) << ofs
                };
                let old_self = Ghost(*self);
                self.mask[i] = mask;
                let oi = Ghost(i);
                let obc = Ghost(bitcount);
                let oofs = Ghost(ofs);
                bitcount -= c;
                ofs = 0;
                i += 1;
                proof {
                    assert(forall|a: u64| a << 0u64 == a) by (bit_vector);
                    let oi   = oi@;
                    let obc  = obc@;
                    let oofs = oofs@;
                    lemma_is_bit_set();
                    old_self@.lemma_change_one_entry(self, oi as int);
                    assert(self@ == old_self@@.union(Set::range(0, 64). filter(|b: usize| is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b)));
                    if oofs > 0 {
                        assert(Set::range(idx as int, idx + (count - bitcount))
                               =~= Set::range(idx + (count - obc), idx + (count - bitcount)));
                        if obc < 64 {
                            assert(mask == sub(1usize << c, 1usize) << oofs);
                            lemma_bitmask_to_is_bit_set(c, oofs);
                            assert(Set::range(idx + (count - obc), idx + (count - bitcount))
                                   =~= Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b))
                            by {
                                let s1 = Set::range(idx + (count - obc), idx + (count - bitcount));
                                let s2 = Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b);
                                assert(forall|j: usize| idx + (count - obc) <= j < idx + (count - bitcount) ==> #[trigger] is_bit_set(self.mask[oi as int], mod64(j)));
                                assert forall|x: int| s1.contains(x) implies s2.contains(x) by {
                                    let b = x % 64;
                                    assert(Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).contains((x % 64) as usize));
                                }
                            }
                            assert(Set::range(idx + (count - obc), idx + (count - bitcount))
                                   =~= Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b));
                        } else {
                            assert(mask == sub(1usize << sub(64usize, oofs), 1usize) << oofs);
                            lemma_bitmask_to_is_bit_set(sub(64, oofs), oofs);
                            assert(Set::range(idx + (count - obc), idx + (count - bitcount))
                                   =~= Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b))
                            by {
                                let s1 = Set::range(idx + (count - obc), idx + (count - bitcount));
                                let s2 = Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b);
                                assert forall|x: int| s1.contains(x) implies s2.contains(x) by {
                                    assert(Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).contains((x % 64) as usize));
                                }
                            }
                            assert(Set::range(idx + (count - obc), idx + (count - bitcount))
                                   =~= Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b));
                        }
                    } else if obc < 64 {
                        assert(Set::range(idx as int, idx + (count - bitcount))
                               =~= Set::range(idx as int, idx + (count - obc))
                                   .union(Set::range(idx + (count - obc), idx + count)));
                        assert(mask == (1usize << obc) - 1usize);
                        lemma_bitmask_to_is_bit_set(obc, 0);
                        assert(Set::range(idx + (count - obc), idx + count)
                               =~= Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b))
                        by {
                            let s1 = Set::range(idx + (count - obc), idx + count);
                            let s2 = Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b);
                            assert forall|x: int| s1.contains(x) implies s2.contains(x) by {
                                assert(Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).contains((x % 64) as usize));
                            }
                        }
                        assert(Set::range(idx + (count - obc), idx + count)
                               =~= Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b));
                    } else {
                        assert(Set::range(idx as int, idx + (count - bitcount))
                               =~= Set::range(idx as int, idx + (count - obc))
                                   .union(Set::range(idx + (count - obc), idx + (count - obc) + 64)));
                        assert(mask == !0usize);
                        let new = Set::range(idx + (count - obc), idx + (count - obc) + 64);
                        assert(Set::range(64 * oi, 64 * oi + 64)
                               =~= Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b))
                        by {
                            let s1 = Set::range(64 * oi, 64 * oi + 64);
                            let s2 = Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b);
                            assert forall|x: int| s1.contains(x) implies s2.contains(x) by {
                                assert(Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).contains((x % 64) as usize));
                            }
                        }
                        assert(Set::range(64 * oi, 64 * oi + 64)
                               =~= Set::range(0, 64).filter(|b: usize| is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b));
                    }
                }
                assert(self@ =~= Set::range(idx as int, idx + (count - bitcount)));
            }
        }
    }

    pub fn create_empty(&mut self)
        ensures final(self)@ == Set::<int>::empty(),
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| 0 <= j < i ==> self.mask[j] == 0
        {
            self.mask[i] = 0;
            i += 1;
        }
        proof {
            lemma_is_bit_set();
            self.lemma_view();
            assert(self@ =~= Set::<int>::empty());
        }
    }

    pub fn create_full(&mut self)
        ensures final(self)@ == Set::range(0, COMMIT_MASK_BITS as int),
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| 0 <= j < i ==> self.mask[j] == !0usize
        {
            self.mask[i] = !0usize;
            i += 1;
        }
        proof {
            const_facts();
            lemma_is_bit_set();
            self.lemma_view();
            let seq_set = Set::range(0, COMMIT_MASK_BITS as int);
            let bit_set = set_8_64().map(|t: (int, usize)| t.0 * 64 + t.1);
            assert forall|i: int| seq_set.contains(i) implies bit_set.contains(i) by {
                assert(set_8_64().contains((i / 64, i as usize % 64)));
            }
            assert(seq_set =~= bit_set);
            assert(self@ =~= Set::range(0, COMMIT_MASK_BITS as int));
        }
    }

    pub fn committed_size(&self, total: usize) -> usize
    {
        todo(); loop { }
    }

    pub fn next_run(&self, idx: usize) -> (res: (usize, usize))
        requires 0 <= idx < COMMIT_MASK_BITS,
        ensures ({ let (next_idx, count) = res;
            next_idx + count <= COMMIT_MASK_BITS
            && (forall |t| next_idx <= t < next_idx + count ==> self@.contains(t))
        }),
    {
        proof { const_facts(); }

        let mut i: usize = idx / usize::BITS as usize;
        let mut ofs: usize = idx % usize::BITS as usize;
        let mut mask: usize = 0;

        assert(ofs < 64) by (nonlinear_arith)
            requires ofs == idx % usize::BITS as usize;
        while i < 8
            invariant
                ofs < 64,
            ensures
                i < 8 ==> mask == self.mask[i as int] >> ofs,
                i < 8 ==> ofs < 64,
                i < 8 ==> mask & 1 == 1
        {
            mask = self.mask[i] >> ofs;
            if mask != 0 {
                while mask & 1 == 0
                    invariant
                        i < 8,
                        ofs < 64,
                        mask == self.mask[i as int] >> ofs,
                        mask != 0,
                {
                    assert((mask >> 1usize) != 0usize) by (bit_vector)
                        requires mask != 0usize, mask & 1 == 0usize;
                    assert(forall|m:u64,n:u64| #![auto] n < 64 ==> (m >> n) >> 1u64 == m >> add(n, 1u64)) by (bit_vector);
                    assert(forall|m: u64| #![auto] (m >> 63u64) >> 1u64 == 0u64) by (bit_vector);
                    mask = mask >> 1usize;
                    ofs += 1;
                }
                assert(mask & 1 == 1usize) by (bit_vector) requires mask & 1 != 0usize;
                break;
            }
            i += 1;
            ofs = 0;
        }

        if i >= COMMIT_MASK_FIELD_COUNT as usize {
            (COMMIT_MASK_BITS as usize, 0)
        } else {
            let mut count: usize = 0;
            let next_idx = i * usize::BITS as usize + ofs;
            assert((i * 64 + ofs) % 64 == ofs) by (nonlinear_arith)
                requires ofs < 64;
            loop
                invariant_except_break
                    mask & 1 == 1,
                    i < 8,
                    mask == self.mask[i as int] >> mod64((next_idx + count) as usize),
                    (next_idx + count) / 64 == i,
                invariant
                    forall|j: usize| next_idx <= j < next_idx + count ==> #[trigger] is_bit_set(self.mask[div64(j) as int], mod64(j)),
                ensures
                    next_idx + count <= 512
            {
                proof { const_facts(); }
                loop
                    invariant_except_break
                        mask & 1 == 1,
                        i < 8,
                        mask == self.mask[i as int] >> mod64((next_idx + count) as usize),
                        (next_idx + count) / 64 == i,
                    invariant
                        forall|j: usize| next_idx <= j < next_idx + count ==> #[trigger] is_bit_set(self.mask[div64(j) as int], mod64(j)),
                    ensures
                        mask & 1 == 0,
                        (next_idx + count) / 64 == if mod64((next_idx + count) as usize) == 0 { i + 1 } else { i as int }
                {
                    proof {
                        assert(forall|m: u64, b: u64| b < 64 && #[trigger] ((m >> b) & 1) == 1 ==> is_bit_set!(m, b)) by (bit_vector);
                        reveal(is_bit_set);
                        assert(forall|j: u64, m: u64| j < 64 ==> #[trigger] ((m >> j) >> 1) == m >> add(j, 1)) by (bit_vector);
                        assert(forall|m: u64, j: u64| j >= 64 ==> #[trigger] ((m >> j) & 1) != 1) by (bit_vector);
                    }
                    count += 1;
                    mask = mask >> 1usize;

                    if (mask & 1) != 1 {
                        assert(mask & 1 == 0usize) by (bit_vector) requires mask & 1 != 1usize;
                        break;
                    }
                }

                if ((next_idx + count) % usize::BITS as usize) == 0 {
                    i += 1;
                    if i >= COMMIT_MASK_FIELD_COUNT as usize {
                        break;
                    }
                    mask = self.mask[i];
                    assert(forall|m: u64| m >> 0u64 == m) by (bit_vector);
                    ofs = 0;
                }

                if (mask & 1) != 1 {
                    break;
                }
            }

            assert forall |j: usize| next_idx <= j < next_idx + count implies self@.contains(j as int) by {
                self.lemma_view();
                assert(self@.contains(div64(j) * 64 + mod64(j)));
            };

            (next_idx, count)
        }
    }

    pub fn is_empty(&self) -> (b: bool)
    ensures b == (self@ == Set::<int>::empty())
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| #![auto] 0 <= j < i ==> self.mask[j] == 0
        {
            if self.mask[i] != 0 {
                proof {
                    lemma_is_bit_set();
                    self.lemma_view();
                    let j = lemma_obtain_bit_index_1(self.mask[i as int]);
                    assert(self@.contains(i * 64 + j));
                }
                return false;
            }
            i += 1;
        }
        proof {
            lemma_is_bit_set();
            self.lemma_view();
            assert(self@ =~= Set::<int>::empty());
        }
        return true;
    }

    pub fn is_full(&self) -> (b: bool)
    ensures b == (self@ == Set::range(0, COMMIT_MASK_BITS as int))
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| #![auto] 0 <= j < i ==> self.mask[j] == !0usize
        {
            if self.mask[i] != (!0usize) {
                proof {
                    const_facts();
                    lemma_is_bit_set();
                    self.lemma_view();
                    let j = lemma_obtain_bit_index_2(self.mask[i as int]);
                    assert(!self@.contains(i * 64 + j));
                    assert(i * 64 + j < 512) by (nonlinear_arith) requires i < 8 && j < 64;
                }
                return false;
            }
            i = i + 1;
        }
        proof {
            lemma_is_bit_set();
            const_facts();
            self.lemma_view();
            assert forall |k: int| 0 <= k < COMMIT_MASK_BITS
                implies self@.contains(k)
            by {
                let t = k / 64;
                let u = (k % 64) as usize;
                assert(t * 64 + u == k);
                assert(is_bit_set(self.mask[t], u));
                assert(0 <= t < 8);
                assert(0 <= u < 64);
                assert(self@.contains(t * 64 + u));
            }
            assert(self@ =~= Set::range(0, COMMIT_MASK_BITS as int));
        }
        return true;
    }
}

#[verifier::external_body]
pub proof fn set_int_range_commit_size(sid: SegmentId, mask: CommitMask)
    requires mask@.contains(0)
    ensures set_int_range(segment_start(sid), segment_start(sid) + COMMIT_SIZE) <= mask.bytes(sid)
{
    unimplemented!()
}


}
}

mod arena {
#![allow(unused_imports)]

use verus_state_machines_macros::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::set_lib::*;

use crate::os_mem::*;
use crate::os_alloc::*;
use crate::bitmap::*;
use crate::config::*;
use crate::types::*;

verus!{

pub type ArenaId = usize;
pub type MemId = usize;

pub fn arena_alloc_aligned(
    size: usize,
    alignment: usize,
    align_offset: usize,
    request_commit: bool,
    allow_large: bool,
    req_arena_id: ArenaId,
) -> (res: (*mut u8, Tracked<MemChunk>, bool, bool, bool, bool, usize))
    requires
        alignment as int % page_size() == 0,
        size as int % page_size() == 0,
        alignment + page_size() <= usize::MAX,
        size == SEGMENT_SIZE,
    ensures ({
        let (addr, mem, commit, large, is_pinned, is_zero, mem_id) = res;
        addr as int != 0 ==> (
          mem@.wf()
            && mem@.os_exact_range(addr as int, size as int)
            && mem@.points_to.provenance() == addr@.provenance
            && addr as int + size <= usize::MAX
            && (request_commit ==> commit)
            && (commit ==> mem@.os_has_range_read_write(addr as int, size as int))
            && (commit ==> mem@.pointsto_has_range(addr as int, size as int))
            && mem@.has_pointsto_for_all_read_write()

            && (alignment != 0 ==> (addr as int + align_offset as int) % alignment as int == 0)
        )
    })
{
    let (p, is_large, Tracked(mem)) = os_alloc_aligned_offset(size, alignment, align_offset, request_commit, allow_large);
    let did_commit = request_commit;
    let is_pinned = is_large;
    let is_zero = true;
    let memid_os = 0;
    proof {
        if p as int != 0 {
            mem.os_restrict(p as int, size as int);
        }
    }
    (p, Tracked(mem), did_commit, is_large, is_pinned, is_zero, memid_os)
}












}
}
mod alloc_fast {
#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;

use crate::tokens::{Mim, BlockId, DelayState};
use crate::types::*;
use crate::layout::*;
use crate::linked_list::*;
use crate::dealloc_token::*;
use crate::alloc_generic::*;
use crate::os_mem_util::*;
use crate::config::*;
use crate::bin_sizes::*;

verus!{



#[inline]
pub fn heap_malloc(heap: HeapPtr, size: usize, Tracked(local): Tracked<&mut Local>)
    -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
        ({
            let (ptr, points_to_raw, dealloc) = t;

            points_to_raw@.is_range(ptr as int, size as int)
              && points_to_raw@.provenance() == ptr@.provenance
              && ptr == dealloc@.ptr()
              && dealloc@.inst() == final(local).inst()
              && dealloc@.size() == size
        })
{
    heap_malloc_zero(heap, size, false, Tracked(&mut *local))
}

#[inline]
pub fn heap_malloc_zero(heap: HeapPtr, size: usize, zero: bool, Tracked(local): Tracked<&mut Local>)
    -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
    ensures
        final(local).wf(),
        ({
            let (ptr, points_to_raw, dealloc) = t;
            points_to_raw@.is_range(ptr as int, size as int)
              && points_to_raw@.provenance() == ptr@.provenance
              && ptr == dealloc@.ptr()
              && dealloc@.inst() == final(local).inst()
              && dealloc@.size() == size
        }),
        common_preserves(*old(local), *final(local)),
{
    heap_malloc_zero_ex(heap, size, zero, 0, Tracked(&mut *local))
}

#[inline]
pub fn heap_malloc_zero_ex(heap: HeapPtr, size: usize, zero: bool, huge_alignment: usize, Tracked(local): Tracked<&mut Local>)
    -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
    ensures
        final(local).wf(),
        ({
            let (ptr, points_to_raw, dealloc) = t;
            points_to_raw@.is_range(ptr as int, size as int)
              && points_to_raw@.provenance() == ptr@.provenance
              && ptr == dealloc@.ptr()
              && dealloc@.inst() == final(local).instance
              && dealloc@.size() == size
        }),
        common_preserves(*old(local), *final(local)),
{
    if likely(size <= SMALL_SIZE_MAX) {
        heap_malloc_small_zero(heap, size, zero, Tracked(&mut *local))
    } else {
        malloc_generic(heap, size, zero, huge_alignment, Tracked(&mut *local))
    }
}

#[inline]
pub fn heap_get_free_small_page(heap: HeapPtr, size: usize, Tracked(local): Tracked<&Local>) -> (page: PagePtr)
    requires 0 <= size <= SMALL_SIZE_MAX,
        local.wf_main(), heap.is_in(*local), heap.wf(),
    ensures
        page.is_empty_global(*local) || ({
          &&& page.wf()
          &&& Some(page.page_id@) ==
            local.page_organization.used_dlist_headers[smallest_bin_fitting_size((size + 7) / 8 * 8)].first
        })
{
    let idx = (size + 7) / 8;
    let ptr = heap.get_pages_free_direct(Tracked(local))[idx];

    let ghost bin_idx = smallest_bin_fitting_size((size + 7) / 8 * 8);
    let ghost page_id =
        local.page_organization.used_dlist_headers[bin_idx].first.unwrap();
    proof {
        bounds_for_smallest_bin_fitting_size((size + 7) / 8 * 8);
    }
    let ptr = with_exposed_provenance(ptr.addr(), Tracked(if ptr as int == local.page_empty_global@.s.points_to.ptr() as int { local.page_empty_global.borrow().s.exposed } else { local.instance.thread_local_state_guards_page(local.thread_id, page_id, &local.thread_token).exposed }));
    let page_ptr = PagePtr { page_ptr: ptr, page_id: Ghost(page_id) };

    return page_ptr;
}

#[inline]
pub fn heap_malloc_small_zero(
    heap: HeapPtr,
    size: usize,
    zero: bool,
    Tracked(local): Tracked<&mut Local>,
) -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
        size <= SMALL_SIZE_MAX,
    ensures
        final(local).wf(),
        ({
            let (ptr, points_to_raw, dealloc) = t;
            points_to_raw@.is_range(ptr as int, size as int)
              && points_to_raw@.provenance() == ptr@.provenance
              && ptr == dealloc@.ptr()
              && dealloc@.inst() == final(local).instance
              && dealloc@.size() == size
        }),
        common_preserves(*old(local), *final(local)),
{

    let page = heap_get_free_small_page(heap, size, Tracked(&*local));

    proof {
        let bin_idx = smallest_bin_fitting_size((size + 7) / 8 * 8);
        bounds_for_smallest_bin_fitting_size((size + 7) / 8 * 8);
        local.page_organization.used_first_is_in(bin_idx);

    }

    let (p, Tracked(points_to_raw), Tracked(mim_dealloc)) = page_malloc(heap, page, size, zero, Tracked(&mut *local));

    (p, Tracked(points_to_raw), Tracked(mim_dealloc))
}

pub fn page_malloc(
    heap: HeapPtr,
    page_ptr: PagePtr,
    size: usize,
    zero: bool,

    Tracked(local): Tracked<&mut Local>,
) -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
        page_ptr.is_empty_global(*old(local)) || ({
            &&& page_ptr.wf()
            &&& page_ptr.is_used_and_primary(*old(local))
            &&& size <= old(local).page_state(page_ptr.page_id@).block_size
        })
    ensures
        final(local).wf(),
        ({
            let (ptr, points_to_raw, dealloc) = t;

            points_to_raw@.is_range(ptr as int, size as int)
              && points_to_raw@.provenance() == ptr@.provenance
              && ptr == dealloc@.ptr()
              && dealloc@.inst() == final(local).instance
              && dealloc@.size() == size
        }),
        common_preserves(*old(local), *final(local)),
{
    if unlikely(page_ptr.get_inner_ref_maybe_empty(Tracked(&*local)).free.is_empty()) {
        return malloc_generic(heap, size, zero, 0, Tracked(&mut *local));
    }

    let popped;

    page_get_mut_inner!(page_ptr, local, page_inner => {
        popped = page_inner.free.pop_block();

        page_inner.used = page_inner.used + 1;
    });

    let ptr = popped.0;

    let tracked dealloc;
    let tracked points_to_raw;
    proof {
        let tracked points_to_r = popped.1.get();
        let tracked block = popped.2.get();

        local.instance.get_block_properties(
            local.thread_token.key(),
            block.key(),
            &local.thread_token,
            &block);




        let tracked dealloc_inner = MimDeallocInner {
            mim_instance: local.instance.clone(),
            mim_block: block,
            ptr: ptr,
        };
        let tracked (dealloc0, points_to_raw0) = dealloc_inner.into_user(points_to_r, size as int);

        dealloc = dealloc0;
        points_to_raw = points_to_raw0;


        preserves_mem_chunk_good(*old(local), *local);
    }

    (ptr, Tracked(points_to_raw), Tracked(dealloc))
}


}
}
mod alloc_generic {
#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;

use crate::tokens::{Mim, BlockId, DelayState, PageId};
use crate::types::*;
use crate::config::*;
use crate::layout::*;
use crate::linked_list::*;
use crate::dealloc_token::*;
use crate::os_mem_util::*;

verus!{

pub fn malloc_generic(
    heap: HeapPtr,
    size: usize,
    zero: bool,
    huge_alignment: usize,
    Tracked(local): Tracked<&mut Local>,
) -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
    ensures
        final(local).wf(),
        ({
            let (ptr, points_to_raw, dealloc) = t;

            points_to_raw@.is_range(ptr as int, size as int)
              && points_to_raw@.provenance() == ptr@.provenance
              && ptr == dealloc@.ptr()
              && dealloc@.inst() == final(local).instance
              && dealloc@.size() == size
        }),
        common_preserves(*old(local), *final(local)),

{


    heap_delayed_free_partial(heap, Tracked(&mut *local));

    let page = crate::page::find_page(heap, size, huge_alignment, Tracked(&mut *local));
    if unlikely(page.is_null()) {
        todo();
    }

    if unlikely(zero && page.get_block_size(Tracked(&*local)) == 0) {
        todo(); loop{}
    } else {
        crate::alloc_fast::page_malloc(heap, page, size, zero, Tracked(&mut *local))
    }
}

pub fn page_free_collect(
    page_ptr: PagePtr,
    force: bool,
    Tracked(local): Tracked<&mut Local>
)
    requires
        old(local).wf(),
        page_ptr.wf(),
        page_ptr.is_used_and_primary(*old(local)),
        old(local).page_organization.pages[page_ptr.page_id@].is_used == true,
    ensures final(local).wf(),
        page_ptr.is_used_and_primary(*final(local)),
        old(local).page_organization == final(local).page_organization,
        common_preserves(*old(local), *final(local)),
        old(local).thread_token == final(local).thread_token,
{
    if force || page_ptr.get_ref(Tracked(&*local)).xthread_free.atomic.load().addr() != 0 {
        page_thread_free_collect(page_ptr, Tracked(&mut *local));
    }

    let ghost old_local = *local;

    page_get_mut_inner!(page_ptr, local, page_inner => {
        if !page_inner.local_free.is_empty() {
            if likely(page_inner.free.is_empty()) {
                let mut ll = LL::new(Ghost(page_inner.local_free.page_id()), Ghost(page_inner.local_free.fixed_page()), Ghost(page_inner.local_free.instance()), Ghost(page_inner.local_free.block_size()), Ghost(None));
                core::mem::swap(&mut ll, &mut page_inner.local_free);
                page_inner.free = ll;
            } else if force {
                page_inner.free.append(&mut page_inner.local_free);
            }
        }
    });

    proof { preserves_mem_chunk_good(old_local, *local); }
}

fn page_thread_free_collect(
    page_ptr: PagePtr,
    Tracked(local): Tracked<&mut Local>,
)
    requires
        old(local).wf(),
        page_ptr.wf(),
        page_ptr.is_used_and_primary(*old(local)),
    ensures final(local).wf(),
        final(local).pages.dom() == old(local).pages.dom(),
        page_ptr.is_used_and_primary(*final(local)),
        old(local).page_organization == final(local).page_organization,
        common_preserves(*old(local), *final(local)),
        old(local).thread_token == final(local).thread_token,
{
    let mut ll = page_ptr.get_ref(Tracked(&*local)).xthread_free.take();

    if ll.is_empty() { return; }

    page_get_mut_inner!(page_ptr, local, page_inner => {
        proof {
            bound_on_1_lists(local.instance, &local.thread_token, &mut ll);
        }
        let count = page_inner.local_free.append(&mut ll);

        proof {
            bound_on_2_lists(local.instance, &local.thread_token,
                &mut page_inner.local_free, &mut page_inner.free);
        }

        page_inner.used = page_inner.used - count;
    });

    proof { preserves_mem_chunk_good(*old(local), *local); }
}

#[verifier::spinoff_prover]
fn page_free_list_extend(
    page_ptr: PagePtr,
    bsize: usize,
    extend: usize,
    Tracked(local): Tracked<&mut Local>
)
    requires
        old(local).wf_main(),
        page_ptr.wf(),
        page_ptr.is_used_and_primary(*old(local)),

        old(local).page_capacity(page_ptr.page_id@) + extend as int
            <= old(local).page_reserved(page_ptr.page_id@),
        bsize == old(local).page_inner(page_ptr.page_id@).xblock_size,
        bsize % 8 == 0,
        extend >= 1,
    ensures
        final(local).wf_main(),
        page_ptr.is_used_and_primary(*final(local)),
        final(local).page_organization == old(local).page_organization,
        common_preserves(*old(local), *final(local)),
{
    let ghost page_id = page_ptr.page_id@;
    proof {
        const_facts();
        let reserved = local.page_reserved(page_id);
        let capacity = local.page_capacity(page_id);
        let count = local.page_organization.pages[page_id].count.unwrap();

        local.page_organization.get_count_bound(page_id);
        local.page_organization.used_offset0_has_count(page_id);
        assert(capacity * bsize <= reserved * bsize) by(nonlinear_arith)
            requires capacity <= reserved, bsize >= 0;
        assert((capacity + extend - 1) * bsize <= reserved * bsize) by(nonlinear_arith)
            requires capacity + extend - 1 <= reserved, bsize >= 0;
        assert((capacity + extend) * bsize <= reserved * bsize) by(nonlinear_arith)
            requires capacity + extend <= reserved, bsize >= 0;
    }

    let capacity = page_ptr.get_inner_ref(Tracked(&*local)).capacity;

    let pag_start = calculate_page_start(page_ptr, bsize);
    let start = calculate_page_block_at(pag_start, bsize, capacity as usize,
        Ghost(page_ptr.page_id@));
    let start = page_ptr.page_ptr.with_addr(start) as *mut u8;

    let x = capacity as usize + extend - 1;

    let last = calculate_page_block_at(pag_start, bsize, x,
        Ghost(page_ptr.page_id@));
    let last = page_ptr.page_ptr.with_addr(last) as *mut u8;

    let ghost rng_start = block_start_at(page_id, bsize as int, capacity as int);
    let ghost rng_size = extend * bsize;
    let ghost segment_id = page_id.segment_id;
    let tracked mut seg = local.segments.tracked_remove(segment_id);
    proof {
        assert(extend * bsize >= 0) by(nonlinear_arith) requires extend >= 0, bsize >= 0;
        segment_mem_has_reserved_range(*old(local), page_id, capacity + extend);
        assert(seg.mem.pointsto_has_range(rng_start, rng_size));
    }
    let tracked mut pt = seg.mem.take_points_to_range(rng_start, rng_size);
    proof { local.segments.tracked_insert(segment_id, seg); }

    let tracked mut thread_token = local.take_thread_token();
    let tracked mut checked_token = local.take_checked_token();

    let ghost mut cap_nat;
    let ghost mut extend_nat;


    proof {
        cap_nat = capacity as nat;
        extend_nat = extend as nat;

        let reserved = local.page_reserved(page_id);

        sub_distribute(reserved as int - capacity as int, extend as int, bsize as int);

        assert((reserved as int - capacity as int) * bsize as int
            >= extend as int * bsize as int) by(nonlinear_arith)
          requires (reserved as int - capacity as int) >= extend
          { }

        assert((capacity as int) * (bsize as int) + (extend as int - 1) * (bsize as int)
            == (capacity as int + extend as int - 1) * (bsize as int)) by (nonlinear_arith);

        block_start_at_diff(page_ptr.page_id@, bsize as nat, cap_nat, cap_nat + extend_nat);

        let page_id = page_ptr.page_id@;
        let block_size = bsize as nat;
        let ts = thread_token.value();
        assert forall |i: nat| cap_nat <= i < cap_nat + extend_nat
            implies Mim::State::okay_to_add_block(ts, page_id, i, block_size)
        by {
            let slice_id = PageId {
                segment_id: page_id.segment_id,
                idx: BlockId::get_slice_idx(page_id, i, block_size),
            };
            start_offset_le_slice_size(bsize as int);
            assert(i * block_size >= 0) by(nonlinear_arith)
                requires i >= 0, block_size >= 0;
            let reserved = local.page_reserved(page_id);
            let capacity = local.page_capacity(page_id);
            assert(i * block_size < reserved * block_size) by(nonlinear_arith)
                requires i < reserved, block_size > 0;
            let count = local.page_organization.pages[page_id].count.unwrap();

            local.page_organization.get_count_bound(page_id);
            local.page_organization.get_offset_for_something_in_used_range(page_id, slice_id);

        }
    }

    let tracked (Tracked(_thread_token), Tracked(block_tokens), Ghost(_s), Tracked(_checked_token)) = local.instance.page_mk_block_tokens(
        local.thread_id,
        page_ptr.page_id@,
        cap_nat as nat,
        cap_nat as nat + extend_nat as nat,
        bsize as nat,
        thread_token,
        checked_token,
    );
    let tracked block_tokens = block_tokens.into_map();
    proof { local.thread_token = _thread_token; local.checked_token = _checked_token; }
    let tracked mut block_tokens = Map::tracked_map_keys(block_tokens,
        Map::<int, BlockId>::new(
          Set::range(cap_nat as int, cap_nat as int + extend_nat),
          |i: int| BlockId {
              page_id: page_ptr.page_id@,
              idx: i as nat,
              slice_idx: BlockId::get_slice_idx(page_ptr.page_id@, i as nat, bsize as nat),
              block_size: bsize as nat
          }
        ));


    proof {
        assert(start.addr() % 8 == 0) by {
            block_ptr_aligned_to_word();
            crate::linked_list::size_of_node();
            segment_start_mult8(page_id.segment_id);
            start_offset_le_slice_size(bsize as int);
            assert(page_start(page_id) % 8 == 0);
            assert(start_offset(bsize as int) % 8 == 0);
            assert(pag_start % 8 == 0);
            mod_mul(capacity as int, bsize as int, 8);
        }
        assert forall |i: int| cap_nat <= i < cap_nat + extend_nat
            implies is_block_ptr1(
                block_start(block_tokens.index(i).key()),
                block_tokens.index(i).key(),
            )
        by {
            let block_id = block_tokens.index(i).key();
            let block_size = bsize as int;
            reveal(is_block_ptr1);
            get_block_start_defn(block_id);
            crate::linked_list::size_of_node();
            start_offset_le_slice_size(block_size);
            let reserved = local.page_reserved(page_id);
            let capacity = local.page_capacity(page_id);
            assert(i * block_size <= reserved * block_size) by(nonlinear_arith)
                requires i <= reserved, block_size >= 0;

        }
    }

    page_get_mut_inner!(page_ptr, local, page_inner => {
        page_inner.free.prepend_contiguous_blocks(
            start, last, bsize,
            Ghost(cap_nat), Ghost(extend_nat),
            Tracked(&mut pt),
            Tracked(&mut block_tokens));

        page_inner.capacity = page_inner.capacity + extend as u16;
    });


    proof {

        block_start_at_diff(page_id, bsize as nat, capacity as nat, (capacity + extend) as nat);

        preserves_mem_chunk_good_on_transfer_to_capacity(*old(local), *local, page_id);
        assert(local.mem_chunk_good(segment_id));
        preserves_mem_chunk_good_except(*old(local), *local, segment_id);

        assert(local.wf_main());
    }
}

const MIN_EXTEND: usize = 4;
const MAX_EXTEND_SIZE: u32 = 4096;

pub fn page_extend_free(
    page_ptr: PagePtr,
    Tracked(local): Tracked<&mut Local>,
)
    requires
        old(local).wf_main(),
        page_ptr.wf(),
        old(local).is_used_primary(page_ptr.page_id@),
        old(local).pages[page_ptr.page_id@].inner.value().xblock_size % 8 == 0,
    ensures
        final(local).wf_main(),
        final(local).is_used_primary(page_ptr.page_id@),
        final(local).page_organization == old(local).page_organization,
        common_preserves(*old(local), *final(local)),
{
    let page_inner = page_ptr.get_inner_ref(Tracked(&*local));


    let reserved = page_inner.reserved;
    let capacity = page_inner.capacity;

    if capacity >= reserved { return; }

    let bsize: usize = page_ptr.get_inner_ref(Tracked(&*local)).xblock_size as usize;



    let mut max_extend: usize = if bsize >= MAX_EXTEND_SIZE as usize {
        MIN_EXTEND
    } else {
        (MAX_EXTEND_SIZE / bsize as u32) as usize
    };
    if max_extend < MIN_EXTEND {
        max_extend = MIN_EXTEND;
    }

    let mut extend: usize = (reserved - capacity) as usize;
    if extend > max_extend {
        extend = max_extend;
    }

    page_free_list_extend(page_ptr, bsize, extend, Tracked(local));

}

fn heap_delayed_free_partial(heap: HeapPtr, Tracked(local): Tracked<&mut Local>) -> (b: bool)
    requires
        old(local).wf(),
        heap.wf(), heap.is_in(*old(local)),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
{
    let mut ll = heap.get_ref(Tracked(&*local)).thread_delayed_free.take();
    let mut all_freed = true;
    while !ll.is_empty()
        invariant
            local.wf(),
            heap.wf(), heap.is_in(*local),
            ll.wf(), common_preserves(*old(local), *local),
            ll.instance().id() == local.instance.id(),
            ll.heap_id() == Some(local.thread_token.value().heap_id)
    {
        let (ptr, Tracked(perm), Tracked(block)) = ll.pop_block();
        proof {
            local.instance.block_in_heap_has_valid_page(
                local.thread_token.key(), block.key(),
                &local.thread_token, &block);
            local.instance.get_block_properties(
                local.thread_token.key(), block.key(),
                &local.thread_token, &block);
        }
        let tracked dealloc_inner = MimDeallocInner {
            mim_instance: local.instance.clone(),
            mim_block: block,
            ptr: ptr,
        };
        let (success, Tracked(p_opt), Tracked(d_opt)) =
                crate::free::free_delayed_block(ptr, Tracked(perm),
                    Tracked(dealloc_inner), Tracked(&mut *local));
        if !success {
            all_freed = false;
            let tracked perm = p_opt.tracked_unwrap();
            let tracked dealloc = d_opt.tracked_unwrap();
            let tracked block = dealloc.mim_block;

            heap.get_ref(Tracked(&*local)).thread_delayed_free
                .atomic_insert_block(ptr as *mut Node, Tracked(perm), Tracked(block));
        }
    }
    return all_freed;
}

}
}
mod free {
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;

use core::intrinsics::{likely, unlikely};

use crate::tokens::{Mim, BlockId, DelayState};
use crate::types::*;
use crate::layout::*;
use crate::linked_list::*;
use crate::dealloc_token::*;

verus!{


pub fn free(ptr: *mut u8, Tracked(user_perm): Tracked<PointsToRaw>, Tracked(user_dealloc): Tracked<Option<MimDealloc>>, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        ptr.addr() != 0 ==> user_dealloc.is_some(),
        ptr.addr() != 0 ==> user_perm.is_range(ptr as int, user_dealloc.unwrap().size()),
        ptr.addr() != 0 ==> user_perm.provenance() == ptr@.provenance,
        ptr.addr() != 0 ==> ptr == user_dealloc.unwrap().ptr(),
        ptr.addr() != 0 ==> old(local).inst() == user_dealloc.unwrap().inst()
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
{
    if ptr.addr() == 0 {
        return;
    }

    let tracked user_dealloc = user_dealloc.tracked_unwrap();

    let tracked dealloc;
    let tracked perm;
    proof {
        let tracked (x, y) = user_dealloc.into_internal(user_perm);
        dealloc = x;
        perm = y;
    }


    let segment_ptr = calculate_segment_ptr_from_block(ptr, Ghost(dealloc.block_id()));

    let tracked segment_shared_access: &SegmentSharedAccess =
        dealloc.mim_instance.alloc_guards_segment_shared_access(
            dealloc.block_id(),
            &dealloc.mim_block,
        );

    let segment: &SegmentHeader = ptr_ref(segment_ptr,
        Tracked(&segment_shared_access.points_to));


    let segment_thread_id_u64 = atomic_with_ghost!(
        &segment.thread_id => load();
        returning thread_id_u64;
        ghost g => {
            if g.value() == local.thread_id {
                local.instance.block_on_the_local_thread(
                    local.thread_token.key(),
                    dealloc.mim_block.key(),
                    &local.thread_token,
                    &dealloc.mim_block,
                    &g,
                    );
            }
        }
    );

    let (thread_id, Tracked(is_thread)) = crate::thread::thread_id();
    proof { local.is_thread.agrees(is_thread); }
    let is_local = thread_id.thread_id == segment_thread_id_u64;


    let slice_page_ptr = calculate_slice_page_ptr_from_block(ptr, segment_ptr, Ghost(dealloc.block_id()));

    let tracked page_slice_shared_access: &PageSharedAccess =
        dealloc.mim_instance.alloc_guards_page_slice_shared_access(
            dealloc.block_id(),
            &dealloc.mim_block,
        );

    let slice_page: &Page = ptr_ref(slice_page_ptr,
        Tracked(&page_slice_shared_access.points_to));


    let offset = slice_page.offset;

    let page_ptr = calculate_page_ptr_subtract_offset(
        slice_page_ptr,
        offset,
        Ghost(dealloc.block_id().page_id_for_slice()),
        Ghost(dealloc.block_id().page_id),
    );



    let ghost page_id = dealloc.block_id().page_id;
    let page = PagePtr {
        page_ptr,
        page_id: Ghost(page_id),
    };
    assert(page_ptr.addr() != 0) by { is_page_ptr_nonzero(page_ptr, page_id); }


    if likely(is_local) {

        if likely(page.get_inner_ref(Tracked(&*local)).not_full_nor_aligned()) {
            let used;
            page_get_mut_inner!(page, local, page_inner => {
                let tracked mim_block = dealloc.mim_block;


                page_inner.free.insert_block(ptr, Tracked(perm), Tracked(mim_block));

                proof {
                    bound_on_2_lists(local.instance, &local.thread_token, &mut page_inner.free, &mut page_inner.local_free);
                }

                used = page_inner.used - 1;
                page_inner.used = used;
            });

            proof {
                crate::os_mem_util::preserves_mem_chunk_good(*old(local), *local);
            }

            if unlikely(used == 0) {
                crate::page::page_retire(page, Tracked(&mut *local));
            }
        } else {
            free_generic(segment_ptr, page, true, ptr,
                Tracked(perm), Tracked(dealloc), Tracked(&mut *local));
        }
    } else {
        free_generic(segment_ptr, page, false, ptr,
            Tracked(perm), Tracked(dealloc), Tracked(&mut *local));
    }
}

fn free_generic(segment: *mut SegmentHeader, page: PagePtr, is_local: bool, p: *mut u8, Tracked(perm): Tracked<PointsToRaw>, Tracked(dealloc): Tracked<MimDeallocInner>, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        dealloc.wf(),
        perm.is_range(p as int, dealloc.block_id().block_size as int),
        perm.provenance() == p@.provenance,
        p == dealloc.ptr,
        old(local).instance == dealloc.mim_instance,
        page.wf(),
        is_local ==> page.is_in(*old(local)),
        is_local ==> old(local).is_used_primary(page.page_id@),
        is_local ==> old(local).thread_token.value().pages[page.page_id@].block_size == dealloc.block_id().block_size,
        page.page_id@ == dealloc.block_id().page_id,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
{

    free_block(page, is_local, p, Tracked(perm), Tracked(dealloc), Tracked(&mut *local));
}

fn free_block(page: PagePtr, is_local: bool, ptr: *mut u8, Tracked(perm): Tracked<PointsToRaw>, Tracked(dealloc): Tracked<MimDeallocInner>, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        dealloc.wf(),
        perm.is_range(ptr as int, dealloc.block_id().block_size as int),
        perm.provenance() == ptr@.provenance,
        ptr == dealloc.ptr,
        old(local).instance == dealloc.mim_instance,
        page.wf(),
        is_local ==> page.is_in(*old(local)),
        is_local ==> old(local).is_used_primary(page.page_id@),
        is_local ==> old(local).thread_token.value().pages[page.page_id@].block_size == dealloc.block_id().block_size,
        page.page_id@ == dealloc.block_id().page_id,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
{
    if likely(is_local) {
        let used;
        page_get_mut_inner!(page, local, page_inner => {
            let tracked mim_block = dealloc.mim_block;


            page_inner.free.insert_block(ptr, Tracked(perm), Tracked(mim_block));

            proof {
                bound_on_2_lists(local.instance, &local.thread_token, &mut page_inner.free, &mut page_inner.local_free);
            }

            used = page_inner.used - 1;
            page_inner.used = used;
        });

        proof {
            crate::os_mem_util::preserves_mem_chunk_good(*old(local), *local);
        }

        if unlikely(used == 0) {
            crate::page::page_retire(page, Tracked(&mut *local));
        } else if unlikely(page.get_inner_ref(Tracked(&*local)).get_in_full()) {
            crate::page::page_unfull(page, Tracked(&mut *local));
        }
    } else {
        free_block_mt(page, ptr, Tracked(perm), Tracked(dealloc), Tracked(&mut *local));
    }
}

fn free_block_mt(page: PagePtr, ptr: *mut u8, Tracked(perm): Tracked<PointsToRaw>, Tracked(dealloc): Tracked<MimDeallocInner>, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        dealloc.wf(),
        perm.is_range(ptr as int, dealloc.block_id().block_size as int),
        perm.provenance() == ptr@.provenance,
        ptr == dealloc.ptr,
        old(local).instance == dealloc.mim_instance,
        page.page_id@ == dealloc.block_id().page_id,
        page.wf(),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
{


    let tracked mut perm = perm;
    let tracked mut delay_actor_token_opt: Option<Mim::delay_actor> = None;
    let tracked MimDeallocInner { mim_block, mim_instance, .. } = dealloc;
    let tracked mut mim_block_opt = Some(mim_block);
    let ptr = ptr as *mut Node;
    let mut use_delayed;

    loop
        invariant
            dealloc.wf(),
            mim_block_opt == Some(dealloc.mim_block),
            mim_instance == dealloc.mim_instance,
            mim_instance == local.instance,
            perm.is_range(ptr as int, dealloc.block_id().block_size as int),
            perm.provenance() == ptr@.provenance,
            ptr as *mut u8 == dealloc.ptr,
            is_page_ptr(page.page_ptr, dealloc.block_id().page_id),
            local.wf(),
            common_preserves(*old(local), *local),

    {
        let tracked page_shared_access: &PageSharedAccess =
            mim_instance.alloc_guards_page_shared_access(
                dealloc.block_id(), mim_block_opt.tracked_borrow());
        let pag: &Page = ptr_ref(page.page_ptr, Tracked(&page_shared_access.points_to));


        let ghost mut next_ptr;
        let ghost mut delay;
        let mask = atomic_with_ghost!(&pag.xthread_free.atomic => load(); ghost g => {
            pag.xthread_free.emp_inst.borrow().agree(pag.xthread_free.emp.borrow(), &g.0);
            next_ptr = g.1.unwrap().1.ptr();
            delay = g.1.unwrap().0.value();
        });

        use_delayed = masked_ptr_delay_get_is_use_delayed(mask, Ghost(delay), Ghost(next_ptr));
        let mask1;

        let tracked mut ptr_mem = None;
        let tracked mut raw_mem = None;
        let tracked mut exposed = None;

        if unlikely(use_delayed) {
            mask1 = masked_ptr_delay_set_freeing(mask, Ghost(delay), Ghost(next_ptr));
        } else {
            proof {
                block_size_ge_word();
                block_ptr_aligned_to_word();
                is_block_ptr_mult4(ptr as *mut u8, dealloc.block_id());
            }

            let (ptr_mem0, raw_mem0) = LL::block_write_ptr(
                ptr,
                Tracked(perm),
                masked_ptr_delay_get_ptr(mask, Ghost(delay), Ghost(next_ptr)));

            let Tracked(exposed0) = expose_provenance(ptr);

            proof {
                perm = PointsToRaw::empty(ptr@.provenance);
                ptr_mem = Some(ptr_mem0.get());
                raw_mem = Some(raw_mem0.get());
                exposed = Some(exposed0);
            }


            mask1 = masked_ptr_delay_set_ptr(mask, ptr, Ghost(delay), Ghost(next_ptr));
        }


        let cas_result = atomic_with_ghost!(
            &pag.xthread_free.atomic => compare_exchange_weak(mask, mask1);
            update v_old -> v_new;
            returning cas_result;
            ghost g =>
        {
            pag.xthread_free.emp_inst.borrow().agree(pag.xthread_free.emp.borrow(), &g.0);
            let tracked (emp_token, pair_opt) = g;
            let tracked pair = pair_opt.tracked_unwrap();
            let tracked (mut delay_token, mut ghost_ll) = pair;

            let ghost ok = cas_result.is_ok();
            if use_delayed {
                if ok {
                    let tracked (Tracked(delay_token0), Tracked(delay_actor_token)) =
                        mim_instance.delay_enter_freeing(
                            dealloc.block_id().page_id,
                            dealloc.block_id(),
                            mim_block_opt.tracked_borrow(),
                            delay_token);
                    delay_token = delay_token0;
                    delay_actor_token_opt = Some(delay_actor_token);
                } else {
                }
            } else {
                if ok {
                    let tracked mim_block = mim_block_opt.tracked_unwrap();
                    LL::ghost_insert_block(mut_ref_tracked(&mut ghost_ll), ptr, ptr_mem.tracked_unwrap(),
                        raw_mem.tracked_unwrap(), mim_block, exposed.tracked_unwrap());

                    mim_block_opt = None;

                    is_block_ptr_mult4(ptr as *mut u8, dealloc.block_id());
                } else {

                    let tracked mut ptr_mem = ptr_mem.tracked_unwrap();
                    let tracked raw_mem = raw_mem.tracked_unwrap();
                    ptr_mem.leak_contents();
                    perm = ptr_mem.into_raw().join(raw_mem);
                }
            }

            g = (emp_token, Some((delay_token, ghost_ll)));

        });

        match cas_result {
            Result::Err(_) => { }
            Result::Ok(_) => {
                if unlikely(use_delayed) {

                    let tracked mut delay_actor_token;
                    let ghost mut heap_id;

                    let tracked page_shared_access: &PageSharedAccess =
                        mim_instance.alloc_guards_page_shared_access(
                            dealloc.block_id(), mim_block_opt.tracked_borrow());
                    let pag: &Page = ptr_ref(page.page_ptr, Tracked(&page_shared_access.points_to));

                    let heap_ptr = atomic_with_ghost!(
                        &pag.xheap.atomic => load();
                        ghost g =>
                    {
                        delay_actor_token = delay_actor_token_opt.tracked_unwrap();
                        pag.xheap.emp_inst.borrow().agree(pag.xheap.emp.borrow(), &g.0);
                        let tracked (Tracked(tok), _) = mim_instance.delay_lookup_heap(
                            dealloc.block_id(),
                            &local.my_inst,
                            mim_block_opt.tracked_borrow(),
                            g.1.tracked_borrow(),
                            delay_actor_token);
                        delay_actor_token = tok;
                        heap_id = g.1.unwrap().value();
                    });

                    let tracked heap_shared_access: &HeapSharedAccess;
                    proof {
                        heap_shared_access = mim_instance.delay_guards_heap_shared_access(
                            dealloc.block_id().page_id,
                            &delay_actor_token,
                        );
                    }
                    let heap: &Heap = ptr_ref(heap_ptr,
                        Tracked(&heap_shared_access.points_to));

                    let tracked mim_block = mim_block_opt.tracked_unwrap();
                    let tracked mim_block = local.instance.block_set_heap_id(mim_block.key(),
                        mim_block, &delay_actor_token);
                    heap.thread_delayed_free.atomic_insert_block(ptr, Tracked(perm), Tracked(mim_block));

                    let tracked page_shared_access: &PageSharedAccess =
                        mim_instance.delay_guards_page_shared_access(
                            dealloc.block_id().page_id, &delay_actor_token);
                    let pag: &Page = ptr_ref(page.page_ptr, Tracked(&page_shared_access.points_to));


                    atomic_with_ghost!(
                        &pag.xthread_free.atomic => fetch_xor(3);
                        update v_old -> v_new;
                        ghost g => {
                            pag.xthread_free.emp_inst.borrow().agree(pag.xthread_free.emp.borrow(), &g.0);
                            let tracked (emp_token, pair_opt) = g;
                            let tracked pair = pair_opt.tracked_unwrap();
                            let tracked (mut delay_token, mut ll) = pair;

                            delay_token = mim_instance.delay_leave_freeing(dealloc.block_id().page_id,
                                delay_token, delay_actor_token);


                            g = (emp_token, Some((delay_token, ll)));

                            let v_old = v_old as usize;

                            assert(v_old % 4 == 1usize ==> (v_old ^ 3) == add(v_old, 1))
                              by (bit_vector);
                        }
                    );
                }
                return;
            }
        }
    }
}

pub fn free_delayed_block(ptr: *mut u8,
    Tracked(perm): Tracked<PointsToRaw>,
    Tracked(dealloc): Tracked<MimDeallocInner>,
    Tracked(local): Tracked<&mut Local>,
) -> (res: (bool, Tracked<Option<PointsToRaw>>, Tracked<Option<MimDeallocInner>>))
    requires old(local).wf(),
        dealloc.wf(),
        perm.is_range(ptr as int, dealloc.block_id().block_size as int),
        perm.provenance() == ptr@.provenance,
        ptr == dealloc.ptr,
        old(local).instance == dealloc.mim_instance,
        dealloc.mim_block.value().heap_id == Some(old(local).thread_token.value().heap_id),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        !res.0 ==> res.1@ == Some(perm),
        !res.0 ==> res.2@ == Some(dealloc),
{
    let ghost block_id = dealloc.mim_block.key();
    let segment = crate::layout::calculate_segment_ptr_from_block(ptr, Ghost(block_id));

    let slice_page_ptr = crate::layout::calculate_slice_page_ptr_from_block(ptr, segment, Ghost(block_id));
    let tracked page_slice_shared_access: &PageSharedAccess =
        local.instance.alloc_guards_page_slice_shared_access(
            block_id,
            &dealloc.mim_block,
        );
    let slice_page: &Page = ptr_ref(slice_page_ptr,
        Tracked(&page_slice_shared_access.points_to));
    let offset = slice_page.offset;
    let page_ptr = crate::layout::calculate_page_ptr_subtract_offset(
        slice_page_ptr,
        offset,
        Ghost(block_id.page_id_for_slice()),
        Ghost(block_id.page_id),
    );
    let ghost page_id = dealloc.block_id().page_id;
    assert(page_ptr as int != 0) by { is_page_ptr_nonzero(page_ptr, page_id); }

    let page = PagePtr { page_ptr: page_ptr, page_id: Ghost(block_id.page_id) };
    proof {
        local.instance.block_in_heap_has_valid_page(
            local.thread_token.key(),
            dealloc.mim_block.key(),
            &local.thread_token,
            &dealloc.mim_block);
    }

    if !crate::page::page_try_use_delayed_free(page, 0, false, Tracked(&*local)) {
        return (false, Tracked(Some(perm)), Tracked(Some(dealloc)));
    }

    crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));


    crate::free::free_block(page, true, ptr,
        Tracked(perm), Tracked(dealloc), Tracked(&mut *local));

    return (true, Tracked(None), Tracked(None));
}

}
}
mod realloc {
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;

use core::intrinsics::{likely, unlikely};

use crate::tokens::{Mim, BlockId, DelayState};
use crate::types::*;
use crate::layout::*;
use crate::linked_list::*;
use crate::dealloc_token::*;

verus!{














}
}
mod segment {
#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;
use vstd::pervasive::*;
use vstd::set_lib::*;
use vstd::cell::pcell::*;
use vstd::atomic_ghost::*;

use crate::tokens::{Mim, BlockId, DelayState, PageId, PageState, SegmentState, ThreadId};
use crate::types::*;
use crate::layout::*;
use crate::bin_sizes::*;
use crate::config::*;
use crate::page_organization::*;
use crate::linked_list::LL;
use crate::arena::*;
use crate::commit_mask::CommitMask;
use crate::os_mem::MemChunk;
use crate::os_mem_util::*;
use crate::commit_segment::*;
use crate::linked_list::ThreadLLWithDelayBits;
use crate::init::current_thread_count;

verus!{

pub open spec fn good_count_for_block_size(block_size: int, count: int) -> bool {
    count * SLICE_SIZE < block_size * 0x10000
}

pub fn segment_page_alloc(
    heap: HeapPtr,
    block_size: usize,
    page_alignment: usize,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (page_ptr: PagePtr)
    requires
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        heap.wf(),
        heap.is_in(*old(local)),
        2 <= block_size,
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        (page_ptr.page_ptr.addr() != 0 ==>
            page_ptr.wf()
            && page_ptr.is_in(*final(local))
            && final(local).page_organization.popped == Popped::Ready(page_ptr.page_id@, true)
            && page_init_is_committed(page_ptr.page_id@, *final(local))
            && good_count_for_block_size(block_size as int,
                    final(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int)
        ),
        page_ptr.page_ptr.addr() == 0 ==> final(local).wf(),
{
    proof { const_facts(); }

    if unlikely(page_alignment > ALIGNMENT_MAX as usize) {
        todo();
    }

    if block_size <= SMALL_OBJ_SIZE_MAX as usize {
        segments_page_alloc(heap, block_size, block_size, tld, Tracked(&mut *local))
    } else if block_size <= MEDIUM_OBJ_SIZE_MAX as usize {
        segments_page_alloc(heap, MEDIUM_PAGE_SIZE as usize, block_size, tld, Tracked(&mut *local))
    } else if block_size <= LARGE_OBJ_SIZE_MAX as usize {
        segments_page_alloc(heap, block_size, block_size, tld, Tracked(&mut *local))
    } else {
        todo(); loop{}
    }
}

fn segments_page_alloc(
    heap: HeapPtr,
    required: usize,
    block_size: usize,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (page_ptr: PagePtr)
    requires
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        heap.wf(),
        heap.is_in(*old(local)),
        2 <= block_size <= LARGE_OBJ_SIZE_MAX,
        1 <= required <= LARGE_OBJ_SIZE_MAX,
        (if block_size <= SMALL_OBJ_SIZE_MAX {
            required == block_size
        } else if block_size <= MEDIUM_OBJ_SIZE_MAX {
            required == MEDIUM_PAGE_SIZE
        } else {
            required == block_size
        }),
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        (page_ptr.page_ptr.addr() != 0 ==>
            page_ptr.wf()
            && page_ptr.is_in(*final(local))
            && final(local).page_organization.popped == Popped::Ready(page_ptr.page_id@, true)
            && page_init_is_committed(page_ptr.page_id@, *final(local))
            && good_count_for_block_size(block_size as int,
                    final(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int)
        ),
        page_ptr.page_ptr.addr() == 0 ==>
            final(local).wf(),

{
    proof { const_facts(); }

    let alignment: usize = if required > MEDIUM_PAGE_SIZE as usize
        { MEDIUM_PAGE_SIZE as usize } else { SLICE_SIZE as usize };
    let page_size = align_up(required, alignment);
    let slices_needed = page_size / SLICE_SIZE as usize;

    proof {
        assert(good_count_for_block_size(block_size as int, slices_needed as int));
    }

    proof {
        assert(page_size == slices_needed * SLICE_SIZE as nat) by {
            assert(MEDIUM_PAGE_SIZE as int % SLICE_SIZE as int == 0);
            assert(SLICE_SIZE as int % SLICE_SIZE as int == 0);
            assert(alignment as int % SLICE_SIZE as int == 0);
            assert(page_size as int % alignment as int == 0);
            mod_trans(page_size as int, alignment as int, SLICE_SIZE as int);
            assert(page_size as int % SLICE_SIZE as int == 0);
        }
        assert(1 <= slices_needed <= SLICES_PER_SEGMENT);
    }

    let page_ptr = segments_page_find_and_allocate(slices_needed, tld,
          Tracked(&mut *local), Ghost(block_size as nat));
    if page_ptr.page_ptr.addr() == 0 {
        let roa = segment_reclaim_or_alloc(heap, slices_needed, block_size, tld,
            Tracked(&mut *local));
        if roa.segment_ptr.addr() == 0 {
            return PagePtr::null();
        } else {
            return segments_page_alloc(heap, required, block_size, tld, Tracked(&mut *local));
        }
    } else {
        return page_ptr;
    }
}

fn segment_reclaim_or_alloc(
    heap: HeapPtr,
    needed_slices: usize,
    block_size: usize,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (segment_ptr: SegmentPtr)
    requires
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        heap.wf(),
        heap.is_in(*old(local)),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),

{

    let arena_id = heap.get_arena_id(Tracked(&*local));
    segment_alloc(0, 0, arena_id, tld, Tracked(&mut *local))
}

#[verifier::spinoff_prover]
fn segments_page_find_and_allocate(
    slice_count0: usize,
    tld_ptr: TldPtr,
    Tracked(local): Tracked<&mut Local>,
    Ghost(block_size): Ghost<nat>,
) -> (page_ptr: PagePtr)
    requires
        old(local).wf(),
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        1 <= slice_count0 <= SLICES_PER_SEGMENT,
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        (page_ptr.page_ptr.addr() != 0 ==>
            page_ptr.wf()
            && page_ptr.is_in(*final(local))
            && final(local).page_organization.popped == Popped::Ready(page_ptr.page_id@, true)
            && page_init_is_committed(page_ptr.page_id@, *final(local))
            && (slice_count0 > 0 ==> final(local).page_organization.pages[page_ptr.page_id@].count == Some(slice_count0 as nat))
        ),
        (page_ptr.page_ptr.addr() == 0 ==> final(local).wf()),
{
    let mut sbin_idx = slice_bin(slice_count0);
    let slice_count = if slice_count0 == 0 { 1 } else { slice_count0 };

    while sbin_idx <= SEGMENT_BIN_MAX
        invariant
            local.wf(),
            tld_ptr.wf(),
            tld_ptr.is_in(*local),
            slice_count > 0,
            local.heap_id == old(local).heap_id,
            slice_count == (if slice_count0 == 0 { 1 } else { slice_count0 }),
            common_preserves(*old(local), *local),
    {
        let mut slice_ptr = ptr_ref(tld_ptr.tld_ptr, Tracked(&local.tld))
              .segments.span_queue_headers[sbin_idx].first;
        let ghost mut list_idx = 0int;
        let ghost mut slice_page_id: Option<PageId> =
            local.page_organization.unused_dlist_headers[sbin_idx as int].first;
        proof {
            local.page_organization.first_is_in(sbin_idx as int);
        }

        while slice_ptr.addr() != 0
            invariant
                local.wf(),
                tld_ptr.wf(),
                tld_ptr.is_in(*local),
                is_page_ptr_opt(slice_ptr, slice_page_id),
                slice_page_id.is_some() ==>
                    local.page_organization.valid_unused_page(
                        slice_page_id.unwrap(), sbin_idx as int, list_idx),
                slice_count > 0,
                local.heap_id == old(local).heap_id,
                slice_count == (if slice_count0 == 0 { 1 } else { slice_count0 }),
                common_preserves(*old(local), *local),
        {
            let slice = PagePtr {
                page_ptr: slice_ptr,
                page_id: Ghost(slice_page_id.unwrap())
            };
            assert(slice.wf());

            let found_slice_count = slice.get_count(Tracked(&*local)) as usize;
            if found_slice_count >= slice_count {
                let segment = SegmentPtr::ptr_segment(slice);

                assert(tld_ptr.is_in(*local));
                span_queue_delete(
                    tld_ptr,
                    sbin_idx,
                    slice,
                    Tracked(&mut *local),
                    Ghost(list_idx),
                    Ghost(found_slice_count as int));

                assert(tld_ptr.is_in(*local));

                if found_slice_count > slice_count {

                    segment_slice_split(
                        slice,
                        found_slice_count,
                        slice_count,
                        tld_ptr,
                        Tracked(&mut *local));
                }

                assert(tld_ptr.is_in(*local));

                let suc = segment_span_allocate(
                    segment,
                    slice,
                    slice_count,
                    tld_ptr,
                    Tracked(&mut *local));
                if !suc {
                    todo();
                }

                return slice;
            }

            slice_ptr = slice.get_next(Tracked(&*local));
            proof {
                local.page_organization.next_is_in(
                    slice_page_id.unwrap(), sbin_idx as int, list_idx);

                slice_page_id = local.page_organization.pages[slice_page_id.unwrap()]
                    .dlist_entry.unwrap().next;
                list_idx = list_idx + 1;
            }
        }

        sbin_idx = sbin_idx + 1;
    }

    PagePtr::null()
}

#[verifier::external_body]
fn span_queue_delete(
    tld_ptr: TldPtr,
    sbin_idx: usize,

    slice: PagePtr,

    Tracked(local): Tracked<&mut Local>,
    Ghost(list_idx): Ghost<int>,
    Ghost(count): Ghost<int>,
)
    requires
        old(local).wf_main(),
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        slice.wf(),
        old(local).page_organization.valid_unused_page(slice.page_id@, sbin_idx as int, list_idx),
        count == old(local).page_organization.pages[slice.page_id@].count.unwrap(),
        (match old(local).page_organization.popped {
            Popped::No => true,
            Popped::SegmentFreeing(sid, idx) =>
                slice.page_id@.segment_id == sid && slice.page_id@.idx == idx,
            _ => false,
        })
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        final(local).page_organization.popped == (match old(local).page_organization.popped {
            Popped::No => Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, count, false),
            Popped::SegmentFreeing(sid, idx) => Popped::SegmentFreeing(sid, idx + count),
            _ => arbitrary(),
        }),

        final(local).page_organization.pages.dom().contains(slice.page_id@),
        old(local).pages[slice.page_id@]
          == final(local).pages[slice.page_id@],
        final(local).page_organization.pages[slice.page_id@].is_used == false,
{
    unimplemented!()
}

#[verifier::spinoff_prover]
fn segment_slice_split(
    slice: PagePtr,
    current_slice_count: usize,
    target_slice_count: usize,
    tld_ptr: TldPtr,

    Tracked(local): Tracked<&mut Local>,
)
    requires
        old(local).wf_main(),
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        slice.wf(),
        old(local).page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, current_slice_count as int, false),
        old(local).page_organization.pages.dom().contains(slice.page_id@),
        old(local).page_organization.pages[slice.page_id@].is_used == false,
        SLICES_PER_SEGMENT >= current_slice_count > target_slice_count,
        target_slice_count > 0,
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        slice.wf(),
        final(local).page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, target_slice_count as int, false),
        final(local).page_organization.pages.dom().contains(slice.page_id@),
        final(local).page_organization.pages[slice.page_id@].is_used == false,
{
    proof {
        local.page_organization.get_count_bound_very_unready();
    }
    let next_slice = slice.add_offset(target_slice_count);

    let bin_idx = slice_bin(current_slice_count - target_slice_count);

    let ghost mut next_state;
    proof {
        next_state = PageOrg::take_step::split_page(
            local.page_organization,
            slice.page_id@,
            current_slice_count as int,
            target_slice_count as int,
            bin_idx as int);
    }

    let first_in_queue;

    let cq = &mut tld_ptr.get_mut(Tracked(local)).segments.span_queue_headers[bin_idx];
    first_in_queue = cq.first;
    cq.first = next_slice.page_ptr;
    if first_in_queue.addr() == 0 {
        cq.last = next_slice.page_ptr;
    }

    if first_in_queue.addr() != 0 {
        let first_in_queue_ptr = PagePtr { page_ptr: first_in_queue,
            page_id: Ghost(local.page_organization.unused_dlist_headers[bin_idx as int].first.unwrap()) };
        unused_page_get_mut_prev!(first_in_queue_ptr, local, p => {
            p = next_slice.page_ptr;
        });
    }

    unused_page_get_mut_count!(slice, local, c => {
        c = target_slice_count as u32;
    });

    unused_page_get_mut_inner!(next_slice, local, inner => {
        inner.xblock_size = 0;
    });
    unused_page_get_mut_prev!(next_slice, local, p => {
        p = core::ptr::null_mut();
    });
    unused_page_get_mut_next!(next_slice, local, n => {
        n = first_in_queue;
    });
    unused_page_get_mut_count!(next_slice, local, c => {
        c = (current_slice_count - target_slice_count) as u32;
    });
    unused_page_get_mut!(next_slice, local, page => {
        page.offset = 0;
    });

    proof { const_facts(); }

    if current_slice_count > target_slice_count + 1 {
        let last_slice = slice.add_offset(current_slice_count - 1);
        unused_page_get_mut_inner!(last_slice, local, inner => {
            inner.xblock_size = 0;
        });
        unused_page_get_mut_count!(last_slice, local, c => {
            c = (current_slice_count - target_slice_count) as u32;
        });
        unused_page_get_mut!(last_slice, local, page => {
            assert(0 <= (current_slice_count - target_slice_count) as u32 <= 512);
            assert(SIZEOF_PAGE_HEADER as u32 == 80);
            assert(0 <= (current_slice_count - target_slice_count - 1) as u32 * 80 <= u32::MAX);
            page.offset = (current_slice_count - target_slice_count - 1) as u32
                * (SIZEOF_PAGE_HEADER as u32);
        });
    }

    proof {
        local.page_organization = next_state;



        local.psa = local.psa.union_prefer_right(local.unused_pages);











        preserves_mem_chunk_good(*old(local), *local);
    }
}

#[verifier::spinoff_prover]
fn segment_span_allocate(
    segment: SegmentPtr,
    slice: PagePtr,
    slice_count: usize,
    tld_ptr: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (success: bool)
    requires
        old(local).wf_main(),
        slice.wf(),
        segment.wf(),
        segment.segment_id == slice.page_id@.segment_id,
        segment.is_in(*old(local)),

        old(local).page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, slice_count as int, false)
          || (old(local).page_organization.popped == Popped::SegmentCreating(slice.page_id@.segment_id) && slice.page_id@.idx == 0 && slice_count < SLICES_PER_SEGMENT),
        old(local).page_organization.pages.dom().contains(slice.page_id@),
        old(local).page_organization.pages[slice.page_id@].is_used == false,

        SLICES_PER_SEGMENT >= slice_count > 0,
    ensures
        final(local).wf_main(),
        success ==> old(local).page_organization.popped.is_VeryUnready() ==> final(local).page_organization.popped == Popped::Ready(slice.page_id@, true),
        success ==> old(local).page_organization.popped.is_SegmentCreating() ==> final(local).page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice_count as int, SLICES_PER_SEGMENT - slice_count as int, true),
        success ==> final(local).page_organization.pages.dom().contains(slice.page_id@),
        success ==> final(local).page_organization.pages[slice.page_id@].count
            == Some(slice_count as nat),
        success ==> page_init_is_committed(slice.page_id@, *final(local)),
        common_preserves(*old(local), *final(local)),
        segment.is_in(*final(local)),
{
    let ghost mut next_state;
    proof {
        const_facts();
        if local.page_organization.popped.is_VeryUnready() {
            next_state = PageOrg::take_step::allocate_popped(local.page_organization);
        } else {
            next_state = PageOrg::take_step::forget_about_first_page(local.page_organization, slice_count as int);
        }
    }

    let p = segment_page_start_from_slice(segment, slice, 0);

    if !segment_ensure_committed(segment, p, slice_count * SLICE_SIZE as usize, Tracked(&mut *local)) {
        return false;
    }

    let ghost old_local = *local;
    let ghost first_page_id = slice.page_id@;


    let ghost range = first_page_id.range_from(0, slice_count as int);

    assert forall |pid| range.contains(pid) implies #[trigger] local.unused_pages.dom().contains(pid)
    by {
        assert(local.pages.dom().contains(pid));
    }

    let tracked mut first_psa = local.unused_pages.tracked_remove(first_page_id);
    let mut page = ptr_mut_read(slice.page_ptr, Tracked(&mut first_psa.points_to));
    page.offset = 0;
    ptr_mut_write(slice.page_ptr, Tracked(&mut first_psa.points_to), page);
    proof {
        local.unused_pages.tracked_insert(first_page_id, first_psa);
    }
    unused_page_get_mut_count!(slice, local, count => {
        count = slice_count as u32;
    });
    unused_page_get_mut_inner!(slice, local, inner => {
        let bsize = slice_count * SLICE_SIZE as usize;
        inner.xblock_size = if bsize >= HUGE_BLOCK_SIZE as usize { HUGE_BLOCK_SIZE } else { bsize as u32 };
    });

    let mut i: usize = 1;
    let ghost local_snapshot = *local;
    let extra = slice_count - 1;
    assert forall |page_id|
        #[trigger] first_page_id.range_from(1, extra + 1).contains(page_id) implies
            local.unused_pages.dom().contains(page_id)
            && local.unused_pages[page_id].points_to.is_init()
            && is_page_ptr(local.unused_pages[page_id].points_to.ptr(), page_id)
            && local.unused_pages[page_id].points_to.ptr()@.provenance == local.unused_pages[page_id].exposed.provenance()
    by {
        assert(local.pages.dom().contains(page_id));
    }
    while i <= extra
        invariant 1 <= i <= extra + 1,
          first_page_id.idx + extra < SLICES_PER_SEGMENT,
          *local == (Local { unused_pages: local.unused_pages, .. local_snapshot }),
          local.unused_pages.dom() == local_snapshot.unused_pages.dom(),
          slice.wf(),
          slice.page_id == first_page_id,
          forall |page_id|
              #[trigger] first_page_id.range_from(1, extra + 1).contains(page_id) ==>
                  local.unused_pages.dom().contains(page_id)
                  && (local.unused_pages.dom().contains(page_id) ==>
                    local.unused_pages[page_id].points_to.is_init()
                    && is_page_ptr(local.unused_pages[page_id].points_to.ptr(), page_id))
                    && local.unused_pages[page_id].points_to.ptr()@.provenance == local.unused_pages[page_id].exposed.provenance(),
          forall |page_id|
              #[trigger] local.unused_pages.dom().contains(page_id) ==>
              (
                  if first_page_id.range_from(1, i as int).contains(page_id) {
                      psa_differ_only_in_offset(
                          local.unused_pages[page_id],
                          local_snapshot.unused_pages[page_id])
                      && local.unused_pages[page_id].points_to.value().offset ==
                          (page_id.idx - first_page_id.idx) * SIZEOF_PAGE_HEADER
                  } else {
                      local.unused_pages[page_id] == local_snapshot.unused_pages[page_id]
                  }
              ),
    {
        proof { const_facts(); }
        let ghost prelocal = *local;
        let this_slice = slice.add_offset(i);
        let ghost this_page_id = PageId { idx: (first_page_id.idx + i) as nat, .. first_page_id };
        assert(first_page_id.range_from(1, extra + 1).contains(this_page_id));

        let tracked mut this_psa = local.unused_pages.tracked_remove(this_page_id);
        let mut page = ptr_mut_read(this_slice.page_ptr, Tracked(&mut this_psa.points_to));
        assert(i <= SLICES_PER_SEGMENT);
        assert(SLICES_PER_SEGMENT == 512);
        assert(0 <= i as u32 <= 512);
        assert(SIZEOF_PAGE_HEADER as u32 == 80);
        assert(i as u32 * 80 <= u32::MAX);
        assert(i as u32 * SIZEOF_PAGE_HEADER as u32 <= u32::MAX);
        page.offset = i as u32 * SIZEOF_PAGE_HEADER as u32;
        ptr_mut_write(this_slice.page_ptr, Tracked(&mut this_psa.points_to), page);
        proof {
            local.unused_pages.tracked_insert(this_page_id, this_psa);
            assert_sets_equal!(local.unused_pages.dom() == prelocal.unused_pages.dom());
        }

        i = i + 1;

    }

    unused_page_get_mut_inner!(slice, local, inner => {
        inner.set_is_reset(false);
        inner.set_is_committed(false);
    });
    segment_get_mut_main2!(segment, local, main2 => {
        main2.used = main2.used + 1;
    });

    proof {
        let old_po = local.page_organization;
        local.page_organization = next_state;
        local.psa = local.psa.union_prefer_right(local.unused_pages);

        preserves_mem_chunk_good(old_local, *local);

    }

    return true;
}


#[verifier::spinoff_prover]
fn segment_alloc(
    required: usize,
    page_alignment: usize,
    req_arena_id: ArenaId,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (segment_ptr: SegmentPtr)
    requires
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        required == 0,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
{
    proof { const_facts(); }

    let (segment_slices, pre_size, info_slices) = segment_calculate_slices(required);
    let eager_delay = (current_thread_count() > 1 &&
          tld.get_segments_count(Tracked(&*local)) < option_eager_commit_delay() as usize);
    let eager = !eager_delay && option_eager_commit();
    let commit = eager || (required > 0);
    let is_zero = false;

    let mut commit_mask = CommitMask::empty();
    let mut decommit_mask = CommitMask::empty();

    let (pre_segment_ptr, new_psegment_slices, new_ppre_size, new_pinfo_slices, is_zero, pcommit, memid, mem_large, is_pinned, align_offset, Tracked(mem_chunk)) = segment_os_alloc(
        required,
        page_alignment,
        eager_delay,
        req_arena_id,
        segment_slices,
        pre_size,
        info_slices,
        &mut commit_mask,
        &mut decommit_mask,
        commit,
        tld,
        Tracked(&mut *local));

    let ghost local_snap1 = *local;

    if pre_segment_ptr.is_null() {
        return pre_segment_ptr;
    }

    let tracked thread_state_tok = local.take_thread_token();
    let ghost pre_segment_id = pre_segment_ptr.segment_id@;
    let ghost segment_state = SegmentState {
        shared_access: arbitrary(),
        is_enabled: false,
    };
    let tracked (Tracked(thread_state_tok), Ghost(tos), Tracked(thread_of_segment_tok))
        = local.instance.create_segment_mk_tokens(
            local.thread_id,
            pre_segment_id,
            segment_state,
            thread_state_tok);
    let ghost segment_id = Mim::State::mk_fresh_segment_id(tos, pre_segment_id);
    let segment_ptr = SegmentPtr {
        segment_ptr: pre_segment_ptr.segment_ptr,
        segment_id: Ghost(segment_id),
    };
    proof {
        local.thread_token = thread_state_tok;
        const_facts();
        segment_start_eq(segment_id, pre_segment_id);
    }


    let tracked seg_header_points_to_raw = mem_chunk.take_points_to_range(
        segment_start(segment_id), SIZEOF_SEGMENT_HEADER as int);

    proof { segment_start_mult8(segment_id); }
    vstd::layout::layout_for_type_is_valid::<SegmentHeader>();

    let tracked mut seg_header_points_to = seg_header_points_to_raw.into_typed::<SegmentHeader>(segment_start(segment_id) as usize);
    let allow_decommit = option_allow_decommit() && !is_pinned && !mem_large;
    let (pcell_main, Tracked(pointsto_main)) = PCell::new(SegmentHeaderMain {
        memid: memid,
        mem_is_pinned: is_pinned,
        mem_is_large: mem_large,
        mem_is_committed: commit_mask.is_full(),
        mem_alignment: page_alignment,
        mem_align_offset: align_offset,
        allow_decommit: allow_decommit,
        decommit_expire: 0,
        decommit_mask: if allow_decommit { decommit_mask } else { CommitMask::empty() },
        commit_mask: commit_mask,
    });
    let (pcell_main2, Tracked(pointsto_main2)) = PCell::new(SegmentHeaderMain2 {
        next: core::ptr::null_mut(),
        abandoned: 0,
        abandoned_visits: 0,
        used: 0,
        cookie: 0,
        segment_slices: 0,
        segment_info_slices: 0,
        kind: if required == 0 { SegmentKind::Normal } else { SegmentKind::Huge },
        slice_entries: 0,
    });
    let (cur_thread_id, Tracked(is_thread)) = crate::thread::thread_id();
    proof { local.is_thread.agrees(is_thread); }
    ptr_mut_write(segment_ptr.segment_ptr, Tracked(&mut seg_header_points_to), SegmentHeader {
        main: pcell_main,
        abandoned_next: 0,
        main2: pcell_main2,
        thread_id: AtomicU64::new(
            Ghost((Ghost(local.instance), Ghost(segment_id))),
            cur_thread_id.thread_id,
            Tracked(thread_of_segment_tok),
        ),
        instance: Ghost(local.instance),
        segment_id: Ghost(segment_id),
    });

    let mut i: usize = 0;
    let mut cur_page_ptr = segment_ptr.segment_ptr.with_addr(
        segment_ptr.segment_ptr.addr() + SIZEOF_SEGMENT_HEADER
    ) as *mut Page;
    let ghost old_mem_chunk = mem_chunk;
    let tracked mut psa_map = Map::<PageId, PageSharedAccess>::tracked_empty();
    let tracked mut pla_map = Map::<PageId, PageLocalAccess>::tracked_empty();
    while i <= SLICES_PER_SEGMENT as usize
        invariant mem_chunk.os == old_mem_chunk.os,
            mem_chunk.wf(),
            set_int_range(
                    segment_start(segment_id) + SIZEOF_SEGMENT_HEADER,
                    segment_start(segment_id) + COMMIT_SIZE) <= old_mem_chunk.points_to.dom(),
            mem_chunk.points_to.dom() =~= old_mem_chunk.points_to.dom() -
                set_int_range(
                    segment_start(segment_id),
                    segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER
                ),

            cur_page_ptr as int == segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER,
            cur_page_ptr@.provenance == segment_ptr.segment_ptr@.provenance,
            mem_chunk.points_to.provenance() == segment_ptr.segment_ptr@.provenance,
            segment_ptr.segment_ptr as int + SEGMENT_SIZE < usize::MAX,
            segment_ptr.wf(),
            segment_ptr.segment_id@ == segment_id,
            i <= SLICES_PER_SEGMENT + 1,
            forall |page_id: PageId|
                #[trigger] psa_map.dom().contains(page_id) ==>
                    page_id.segment_id == segment_id && 0 <= page_id.idx < i,
            forall |page_id: PageId|
                #[trigger] pla_map.dom().contains(page_id) ==>
                    page_id.segment_id == segment_id && 0 <= page_id.idx < i,
            forall |page_id: PageId|
                #![trigger psa_map.dom().contains(page_id)]
                #![trigger psa_map.index(page_id)]
                #![trigger pla_map.dom().contains(page_id)]
                #![trigger pla_map.index(page_id)]
            {
                page_id.segment_id == segment_id && 0 <= page_id.idx < i ==> {
                    &&& psa_map.dom().contains(page_id)
                    &&& pla_map.dom().contains(page_id)
                    &&& pla_map[page_id].inner.value().zeroed()
                    &&& pla_map[page_id].count.value() == 0
                    &&& pla_map[page_id].prev.value().addr() == 0
                    &&& pla_map[page_id].next.value().addr() == 0

                    &&& is_page_ptr(psa_map[page_id].points_to.ptr(), page_id)
                    &&& psa_map[page_id].points_to.is_init()
                    &&& psa_map[page_id].points_to.value().count.id() == pla_map[page_id].count.id()
                    &&& psa_map[page_id].points_to.value().inner.id() == pla_map[page_id].inner.id()
                    &&& psa_map[page_id].points_to.value().prev.id() == pla_map[page_id].prev.id()
                    &&& psa_map[page_id].points_to.value().next.id() == pla_map[page_id].next.id()
                    &&& psa_map[page_id].points_to.ptr()@.provenance == psa_map[page_id].exposed.provenance()
                    &&& psa_map[page_id].points_to.value().offset == 0
                    &&& psa_map[page_id].points_to.value().xthread_free.is_empty()
                    &&& psa_map[page_id].points_to.value().xthread_free.wf()
                    &&& psa_map[page_id].points_to.value().xthread_free.instance == local.instance
                    &&& psa_map[page_id].points_to.value().xheap.is_empty()
                }
            }
    {
        let ghost page_id = PageId { segment_id, idx: i as nat };
        proof {
            const_facts();
            segment_start_mult8(segment_id);
            assert(
                COMMIT_SIZE - (SIZEOF_SEGMENT_HEADER + SLICES_PER_SEGMENT * SIZEOF_PAGE_HEADER)
                <= COMMIT_SIZE - (SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER))
                by(nonlinear_arith) requires i <= SLICES_PER_SEGMENT;
            assert(i * SIZEOF_PAGE_HEADER + SIZEOF_PAGE_HEADER == (i + 1) * SIZEOF_PAGE_HEADER) by(nonlinear_arith);
        }

        let ghost phstart = segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER;
        vstd::layout::layout_for_type_is_valid::<Page>();
        let tracked page_header_points_to_raw = mem_chunk.take_points_to_range(
            phstart, SIZEOF_PAGE_HEADER as int);
        let tracked mut page_header_points_to = page_header_points_to_raw.into_typed::<Page>(phstart as usize);
        let (pcell_count, Tracked(pointsto_count)) = PCell::new(0);
        let (pcell_inner, Tracked(pointsto_inner)) = PCell::new(PageInner {
            flags0: 0,
            capacity: 0,
            reserved: 0,
            flags1: 0,
            flags2: 0,
            free: LL::empty(),
            used: 0,
            xblock_size: 0,
            local_free: LL::empty(),
        });
        let (pcell_prev, Tracked(pointsto_prev)) = PCell::new(core::ptr::null_mut());
        let (pcell_next, Tracked(pointsto_next)) = PCell::new(core::ptr::null_mut());
        let page = Page {
            count: pcell_count,
            offset: 0,
            inner: pcell_inner,
            xthread_free: ThreadLLWithDelayBits::empty(Tracked(local.instance.clone())),
            xheap: AtomicHeapPtr::empty(),
            prev: pcell_prev,
            next: pcell_next,
            padding: 0,
        };
        let tracked pla = PageLocalAccess {
            count: pointsto_count,
            inner: pointsto_inner,
            prev: pointsto_prev,
            next: pointsto_next,
        };
        ptr_mut_write(cur_page_ptr, Tracked(&mut page_header_points_to), page);
        let Tracked(exposed) = expose_provenance(cur_page_ptr);
        let tracked psa = PageSharedAccess { points_to: page_header_points_to, exposed };
        proof {
            psa_map.tracked_insert(page_id, psa);
            pla_map.tracked_insert(page_id, pla);
        }


        i = i + 1;
        cur_page_ptr = cur_page_ptr.with_addr(cur_page_ptr.addr() + SIZEOF_PAGE_HEADER);



    }

    proof {
        local.unused_pages.tracked_union_prefer_right(psa_map);
        local.pages.tracked_union_prefer_right(pla_map);
        local.psa = local.psa.union_prefer_right(psa_map);

        let tracked ssa = SegmentSharedAccess {
            points_to: seg_header_points_to,
        };
        let tracked sla = SegmentLocalAccess {
            mem: mem_chunk,
            main: pointsto_main,
            main2: pointsto_main2,
        };
        local.segments.tracked_insert(segment_id, sla);

        let tracked thread_state_tok = local.take_thread_token();
        let tracked thread_state_tok = local.instance.segment_enable(
                local.thread_id,
                segment_id,
                ssa,
                thread_state_tok,
                ssa);
        local.thread_token = thread_state_tok;


        local.page_organization = PageOrg::take_step::create_segment(local.page_organization, segment_id);

        assert(local.thread_token.value().segments.dom() =~= local.segments.dom());


        preserves_mem_chunk_good_except(local_snap1, *local, segment_id);
        assert(mem_chunk_good1(
            local.segments[segment_id].mem,
            segment_id,
            local.commit_mask(segment_id).bytes(segment_id),
            local.decommit_mask(segment_id).bytes(segment_id),
            local.segment_pages_range_total(segment_id),
            local.segment_pages_used_total(segment_id),
        )) by {
            reveal(CommitMask::bytes);
            empty_segment_pages_used_total(*local, segment_id);
        }
    }

    let first_slice = PagePtr {
        page_ptr: segment_ptr.segment_ptr.with_addr(
            segment_ptr.segment_ptr.addr() + SIZEOF_SEGMENT_HEADER) as *mut Page,
        page_id: Ghost(PageId { segment_id, idx: 0 }),
    };
    let success = segment_span_allocate(segment_ptr, first_slice, 1, tld, Tracked(&mut *local));
    if !success {
        todo();
    }


    let ghost local_snap = *local;
    let ghost next_state = PageOrg::take_step::forget_about_first_page2(local.page_organization);
    segment_get_mut_main2!(segment_ptr, local, main2 => {
        main2.used = main2.used - 1;
    });
    proof {
        local.page_organization = next_state;
        local.psa = local.psa.union_prefer_right(local.unused_pages);
        preserves_mem_chunk_good(local_snap, *local);
    }

    if required == 0 {
        segment_span_free(segment_ptr, 1, SLICES_PER_SEGMENT as usize - 1, false, tld, Tracked(&mut *local));
    } else {
        todo();
    }

    return segment_ptr;
}

#[verifier::spinoff_prover]
fn segment_os_alloc(
    required: usize,
    page_alignment: usize,
    eager_delay: bool,
    req_arena_id: ArenaId,
    psegment_slices: usize,
    pre_size: usize,
    pinfo_slices: usize,
    pcommit_mask: &mut CommitMask,
    pdecommit_mask: &mut CommitMask,
    request_commit: bool,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (res: (SegmentPtr, usize, usize, usize, bool, bool, MemId, bool, bool, usize, Tracked<MemChunk>))
    requires psegment_slices as int * SLICE_SIZE as int <= usize::MAX,
        pinfo_slices == 1,
        psegment_slices >= 1,
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        psegment_slices == SLICES_PER_SEGMENT,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        final(local).page_organization == old(local).page_organization,
        *final(pdecommit_mask) == *old(pdecommit_mask),
    ({
        let (segment_ptr, new_psegment_slices, new_ppre_size, new_pinfo_slices, is_zero, pcommit, mem_id, mem_large, is_pinned, align_offset, mem_chunk) = res; {
        &&& (segment_ptr.segment_ptr.addr() != 0 ==> {
            &&& segment_ptr.wf()
            &&& mem_chunk@.wf()
            &&& mem_chunk@.os_exact_range(segment_ptr.segment_ptr as int, SEGMENT_SIZE as int)
            &&& mem_chunk@.points_to.provenance() == segment_ptr.segment_ptr@.provenance
            &&& segment_ptr.segment_ptr@.provenance == segment_ptr.segment_id@.provenance
            &&& set_int_range(segment_start(segment_ptr.segment_id@),
                    segment_start(segment_ptr.segment_id@) + COMMIT_SIZE).subset_of( final(pcommit_mask).bytes(segment_ptr.segment_id@) )
            &&& final(pcommit_mask).bytes(segment_ptr.segment_id@).subset_of(mem_chunk@.os_rw_bytes())
            &&& mem_chunk@.os_rw_bytes().subset_of(mem_chunk@.points_to.dom())
        })
        }
    })
{
    proof { const_facts(); }

    let mut mem_large = !eager_delay;
    let mut is_pinned = false;
    let mut mem_id: usize = 0;
    let mut align_offset: usize = 0;
    let mut alignment: usize = SEGMENT_ALIGN as usize;
    let mut is_zero = false;
    let mut pcommit = request_commit;
    let mut psegment_slices = psegment_slices;
    let mut pinfo_slices = pinfo_slices;
    let mut pre_size = pre_size;
    let tracked mut mem = MemChunk::empty();

    if page_alignment > 0 {
        todo();
    }

    let segment_size = psegment_slices * SLICE_SIZE as usize;

    let mut segment = SegmentPtr::null();

    if page_alignment == 0 {
    }

    if segment.is_null() {
        let (_segment, Tracked(_mem), commit, _large, _is_pinned, _is_zero, _mem_id) =
          arena_alloc_aligned(
            segment_size, alignment, align_offset, request_commit, mem_large, req_arena_id);
        segment = SegmentPtr {
            segment_ptr: _segment as *mut SegmentHeader,
            segment_id: Ghost(mk_segment_id(_segment as *mut SegmentHeader)),
        };
        mem_id = _mem_id;
        mem_large = _large;
        is_zero = _is_zero;
        is_pinned = _is_pinned;
        pcommit = commit;
        proof {
            mem = _mem;
        }

        if segment.is_null() {
            return (segment,
                psegment_slices, pre_size, pinfo_slices, is_zero, pcommit, mem_id, mem_large, is_pinned, align_offset, Tracked(MemChunk::empty()))
        }
        if pcommit {
            pcommit_mask.create_full();
        } else {
            pcommit_mask.create_empty();
        }
    }

    let commit_needed = pinfo_slices;
    let mut commit_needed_mask = CommitMask::empty();
    commit_needed_mask.create(0, commit_needed);
    if !pcommit_mask.all_set(&commit_needed_mask) {

        let (success, is_zero) = crate::os_commit::os_commit(
            segment.segment_ptr as *mut u8,
            commit_needed * COMMIT_SIZE as usize,
            Tracked(&mut mem));
        if !success {
            return (SegmentPtr::null(), 0, 0, 0, false, false, 0, false, false, 0, Tracked(MemChunk::empty()));
        }
        pcommit_mask.set(&commit_needed_mask);
    }



    proof {
        crate::commit_mask::set_int_range_commit_size(segment.segment_id@, *pcommit_mask);
        assert(pcommit_mask.bytes(segment.segment_id@).subset_of(mem.os_rw_bytes()))
        by {
            reveal(CommitMask::bytes);
        }
        assert(mem.os_rw_bytes().subset_of(mem.points_to.dom()));
    }

    return (segment, psegment_slices, pre_size, pinfo_slices, is_zero, pcommit, mem_id, mem_large, is_pinned, align_offset, Tracked(mem));
}

fn segment_free(segment: SegmentPtr, force: bool, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        segment.wf(),
        segment.is_in(*old(local)),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
{
    todo();





}

fn segment_os_free(segment: SegmentPtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main(),
        segment.wf(), segment.is_in(*old(local)),
        tld.wf(), tld.is_in(*old(local)),
{

    todo();




}

fn segment_calculate_slices(required: usize)
  -> (res: (usize, usize, usize))
  requires required == 0,
  ensures ({ let (num_slices, pre_size, info_slices) = res;
      required == 0 ==> num_slices == SLICES_PER_SEGMENT
          && pre_size == crate::os_mem::page_size()
          && info_slices == 1
  })
{
    proof { const_facts(); }

    let page_size = crate::os_mem::get_page_size();
    let i_size = align_up(SIZEOF_SEGMENT_HEADER, page_size);
    let guardsize = 0;

    let pre_size = i_size;
    let j_size = align_up(i_size + guardsize, SLICE_SIZE as usize);
    let info_slices = j_size / SLICE_SIZE as usize;
    let segment_size = if required == 0 {
        SEGMENT_SIZE as usize
    } else {
        align_up(required + j_size + guardsize, SLICE_SIZE as usize)
    };
    let num_slices = segment_size / SLICE_SIZE as usize;

    (num_slices, pre_size, info_slices)
}

#[verifier::external_body]
fn segment_span_free(
    segment_ptr: SegmentPtr,
    slice_index: usize,
    slice_count: usize,
    allow_decommit: bool,
    tld_ptr: TldPtr,
    Tracked(local): Tracked<&mut Local>,
)
    requires
        old(local).wf_main(),
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        segment_ptr.wf(),
        segment_ptr.is_in(*old(local)),
        0 <= slice_index,
        slice_index + slice_count <= SLICES_PER_SEGMENT,

        old(local).page_organization.popped == Popped::VeryUnready(segment_ptr.segment_id@, slice_index as int, slice_count as int, old(local).page_organization.popped.get_VeryUnready_3()),
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        segment_ptr.is_in(*final(local)),
        final(local).page_organization.popped == if old(local).page_organization.popped.get_VeryUnready_3() {
            Popped::ExtraCount(segment_ptr.segment_id@)
        } else {
            Popped::No
        },
        final(local).pages.dom() =~= old(local).pages.dom(),
{
    unimplemented!()
}

pub fn segment_page_free(page: PagePtr, force: bool, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main(),
        tld.wf(),
        tld.is_in(*old(local)),
        page.wf(),
        page.is_in(*old(local)),
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        old(local).pages[page.page_id@].inner.value().used == 0,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
{
    let segment = SegmentPtr::ptr_segment(page);
    segment_page_clear(page, tld, Tracked(&mut *local));

    let used = segment.get_used(Tracked(&*local));
    if used == 0 {
        segment_free(segment, force, tld, Tracked(&mut *local));
    } else if used == segment.get_abandoned(Tracked(&*local)) {
        todo();
    }
}

#[verifier::spinoff_prover]
fn segment_page_clear(page: PagePtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main(),
        tld.wf(),
        tld.is_in(*old(local)),
        page.wf(),
        page.is_in(*old(local)),
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        old(local).pages[page.page_id@].inner.value().used == 0,
    ensures
        final(local).wf(),
        page.is_in(*final(local)),
        common_preserves(*old(local), *final(local)),
{
    let ghost page_id = page.page_id@;
    let ghost next_state = PageOrg::take_step::set_range_to_not_used(local.page_organization);
    let ghost n_slices = local.page_organization.pages[page_id].count.unwrap();
    let ghost page_state = local.thread_token.value().pages[page_id];

    let segment = SegmentPtr::ptr_segment(page);

    let mem_is_pinned = segment.get_mem_is_pinned(Tracked(&*local));
    let is_reset = page.get_inner_ref(Tracked(&*local)).get_is_reset();
    let option_page_reset = option_page_reset();
    if !mem_is_pinned && !is_reset && option_page_reset {
        todo();
    }

    let tracked block_tokens;
    let tracked block_pt;
    page_get_mut_inner!(page, local, inner => {
        inner.set_is_zero_init(false);
        inner.capacity = 0;
        inner.reserved = 0;
        let (Tracked(ll_state1)) = inner.free.make_empty();
        inner.flags1 = 0;
        inner.flags2 = 0;
        inner.used = 0;
        inner.xblock_size = 0;
        let (Tracked(ll_state2)) = inner.local_free.make_empty();

        let tracked (_block_pt, _block_tokens) = LL::reconvene_state(
            local.instance.clone(), &local.thread_token, ll_state1, ll_state2,
            page_state.num_blocks as int);
        proof { block_tokens = _block_tokens; block_pt = _block_pt; }
    });

    let tracked psa_map;
    proof {
        let tracked thread_state_tok = local.take_thread_token();
        let block_state_map = Map::new(
            block_tokens.dom(),
            |block_id: BlockId| block_tokens[block_id].value(),
        );
        assert(block_state_map.dom() =~= block_tokens.dom());
        let tracked thread_state_tok = local.instance.page_destroy_block_tokens(
            local.thread_id, page_id, block_state_map,
            thread_state_tok, Mim::block_map::from_map(local.instance.id(), block_tokens));
        assert forall |pid: PageId| page_id.range_from(0, n_slices as int).contains(pid)
            implies thread_state_tok.value().pages.dom().contains(pid)
        by {
            assert(pid.segment_id == page_id.segment_id);
            assert(page_id.idx <= pid.idx < page_id.idx + n_slices);
            assert(local.page_organization.pages.dom().contains(pid));
            assert(local.page_organization.pages[pid].is_used);
        }
        local.thread_token = thread_state_tok;
    }
    let tracked checked_tok = local.take_checked_token();
    let tracked perm = &local.instance.thread_local_state_guards_page(
                local.thread_id, page.page_id@, &local.thread_token).points_to;
    let Tracked(checked_tok) = ptr_ref(page.page_ptr, Tracked(perm)).xthread_free.check_is_good(
        Tracked(&local.thread_token),
        Tracked(checked_tok));
    proof {
        let tracked thread_state_tok = local.take_thread_token();

        let tracked (Tracked(thread_state_tok), Tracked(_psa_map)) = local.instance.page_disable(
            local.thread_id, page_id, n_slices,
            thread_state_tok, &checked_tok);
        local.thread_token = thread_state_tok;
        local.checked_token = checked_tok;
        psa_map = _psa_map;

        local.unused_pages.tracked_union_prefer_right(psa_map);
    }

    let tracked delay_token;
    let tracked heap_of_page_token;
    unused_page_get_mut!(page, local, page => {
        let Tracked(_delay_token) = page.xthread_free.disable();
        let Tracked(_heap_of_page_token) = page.xheap.disable();

        proof { delay_token = _delay_token; heap_of_page_token = _heap_of_page_token; }
    });

    proof {

        local.psa = local.psa.union_prefer_right(local.unused_pages);

        let segment_id = page_id.segment_id;
        let tracked mut seg = local.segments.tracked_remove(segment_id);
        seg.mem.give_points_to_range(block_pt);
        local.segments.tracked_insert(segment_id, seg);
        local.page_organization = next_state;


        let tracked thread_state_tok = local.take_thread_token();
        let tracked thread_tok = local.instance.page_destroy_tokens(local.thread_id, page_id, n_slices, thread_state_tok, delay_token, heap_of_page_token);
        local.thread_token = thread_tok;

        preserves_mem_chunk_good_on_transfer_back(*old(local), *local, page_id);
        preserves_mem_chunk_good_except(*old(local), *local, segment_id);











        assert(local.wf_main());
    }

    segment_span_free_coalesce(page, tld, Tracked(&mut *local));

    let ghost local_snap = *local;

    let ghost next_state = PageOrg::take_step::clear_ec(local.page_organization);
    segment_get_mut_main2!(segment, local, main2 => {
        main2.used = main2.used - 1;
    });
    proof {
        local.page_organization = next_state;
        local.psa = local.psa.union_prefer_right(local.unused_pages);
        preserves_mem_chunk_good(local_snap, *local);
    }

    proof {
        preserves_mem_chunk_good(local_snap, *local);
    }
}

fn segment_span_free_coalesce(slice: PagePtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main(),
        tld.wf(),
        tld.is_in(*old(local)),
        slice.wf(),
        slice.is_in(*old(local)),
        match old(local).page_organization.popped {
            Popped::VeryUnready(sid, idx, c, _) => slice.page_id@.segment_id == sid
                && slice.page_id@.idx == idx
                && c == old(local).pages[slice.page_id@].count.value(),
            _ => false,
        },
    ensures
        final(local).wf_main(),
        slice.is_in(*final(local)),
        common_preserves(*old(local), *final(local)),
        final(local).page_organization.popped == (match old(local).page_organization.popped {
            Popped::VeryUnready(_, _, _, b) => {
                if b {
                    Popped::ExtraCount(slice.page_id@.segment_id)
                } else {
                    Popped::No
                }
            }
            _ => arbitrary(),
        }),
{
    let segment = SegmentPtr::ptr_segment(slice);
    let is_abandoned = segment.is_abandoned(Tracked(&*local));
    if is_abandoned { todo(); }

    let kind = segment.get_segment_kind(Tracked(&*local));
    if matches!(kind, SegmentKind::Huge) {
        todo();
    }

    let mut slice_count = slice.get_count(Tracked(&*local));

    proof {
        local.page_organization.get_count_bound_very_unready();
        const_facts();
    }


    let (page, less_than_end) = slice.add_offset_and_check(slice_count as usize, segment);
    proof {
        if less_than_end {
            local.page_organization.valid_page_after();
        }
    }
    if less_than_end && page.get_inner_ref(Tracked(&*local)).xblock_size == 0 {
        let ghost page_id = page.page_id@;
        let ghost local_snap = *local;
        let ghost next_state = PageOrg::take_step::merge_with_after(local.page_organization);

        let prev_ptr = page.get_prev(Tracked(&*local));
        let next_ptr = page.get_next(Tracked(&*local));

        let ghost prev_page_id = local.page_organization.pages[page_id].dlist_entry.unwrap().prev.unwrap();
        let prev = PagePtr {
            page_ptr: prev_ptr, page_id: Ghost(prev_page_id),
        };
        let ghost next_page_id = local.page_organization.pages[page_id].dlist_entry.unwrap().next.unwrap();
        let next = PagePtr {
            page_ptr: next_ptr, page_id: Ghost(next_page_id),
        };

        let n_count = page.get_count(Tracked(&*local));
        let sbin_idx = slice_bin(n_count as usize);

        if prev_ptr.addr() != 0 {
            unused_page_get_mut_next!(prev, local, n => {
                n = next_ptr;
            });
        }
        if next_ptr.addr() != 0 {
            unused_page_get_mut_prev!(next, local, p => {
                p = prev_ptr;
            });
        }

        let cq = &mut tld.get_mut(Tracked(local)).segments.span_queue_headers[sbin_idx];
        if prev_ptr.addr() == 0 {
            cq.first = next_ptr;
        }
        if next_ptr.addr() == 0 {
            cq.last = prev_ptr;
        }

        slice_count += n_count;

        proof {
            local.page_organization = next_state;



            preserves_mem_chunk_good(local_snap, *local);
        }
    }

    assert(local.wf_main());


    let (slice, slice_count) = segment_span_free_coalesce_before(segment, slice, tld, Tracked(&mut *local), slice_count);

    segment_span_free(segment, slice.get_index(), slice_count as usize, true, tld,
        Tracked(&mut *local));
}

#[inline(always)]
#[verifier::spinoff_prover]
fn segment_span_free_coalesce_before(segment: SegmentPtr, slice: PagePtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>, slice_count: u32)
    -> (res: (PagePtr, u32))
    requires
        old(local).wf_main(),
        tld.wf(),
        tld.is_in(*old(local)),
        segment.wf(),
        segment.segment_id@ == slice.page_id@.segment_id,
        slice.wf(),
        slice.is_in(*old(local)),
        old(local).page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, slice_count as int, old(local).page_organization.popped.get_VeryUnready_3())
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        slice.is_in(*final(local)),
        slice.page_id@.segment_id == res.0.page_id@.segment_id,
        ({ let (slice, slice_count) = res;
          slice.wf()
          && final(local).page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, slice_count as int, old(local).page_organization.popped.get_VeryUnready_3())
          && slice.page_id@.idx + slice_count <= SLICES_PER_SEGMENT
        })
{
    proof { const_facts(); }

    let ghost orig_id = slice.page_id@;

    let mut slice = slice;
    let mut slice_count = slice_count;

    if slice.is_gt_0th_slice(segment) {
        proof {
            local.page_organization.valid_page_before();
        }
        let last = slice.sub_offset(1);
        let offset = last.get_ref(Tracked(&*local)).offset;
        let ghost o = local.page_organization.pages[last.page_id@].offset.unwrap();
        let ghost page_id = PageId { segment_id: last.page_id@.segment_id,
                idx: (last.page_id@.idx - o) as nat };
        let page_ptr = calculate_page_ptr_subtract_offset(last.page_ptr, offset,
            Ghost(last.page_id@),
            Ghost(page_id));
        let page = PagePtr { page_ptr, page_id: Ghost(page_id) };
        proof {
            is_page_ptr_nonzero(page_ptr, page_id);
        }
        if page.get_inner_ref(Tracked(&*local)).xblock_size == 0 {
            let ghost local_snap = *local;
            let ghost next_state = PageOrg::take_step::merge_with_before(local.page_organization);

            let prev_ptr = page.get_prev(Tracked(&*local));
            let next_ptr = page.get_next(Tracked(&*local));

            let ghost prev_page_id = local.page_organization.pages[page_id].dlist_entry.unwrap().prev.unwrap();
            let prev = PagePtr {
                page_ptr: prev_ptr, page_id: Ghost(prev_page_id),
            };
            let ghost next_page_id = local.page_organization.pages[page_id].dlist_entry.unwrap().next.unwrap();
            let next = PagePtr {
                page_ptr: next_ptr, page_id: Ghost(next_page_id),
            };

            let n_count = page.get_count(Tracked(&*local));
            let sbin_idx = slice_bin(n_count as usize);

            if prev_ptr.addr() != 0 {
                unused_page_get_mut_next!(prev, local, n => {
                    n = next_ptr;
                });
            }
            if next_ptr.addr() != 0 {
                unused_page_get_mut_prev!(next, local, p => {
                    p = prev_ptr;
                });
            }

            let cq = &mut tld.get_mut(Tracked(local)).segments.span_queue_headers[sbin_idx];
            if prev_ptr.addr() == 0 {
                cq.first = next_ptr;
            }
            if next_ptr.addr() == 0 {
                cq.last = prev_ptr;
            }

            slice_count += n_count;
            slice = page;

            proof {
                local.page_organization = next_state;
                preserves_mem_chunk_good(local_snap, *local);


            }
        }
    }

    proof {
        local.page_organization.get_count_bound_very_unready();
    }

    (slice, slice_count)
}

}
}
mod commit_segment {
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;

use crate::commit_mask::*;
use crate::types::*;
use crate::layout::*;
use crate::config::*;
use crate::segment::*;
use crate::os_mem_util::*;
use crate::tokens::*;
use crate::os_mem::*;

verus!{

fn clock_now() -> i64 {
    let t = clock_gettime_monotonic();
    t.tv_sec.wrapping_mul(1000).wrapping_add( (((t.tv_nsec as u64) / 1000000) as i64) )
}

fn segment_commit_mask(
    segment_ptr: *mut u8,
    conservative: bool,
    p: usize,
    size: usize,
    cm: &mut CommitMask)
 -> (res: (*mut u8, usize))
    requires
        segment_ptr as int % SEGMENT_SIZE as int == 0,
        segment_ptr as int + SEGMENT_SIZE <= usize::MAX,
        p >= segment_ptr as int,
        p + size <= segment_ptr as int + SEGMENT_SIZE,
        old(cm)@ == Set::<int>::empty(),
    ensures ({ let (start_p, full_size) = res; {
        (final(cm)@ == Set::<int>::empty() ==> !conservative ==> size == 0)
        && (final(cm)@ != Set::<int>::empty() ==>
            (conservative ==> p <= start_p as int <= start_p as int + full_size <= p + size)
            && (!conservative ==> start_p as int <= p <= p + size <= start_p as int + full_size)
            && start_p as int >= segment_ptr as int
            && start_p as int + full_size <= segment_ptr as int + SEGMENT_SIZE
            && start_p as int % COMMIT_SIZE as int == 0
            && full_size as int % COMMIT_SIZE as int == 0
            && final(cm)@ =~=
                set_int_range((start_p as int - segment_ptr as int) / COMMIT_SIZE as int,
                    (((start_p as int + full_size - segment_ptr as int) / COMMIT_SIZE as int)))
            && start_p@.provenance == segment_ptr@.provenance
        )
        && (!conservative ==> forall |i| #[trigger] final(cm)@.contains(i) ==>
            start_p as int <= segment_ptr as int + i * SLICE_SIZE
            && start_p as int + full_size >= segment_ptr as int + (i + 1) * SLICE_SIZE
        )
    }})
{
    proof { const_facts(); }

    if size == 0 || size > SEGMENT_SIZE as usize {
        return (core::ptr::null_mut(), 0);
    }

    let segstart: usize = SLICE_SIZE as usize;
    let segsize: usize = SEGMENT_SIZE as usize;

    if p >= segment_ptr.addr() + segsize {
        return (core::ptr::null_mut(), 0);
    }

    let pstart: usize = p - segment_ptr.addr();

    let mut start: usize;
    let mut end: usize;
    if conservative {
        start = align_up(pstart, COMMIT_SIZE as usize);
        end = align_down(pstart + size, COMMIT_SIZE as usize);
    } else {
        start = align_down(pstart, COMMIT_SIZE as usize);
        end = align_up(pstart + size, COMMIT_SIZE as usize);
    }

    if pstart >= segstart && start < segstart {
        start = segstart;
    }

    if end > segsize {
        end = segsize;
    }

    let start_p = segment_ptr.with_addr(segment_ptr.addr() + start);
    let full_size = if end > start { end - start } else { 0 };
    if full_size == 0 {
        return (start_p, full_size);
    }

    let bitidx = start / COMMIT_SIZE as usize;
    let bitcount = full_size / COMMIT_SIZE as usize;
    cm.create(bitidx, bitcount);

    proof {
        let start_p = start_p as int;
        if conservative {
            assert(p <= start_p);
            assert(start_p + full_size <= p + size);
        } else {
            assert(start_p <= p);

            assert(start_p + full_size == segment_ptr as int + end);
            assert(p + size == segment_ptr as int + pstart + size);
            assert(end >= pstart + size);

            assert(p + size <= start_p + full_size);

            assert((p - segment_ptr as int) / COMMIT_SIZE as int >= bitidx);
            assert((((p + size - 1 - segment_ptr as int) / COMMIT_SIZE as int) + 1) <= bitidx + bitcount);
        }
        if full_size > 0 {
            assert(cm@.contains(bitidx as int));
        }
    }

    return (start_p, full_size);
}

#[verifier::external_body]
fn segment_commitx(
    segment: SegmentPtr,
    commit: bool,
    p: usize,
    size: usize,
    Tracked(local): Tracked<&mut Local>,
) -> (success: bool)
    requires old(local).wf_main(),
        segment.wf(),
        segment.is_in(*old(local)),
        p >= segment.segment_ptr.addr(),
        p + size <= segment.segment_ptr.addr() + SEGMENT_SIZE,
        !commit ==>
            set_int_range(p as int, p + size)
             <= old(local).decommit_mask(segment.segment_id@).bytes(segment.segment_id@),
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        commit ==> success ==> final(local).segments[segment.segment_id@]
            .mem.os_has_range_read_write(p as int, size as int),
        commit ==> success ==> set_int_range(p as int, p + size) <=
            final(local).commit_mask(segment.segment_id@).bytes(segment.segment_id@)
             - final(local).decommit_mask(segment.segment_id@).bytes(segment.segment_id@),

        final(local).page_organization == old(local).page_organization,
        final(local).pages == old(local).pages,
        final(local).psa == old(local).psa,
{
   unimplemented!()
}

pub fn segment_ensure_committed(
    segment: SegmentPtr,
    p: usize,
    size: usize,
    Tracked(local): Tracked<&mut Local>
) -> (success: bool)
    requires old(local).wf_main(),
        segment.wf(),
        segment.is_in(*old(local)),
        p >= segment.segment_ptr.addr(),
        p + size <= segment.segment_ptr.addr() + SEGMENT_SIZE,
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        success ==> set_int_range(p as int, p + size) <=
            final(local).commit_mask(segment.segment_id@).bytes(segment.segment_id@)
            - final(local).decommit_mask(segment.segment_id@).bytes(segment.segment_id@),

        final(local).page_organization == old(local).page_organization,
{
    if segment.get_commit_mask(Tracked(&*local)).is_full()
        && segment.get_decommit_mask(Tracked(&*local)).is_empty()
    {
        proof {
                const_facts();
                reveal(CommitMask::bytes);
        }

        return true;
    }

    segment_commitx(segment, true, p, size, Tracked(local))
}

pub fn segment_perhaps_decommit(
    segment: SegmentPtr,
    p: usize,
    size: usize,
    Tracked(local): Tracked<&mut Local>,
)
    requires old(local).wf_main(),
        segment.wf(),
        segment.is_in(*old(local)),
        p >= segment.segment_ptr.addr(),
        p + size <= segment.segment_ptr.addr() + SEGMENT_SIZE,
        set_int_range(p as int, p + size).disjoint(
            segment_info_range(segment.segment_id@)
                + old(local).segment_pages_used_total(segment.segment_id@)
        )
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        final(local).page_organization == old(local).page_organization,
        final(local).pages == old(local).pages,
        final(local).psa == old(local).psa,
{
    if !segment.get_allow_decommit(Tracked(&*local)) {
        return;
    }

    if option_decommit_delay() == 0 {
        todo();
    } else {
        proof {
            segment_id_divis(segment);
        }

        let mut mask: CommitMask = CommitMask::empty();
        let (start, full_size) =
            segment_commit_mask(segment.segment_ptr as *mut u8, true, p, size, &mut mask);

        if mask.is_empty() || full_size == 0 {
            return;
        }

        let mut cmask = CommitMask::empty();
        segment_get_mut_main!(segment, local, main => {
            main.commit_mask.create_intersect(&mask, &mut cmask);
            main.decommit_mask.set(&cmask);
        });

        proof {
            const_facts();
            reveal(CommitMask::bytes);
            let segment_id = segment.segment_id@;
            segment_start_mult_commit_size(segment_id);
            assert(segment.segment_ptr as int % COMMIT_SIZE as int == 0);
            assert(mask.bytes(segment_id)
                <= set_int_range(p as int, p + size));
            assert(cmask.bytes(segment_id)
                <= set_int_range(p as int, p + size));
            assert(local.decommit_mask(segment_id).bytes(segment_id) =~=
                old(local).decommit_mask(segment_id).bytes(segment_id) + cmask.bytes(segment_id));
            assert(old(local).mem_chunk_good(segment_id));
            preserve_totals(*old(local), *local, segment_id);
            preserves_mem_chunk_good_except(*old(local), *local, segment.segment_id@);
            assert(mem_chunk_good1(
                local.segments[segment_id].mem,
                segment_id,
                local.commit_mask(segment_id).bytes(segment_id),
                local.decommit_mask(segment_id).bytes(segment_id),
                local.segment_pages_range_total(segment_id),
                local.segment_pages_used_total(segment_id),
            ));
            assert(local.mem_chunk_good(segment.segment_id@));
            assert(local.unused_pages === old(local).unused_pages);
            assert(local.page_organization === old(local).page_organization);
            assert(local.wf_main());
        }
        let ghost local_snap = *local;

        let now = clock_now();
        if segment.get_decommit_expire(Tracked(&*local)) == 0 {
            segment_get_mut_main!(segment, local, main => {
                main.decommit_expire = now.wrapping_add(option_decommit_delay());
            });
            proof { preserves_mem_chunk_good(local_snap, *local); }
        } else if segment.get_decommit_expire(Tracked(&*local)) <= now {
            let ded = option_decommit_extend_delay();
            if segment.get_decommit_expire(Tracked(&*local)).wrapping_add(option_decommit_extend_delay()) <= now {
                segment_delayed_decommit(segment, true, Tracked(&mut *local));
            } else {
                segment_get_mut_main!(segment, local, main => {
                    main.decommit_expire = now.wrapping_add(option_decommit_extend_delay());
                });
                proof { preserves_mem_chunk_good(local_snap, *local); }
            }
        } else {
            segment_get_mut_main!(segment, local, main => {
                main.decommit_expire =
                    main.decommit_expire.wrapping_add(option_decommit_extend_delay());
            });
            proof { preserves_mem_chunk_good(local_snap, *local); }
        }
    }

    assert(local.unused_pages === old(local).unused_pages);
    assert(local.page_organization === old(local).page_organization);
}

pub fn segment_delayed_decommit(
    segment: SegmentPtr,
    force: bool,
    Tracked(local): Tracked<&mut Local>,
)
    requires old(local).wf_main(),
        segment.wf(),
        segment.is_in(*old(local)),
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        final(local).page_organization == old(local).page_organization,
        final(local).pages == old(local).pages,
        final(local).psa == old(local).psa,
{
    if !segment.get_allow_decommit(Tracked(&*local))
        || segment.get_decommit_mask(Tracked(&*local)).is_empty()
    {
        return;
    }

    let now = clock_now();
    if !force && now < segment.get_decommit_expire(Tracked(&*local)) {
        return;
    }

    proof { const_facts(); }

    let mut idx = 0;
    loop
        invariant_except_break
            local.wf_main(),
            segment.wf(),
            segment.is_in(*local),
            0 <= idx < COMMIT_MASK_BITS,
        invariant
            local.wf_main(),
            common_preserves(*old(local), *local),
            local.page_organization == old(local).page_organization,
            local.pages == old(local).pages,
            local.psa == old(local).psa,
    {
        proof {
            const_facts();
            reveal(CommitMask::bytes);
        }

        let mask = segment.get_decommit_mask(Tracked(&*local));
        let (next_idx, count) = mask.next_run(idx);
        if count == 0 {
            break;
        }
        idx = next_idx;

        proof {
            assert((idx + count) * (COMMIT_SIZE as int) <= SEGMENT_SIZE) by (nonlinear_arith)
                requires idx + count <= COMMIT_MASK_BITS, COMMIT_MASK_BITS == 512,
                    COMMIT_SIZE == 65536, SEGMENT_SIZE == 33554432;
            assert(idx * (COMMIT_SIZE as int) + count * (COMMIT_SIZE as int)
                   == (idx + count) * (COMMIT_SIZE as int)) by (nonlinear_arith);
        }
        let p = segment.segment_ptr.addr() + idx * COMMIT_SIZE as usize;
        let size = count * COMMIT_SIZE as usize;
        segment_commitx(segment, false, p, size, Tracked(&mut *local));
    }
}

}
}
mod os_commit {
use core::intrinsics::{unlikely, likely};
use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::raw_ptr::*;
use crate::config::*;
use crate::os_mem::*;
use crate::layout::*;
use crate::types::todo;
use vstd::set_lib::set_int_range;


verus!{

pub fn os_commit(addr: *mut u8, size: usize, Tracked(mem): Tracked<&mut MemChunk>)
    -> (res: (bool, bool))
    requires old(mem).wf(),
        old(mem).os_has_range(addr as int, size as int),
        addr as int % page_size() == 0,
        size as int % page_size() == 0,
        addr as int != 0,
        addr as int + size <= usize::MAX,
        addr@.provenance == old(mem).points_to.provenance(),
    ensures ({
        let (success, is_zero) = res;
        final(mem).wf()
        && final(mem).has_new_pointsto(&*old(mem))
        && final(mem).os.dom() == old(mem).os.dom()
        && final(mem).points_to.provenance() == old(mem).points_to.provenance()
        && (success ==> final(mem).os_has_range_read_write(addr as int, size as int))
    })
{
    os_commitx(addr, size, true, false, Tracked(&mut *mem))
}

pub fn os_decommit(addr: *mut u8, size: usize, Tracked(mem): Tracked<&mut MemChunk>)
    -> (success: bool)
    requires old(mem).wf(),
        old(mem).os_has_range(addr as int, size as int),
        old(mem).pointsto_has_range(addr as int, size as int),
        addr as int % page_size() == 0,
        size as int % page_size() == 0,
        addr as int != 0,
        addr as int + size <= usize::MAX,
        addr@.provenance == old(mem).points_to.provenance(),
    ensures
        final(mem).wf(),
        final(mem).os.dom() =~= old(mem).os.dom(),

        final(mem).points_to.dom().subset_of(old(mem).points_to.dom()),
        final(mem).os_rw_bytes().subset_of(old(mem).os_rw_bytes()),
        final(mem).points_to.provenance() == old(mem).points_to.provenance(),

        old(mem).points_to.dom() - final(mem).points_to.dom()
            =~= old(mem).os_rw_bytes() - final(mem).os_rw_bytes(),
        old(mem).os_rw_bytes() - final(mem).os_rw_bytes()
            <= set_int_range(addr as int, addr as int + size),
{
    let tracked mut t = mem.split(addr as int, size as int);
    let ghost t1 = t;
    let (success, _) = os_commitx(addr, size, false, true, Tracked(&mut t));
    proof {
        mem.join(t);

        assert(t.os_rw_bytes().subset_of(t1.os_rw_bytes()));
        assert forall |p| mem.os_rw_bytes().contains(p)
            implies old(mem).os_rw_bytes().contains(p)
        by {
            if addr as int <= p < addr as int + size {
                assert(t1.os_rw_bytes().contains(p));
                assert(t.os_rw_bytes().contains(p));
                assert(old(mem).os_rw_bytes().contains(p));
            } else {
                assert(old(mem).os_rw_bytes().contains(p));
            }
        }
        assert_sets_equal!(old(mem).points_to.dom() - mem.points_to.dom(),
            old(mem).os_rw_bytes() - mem.os_rw_bytes(),
            p =>
        {
            if (old(mem).points_to.dom() - mem.points_to.dom()).contains(p) {
                if addr as int <= p < addr as int + size {
                    assert((t1.points_to.dom() - t.points_to.dom()).contains(p));
                    assert((t1.os_rw_bytes() - t.os_rw_bytes()).contains(p));
                    assert((old(mem).os_rw_bytes() - mem.os_rw_bytes()).contains(p));
                } else {
                    assert((old(mem).os_rw_bytes() - mem.os_rw_bytes()).contains(p));
                }
            }
            if (old(mem).os_rw_bytes() - mem.os_rw_bytes()).contains(p) {
                if addr as int <= p < addr as int + size {
                    assert((t1.os_rw_bytes() - t.os_rw_bytes()).contains(p));
                    assert((t1.points_to.dom() - t.points_to.dom()).contains(p));
                    assert((old(mem).points_to.dom() - mem.points_to.dom()).contains(p));
                } else {
                    assert((old(mem).points_to.dom() - mem.points_to.dom()).contains(p));
                }
            }
        });
        assert(mem.os_rw_bytes().subset_of(old(mem).os_rw_bytes()));
    }
    success
}

fn os_page_align_areax(conservative: bool, addr: usize, size: usize)
    -> (res: (usize, usize))
    requires
        addr as int % page_size() == 0,
        size as int % page_size() == 0,
        addr != 0,
        addr + size <= usize::MAX,
    ensures
        ({ let (start, csize) = res;
            start as int % page_size() == 0
            && csize as int % page_size() == 0
            && (size != 0 ==> start == addr)
            && (size != 0 ==> csize == size)
            && (size == 0 ==> start == 0 && csize == 0)
        })
{
    if size == 0 || addr == 0 {
        return (0, 0);
    }

    let start = if conservative {
        align_up(addr, get_page_size())
    } else {
        align_down(addr, get_page_size())
    };
    let end = if conservative {
        align_down(addr + size, get_page_size())
    } else {
        align_up(addr + size, get_page_size())
    };

    let diff = end - start;
    if diff <= 0 {
        return (0, 0);
    }
    (start, diff)
}

fn os_commitx(
    addr: *mut u8, size: usize, commit: bool, conservative: bool,
    Tracked(mem): Tracked<&mut MemChunk>
) -> (res: (bool, bool))
    requires old(mem).wf(),
        old(mem).os_has_range(addr as int, size as int),
        addr as int % page_size() as int == 0,
        size as int % page_size() as int == 0,
        addr as int != 0,
        addr as int + size <= usize::MAX,
        !commit ==> old(mem).pointsto_has_range(addr as int, size as int),
        addr@.provenance == old(mem).points_to.provenance()
    ensures
        final(mem).wf(),
        final(mem).os.dom() =~= old(mem).os.dom(),
        commit ==> final(mem).has_new_pointsto(&*old(mem)),
        commit ==> res.0 ==> final(mem).os_has_range_read_write(addr as int, size as int),
        !commit ==> final(mem).points_to.dom().subset_of(old(mem).points_to.dom()),
        !commit ==> final(mem).os_rw_bytes().subset_of(old(mem).os_rw_bytes()),
        !commit ==> old(mem).points_to.dom() - final(mem).points_to.dom()
                    =~= old(mem).os_rw_bytes() - final(mem).os_rw_bytes(),
        final(mem).points_to.provenance() == old(mem).points_to.provenance()
{
    let is_zero = false;
    let (start, csize) = os_page_align_areax(conservative, addr.addr(), size);
    if csize == 0 {
        return (true, is_zero);
    }
    let err = 0;

    let p = addr.with_addr(start);

    let tracked weird_extra = mem.take_points_to_set(
          mem.points_to.dom() - mem.os_rw_bytes());
    let tracked mut exact_mem = mem.split(addr as int, size as int);
    let ghost em = exact_mem;

    if commit {
        mprotect_prot_read_write(p, csize, Tracked(&mut exact_mem));
    } else {
        mprotect_prot_none(p, csize, Tracked(&mut exact_mem));
    }

    proof {
        mem.join(exact_mem);
        mem.give_points_to_range(weird_extra);
        if commit {
        }
        if !commit {



        }
        assert(mem.os.dom() =~= old(mem).os.dom());
    }

    return (true, is_zero);
}

}
}
mod os_alloc {
use core::intrinsics::{unlikely, likely};
use vstd::prelude::*;
use crate::config::*;
use crate::os_mem::*;
use crate::layout::*;
use crate::types::todo;


verus!{

pub fn os_alloc_aligned_offset(
    size: usize,
    alignment: usize,
    offset: usize,
    request_commit: bool,
    allow_large: bool,
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
    requires alignment + page_size() <= usize::MAX,
        size as int % page_size() == 0,
        size == SEGMENT_SIZE,
        alignment as int % page_size() == 0,
    ensures ({ let (addr, is_large, mem) = res;
        addr as int != 0 ==> (
            mem@.wf()
            && mem@.os_has_range(addr as int, size as int)
            && mem@.points_to.provenance() == addr@.provenance
            && addr as int + size <= usize::MAX
            && (request_commit ==> mem@.os_has_range_read_write(addr as int, size as int))
            && (request_commit ==> mem@.pointsto_has_range(addr as int, size as int))
            && (!request_commit ==> mem@.os_has_range_no_read_write(addr as int, size as int))
            && (alignment != 0 ==> (addr as int + offset) % alignment as int == 0)
        )
    })
{
    if offset > SEGMENT_SIZE as usize {
        return (core::ptr::null_mut(), allow_large, Tracked(MemChunk::empty()));
    }

    if offset == 0 {
        return os_alloc_aligned(size, alignment, request_commit, allow_large);
    } else {
        todo(); loop{}


    }
}

pub fn os_good_alloc_size(size: usize) -> (res: usize)
    requires size as int % page_size() == 0,
    ensures res as int % page_size() == 0,
      res >= size,
      size == SEGMENT_SIZE ==> res == SEGMENT_SIZE,
{
    let kib = 1024;
    let mib = 1024*1024;

    let align_size = if size < 512 * kib {
        get_page_size()
    } else if size < 2 * mib {
        64 * kib
    } else if size < 8 * mib {
        256 * kib
    } else if size < 32 * mib {
        mib
    } else {
        4 * mib
    };

    if unlikely(size >= usize::MAX - align_size) {
        size
    } else {
        let x = align_up(size, align_size);
        proof {
            const_facts();
            mod_trans(x as int, align_size as int, page_size());
            if size <= SEGMENT_SIZE {
                assert((size + page_size() - 1) / page_size() <= 8192);
                assert((size + page_size() - 1) / page_size() * page_size() <= SEGMENT_SIZE);
                assert((SEGMENT_SIZE + 0x400000 - 1) / 0x400000 as int == 8) by(compute);
            }
        }
        return x;
    }
}

pub fn os_alloc_aligned(
    size: usize,
    alignment: usize,
    request_commit: bool,
    allow_large: bool
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
    requires
        alignment + page_size() <= usize::MAX,
        size == SEGMENT_SIZE,
        size as int % page_size() == 0,
        alignment as int % page_size() == 0,
    ensures ({ let (addr, is_large, mem) = res;
        addr as int != 0 ==> (
            mem@.wf()
            && mem@.os_has_range(addr as int, size as int)
            && mem@.points_to.provenance() == addr@.provenance
            && addr as int + size <= usize::MAX
            && (request_commit ==> mem@.os_has_range_read_write(addr as int, size as int))
            && (request_commit ==> mem@.pointsto_has_range(addr as int, size as int))
            && (!request_commit ==> mem@.os_has_range_no_read_write(addr as int, size as int))
            && (alignment != 0 ==> addr as int % alignment as int == 0)
        )
    })
{
    if size == 0 {
        return (core::ptr::null_mut(), allow_large, Tracked(MemChunk::empty()));
    }
    let size1 = os_good_alloc_size(size);
    let alignment1 = align_up(alignment, get_page_size());
    proof {
        assert(alignment1 == alignment);
        assert(size1 >= size);
        const_facts();
    }
    os_mem_alloc_aligned(size1, alignment1, request_commit, allow_large)
}

pub fn os_mem_alloc_aligned(
    size: usize,
    alignment: usize,
    request_commit: bool,
    allow_large: bool,
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
    requires
        size as int % page_size() == 0,
        size <= SEGMENT_SIZE,
        alignment as int % page_size() == 0,
    ensures ({ let (addr, is_large, mem) = res;
        addr as int != 0 ==> (
            mem@.wf()
            && mem@.os_exact_range(addr as int, size as int)
            && mem@.points_to.provenance() == addr@.provenance
            && addr as int + size <= usize::MAX
            && (request_commit ==> mem@.os_has_range_read_write(addr as int, size as int))
            && (request_commit ==> mem@.pointsto_has_range(addr as int, size as int))
            && (!request_commit ==> mem@.os_has_range_no_read_write(addr as int, size as int))
            && (alignment != 0 ==> addr as int % alignment as int == 0)
        )
    })
{
    let mut allow_large = allow_large;
    if !request_commit {
        allow_large = false;
    }

    if (!(alignment >= get_page_size() && ((alignment & (alignment - 1)) == 0))) {
        return (core::ptr::null_mut(), allow_large, Tracked(MemChunk::empty()));
    }

    let (p, is_large, Tracked(mem)) = os_mem_alloc(size, alignment, request_commit, allow_large);
    if p.addr() == 0 {
        return (p, is_large, Tracked(mem));
    }

    if p.addr() % alignment != 0 {
        todo();
    }

    (p, is_large, Tracked(mem))
}

fn os_mem_alloc(
    size: usize,
    try_alignment: usize,
    request_commit: bool,
    allow_large: bool,
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
    requires
        size as int % page_size() == 0,
        size <= SEGMENT_SIZE,
        try_alignment == 1 || try_alignment as int % page_size() == 0,
    ensures ({ let (addr, is_large, mem) = res;
        addr as int != 0 ==> (
            mem@.wf()
            && mem@.points_to.provenance() == addr@.provenance
            && addr as int + size <= usize::MAX
            && mem@.os_exact_range(addr as int, size as int)
            && (request_commit ==> mem@.os_has_range_read_write(addr as int, size as int))
            && (request_commit ==> mem@.pointsto_has_range(addr as int, size as int))
            && (!request_commit ==> mem@.os_has_range_no_read_write(addr as int, size as int))
        )
    })
{
    if size == 0 {
        return (core::ptr::null_mut(), allow_large, Tracked(MemChunk::empty()));
    }

    let mut allow_large = allow_large;
    if !request_commit {
        allow_large = false;
    }

    let mut try_alignment = try_alignment;
    if try_alignment == 0 { try_alignment = 1; }

    unix_mmap(core::ptr::null_mut(), size, try_alignment, request_commit, false, allow_large)
}

fn use_large_os_page(size: usize, alignment: usize) -> bool {
    false
}

fn unix_mmap(
    addr: *mut u8,
    size: usize,
    try_alignment: usize,
    prot_rw: bool,
    large_only: bool,
    allow_large: bool,
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
    requires
        addr as int % page_size() == 0,
        size as int % page_size() == 0,
        size <= SEGMENT_SIZE,
        try_alignment == 1 || try_alignment as int % page_size() == 0,
    ensures ({ let (addr, is_large, mem) = res;
        addr as int != 0 ==> (
            mem@.wf()
            && mem@.points_to.provenance() == addr@.provenance
            && mem@.os_exact_range(addr as int, size as int)
            && addr as int + size <= usize::MAX
            && (prot_rw ==> mem@.os_has_range_read_write(addr as int, size as int))
            && (prot_rw ==> mem@.pointsto_has_range(addr as int, size as int))
            && (!prot_rw ==> mem@.os_has_range_no_read_write(addr as int, size as int))
        )
    })
{
    let is_large = true;
    if (large_only || use_large_os_page(size, try_alignment)) && allow_large {
        todo();
    }

    let is_large = false;
    let (p, Tracked(mem)) = unix_mmapx(addr, size, try_alignment, prot_rw);
    if p.addr() != 0 {
        if allow_large && use_large_os_page(size, try_alignment) {
            todo();
        }
        return (p, is_large, Tracked(mem));
    } else {
        todo(); loop{}
    }
}

exec static ALIGNED_BASE: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

#[inline]
fn aligned_base_add(s: usize) -> usize {
    ALIGNED_BASE.fetch_add(s, core::sync::atomic::Ordering::AcqRel)
}

#[inline]
fn aligned_base_cas(s: usize, t: usize) {
    let _ = ALIGNED_BASE.compare_exchange(s, t, core::sync::atomic::Ordering::AcqRel, core::sync::atomic::Ordering::Acquire);
}

const HINT_BASE: usize = (2 as usize) << (40 as usize);
const HINT_AREA: usize = (4 as usize) << (40 as usize);
const HINT_MAX: usize = (30 as usize) << (40 as usize);

fn os_get_aligned_hint(try_alignment: usize, size: usize) -> (hint: usize)
    requires size <= SEGMENT_SIZE,
    ensures try_alignment != 0 ==> hint % try_alignment == 0,
      try_alignment <= 1 ==> hint == 0,
{
    proof { const_facts(); }

    if try_alignment <= 1 || try_alignment > SEGMENT_SIZE as usize {
        return 0;
    }

    let size = align_up(size, SEGMENT_SIZE as usize);
    if size > 1024*1024*1024 {
        return 0;
    }

    let mut hint = aligned_base_add(size);
    if hint == 0 || hint > HINT_MAX {
        let iinit = HINT_BASE;


        let expected = hint.wrapping_add(size);
        aligned_base_cas(expected, iinit);
        hint = aligned_base_add(size);
    }

    if hint % try_alignment != 0 {
        return 0;
    }
    return hint;
}

fn unix_mmapx(
    hint: *mut u8,
    size: usize,
    try_alignment: usize,
    prot_rw: bool,
) -> (res: (*mut u8, Tracked<MemChunk>))
    requires
        hint as int % page_size() == 0,
        size as int % page_size() == 0,
        size <= SEGMENT_SIZE,
        try_alignment > 1 ==> try_alignment as int % page_size() == 0,
    ensures ({ let (addr, mem) = res;
        addr as int != 0 ==> (
            mem@.wf()
            && mem@.os_exact_range(addr as int, size as int)
            && mem@.points_to.provenance() == addr@.provenance
            && addr as int + size <= usize::MAX
            && (prot_rw ==> mem@.os_has_range_read_write(addr as int, size as int))
            && (prot_rw ==> mem@.pointsto_has_range(addr as int, size as int))
            && (!prot_rw ==> mem@.os_has_range_no_read_write(addr as int, size as int))
        )
    })
{
    if hint.addr()  == 0 && INTPTR_SIZE >= 8 {
        let hinti = os_get_aligned_hint(try_alignment, size);
        let hint = hint.with_addr(hinti);
        proof {
            const_facts();
            if try_alignment > 1 {
                mod_trans(hint as int, try_alignment as int, page_size());
            }
        }
        if hint.addr() != 0 {
            let (p, Tracked(mem)) = if prot_rw {
                mmap_prot_read_write(hint, size)
            } else {
                mmap_prot_none(hint, size)
            };
            if p.addr() != MAP_FAILED {
                return (p, Tracked(mem));
            }
        }
    }
    let (p, Tracked(mem)) = if prot_rw {
        mmap_prot_read_write(hint, size)
    } else {
        mmap_prot_none(hint, size)
    };
    if p.addr() != MAP_FAILED {
        return (p, Tracked(mem));
    }

    return (core::ptr::null_mut(), Tracked(mem));
}

}
}
mod page {
#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;
use vstd::pervasive::*;
use vstd::atomic_ghost::*;

use crate::tokens::{Mim, BlockId, DelayState, PageId, PageState};
use crate::types::*;
use crate::layout::*;
use crate::bin_sizes::*;
use crate::config::*;
use crate::page_organization::*;
use crate::linked_list::LL;
use crate::os_mem_util::*;
use crate::commit_segment::*;
use crate::segment::good_count_for_block_size;
use crate::queues::*;

verus!{

pub fn find_page(heap_ptr: HeapPtr, size: usize, huge_alignment: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        page.page_ptr.addr() != 0 ==> page.wf() && page.is_in(*final(local))
            && page.is_used_and_primary(*final(local)),
        page.page_ptr.addr() != 0 ==>
            final(local).pages.index(page.page_id@).inner.value().xblock_size >= size,
{
    proof { const_facts(); }

    let req_size = size;
    if unlikely(req_size > MEDIUM_OBJ_SIZE_MAX as usize || huge_alignment > 0) {
        if unlikely(req_size > MAX_ALLOC_SIZE) {
            return PagePtr::null();
        } else {
            todo(); loop { }
        }
    } else {
        return find_free_page(heap_ptr, size, Tracked(&mut *local));
    }
}

fn find_free_page(heap_ptr: HeapPtr, size: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        size <= MEDIUM_OBJ_SIZE_MAX,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        page.page_ptr.addr() != 0 ==> page.wf() && page.is_in(*final(local))
            && page.is_used_and_primary(*final(local)),
        page.page_ptr.addr() != 0 ==>
            final(local).pages.index(page.page_id@).inner.value().xblock_size >= size,
{
    proof { const_facts(); }
    let pq = bin(size) as usize;

    proof {
        local.page_organization.used_first_is_in(pq as int);
        crate::bin_sizes::bin_size_result(size);
    }

    let mut page = PagePtr { page_ptr: heap_ptr.get_pages(Tracked(&*local))[pq].first, page_id: Ghost(local.page_organization.used_dlist_headers[pq as int].first.unwrap()) };

    if page.page_ptr.addr() != 0 {
        crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));

        if !page.get_inner_ref(Tracked(&*local)).free.is_empty() {
            return page;
        }
    }

    page_queue_find_free_ex(heap_ptr, pq, true, Tracked(&mut *local))
}

fn page_queue_find_free_ex(heap_ptr: HeapPtr, pq: usize, first_try: bool, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        valid_bin_idx(pq as int),
        size_of_bin(pq as int) <= MEDIUM_OBJ_SIZE_MAX,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        page.page_ptr.addr() != 0 ==> page.wf() && page.is_in(*final(local))
            && page.is_used_and_primary(*final(local)),
        page.page_ptr.addr() != 0 ==>
            final(local).pages.index(page.page_id@).inner.value().xblock_size == size_of_bin(pq as int)
{
    let mut page = PagePtr { page_ptr: heap_ptr.get_pages(Tracked(&*local))[pq].first, page_id: Ghost(local.page_organization.used_dlist_headers[pq as int].first.unwrap()) };
    let ghost mut list_idx = 0;
    proof {
        local.page_organization.used_first_is_in(pq as int);
    }

    loop
        invariant
            local.wf(),
            heap_ptr.wf(),
            heap_ptr.is_in(*local),
            common_preserves(*old(local), *local),
            0 <= pq <= BIN_HUGE,
            size_of_bin(pq as int) <= MEDIUM_OBJ_SIZE_MAX,
            page.page_ptr.addr() != 0 ==>
                page.wf()
                && local.page_organization.valid_used_page(page.page_id@, pq as int, list_idx),
    {
        if page.page_ptr.addr() == 0 {
            break;
        }

        let next_ptr = page.get_next(Tracked(&*local));
        let ghost page_id = page.page_id@;
        let ghost next_id = local.page_organization.pages[page_id].dlist_entry.unwrap().next.unwrap();
        proof {
            local.page_organization.used_next_is_in(page.page_id@, pq as int, list_idx);
            size_of_bin_mult_word_size(pq as int);
        }

        crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));

        if !page.get_inner_ref(Tracked(&*local)).free.is_empty() {
            break;
        }

        if page.get_inner_ref(Tracked(&*local)).capacity < page.get_inner_ref(Tracked(&*local)).reserved {
            crate::alloc_generic::page_extend_free(page, Tracked(&mut *local));
            break;
        }

        page_to_full(page, heap_ptr, pq, Tracked(&mut *local), Ghost(list_idx), Ghost(next_id));

        page = PagePtr { page_ptr: next_ptr, page_id: Ghost(next_id) };

        proof {
        }
    }

    if page.page_ptr.addr() == 0 {
        let page = page_fresh(heap_ptr, pq, Tracked(&mut *local));
        if page.page_ptr.addr() == 0 && first_try {
            return page_queue_find_free_ex(heap_ptr, pq, false, Tracked(&mut *local))
        } else {
            return page;
        }
    } else {
        let ghost old_local = *local;
        page_get_mut_inner!(page, local, inner => {
            inner.set_retire_expire(0);
        });
        proof { preserves_mem_chunk_good(old_local, *local); }
        return page;
    }
}

fn page_fresh(heap_ptr: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        valid_bin_idx(pq as int),
        size_of_bin(pq as int) <= MEDIUM_OBJ_SIZE_MAX,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        page.page_ptr.addr() != 0 ==> page.wf() && page.is_in(*final(local))
            && page.is_used_and_primary(*final(local)),
        page.page_ptr.addr() != 0 ==>
            final(local).pages.index(page.page_id@).inner.value().xblock_size == size_of_bin(pq as int)

{
    proof { size_of_bin_bounds(pq as int); }
    let block_size = heap_ptr.get_pages(Tracked(&*local))[pq].block_size;
    page_fresh_alloc(heap_ptr, pq, block_size, 0, Tracked(&mut *local))
}

fn page_fresh_alloc(heap_ptr: HeapPtr, pq: usize, block_size: usize, page_alignment: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        2 <= block_size,
        valid_bin_idx(pq as int),
        block_size == size_of_bin(pq as int),
        block_size <= MEDIUM_OBJ_SIZE_MAX,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        page.page_ptr.addr() != 0 ==> page.wf() && page.is_in(*final(local))
            && page.is_used_and_primary(*final(local)),
        page.page_ptr.addr() != 0 ==>
            final(local).pages.index(page.page_id@).inner.value().xblock_size == block_size,
{
    let tld_ptr = heap_ptr.get_ref(Tracked(&*local)).tld_ptr;
    let page_ptr = crate::segment::segment_page_alloc(heap_ptr, block_size, page_alignment, tld_ptr, Tracked(&mut *local));
    if page_ptr.page_ptr.addr() == 0 {
        return page_ptr;
    }

    let full_block_size: usize = block_size;
    let tld_ptr = heap_ptr.get_ref(Tracked(&*local)).tld_ptr;

    proof {
        smallest_bin_fitting_size_size_of_bin(pq as int);
        size_of_bin_mult_word_size(pq as int);
        if pq != BIN_HUGE {
            size_of_bin_bounds_not_huge(pq as int);
        }
        lemma_bin_sizes_constants();
    }

    page_init(heap_ptr, page_ptr, full_block_size, tld_ptr, Tracked(&mut *local), Ghost(pq as int));
    page_queue_push(heap_ptr, pq, page_ptr, Tracked(&mut *local));

    return page_ptr;
}

fn page_init(heap_ptr: HeapPtr, page_ptr: PagePtr, block_size: usize, tld_ptr: TldPtr, Tracked(local): Tracked<&mut Local>, Ghost(pq): Ghost<int>)
    requires
        old(local).wf_main(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        page_ptr.wf(),
        page_ptr.is_in(*old(local)),
        old(local).page_organization.popped == Popped::Ready(page_ptr.page_id@, true),
        block_size != 0,
        block_size % 8 == 0,
        block_size <= u32::MAX,
        valid_bin_idx(pq),
        size_of_bin(pq) == block_size,
        page_init_is_committed(page_ptr.page_id@, *old(local)),
        good_count_for_block_size(block_size as int,
              old(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int),
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        page_ptr.is_used(*final(local)),
        final(local).page_organization.popped == Popped::Used(page_ptr.page_id@, true),
        final(local).page_organization.pages[page_ptr.page_id@].page_header_kind == Some(PageHeaderKind::Normal(pq as int, block_size as int)),
{
    let ghost mut next_state;
    proof {
        next_state = PageOrg::take_step::set_range_to_used(local.page_organization, PageHeaderKind::Normal(pq as int, block_size as int));
    }

    let ghost page_id = page_ptr.page_id@;
    let ghost n_slices = local.page_organization.pages[page_id].count.unwrap();
    let ghost n_blocks = n_slices * SLICE_SIZE / block_size as int;
    let ghost range = page_id.range_from(0, n_slices as int);
    assert forall |pid| range.contains(pid) implies local.unused_pages.dom().contains(pid) by {
        assert(local.page_organization.pages.dom().contains(pid));
        assert(local.page_organization.pages[pid].is_used == false);
    }
    let ghost new_page_state_map = Map::new(
            range,
            |pid: PageId| PageState {
                offset: pid.idx - page_id.idx,
                block_size: block_size as nat,
                num_blocks: 0,
                shared_access: arbitrary(),
                is_enabled: false,
            });
    assert(n_slices > 0);
    assert(range.contains(page_id));

    let count = page_ptr.get_count(Tracked(&*local));

    let tracked thread_token = local.take_thread_token();
    let tracked (
        Tracked(thread_token),
        Tracked(delay_token),
        Tracked(heap_of_page_token),
    ) = local.instance.create_page_mk_tokens(
            local.thread_id,
            page_id,
            n_slices as nat,
            block_size as nat,
            new_page_state_map,
            thread_token,
        );

    unused_page_get_mut!(page_ptr, local, page => {
        let tracked (Tracked(emp_inst), Tracked(emp_x), Tracked(emp_y)) = BoolAgree::Instance::initialize(false);
        let ghost g = (Ghost(local.instance), Ghost(page_ptr.page_id@), Tracked(emp_x), Tracked(emp_inst));
        page.xheap = AtomicHeapPtr {
            atomic: AtomicPtr::new(Ghost(g), heap_ptr.heap_ptr, Tracked((emp_y, Some(heap_of_page_token)))),
            instance: Ghost(local.instance), page_id: Ghost(page_ptr.page_id@), emp: Tracked(emp_x), emp_inst: Tracked(emp_inst), };
        page.xthread_free.enable(Ghost(block_size as nat), Ghost(page_ptr.page_id@),
            Tracked(local.instance.clone()), Tracked(delay_token));
    });

    unused_page_get_mut_inner!(page_ptr, local, inner => {
        proof {
            const_facts();

            local.page_organization.get_count_bound(page_ptr.page_id@);

            let start_offs = start_offset(block_size as int);
            start_offset_le_slice_size(block_size as int);
            assert((count * SLICE_SIZE - start_offs) / block_size as int <= u16::MAX) by(nonlinear_arith)
                requires (count * SLICE_SIZE) <= block_size * u16::MAX,
                  count >= 0, SLICE_SIZE >= 0, block_size > 0, start_offs >= 0;
        }

        inner.xblock_size = block_size as u32;
        let start_offs = calculate_start_offset(block_size);
        let page_size = count * SLICE_SIZE as u32 - start_offs;
        inner.reserved = (page_size / block_size as u32) as u16;

        inner.free.set_ghost_data(
            Ghost(page_id), Ghost(true), Ghost(local.instance), Ghost(block_size as nat), Ghost(None));
        inner.local_free.set_ghost_data(
            Ghost(page_id), Ghost(true), Ghost(local.instance), Ghost(block_size as nat), Ghost(None));


        assert(page_size as int / block_size as int * block_size as int <= page_size) by(nonlinear_arith)
            requires page_size >= 0, block_size > 0;
    });

    proof {
        let tracked new_psa_map = local.unused_pages.tracked_remove_keys(range);
        let ghost new_page_state_map2 = Map::new(
            range,
            |pid: PageId| PageState {
                is_enabled: true,
                shared_access: new_psa_map[pid],
                .. thread_token.value().pages[pid]
            });

        let tracked thread_token = local.instance.page_enable(
                local.thread_id,
                page_id,
                n_slices as nat,
                new_page_state_map2,
                new_psa_map,
                thread_token,
                new_psa_map,
            );

        local.thread_token = thread_token;
        local.page_organization = next_state;
        local.psa = local.psa.insert(page_id, new_psa_map[page_id]);




        preserves_mem_chunk_good_except(*old(local), *local, page_id.segment_id);
        preserves_mem_chunk_on_set_used(*old(local), *local, page_id);

    }

    crate::alloc_generic::page_extend_free(page_ptr, Tracked(&mut *local))
}

fn page_queue_of(page: PagePtr, Tracked(local): Tracked<&Local>) -> (res: (HeapPtr, usize, Ghost<int>))
    requires local.wf(),
        page.wf(), page.is_in(*local),
        page.is_used_and_primary(*local),
    ensures ({ let (heap, pq, list_idx) = res; {
        &&& heap.wf()
        &&& heap.is_in(*local)
        &&& (valid_bin_idx(pq as int) || pq == BIN_FULL)
        &&& local.page_organization.valid_used_page(page.page_id@, pq as int, list_idx@)
    }}),

{
    let is_in_full = page.get_inner_ref(Tracked(&*local)).get_in_full();

    let ghost mut list_idx;
    proof {
        if is_in_full {
            list_idx = local.page_organization.marked_full_is_in(page.page_id@);
        } else {
            list_idx = local.page_organization.marked_unfull_is_in(page.page_id@);
        }
        const_facts();
    }

    let bin = if is_in_full {
        BIN_FULL as usize
    } else {
        bin(page.get_inner_ref(Tracked(&*local)).xblock_size as usize) as usize
    };

    let heap = page.get_heap(Tracked(&*local));
    (heap, bin, Ghost(list_idx))
}

const MAX_RETIRE_SIZE: u32 = MEDIUM_OBJ_SIZE_MAX as u32;

pub fn page_retire(page: PagePtr, Tracked(local): Tracked<&mut Local>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        old(local).pages[page.page_id@].inner.value().used == 0,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
{
    let (heap, pq, Ghost(list_idx)) = page_queue_of(page, Tracked(&*local));
    if likely(
        page.get_inner_ref(Tracked(&*local)).xblock_size <= MAX_RETIRE_SIZE
          && !(heap.get_pages(Tracked(&*local))[pq].block_size > MEDIUM_OBJ_SIZE_MAX as usize)
    )
    {
        if heap.get_pages(Tracked(&*local))[pq].last.addr() == page.page_ptr.addr() &&
            heap.get_pages(Tracked(&*local))[pq].first.addr() == page.page_ptr.addr()
        {
            let RETIRE_CYCLES = 8;
            page_get_mut_inner!(page, local, inner => {
                let xb = inner.xblock_size as u64;
                inner.set_retire_expire(1 + (if xb <= SMALL_OBJ_SIZE_MAX { RETIRE_CYCLES } else { RETIRE_CYCLES/4 }));
            });

            if pq < heap.get_page_retired_min(Tracked(&*local)) {
                heap.set_page_retired_min(Tracked(&mut *local), pq);
            }
            if pq > heap.get_page_retired_max(Tracked(&*local)) {
                heap.set_page_retired_max(Tracked(&mut *local), pq);
            }

            proof { preserves_mem_chunk_good(*old(local), *local); }
            return;
        }
    }

    page_free(page, pq, false, Tracked(&mut *local), Ghost(list_idx));
}

fn page_free(page: PagePtr, pq: usize, force: bool, Tracked(local): Tracked<&mut Local>, Ghost(list_idx): Ghost<int>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        old(local).page_organization.valid_used_page(page.page_id@, pq as int, list_idx),
        old(local).pages[page.page_id@].inner.value().used == 0,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
{
    page_get_mut_inner!(page, local, inner => {
        inner.set_has_aligned(false);
    });
    proof { preserves_mem_chunk_good(*old(local), *local); }
    let heap = page.get_heap(Tracked(&*local));

    page_queue_remove(heap, pq, page, Tracked(&mut *local), Ghost(list_idx), Ghost(arbitrary()));

    let tld = heap.get_ref(Tracked(&*local)).tld_ptr;
    crate::segment::segment_page_free(page, force, tld, Tracked(&mut *local));
}

fn page_to_full(page: PagePtr, heap: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>,
      Ghost(list_idx): Ghost<int>, Ghost(next_id): Ghost<PageId>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        heap.wf(), heap.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        valid_bin_idx(pq as int),
        old(local).page_organization.valid_used_page(page.page_id@, pq as int, list_idx),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        old(local).page_organization.valid_used_page(next_id, pq as int, list_idx + 1) ==>
            final(local).page_organization.valid_used_page(next_id, pq as int, list_idx),
{
    page_queue_enqueue_from(heap, BIN_FULL as usize, pq, page, Tracked(&mut *local),
        Ghost(list_idx), Ghost(next_id));
    crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));
}

pub fn page_unfull(page: PagePtr, Tracked(local): Tracked<&mut Local>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        old(local).pages[page.page_id@].inner.value().in_full(),
    ensures final(local).wf(),
        common_preserves(*old(local), *final(local)),
{
    let heap = page.get_heap(Tracked(&*local));
    proof {
        local.page_organization.marked_full_is_in(page.page_id@);
        const_facts();
    }
    let pq = bin(page.get_inner_ref(Tracked(&mut *local)).xblock_size as usize);
    let ghost list_idx = local.page_organization.marked_full_is_in(page.page_id@);
    page_queue_enqueue_from(heap, pq as usize, BIN_FULL as usize, page,
        Tracked(&mut *local), Ghost(list_idx), Ghost(arbitrary()));
}

fn page_queue_enqueue_from(heap: HeapPtr, to: usize, from: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>, Ghost(list_idx): Ghost<int>, Ghost(next_id): Ghost<PageId>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        heap.wf(), heap.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        old(local).page_organization.valid_used_page(page.page_id@, from as int, list_idx),
        (valid_bin_idx(from as int) && to == BIN_FULL)
          || (match old(local).page_organization.pages[page.page_id@].page_header_kind {
            Some(PageHeaderKind::Normal(b, bsize)) =>
              from == BIN_FULL
                && to == b,
            None => false,
          })
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        old(local).page_organization.valid_used_page(next_id, from as int, list_idx + 1) ==>
            final(local).page_organization.valid_used_page(next_id, from as int, list_idx),
        page.is_used_and_primary(*final(local)),
{
    page_queue_remove(heap, from, page, Tracked(&mut *local), Ghost(list_idx), Ghost(next_id));
    page_queue_push_back(heap, to, page, Tracked(&mut *local), Ghost(next_id), Ghost(from as int), Ghost(list_idx));
}

pub fn page_try_use_delayed_free(page: PagePtr, delay: usize, override_never: bool, Tracked(local): Tracked<&Local>) -> bool
    requires local.wf(), page.wf(), page.is_in(*local),
        page.is_used_and_primary(*local),
        delay == 0, !override_never,
{
    page.get_ref(Tracked(&*local)).xthread_free.try_use_delayed_free(delay, override_never)
}

}
}
mod queues {
#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;
use vstd::pervasive::*;

use crate::tokens::{Mim, BlockId, DelayState, PageId, PageState};
use crate::types::*;
use crate::layout::*;
use crate::bin_sizes::*;
use crate::config::*;
use crate::page_organization::*;
use crate::linked_list::LL;
use crate::os_mem_util::*;
use crate::commit_segment::*;
use crate::segment::good_count_for_block_size;

verus!{


#[verifier::external_body]
pub fn page_queue_remove(heap: HeapPtr, pq: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>, Ghost(list_idx): Ghost<int>, Ghost(next_id): Ghost<PageId>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        heap.wf(), heap.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        old(local).page_organization.valid_used_page(page.page_id@, pq as int, list_idx),
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        page.is_in(*final(local)),
        final(local).page_organization.popped == Popped::Used(page.page_id@, true),
        final(local).page_organization.pages[page.page_id@].page_header_kind
            == old(local).page_organization.pages[page.page_id@].page_header_kind,
        final(local).tld_id == old(local).tld_id,
        old(local).page_organization.valid_used_page(next_id, pq as int, list_idx + 1) ==>
            final(local).page_organization.valid_used_page(next_id, pq as int, list_idx),
        old(local).pages[page.page_id@].inner.value().used
            == final(local).pages[page.page_id@].inner.value().used,
{
   unimplemented!()
}

#[verifier::external_body]
pub fn page_queue_push(heap: HeapPtr, pq: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main(),
        pq == BIN_FULL || valid_bin_idx(pq as int),
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        (match old(local).page_organization.pages[page.page_id@].page_header_kind.unwrap() {
              PageHeaderKind::Normal(b, bsize) => {
                  (pq == BIN_FULL || pq as int == b)
                  && valid_bin_idx(b as int)
                  && bsize == crate::bin_sizes::size_of_bin(b)
                  && bsize <= MEDIUM_OBJ_SIZE_MAX
              }
          }),
        heap.wf(),
        heap.is_in(*old(local)),
        page.wf(),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        page.wf(),
        page.is_in(*final(local)),
        page.is_used_and_primary(*final(local)),
        final(local).pages.index(page.page_id@).inner.value().xblock_size ==
            old(local).pages.index(page.page_id@).inner.value().xblock_size,
        final(local).tld_id == old(local).tld_id,
{
    unimplemented!()
}

#[verifier::external_body]
pub fn page_queue_push_back(heap: HeapPtr, pq: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>, Ghost(other_id): Ghost<PageId>, Ghost(other_pq): Ghost<int>, Ghost(other_list_idx): Ghost<int>)
    requires
        old(local).wf_main(),
        pq == BIN_FULL || valid_bin_idx(pq as int),
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        (match old(local).page_organization.pages[page.page_id@].page_header_kind.unwrap() {
              PageHeaderKind::Normal(b, bsize) => {
                  (pq == BIN_FULL || b == pq as int)
                  && valid_bin_idx(b as int)
                  && bsize == crate::bin_sizes::size_of_bin(b)
                  && bsize <= MEDIUM_OBJ_SIZE_MAX
              }
          }),
        heap.wf(),
        heap.is_in(*old(local)),
        page.wf(),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        page.wf(),
        page.is_in(*final(local)),
        page.is_used_and_primary(*final(local)),
        final(local).pages.index(page.page_id@).inner.value().xblock_size ==
            old(local).pages.index(page.page_id@).inner.value().xblock_size,
        final(local).tld_id == old(local).tld_id,

        old(local).page_organization.valid_used_page(other_id, other_pq, other_list_idx) ==>
            final(local).page_organization.valid_used_page(other_id, other_pq, other_list_idx),
{
    unimplemented!()
}



spec fn local_direct_update(loc1: Local, loc2: Local, i: int, j: int, pq: int) -> bool {
    &&& loc2 == Local { heap: loc2.heap, .. loc1 }
    &&& loc2.heap == HeapLocalAccess { pages_free_direct: loc2.heap.pages_free_direct, .. loc1.heap }
    &&& loc1.heap.pages_free_direct.id() == loc2.heap.pages_free_direct.id()
    &&& pfd_direct_update(
          loc1.heap.pages_free_direct.value()@,
          loc2.heap.pages_free_direct.value()@, i, j,
            loc1.page_empty_global@.s.points_to.ptr(),
            loc1.heap.pages.value()@[pq].first)
}

spec fn pfd_direct_update(pfd1: Seq<*mut Page>, pfd2: Seq<*mut Page>, i: int, j: int, emp: *mut Page, p: *mut Page) -> bool {
    &&& pfd1.len() == pfd2.len() == PAGES_DIRECT
    &&& (forall |k|
        #![trigger(pfd1.index(k))]
        #![trigger(pfd2.index(k))]
      0 <= k < pfd1.len() && !(i <= k < j) ==> pfd1[k] == pfd2[k])
    &&& (forall |k| #![trigger pfd2.index(k)]
        0 <= k < pfd2.len() && i <= k < j ==>
            pages_free_direct_match(pfd2[k], p, emp))
}

#[verifier::external_body]
proof fn holds_on_present_value(local: Local, pq: int)
    requires local.wf_main(),
        valid_bin_idx(pq as int) || pq == BIN_FULL,
    ensures
        pq != BIN_FULL ==> (forall |k: int| k < PAGES_DIRECT &&
            pfd_lower(pq as int) <= k <= pfd_upper(pq as int) ==>
                pages_free_direct_match(
                    #[trigger] local.heap.pages_free_direct.value()@[k],
                    local.heap.pages.value()@[pq].first,
                    local.page_empty_global@.s.points_to.ptr())
        )
{
    unimplemented!()
}

fn heap_queue_first_update(heap: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>, Ghost(old_p): Ghost<*mut Page>)
    requires
        old(local).wf_basic(),
        heap.wf(),
        heap.is_in(*old(local)),
        valid_bin_idx(pq as int) || pq == BIN_FULL,
        pq != BIN_FULL ==> (forall |k: int| k < PAGES_DIRECT &&
            pfd_lower(pq as int) <= k <= pfd_upper(pq as int) ==>
                pages_free_direct_match(
                    #[trigger] old(local).heap.pages_free_direct.value()@[k],
                    old_p, old(local).page_empty_global@.s.points_to.ptr())
        ),
    ensures
        pq == BIN_FULL ==> *final(local) == *old(local),
        pq != BIN_FULL ==> local_direct_update(*old(local), *final(local),
            pfd_lower(pq as int) as int,
            pfd_upper(pq as int) as int + 1,
            pq as int)
{
    proof { const_facts(); }

    let size = heap.get_pages(Tracked(&*local))[pq].block_size;
    if size > SMALL_SIZE_MAX {
        proof {
            if pq != BIN_FULL {
                out_of_small_range(pq as int);
            }
        }
        return;
    }

    let mut page_ptr = heap.get_pages(Tracked(&*local))[pq].first;
    if page_ptr.addr() == 0 {
        let (_page, Tracked(emp)) = heap.get_page_empty(Tracked(&*local));
        page_ptr = _page;
    }

    let idx = size / 8;

    if heap.get_pages_free_direct(Tracked(&*local))[idx].addr() == page_ptr.addr() {

        return;
    }

    let start = if idx <= 1 {
        0
    } else {
        let b = bin(size);
        let prev = pq - 1;


        let prev_block_size = heap.get_pages(Tracked(&*local))[prev].block_size;
        proof {
            const_facts();
            if prev != 0 {
                size_of_bin_bounds_not_huge(prev as int);
                assert(valid_bin_idx(prev as int));
                assert(prev_block_size == size_of_bin(prev as int));
            }
        }
        let s = 1 + prev_block_size / 8;
        s
    };

    proof {
        if idx <= 1 {
            size_le_8_implies_idx_eq_1(pq as int);
            assert(pq == 1);
            assert(start == pfd_lower(pq as int));
        } else {
            size_gt_8_implies_idx_gt_1(pq as int);
            assert(pq > 1);
            assert(start == pfd_lower(pq as int));
        }
        assert(idx == pfd_upper(pq as int));
        pfd_lower_le_upper(pq as int);
        assert(start <= idx);
    }

    let mut sz = start;
    while sz <= idx
        invariant
            local.wf_basic(),
            heap.wf(),
            heap.is_in(*local),
            start <= sz <= idx + 1,
            idx < PAGES_DIRECT,
            local_direct_update(*old(local), *local, start as int, sz as int, pq as int),
            page_ptr as int != 0,
            pages_free_direct_match(page_ptr,
                old(local).heap.pages.value()@[pq as int].first,
                local.page_empty_global@.s.points_to.ptr()),
    {
        let ghost prev_local = *local;
        heap_get_pages_free_direct!(heap, local, pages_free_direct => {
            pages_free_direct[sz] = page_ptr;
        });

        sz += 1;
    }
}


}
}
mod init {
#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;
use vstd::cell::pcell::*;
use vstd::shared::Shared;

use crate::tokens::{Mim, BlockId, DelayState, ThreadState, HeapState, HeapId, TldId, ThreadId};
use crate::types::*;
use crate::layout::*;
use crate::linked_list::*;
use crate::dealloc_token::*;
use crate::alloc_generic::*;
use crate::os_mem_util::*;
use crate::config::*;
use crate::bin_sizes::*;
use crate::page_organization::*;
use crate::os_mem::*;
use crate::thread::*;

verus!{

pub tracked struct Global {
    pub(crate) tracked instance: Mim::Instance,
    pub(crate) tracked my_inst: Mim::my_inst,
}

impl Global {
    #[verifier::type_invariant]
    pub(crate) closed spec fn wf(&self) -> bool {
        self.my_inst.instance_id() == self.instance.id()
        && self.my_inst.value() == self.instance.id()
    }

    pub open(crate) spec fn wf_right_to_use_thread(&self, right: RightToUseThread, tid: ThreadId) -> bool {
        right.instance_id() == self.instance.id() && right.element() == tid
    }

    pub open(crate) spec fn inst(&self) -> MimInst {
        self.instance
    }
}

type RightToUseThread = Mim::right_to_use_thread;
type MimInst = Mim::Instance;




#[verifier::external_body]
pub proof fn global_init() -> (tracked res: (Global, Map<ThreadId, Mim::right_to_use_thread>))
    ensures
        forall |tid: ThreadId| #[trigger] res.1.dom().contains(tid)
          && res.0.wf_right_to_use_thread(res.1[tid], tid)
{
    unimplemented!()
}

pub fn heap_init(Tracked(global): Tracked<Global>,
      Tracked(right): Tracked<Mim::right_to_use_thread>,
      Tracked(cur_thread): Tracked<IsThread>
) -> (res: (HeapPtr, Tracked<Option<Local>>))
    requires global.wf_right_to_use_thread(right, cur_thread@),
    ensures ({ let (heap, local_opt) = res; {
        heap.heap_ptr.addr() != 0 ==>
            local_opt@.is_some()
            && local_opt@.unwrap().wf()
            && local_opt@.unwrap().inst() == global.inst()
            && heap.wf()
            && heap.is_in(local_opt@.unwrap())
    }})
{
    proof { use_type_invariant(&global); }
    increment_thread_count();

    let (addr, Tracked(mem)) = thread_data_alloc();
    if addr.addr() == 0 {
        return (HeapPtr { heap_ptr: core::ptr::null_mut(), heap_id: Ghost(arbitrary()) }, Tracked(None));
    }

    proof {
        const_facts();
        assert(SIZEOF_HEAP == vstd::layout::size_of::<Heap>());
        assert(SIZEOF_TLD == vstd::layout::size_of::<Tld>());
        assert(addr as int % vstd::layout::align_of::<Heap>() as int == 0);
        assert((addr as usize + SIZEOF_HEAP) as int % vstd::layout::align_of::<Tld>() as int == 0);
    }
    vstd::layout::layout_for_type_is_valid::<Heap>();
    vstd::layout::layout_for_type_is_valid::<Tld>();

    let tracked points_to_heap_raw = mem.take_points_to_range(addr as int, SIZEOF_HEAP as int);
    let tracked points_to_tld_raw = mem.take_points_to_range(addr as usize + SIZEOF_HEAP, SIZEOF_TLD as int);
    let tracked mut points_to_heap = points_to_heap_raw.into_typed(addr as usize);
    let tracked mut points_to_tld = points_to_tld_raw.into_typed((addr as int + SIZEOF_HEAP) as usize);
    let heap_ptr = addr as *mut Heap;
    let tld_ptr = addr.with_addr(addr.addr() + SIZEOF_HEAP) as *mut Tld;

    let tracked (_, _, Tracked(uniq_reservation_tok)) = global.instance.reserve_uniq_identifier();
    let heap = HeapPtr { heap_ptr, heap_id: Ghost(HeapId { id: heap_ptr.addr() as nat, provenance: heap_ptr@.provenance, uniq: uniq_reservation_tok.element().uniq }) };
    let tld = TldPtr { tld_ptr, tld_id: Ghost(TldId { id: tld_ptr.addr() as nat, provenance: tld_ptr@.provenance }) };

    let page_empty_stuff = init_empty_page_ptr();
    let EmptyPageStuff { ptr: page_empty_ptr, pfa: Tracked(page_empty_ptr_access) } = page_empty_stuff;

    let mut pages_free_direct = pages_free_direct_tmp();
    let mut pages = pages_tmp();
    let mut span_queue_headers = span_queue_headers_tmp();

    let mut i = 0;
    while i < PAGES_DIRECT
        invariant 0 <= i <= PAGES_DIRECT,
          forall |j: int| 0 <= j < i ==> pages_free_direct[j] == page_empty_ptr,
    {
        pages_free_direct[i] = page_empty_ptr;
        i = i + 1;
    }

    let mut i = 0;
    while i < SEGMENT_BIN_MAX + 1
        invariant 0 <= i <= SEGMENT_BIN_MAX + 1,
          forall |j: int| 0 <= j < i ==> (#[trigger] span_queue_headers[j]).first.addr() == 0
              && span_queue_headers[j].last.addr() == 0,
    {
        span_queue_headers[i] = SpanQueueHeader {
            first: core::ptr::null_mut(),
            last: core::ptr::null_mut(),
        };
        i = i + 1;
    }



    let (pages_free_direct_pcell, Tracked(pages_free_direct_pointsto)) = PCell::new(pages_free_direct);
    let (pages_pcell, Tracked(pages_pointsto)) = PCell::new(pages);
    let (page_count_pcell, Tracked(page_count_pointsto)) = PCell::new(0);
    let (page_retired_min_pcell, Tracked(page_retired_min_pointsto)) = PCell::new(0);
    let (page_retired_max_pcell, Tracked(page_retired_max_pointsto)) = PCell::new(0);

    let (thread_id, Tracked(is_thread)) = crate::thread::thread_id();
    proof {
        is_thread.agrees(cur_thread);
    }

    ptr_mut_write(heap_ptr, Tracked(&mut points_to_heap), Heap {
        tld_ptr: tld,
        pages_free_direct: pages_free_direct_pcell,
        pages: pages_pcell,
        thread_delayed_free: ThreadLLSimple::empty(Ghost(global.instance), Ghost(heap.heap_id@)),
        thread_id,
        arena_id: 0,
        page_count: page_count_pcell,
        page_retired_min: page_retired_min_pcell,
        page_retired_max: page_retired_max_pcell,
        no_reclaim: false,
        page_empty_ptr,
    });

    ptr_mut_write(tld_ptr, Tracked(&mut points_to_tld), Tld {
        heap_backing: heap_ptr,
        segments: SegmentsTld {
            span_queue_headers,
            count: 0,
            peak_count: 0,
            current_size: 0,
            peak_size: 0,
        },
    });

    let tracked heap_shared_access = HeapSharedAccess { points_to: points_to_heap };
    assert(global.instance.id() == right.instance_id());
    assert(right.element() == thread_id);

    let tracked (Tracked(thread_token), Tracked(checked_token)) = global.instance.create_thread_mk_tokens(
            thread_id,
            ThreadState {
                heap_id: heap.heap_id@,
                heap: HeapState {
                    shared_access: heap_shared_access,
                },
                segments: Map::empty(),
                pages: Map::empty(),
            },
            &global.my_inst,
            right,
            heap_shared_access,
            uniq_reservation_tok);

    let ghost page_organization = PageOrg::take_step::initialize();
    let tracked my_inst = global.my_inst.clone();
    let tracked local = Local {
        thread_id,
        my_inst,
        is_thread,
        instance: global.instance,
        thread_token,
        checked_token,
        heap_id: heap.heap_id@,
        heap: HeapLocalAccess {
            pages_free_direct: pages_free_direct_pointsto,
            pages: pages_pointsto,
            page_count: page_count_pointsto,
            page_retired_min: page_retired_min_pointsto,
            page_retired_max: page_retired_max_pointsto,
        },
        tld_id: tld.tld_id@,
        tld: points_to_tld,
        segments: Map::tracked_empty(),
        pages: Map::tracked_empty(),
        psa: Map::empty(),
        unused_pages: Map::tracked_empty(),
        page_organization,
        page_empty_global: page_empty_ptr_access,
    };

    proof {
        let emp = local.page_empty_global@.s.points_to.ptr();
        let pfd = local.heap.pages_free_direct.value()@;
        let pages = local.heap.pages.value()@;
        assert forall |wsize|
          0 <= wsize < pfd.len() implies
            pages_free_direct_match(
                (#[trigger] pfd[wsize]),
                pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first,
                emp)
        by {
            bounds_for_smallest_bin_fitting_size(wsize * INTPTR_SIZE);
        }

        assert(pages_free_direct_is_correct(
            local.heap.pages_free_direct.value()@,
            local.heap.pages.value()@,
            emp));
        assert(local.heap.wf_basic(local.heap_id, local.thread_token.value().heap, local.tld_id, local.instance.id()));
        assert(local.heap.wf(local.heap_id, local.thread_token.value().heap, local.tld_id, local.instance.id(), local.page_empty_global@.s.points_to.ptr()));
        assert(local.wf_main());
        assert(local.wf());
    }

    (heap, Tracked(Some(local)))
}


impl PageQueue {
    #[inline]
    fn empty(wsize: usize) -> (pq: PageQueue)
        requires wsize < 0x1_0000_0000_0000,
        ensures
          pq.first.addr() == 0,
          pq.last.addr() == 0,
          pq.block_size == wsize * INTPTR_SIZE
    {
        assert(INTPTR_SIZE as usize == 8);
        PageQueue {
            first: core::ptr::null_mut(),
            last: core::ptr::null_mut(),
            block_size: wsize * INTPTR_SIZE as usize,
        }
    }
}

#[inline]
fn pages_tmp() -> (pages: [PageQueue; 75])
    ensures pages@.len() == BIN_FULL + 1,
      forall |p| 0 <= p < pages@.len() ==> (#[trigger] pages[p]).first.addr() == 0
          && pages[p].last.addr() == 0
          && (valid_bin_idx(p) ==> pages[p].block_size == size_of_bin(p)),
      pages[0].block_size == 8,
      pages[BIN_FULL as int].block_size == 8 * (524288 + 2),
{
    proof { const_facts(); }
    let pages = [
        PageQueue::empty(1),

        PageQueue::empty(1),
        PageQueue::empty(2),
        PageQueue::empty(3),
        PageQueue::empty(4),
        PageQueue::empty(5),
        PageQueue::empty(6),
        PageQueue::empty(7),
        PageQueue::empty(8),

        PageQueue::empty(10),
        PageQueue::empty(12),
        PageQueue::empty(14),
        PageQueue::empty(16),
        PageQueue::empty(20),
        PageQueue::empty(24),
        PageQueue::empty(28),
        PageQueue::empty(32),

        PageQueue::empty(40),
        PageQueue::empty(48),
        PageQueue::empty(56),
        PageQueue::empty(64),
        PageQueue::empty(80),
        PageQueue::empty(96),
        PageQueue::empty(112),
        PageQueue::empty(128),

        PageQueue::empty(160),
        PageQueue::empty(192),
        PageQueue::empty(224),
        PageQueue::empty(256),
        PageQueue::empty(320),
        PageQueue::empty(384),
        PageQueue::empty(448),
        PageQueue::empty(512),

        PageQueue::empty(640),
        PageQueue::empty(768),
        PageQueue::empty(896),
        PageQueue::empty(1024),
        PageQueue::empty(1280),
        PageQueue::empty(1536),
        PageQueue::empty(1792),
        PageQueue::empty(2048),

        PageQueue::empty(2560),
        PageQueue::empty(3072),
        PageQueue::empty(3584),
        PageQueue::empty(4096),
        PageQueue::empty(5120),
        PageQueue::empty(6144),
        PageQueue::empty(7168),
        PageQueue::empty(8192),

        PageQueue::empty(10240),
        PageQueue::empty(12288),
        PageQueue::empty(14336),
        PageQueue::empty(16384),
        PageQueue::empty(20480),
        PageQueue::empty(24576),
        PageQueue::empty(28672),
        PageQueue::empty(32768),

        PageQueue::empty(40960),
        PageQueue::empty(49152),
        PageQueue::empty(57344),
        PageQueue::empty(65536),
        PageQueue::empty(81920),
        PageQueue::empty(98304),
        PageQueue::empty(114688),
        PageQueue::empty(131072),

        PageQueue::empty(163840),
        PageQueue::empty(196608),
        PageQueue::empty(229376),
        PageQueue::empty(262144),
        PageQueue::empty(327680),
        PageQueue::empty(393216),
        PageQueue::empty(458752),
        PageQueue::empty(524288),

        PageQueue::empty(524288 + 1),
        PageQueue::empty(524288 + 2),
    ];

    proof {
        assert forall |p| 0 <= p < pages@.len() implies (#[trigger] pages[p]).first.addr() == 0
            && pages[p].last.addr() == 0
            && (valid_bin_idx(p) ==> pages[p].block_size == size_of_bin(p))
        by {
            if valid_bin_idx(p) {
                reveal(size_of_bin);
                if p <= 1 { assert(p == 1); assert(size_of_bin(1) == 8) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 2 { assert(p == 2); assert(size_of_bin(2) == 16) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 3 { assert(p == 3); assert(size_of_bin(3) == 24) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 4 { assert(p == 4); assert(size_of_bin(4) == 32) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 5 { assert(p == 5); assert(size_of_bin(5) == 40) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 6 { assert(p == 6); assert(size_of_bin(6) == 48) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 7 { assert(p == 7); assert(size_of_bin(7) == 56) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 8 { assert(p == 8); assert(size_of_bin(8) == 64) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 9 { assert(p == 9); assert(size_of_bin(9) == 80) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 10 { assert(p == 10); assert(size_of_bin(10) == 96) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 11 { assert(p == 11); assert(size_of_bin(11) == 112) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 12 { assert(p == 12); assert(size_of_bin(12) == 128) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 13 { assert(p == 13); assert(size_of_bin(13) == 160) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 14 { assert(p == 14); assert(size_of_bin(14) == 192) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 15 { assert(p == 15); assert(size_of_bin(15) == 224) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 16 { assert(p == 16); assert(size_of_bin(16) == 256) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 17 { assert(p == 17); assert(size_of_bin(17) == 320) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 18 { assert(p == 18); assert(size_of_bin(18) == 384) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 19 { assert(p == 19); assert(size_of_bin(19) == 448) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 20 { assert(p == 20); assert(size_of_bin(20) == 512) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 21 { assert(p == 21); assert(size_of_bin(21) == 640) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 22 { assert(p == 22); assert(size_of_bin(22) == 768) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 23 { assert(p == 23); assert(size_of_bin(23) == 896) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 24 { assert(p == 24); assert(size_of_bin(24) == 1024) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 25 { assert(p == 25); assert(size_of_bin(25) == 1280) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 26 { assert(p == 26); assert(size_of_bin(26) == 1536) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 27 { assert(p == 27); assert(size_of_bin(27) == 1792) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 28 { assert(p == 28); assert(size_of_bin(28) == 2048) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 29 { assert(p == 29); assert(size_of_bin(29) == 2560) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 30 { assert(p == 30); assert(size_of_bin(30) == 3072) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 31 { assert(p == 31); assert(size_of_bin(31) == 3584) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 32 { assert(p == 32); assert(size_of_bin(32) == 4096) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 33 { assert(p == 33); assert(size_of_bin(33) == 5120) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 34 { assert(p == 34); assert(size_of_bin(34) == 6144) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 35 { assert(p == 35); assert(size_of_bin(35) == 7168) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 36 { assert(p == 36); assert(size_of_bin(36) == 8192) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 37 { assert(p == 37); assert(size_of_bin(37) == 10240) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 38 { assert(p == 38); assert(size_of_bin(38) == 12288) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 39 { assert(p == 39); assert(size_of_bin(39) == 14336) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 40 { assert(p == 40); assert(size_of_bin(40) == 16384) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 41 { assert(p == 41); assert(size_of_bin(41) == 20480) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 42 { assert(p == 42); assert(size_of_bin(42) == 24576) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 43 { assert(p == 43); assert(size_of_bin(43) == 28672) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 44 { assert(p == 44); assert(size_of_bin(44) == 32768) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 45 { assert(p == 45); assert(size_of_bin(45) == 40960) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 46 { assert(p == 46); assert(size_of_bin(46) == 49152) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 47 { assert(p == 47); assert(size_of_bin(47) == 57344) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 48 { assert(p == 48); assert(size_of_bin(48) == 65536) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 49 { assert(p == 49); assert(size_of_bin(49) == 81920) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 50 { assert(p == 50); assert(size_of_bin(50) == 98304) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 51 { assert(p == 51); assert(size_of_bin(51) == 114688) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 52 { assert(p == 52); assert(size_of_bin(52) == 131072) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 53 { assert(p == 53); assert(size_of_bin(53) == 163840) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 54 { assert(p == 54); assert(size_of_bin(54) == 196608) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 55 { assert(p == 55); assert(size_of_bin(55) == 229376) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 56 { assert(p == 56); assert(size_of_bin(56) == 262144) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 57 { assert(p == 57); assert(size_of_bin(57) == 327680) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 58 { assert(p == 58); assert(size_of_bin(58) == 393216) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 59 { assert(p == 59); assert(size_of_bin(59) == 458752) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 60 { assert(p == 60); assert(size_of_bin(60) == 524288) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 61 { assert(p == 61); assert(size_of_bin(61) == 655360) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 62 { assert(p == 62); assert(size_of_bin(62) == 786432) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 63 { assert(p == 63); assert(size_of_bin(63) == 917504) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 64 { assert(p == 64); assert(size_of_bin(64) == 1048576) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 65 { assert(p == 65); assert(size_of_bin(65) == 1310720) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 66 { assert(p == 66); assert(size_of_bin(66) == 1572864) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 67 { assert(p == 67); assert(size_of_bin(67) == 1835008) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 68 { assert(p == 68); assert(size_of_bin(68) == 2097152) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 69 { assert(p == 69); assert(size_of_bin(69) == 2621440) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 70 { assert(p == 70); assert(size_of_bin(70) == 3145728) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 71 { assert(p == 71); assert(size_of_bin(71) == 3670016) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 72 { assert(p == 72); assert(size_of_bin(72) == 4194304) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else { assert(p == 73); assert(size_of_bin(73) == 8 * (524288 + 1)) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                assert(pages[p].block_size == size_of_bin(p));
            }
        }
    }

    pages
}

fn pages_free_direct_tmp() -> [*mut Page; 129] {
    [
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
    ]
}

fn span_queue_headers_tmp() -> [SpanQueueHeader; 32] {
    [
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
    ]
}

fn thread_data_alloc()
    -> (res: (*mut u8, Tracked<MemChunk>))
    ensures ({ let (p, mc) = res; {
        p.addr() != 0 ==> (
            mc@.pointsto_has_range(p as int, SIZEOF_HEAP + SIZEOF_TLD)
            && p as int + page_size() <= usize::MAX
            && p as int % 4096 == 0
            && p@.provenance == mc@.points_to.provenance()
        )
    }})
{
    let (addr, Tracked(mc)) = crate::os_mem::mmap_prot_read_write(core::ptr::null_mut(), 4096);

    if addr.addr() == MAP_FAILED {
        todo();
    }

    proof {
    }
    (addr, Tracked(mc))
}



struct EmptyPageStuff {
    ptr: *mut Page,
    pfa: Tracked<Shared<PageFullAccess>>,
}

impl EmptyPageStuff {
    pub closed spec fn wf(&self) -> bool {
        self.pfa@@.wf_empty_page_global()
        && self.pfa@@.s.points_to.ptr() == self.ptr
        && self.ptr.addr() != 0
    }
}


fn init_empty_page_ptr() -> (e: EmptyPageStuff)
    ensures e.wf(),
{
    let (pt, Tracked(mut mc)) = crate::os_mem::mmap_prot_read_write(core::ptr::null_mut(), 4096);

    if pt.addr() == MAP_FAILED {
        todo();
    }

    proof { const_facts(); }

    assert(set_int_range(pt as int, pt as int + 4096) <= mc.range_os_rw());
    assert(set_int_range(pt as int, pt as int + 4096) <= mc.range_points_to());
    assert(mc.pointsto_has_range(pt as int, 4096));
    assert(mc.pointsto_has_range(pt as int, SIZEOF_PAGE_HEADER as int));
    let tracked points_to_raw = mc.take_points_to_range(pt as int, SIZEOF_PAGE_HEADER as int);
    proof {
        assert(SIZEOF_PAGE_HEADER == vstd::layout::size_of::<Page>());
        mod_trans(pt as int, 4096,
            vstd::layout::align_of::<Page>() as int);
        assert(pt as int % vstd::layout::align_of::<Page>() as int == 0);
    }
    vstd::layout::layout_for_type_is_valid::<Page>();
    let tracked mut points_to = points_to_raw.into_typed::<Page>(pt as usize);
    proof { points_to.is_nonnull(); }

    let (count_pcell, Tracked(count_perm)) = PCell::new(0);
    let (prev_pcell, Tracked(prev_perm)) = PCell::new(std::ptr::null_mut());
    let (next_pcell, Tracked(next_perm)) = PCell::new(std::ptr::null_mut());
    let (inner_pcell, Tracked(inner_perm)) = PCell::new(PageInner {
        flags0: 0,
        flags1: 0,
        flags2: 0,
        capacity: 0,
        reserved: 0,
        free: LL::empty(),
        used: 0,
        xblock_size: 0,
        local_free: LL::empty(),
    });

    let tracked fake_inst = global_init().0.instance;

    let page_ptr = pt as *mut Page;
    ptr_mut_write(page_ptr, Tracked(&mut points_to), Page {
        count: count_pcell,
        offset: 0,
        inner: inner_pcell,
        xthread_free: ThreadLLWithDelayBits::empty(Tracked(fake_inst)),
        xheap: AtomicHeapPtr::empty(),
        prev: prev_pcell,
        next: next_pcell,
        padding: 0,
    });
    let Tracked(exposed) = expose_provenance(page_ptr);

    let tracked pfa = Shared::new(PageFullAccess {
        s: PageSharedAccess { points_to, exposed },
        l: PageLocalAccess {
            count: count_perm,
            inner: inner_perm,
            prev: prev_perm,
            next: next_perm,
        },
    });
    EmptyPageStuff { ptr: page_ptr, pfa: Tracked(pfa) }
}







exec static THREAD_COUNT: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);


#[inline]
fn increment_thread_count() {
    THREAD_COUNT.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
}

#[inline]
pub fn current_thread_count() -> usize {
    THREAD_COUNT.load(core::sync::atomic::Ordering::Relaxed)
}


}
}

use vstd::prelude::*;

verus!{
}

#[verifier::external_body]
fn big_test(heap: crate::types::HeapPtr) {
    for j in 0 .. 30 {
        dbg!(j);
        let mut v = Vec::new();
        for i in 0 .. 100000 {
            let (p, _, _) = crate::alloc_fast::heap_malloc(heap, 100, Tracked::assume_new());
            v.push(p);
        }
        for (i, p) in v.iter().enumerate() {
            crate::free::free(*p, Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new());
        }
    }
}



use core::ffi::c_void;
use crate::types::todo;

#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn verus_mi_thread_init_default_heap() -> *mut c_void {


    let (heap, _) = crate::init::heap_init(Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new());
    heap.heap_ptr as *mut c_void
}

#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn verus_mi_heap_malloc(heap: *mut c_void, size: usize) -> *mut c_void {
    let heap = crate::types::HeapPtr {
        heap_ptr: heap as *mut crate::types::Heap,
        heap_id: Ghost::assume_new(),
    };
    let (p, _, _) = crate::alloc_fast::heap_malloc(heap, size, Tracked::assume_new());
    p as *mut c_void
}

#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn verus_mi_free(ptr: *mut c_void) {
    let p = ptr as *mut u8;
    crate::free::free(p, Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new());
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn malloc(size: usize) -> *mut c_void {
    verus_mi_heap_malloc(get_default_heap(), size)
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn calloc(number: usize, size: usize) -> *mut c_void {
    unsafe {
        let (sz, ov) = count_size_overflow(number, size);
        let p = malloc(sz);
        if p != core::ptr::null_mut() {
            core::ptr::write_bytes(p, 0, sz)
        }
        p
    }
}

verus!{

#[inline(always)]
#[verifier::external_body]
#[verus::line_count::ignore]
pub fn count_size_overflow(count: usize, size: usize) -> (x: (usize, bool))
    ensures x.1 <==> (count * size >= usize::MAX),
          !x.1 ==> x.0 == count * size
{
    if count == 1 {
        (size, false)
    } else {
        count.overflowing_mul(size)
    }
}

}


#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn realloc(ptr: *mut c_void, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn free(ptr: *mut c_void) {
    verus_mi_free(ptr)
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn reallocf(ptr: *mut c_void, newsize: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn malloc_size(ptr: *mut c_void) -> usize {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn malloc_usable_size(ptr: *mut c_void) -> usize {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn valloc(size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn vfree(ptr: *mut c_void) {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn malloc_good_size(size: usize) -> usize {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn posix_memalign(p: *mut *mut c_void, alignment: usize, size: usize) -> i32 {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn aligned_alloc(alignment: usize, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn cfree(ptr: *mut c_void) {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn pvalloc(size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn reallocarray(ptr: *mut c_void, count: usize, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn reallocarr(ptr: *mut c_void, count: usize, size: usize) -> i32 {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn memalign(alignment: usize, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn _aligned_malloc(alignment: usize, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_malloc(size: usize) -> *mut c_void {
    verus_mi_heap_malloc(get_default_heap(), size)
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_calloc(number: usize, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_realloc(ptr: *mut c_void, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_free(ptr: *mut c_void) {
    verus_mi_free(ptr)
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_cfree(ptr: *mut c_void) {
    verus_mi_free(ptr)
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_valloc(size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_pvalloc(size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_memalign(alignment: usize, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __posix_memalign(p: *mut *mut c_void, alignment: usize, size: usize) -> i32 {
    todo(); loop{}
}












#[cfg(feature = "override_system_allocator")]
extern "C" {
    #[verifier::external]
    #[no_mangle]
    pub fn get_default_heap() -> *mut c_void;

    #[verifier::external]
    #[no_mangle]
    pub fn thread_id_helper() -> u64;




}

fn main() {}
