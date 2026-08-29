// SPDX-License-Identifier: MPL-2.0
//
// Standalone Verus version of `wait.rs`.
//
// Run with the same Verus flags and dependencies used by the `ostd` target,
// e.g. `cargo dv verify --targets ostd -- --verify-only-module sync::wait_inline`.
#![feature(proc_macro_hygiene)]

extern crate alloc;

use vstd::atomic_ghost::*;
use vstd::cell::pcell::PointsTo;
use vstd::prelude::*;
use vstd::resource::{
    Loc,
    ghost_var::{GhostVar, GhostVarAuth},
};

use alloc::{collections::VecDeque, sync::Arc};
use core::{marker::PhantomData, ops::{Deref, DerefMut}};

verus! {

// Inlined from `sync/guard.rs`.
// `SpinLock` only carries this type parameter in this standalone file; the
// platform-specific interrupt guard implementation is not needed by `wait.rs`.
pub struct LocalIrqDisabled(());

// Inlined from `sync/spin.rs`.
pub trait SpinLockPredicate<T>: Sized {
    type State;

    spec fn inv(self, value: T, state: Self::State) -> bool;
}

// Inlined from `sync/spin.rs`.
// These declarations preserve the spin-lock proof interface used below. Their
// executable implementations are intentionally external in this standalone
// harness.
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(G)]
pub struct SpinLock<T, G, P: SpinLockPredicate<T>> {
    predicate: Ghost<P>,
    phantom: PhantomData<(T, G)>,
}

impl<T, G, P: SpinLockPredicate<T>> SpinLock<T, G, P> {
    #[verifier::external_body]
    pub const fn new_with_pred(
        val: T,
        Ghost(predicate): Ghost<P>,
        Tracked(state): Tracked<P::State>,
    ) -> (res: Self)
        requires
            predicate.inv(val, state),
        ensures
            res.predicate() == predicate,
    {
        unimplemented!()
    }

    pub closed spec fn predicate(self) -> P {
        self.predicate@
    }

    #[verus_spec(ret =>
        ensures
            ret.predicate() == self.predicate(),
            ret.predicate_inv(),
    )]
    #[verifier::external_body]
    pub fn lock(&self) -> SpinLockGuard<'_, T, G, P> {
        unimplemented!()
    }
}

// Inlined from `sync/spin.rs`.
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(G)]
pub struct SpinLockGuard<'a, T, G, P: SpinLockPredicate<T>> {
    lock: &'a SpinLock<T, G, P>,
    tracked_perm: Tracked<PointsTo<T>>,
    tracked_state: Tracked<Option<P::State>>,
}

impl<T, G, P: SpinLockPredicate<T>> SpinLockGuard<'_, T, G, P> {
    pub closed spec fn value(self) -> T {
        *self.tracked_perm@.value()
    }

    pub closed spec fn predicate_state(self) -> P::State
        recommends
            self.has_predicate_state(),
    {
        self.tracked_state@->0
    }

    pub closed spec fn has_predicate_state(self) -> bool {
        self.tracked_state@ is Some
    }

    pub closed spec fn predicate(self) -> P {
        self.lock.predicate()
    }

    pub open spec fn predicate_inv(self) -> bool {
        &&& self.has_predicate_state()
        &&& self.predicate().inv(self.value(), self.predicate_state())
    }

    pub open spec fn view(self) -> T {
        self.value()
    }

    #[verus_spec(ret =>
        with
            -> state: Tracked<P::State>,
        requires
            old(self).has_predicate_state(),
        ensures
            state@ == old(self).predicate_state(),
            !final(self).has_predicate_state(),
            final(self).value() == old(self).value(),
            final(self).predicate() == old(self).predicate(),
    )]
    #[verifier::external_body]
    pub fn take_predicate_state(&mut self) {
        unimplemented!()
    }

    #[verus_spec(
        with
            Tracked(state): Tracked<P::State>,
        requires
            !old(self).has_predicate_state(),
        ensures
            final(self).has_predicate_state(),
            final(self).predicate_state() == state,
            final(self).value() == old(self).value(),
            final(self).predicate() == old(self).predicate(),
    )]
    #[verifier::external_body]
    pub fn put_predicate_state(&mut self) {
        unimplemented!()
    }

    #[verus_spec(
        requires
            self.predicate_inv(),
    )]
    #[verifier::external_body]
    pub fn drop(self) {
        unimplemented!()
    }
}

impl<T, G, P: SpinLockPredicate<T>> Deref for SpinLockGuard<'_, T, G, P> {
    type Target = T;

    #[verus_spec(returns self.view())]
    #[verifier::external_body]
    fn deref(&self) -> &T {
        unimplemented!()
    }
}

impl<T, G, P: SpinLockPredicate<T>> DerefMut for SpinLockGuard<'_, T, G, P> {
    #[verus_spec(ret =>
        ensures
            final(self).view() == *final(ret),
            old(self).view() == *ret,
            final(self).has_predicate_state() == old(self).has_predicate_state(),
            old(self).has_predicate_state() ==> final(self).predicate_state()
                == old(self).predicate_state(),
            final(self).predicate() == old(self).predicate(),
    )]
    #[verifier::external_body]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unimplemented!()
    }
}

// Inlined from `task/mod.rs`.
#[derive(Debug)]
pub struct Task {}

// Inlined from `sync/wait.rs`.
struct WakersPredicate {
    ghost_id: Ghost<Loc>,
}

impl WakersPredicate {
    closed spec fn id(self) -> Loc {
        self.ghost_id@
    }
}

impl SpinLockPredicate<VecDeque<Arc<Waker>>> for WakersPredicate {
    type State = GhostVar<int>;

    /// While the spin lock is unlocked, its mirror records the exact queue
    /// length. Lock acquisition transfers the mirror to the guard, allowing
    /// the relation to be updated together with `num_wakers` before unlock.
    closed spec fn inv(self, wakers: VecDeque<Arc<Waker>>, mirror: GhostVar<int>) -> bool {
        &&& mirror.id() == self.id()
        &&& mirror@ == wakers@.len()
    }
}

struct_with_invariants! {

/// A wait queue.
pub struct WaitQueue {
    num_wakers: AtomicU32<_, GhostVarAuth<int>, _>,
    wakers: SpinLock<VecDeque<Arc<Waker>>, LocalIrqDisabled, WakersPredicate>,
}

closed spec fn wf(self) -> bool {
    invariant on num_wakers with (wakers) is (v: u32, g: GhostVarAuth<int>) {
        &&& g.id() == wakers.predicate().id()
        &&& g@ == v as int
    }
}
}

impl WaitQueue {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        self.wf()
    }
}

impl WaitQueue {
    pub const fn new() -> Self {
        proof_decl! {
            let tracked (count_auth, count_mirror) = GhostVarAuth::<int>::new(0int);
        }
        let ghost ghost_id = count_auth.id();
        let wakers = SpinLock::new_with_pred(
            VecDeque::new(),
            Ghost(WakersPredicate { ghost_id: Ghost(ghost_id) }),
            Tracked(count_mirror),
        );
        WaitQueue { num_wakers: AtomicU32::new(Ghost(wakers), 0, Tracked(count_auth)), wakers }
    }

    #[track_caller]
    #[verus_spec(ret =>
        requires
            cond.requires(()),
        ensures
            cond.ensures((), Some(ret)),
    )]
    #[verifier::exec_allows_no_decreases_clause]
    pub fn wait_until<F, R>(&self, mut cond: F) -> R where F: FnMut() -> Option<R> {
        if let Some(res) = cond() {
            return res;
        }
        let (waiter, _) = Waiter::new_pair();
        #[verus_spec(invariant
            cond.requires(()),
        )]
        loop {
            self.enqueue(waiter.waker());
            if let Some(res) = cond() {
                assert(cond.ensures((), Some(res)));
                proof! { admit(); }  // FIXME: https://github.com/verus-lang/verus/issues/2295
                return res;
            }
            waiter.wait();
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn wake_one(&self) -> (r: bool) {
        proof! { use_type_invariant(self); }
        if self.is_empty() {
            return false;
        }
        loop invariant self.wf(), {
            let mut wakers = self.wakers.lock();
            let Some(waker) = wakers.pop_front() else {
                wakers.drop();
                return false;
            };
            proof_decl! { let tracked mut count_mirror: GhostVar<int>; }
            #[verus_spec(with => Tracked(count_mirror))]
            wakers.take_predicate_state();
            atomic_with_ghost! {
                self.num_wakers => fetch_sub(1);
                update prev -> next;
                ghost count_auth => {
                    count_auth.agree(&count_mirror);
                    assert(count_mirror@ == wakers.value()@.len() + 1);
                    count_auth.update(&mut count_mirror, next);
                }
            };
            #[verus_spec(with Tracked(count_mirror))]
            wakers.put_predicate_state();
            wakers.drop();
            if waker.wake_up() { return true; }
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn wake_all(&self) -> (r: usize) {
        proof! { use_type_invariant(self); }
        if self.is_empty() { return 0; }
        let mut num_woken = 0;
        loop invariant self.wf(), {
            let mut wakers = self.wakers.lock();
            let Some(waker) = wakers.pop_front() else {
                wakers.drop();
                break;
            };
            proof_decl! { let tracked mut count_mirror: GhostVar<int>; }
            #[verus_spec(with => Tracked(count_mirror))]
            wakers.take_predicate_state();
            atomic_with_ghost! {
                self.num_wakers => fetch_sub(1);
                update prev -> next;
                ghost count_auth => {
                    count_auth.agree(&count_mirror);
                    assert(count_mirror@ == wakers.value()@.len() + 1);
                    count_auth.update(&mut count_mirror, next);
                }
            };
            #[verus_spec(with Tracked(count_mirror))]
            wakers.put_predicate_state();
            wakers.drop();
            if waker.wake_up() {
                assume(num_woken < usize::MAX);
                num_woken += 1;
            }
        }
        num_woken
    }

    fn is_empty(&self) -> bool {
        proof! { use_type_invariant(self); }
        self.num_wakers.load() == 0
    }

    #[doc(hidden)]
    pub fn enqueue(&self, waker: Arc<Waker>) {
        proof! { use_type_invariant(self); }
        let mut wakers = self.wakers.lock();
        wakers.push_back(waker);
        proof_decl! { let tracked mut count_mirror: GhostVar<int>; }
        #[verus_spec(with => Tracked(count_mirror))]
        wakers.take_predicate_state();
        atomic_with_ghost! {
            self.num_wakers => fetch_add(1);
            update prev -> next;
            ghost count_auth => {
                assume(prev < u32::MAX);
                count_auth.update(&mut count_mirror, next);
            }
        };
        #[verus_spec(with Tracked(count_mirror))]
        wakers.put_predicate_state();
        wakers.drop();
    }
}

impl Default for WaitQueue {
    fn default() -> Self { Self::new() }
}

// Inlined from `sync/wait.rs`.
pub struct Waiter { waker: Arc<Waker> }
impl !Send for Waiter {}
impl !Sync for Waiter {}
impl Waiter {
    pub closed spec fn rel_waker(self, waker: Arc<Waker>) -> bool { self.waker == waker }
}

struct_with_invariants! {
pub struct Waker {
    has_woken: AtomicBool<_, (), _>,
    task: Arc<Task>,
}
closed spec fn wf(self) -> bool {
    invariant on has_woken is (_v: bool, _g: ()) { true }
}
}

impl Waker {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool { self.wf() }
}

#[verus_verify]
impl Waiter {
    #[verus_spec(ret => ensures ret.0.rel_waker(ret.1))]
    pub fn new_pair() -> (Self, Arc<Waker>) {
        let waker = Arc::new(Waker {
            has_woken: AtomicBool::new(Ghost(()), false, Tracked(())),
            task: Arc::new(Task {}),
        });
        let waiter = Self { waker: waker.clone() };
        (waiter, waker)
    }

    #[track_caller]
    pub fn wait(&self) { self.waker.do_wait(); }

    #[verus_spec(ret =>
        requires cond.requires(()), cancel_cond.requires(()),
        ensures match ret {
            Ok(res) => cond.ensures((),Some(res)),
            Err(e) => cancel_cond.ensures((), Err(e)),
        },
    )]
    #[track_caller]
    #[verifier::exec_allows_no_decreases_clause]
    pub fn wait_until_or_cancelled<F, R, FCancel, E>(
        &self, mut cond: F, cancel_cond: FCancel,
    ) -> core::result::Result<R, E> where
        F: FnMut() -> Option<R>, FCancel: Fn() -> core::result::Result<(), E>,
    {
        #[verus_spec(invariant cond.requires(()), cancel_cond.requires(()))]
        loop {
            if let Some(res) = cond() {
                assert(cond.ensures((), Some(res))) by { admit(); };
                proof! { admit(); }
                return Ok(res);
            };
            if let Err(e) = cancel_cond() {
                self.waker.close();
                proof! { admit(); }
                return cond().ok_or(e);
            }
            self.wait();
        }
    }

    #[verus_spec(ret => ensures self.rel_waker(ret))]
    pub fn waker(&self) -> Arc<Waker> { self.waker.clone() }
    pub fn task(&self) -> &Arc<Task> { &self.waker.task }
    pub fn drop(self) { self.waker.close(); }
}

impl Waker {
    #[verifier::external_body]
    pub fn wake_up(&self) -> bool { unimplemented!() }
    #[track_caller]
    #[verifier::external_body]
    fn do_wait(&self) { unimplemented!() }
    fn close(&self) {
        proof! { use_type_invariant(self); }
        let _ = atomic_with_ghost! {
            self.has_woken => swap(true);
            update _prev -> _next;
            ghost _g => {}
        };
    }
}

} // verus!

// Standalone entry point so `verus wait_inline.rs` uses its default binary
// crate mode. The verified wait-queue definitions above do not use it.
fn main() {}
