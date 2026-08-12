#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::atomic_ghost::*;
use vstd::imap::*;
use vstd::multiset::*;
use vstd::prelude::*;

use verus_state_machines_macros::tokenized_state_machine;

verus! {

tokenized_state_machine!{
    DistRwLock<T> {
        fields {
            #[sharding(constant)]
            pub rc_width: int,

            #[sharding(storage_option)]
            pub storage: Option<T>,

            #[sharding(variable)]
            pub exc_locked: bool,

            #[sharding(imap)]
            pub ref_counts: IMap<int, int>,

            #[sharding(option)]
            pub exc_pending: Option<int>,

            #[sharding(option)]
            pub exc_guard: Option<()>,

            #[sharding(multiset)]
            pub shared_pending: Multiset<int>,

            #[sharding(multiset)]
            pub shared_guard: Multiset<(int, T)>,
        }

        init!{
            initialize(rc_width: int, init_t: T) {
                require(0 < rc_width);
                init rc_width = rc_width;
                init storage = Option::Some(init_t);
                init exc_locked = false;
                init ref_counts = IMap::new(
                    |i| 0 <= i < rc_width,
                    |i| 0,
                );
                init exc_pending = Option::None;
                init exc_guard = Option::None;
                init shared_pending = Multiset::empty();
                init shared_guard = Multiset::empty();
            }
        }

        transition!{
            exc_start() {
                require(!pre.exc_locked);
                update exc_locked = true;
                add exc_pending += Some(0);
            }
        }

        transition!{
            exc_check_count() {
                remove exc_pending -= Some(let r);
                have ref_counts >= [r => 0];

                add exc_pending += Some(r + 1);
            }
        }

        transition!{
            exc_finish() {
                remove exc_pending -= Some(pre.rc_width);
                add exc_guard += Some(());
                withdraw storage -= Some(let _);
            }
        }

        transition!{
            exc_release(t: T) {
                update exc_locked = false;
                remove exc_guard -= Some(());
                deposit storage += Some(t);
            }
        }

        transition!{
            shared_start(r: int) {
                remove ref_counts -= [r => let rc];
                add ref_counts += [r => rc + 1];
                add shared_pending += {r};
            }
        }

        transition!{
            shared_finish(r: int) {
                require(!pre.exc_locked);
                remove shared_pending -= {r};

                birds_eye let t = pre.storage->0;
                add shared_guard += {(r, t)};
            }
        }

        transition!{
            shared_release(val: (int, T)) {
                remove shared_guard -= {val};

                let r = val.0;
                remove ref_counts -= [r => let rc];
                add ref_counts += [r => rc - 1];

                assert(rc > 0) by {
                    assert(0 <= r < pre.rc_width);
                    assert(pre.shared_guard.count(val) > 0);
                    assert(Self::filter_r(pre.shared_guard, r).count(val) > 0);
                    assert(Self::filter_r(pre.shared_guard, r).len() > 0);
                    assert(pre.ref_counts.index(r) > 0);
                };
            }
        }

        property!{
            do_guard(val: (int, T)) {
                have shared_guard >= {val};
                guard storage >= Some(val.1);
            }
        }

        ///// Invariants and proofs

        #[invariant]
        pub fn ref_counts_domain(&self) -> bool {
            &&& 0 < self.rc_width
            &&& forall |i: int| 0 <= i < self.rc_width <==> self.ref_counts.dom().contains(i)
        }

        #[invariant]
        pub fn exc_inv(&self) -> bool {
            &&& self.exc_locked <==> (self.exc_pending is Some || self.exc_guard is Some)
            &&& self.storage is Some <==> self.exc_guard is None
            &&& if let Option::Some(cur_r) = self.exc_pending {
                &&& 0 <= cur_r <= self.rc_width
                &&& self.exc_guard is None
                &&& forall |x| self.shared_guard.count(x) > 0 ==> !(0 <= x.0 < cur_r)
            } else {
                true
            }
        }

        #[invariant]
        pub fn shared_pending_in_range(&self) -> bool {
            forall |r| self.shared_pending.count(r) > 0 ==> (0 <= r < self.rc_width)
        }

        #[invariant]
        pub fn shared_guard_in_range(&self) -> bool {
            forall |x| self.shared_guard.count(x) > 0 ==> (0 <= x.0 < self.rc_width)
        }

        #[invariant]
        pub fn shared_inv_agree(&self) -> bool {
            forall |v| #[trigger] self.shared_guard.count(v) > 0 ==>
                self.storage == Option::Some(v.1)
        }

        pub closed spec fn filter_r(shared_guard: Multiset<(int, T)>, r: int) -> Multiset<(int, T)> {
            shared_guard.filter(|val: (int, T)| val.0 == r)
        }

        #[invariant]
        pub fn shared_counts_agree(&self) -> bool {
            forall |r| 0 <= r < self.rc_width ==>
                #[trigger] self.ref_counts.index(r) ==
                    self.shared_pending.count(r) as int +
                        Self::filter_r(self.shared_guard, r).len() as int
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, rc_width: int, init_t: T) {
            // After initialization:
            // - rc_width = rc_width (parameter)
            // - storage = Some(init_t)
            // - exc_locked = false
            // - ref_counts = IMap::new(|i| 0 <= i < rc_width, |i| 0)  // All zeros
            // - exc_pending = None
            // - exc_guard = None
            // - shared_pending = empty multiset
            // - shared_guard = empty multiset

            // Prove ref_counts_domain
            assert(post.ref_counts_domain()) by {
                assert forall |i: int| 0 <= i < post.rc_width <==> post.ref_counts.dom().contains(i) by {
                    assert(post.ref_counts.dom() =~= ISet::new(|j| 0 <= j < rc_width));
                }
            }
            
            // Prove exc_inv
            assert(post.exc_inv()) by {
                assert(!post.exc_locked);
                assert(post.exc_pending is None);
                assert(post.exc_guard is None);
                assert(post.storage is Some);
                
                // Check the biconditionals:
                assert(post.exc_locked <==> (post.exc_pending is Some || post.exc_guard is Some));
                assert(post.storage is Some <==> post.exc_guard is None);
                
                // The conditional part is vacuously true since exc_pending is None
            }
            
            // Prove shared_pending_in_range
            assert(post.shared_pending_in_range()) by {
                assert forall |r| post.shared_pending.count(r) > 0 implies (0 <= r < post.rc_width) by {
                    assert(post.shared_pending == Multiset::empty());
                    assert(post.shared_pending.count(r) == 0);
                }
            }
            
            // Prove shared_guard_in_range
            assert(post.shared_guard_in_range()) by {
                assert forall |x| post.shared_guard.count(x) > 0 implies (0 <= x.0 < post.rc_width) by {
                    assert(post.shared_guard == Multiset::empty());
                    assert(post.shared_guard.count(x) == 0);
                }
            }
            
            // Prove shared_inv_agree
            assert(post.shared_inv_agree()) by {
                assert forall |v| #[trigger] post.shared_guard.count(v) > 0 implies
                    post.storage == Option::Some(v.1) by {
                    assert(post.shared_guard == Multiset::empty());
                    assert(post.shared_guard.count(v) == 0);
                }
            }
            
            // Prove shared_counts_agree
            assert(post.shared_counts_agree()) by {
                assert forall |r| 0 <= r < post.rc_width implies
                    #[trigger] post.ref_counts.index(r) ==
                        post.shared_pending.count(r) as int +
                            Self::filter_r(post.shared_guard, r).len() as int by {
                    
                    // After initialization:
                    // - ref_counts[r] = 0 for all r in range
                    // - shared_pending = empty multiset, so shared_pending.count(r) = 0
                    // - shared_guard = empty multiset, so filter_r(shared_guard, r) = empty, so len() = 0
                    // So we need to show: 0 == 0 + 0, which is true
                    
                    assert(post.ref_counts.index(r) == 0) by {
                        assert(post.ref_counts == IMap::new(|i| 0 <= i < post.rc_width, |i| 0));
                    };
                    assert(post.shared_pending.count(r) == 0);
                    assert(Self::filter_r(post.shared_guard, r) == Multiset::empty());
                    assert(Self::filter_r(post.shared_guard, r).len() == 0);
                }
            }
        }
        
        #[inductive(exc_start)]
        fn exc_start_inductive(pre: Self, post: Self) {
            admit()
        }
        #[inductive(exc_check_count)]
        fn exc_check_count_inductive(pre: Self, post: Self) {
            admit()
        }
        #[inductive(exc_finish)]
        fn exc_finish_inductive(pre: Self, post: Self) {
            admit()
        }
        #[inductive(exc_release)]
        fn exc_release_inductive(pre: Self, post: Self, t: T) {
            admit()
        }
        #[inductive(shared_start)]
        fn shared_start_inductive(pre: Self, post: Self, r: int) {
            admit()
        }
        #[inductive(shared_finish)]
        fn shared_finish_inductive(pre: Self, post: Self, r: int) {
            admit()
        }
        #[inductive(shared_release)]
        fn shared_release_inductive(pre: Self, post: Self, val: (int, T)) {
            admit()
        }
    }
}

struct_with_invariants!{
    struct RwLock<T> {
        inst: Tracked<DistRwLock::Instance<T>>,
        exc_locked: AtomicBool<_, DistRwLock::exc_locked<T>, _>,
        ref_counts: Vec<AtomicU64<_, DistRwLock::ref_counts<T>, _>>,
    }

    spec fn wf(&self) -> bool {

        predicate {
            &&& self.inst@.rc_width() == self.ref_counts@.len()

            &&& forall |i: int| (0 <= i && i < self.ref_counts@.len()) ==>
                #[trigger] self.ref_counts@.index(i).well_formed()
                && self.ref_counts@.index(i).constant() == (self.inst, i)
        }

        invariant on exc_locked with (inst) is (b: bool, g: DistRwLock::exc_locked<T>) {
            g.instance_id() == inst@.id()
            && g.value() == b
        }

        invariant on ref_counts with (inst)
            forall |i: int|
            where (0 <= i < self.ref_counts@.len())
            specifically (self.ref_counts@[i])
            is (v: u64, g: DistRwLock::ref_counts<T>)
        {
            g.instance_id() == inst@.id()
            && g.key() == i
            && g.value() == v as int
        }
    }
}

impl<T> RwLock<T> {
    #[verifier::spinoff_prover]
    fn new(rc_width: usize, t: T) -> (s: Self)
        requires
            0 < rc_width,
        ensures
            s.wf(),
    {
        let tracked inst;
        let tracked exc_locked_token;
        let tracked mut ref_counts_tokens;
        proof {
            let tracked (
                Tracked(inst0),
                Tracked(exc_locked_token0),
                Tracked(ref_counts_tokens0),
                _,
                _,
                _,
                _,
            ) = DistRwLock::Instance::initialize(rc_width as int, t, Option::Some(t));
            inst = inst0;
            exc_locked_token = exc_locked_token0;
            ref_counts_tokens = ref_counts_tokens0;
        }
        let tracked_inst: Tracked<DistRwLock::Instance<T>> = Tracked(inst.clone());
        let exc_locked_atomic = AtomicBool::new(
            Ghost(tracked_inst),
            false,
            Tracked(exc_locked_token),
        );
        let mut v: Vec<AtomicU64<(Tracked<DistRwLock::Instance<T>>, int), DistRwLock::ref_counts<T>, _>> = Vec::new();
        let mut i: usize = 0;
        assert forall|j: int|
            i <= j && j < rc_width implies #[trigger] ref_counts_tokens.dom().contains(j)
              && equal(ref_counts_tokens.index(j), 0)
        by {
            assert(ref_counts_tokens.dom().contains(j));
            assert(equal(ref_counts_tokens.index(j), 0));
        }
        assert(forall|j: int|
            #![trigger( ref_counts_tokens.dom().contains(j) )]
            #![trigger( ref_counts_tokens.index(j) )]
            i <= j && j < rc_width ==> (ref_counts_tokens.dom().contains(j)
              && equal(ref_counts_tokens.index(j), 0)));
        while i < rc_width
            invariant
                i <= rc_width,
                v@.len() == i as int,
                forall|j: int|
                    0 <= j && j < i ==> #[trigger] v@.index(j).well_formed()
                      && equal(v@.index(j).constant(), (tracked_inst, j)),
                tracked_inst@ == inst,
                ref_counts_tokens.instance_id() == inst.id(),
                forall|j: int|
                    #![trigger( ref_counts_tokens.dom().contains(j) )]
                    #![trigger( ref_counts_tokens.index(j) )]
                    i <= j && j < rc_width ==> (ref_counts_tokens.dom().contains(j)
                      && equal(ref_counts_tokens.index(j), 0)),
        {
            assert(ref_counts_tokens.dom().contains(i as int));
            let tracked ref_count_token = ref_counts_tokens.remove(i as int);
            let rc_atomic = AtomicU64::new(
                Ghost((tracked_inst, i as int)),
                0,
                Tracked(ref_count_token),
            );
            v.push(rc_atomic);
            i = i + 1;
            assert forall|j: int|
                i <= j && j < rc_width implies #[trigger] ref_counts_tokens.dom().contains(j)
                && equal(ref_counts_tokens.index(j), 0)
            by {
                assert(ref_counts_tokens.dom().contains(j));
                assert(equal(ref_counts_tokens.index(j), 0));
            }
        }
        let s = RwLock { inst: Tracked(inst), exc_locked: exc_locked_atomic, ref_counts: v };
        assert(s.inst@.rc_width() == s.ref_counts@.len());
        s
    }
}

} // verus!
fn main() {}