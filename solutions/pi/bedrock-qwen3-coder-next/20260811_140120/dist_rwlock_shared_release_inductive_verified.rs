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
            admit()
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
            let r = val.0;

            // The shared_release transition removes val from shared_guard and decrements ref_counts[r]
            // We need to show that shared_counts_agree is preserved:
            // post.ref_counts[r] == post.shared_pending.count(r) + filter_r(post.shared_guard, r).len()

            // Step 1: The removed element is in range
            assert(0 <= r < pre.rc_width) by {
                assert(pre.shared_guard.count(val) > 0);
                assert(pre.shared_guard_in_range());
                assert(pre.shared_guard.count(val) > 0 ==> 0 <= val.0 < pre.rc_width);
                assert(0 <= val.0 < pre.rc_width);
            };

            // Step 2: filter_r doesn't change for other reader ids
            assert forall |r_prime: int|
                r_prime != r && 0 <= r_prime < post.rc_width implies
                #[trigger] Self::filter_r(post.shared_guard, r_prime).len() ==
                    Self::filter_r(pre.shared_guard, r_prime).len()
            by {
                assert(post.shared_guard == pre.shared_guard.remove(val));
                assert(post.rc_width == pre.rc_width);
                assert(0 <= r_prime < pre.rc_width);
                assert(Self::filter_r(post.shared_guard, r_prime) ==
                    post.shared_guard.filter(|val: (int, T)| val.0 == r_prime));
                assert(Self::filter_r(pre.shared_guard, r_prime) ==
                    pre.shared_guard.filter(|val: (int, T)| val.0 == r_prime));
                assert(post.shared_guard.count(val) > 0 ==> 0 <= val.0 < pre.rc_width);
                assert(val.0 == r);
                assert(r_prime != r);
                assert(!post.shared_guard.contains(val) || val.0 != r_prime);
                assert(post.shared_guard.filter(|val: (int, T)| val.0 == r_prime) ==
                    pre.shared_guard.filter(|val: (int, T)| val.0 == r_prime));
                let pre_filter = Self::filter_r(pre.shared_guard, r_prime);
                let post_filter = Self::filter_r(post.shared_guard, r_prime);
                assert forall |v: (int, T)| post_filter.contains(v) <==> pre_filter.contains(v) by {
                    if post_filter.contains(v) {
                        assert(post.shared_guard.contains(v));
                        assert(post.shared_guard.count(v) > 0);
                        assert(post.shared_guard == pre.shared_guard.remove(val));
                        assert(pre.shared_guard.count(v) > 0 && v != val);
                        assert(pre_filter.contains(v));
                    }
                    if pre_filter.contains(v) {
                        assert(pre.shared_guard.contains(v));
                        assert(v.0 == r_prime);
                        assert(val.0 == r);
                        assert(r_prime != r);
                        assert(v != val);
                        assert(post.shared_guard.contains(v));
                        assert(post_filter.contains(v));
                    }
                }
                assert(post_filter =~= pre_filter);
                assert(post_filter.len() == pre_filter.len());
            };

            // Step 3: filter_r for reader r loses exactly one element (val)
            assert(Self::filter_r(post.shared_guard, r).len() ==
                Self::filter_r(pre.shared_guard, r).len() - 1) by {
                assert(post.shared_guard == pre.shared_guard.remove(val));
                assert(Self::filter_r(post.shared_guard, r) ==
                    post.shared_guard.filter(|val: (int, T)| val.0 == r));
                assert(Self::filter_r(pre.shared_guard, r) ==
                    pre.shared_guard.filter(|val: (int, T)| val.0 == r));
                assert(pre.shared_guard.count(val) > 0);
                assert(val.0 == r);
                assert(Self::filter_r(pre.shared_guard, r).count(val) == pre.shared_guard.count(val));
                assert(Self::filter_r(pre.shared_guard, r).count(val) > 0);
                assert(Self::filter_r(pre.shared_guard, r).len() > 0);
                let pre_filter = Self::filter_r(pre.shared_guard, r);
                let post_filter = Self::filter_r(post.shared_guard, r);
                assert(post_filter =~= pre_filter.remove(val)) by {
                    // Use extensionality: for all v, post_filter.contains(v) <==> pre_filter.remove(val).contains(v)
                    // where pre_filter.remove(val).contains(v) iff (v != val && pre_filter.contains(v)) || (v == val && pre_filter.count(val) > 1)
                    assert forall |v: (int, T)| post_filter.contains(v) <==> pre_filter.remove(val).contains(v) by {
                        if post_filter.contains(v) {
                            assert(post.shared_guard.filter(|val: (int, T)| val.0 == r).contains(v));
                            assert(post.shared_guard.contains(v));
                            assert(v.0 == r);
                            assert(post.shared_guard == pre.shared_guard.remove(val));
                            // post.shared_guard = pre.shared_guard.remove(val)
                            // So post.shared_guard.contains(v) means:
                            //   - v != val && pre.shared_guard.contains(v), OR
                            //   - v == val && pre.shared_guard.count(val) > 1
                            // Since v.0 == r == val.0, if v == val then v is in pre_filter
                            // And if v != val and pre.shared_guard.contains(v), then v is in pre_filter
                            // In either case, v is in pre_filter.remove(val)
                            assert(pre.shared_guard.contains(v));
                            assert(pre_filter.contains(v));
                            if v == val {
                                // v == val and v is in post.shared_guard
                                // post.shared_guard = pre.shared_guard.remove(val)
                                // So pre.shared_guard.count(val) > 1
                                assert(pre.shared_guard.count(val) > 1);
                                assert(pre_filter.count(val) > 1);
                                // pre_filter.remove(val).contains(v) because v == val and pre_filter.count(val) > 1
                            } else {
                                assert(v != val);
                                // pre_filter.remove(val).contains(v) because v != val and pre_filter.contains(v)
                            }
                        }
                        if pre_filter.remove(val).contains(v) {
                            // pre_filter.remove(val).contains(v) iff (v != val && pre_filter.contains(v)) || (v == val && pre_filter.count(val) > 1)
                            if v == val {
                                assert(pre_filter.count(val) > 1);
                                assert(pre.shared_guard.filter(|val: (int, T)| val.0 == r).count(val) > 1);
                                assert(pre.shared_guard.count(val) > 1);
                                // post.shared_guard = pre.shared_guard.remove(val)
                                // So post.shared_guard.count(val) = pre.shared_guard.count(val) - 1 > 0
                                assert(post.shared_guard.count(val) > 0);
                                assert(post_filter.contains(v));
                            } else {
                                assert(v != val);
                                assert(pre_filter.contains(v));
                                assert(pre.shared_guard.filter(|val: (int, T)| val.0 == r).contains(v));
                                assert(pre.shared_guard.contains(v));
                                assert(v.0 == r);
                                // v != val and pre.shared_guard.contains(v)
                                // So post.shared_guard = pre.shared_guard.remove(val) still contains v
                                assert(post.shared_guard.contains(v));
                                assert(post_filter.contains(v));
                            }
                        }
                    }
                    assert(post_filter =~= pre_filter.remove(val));
                }
                assert(post_filter.len() == pre_filter.len() - 1);
            };

            // Step 4: shared_pending doesn't change
            assert(post.shared_pending =~= pre.shared_pending) by {
                assert(post.shared_pending == pre.shared_pending);
            };

            // Step 5: ref_counts[r] is decremented
            // The state machine DSL removes [r => rc] and adds [r => rc - 1]
            // So: post.ref_counts == pre.ref_counts.remove(r).insert(r, pre_rc - 1)
            // where pre_rc = pre.ref_counts.index(r)
            
            // From the transition, we know that pre.ref_counts.contains_pair(r, pre_rc)
            // for some pre_rc, and post.ref_counts is the result of removing r and adding it back with pre_rc - 1
            assert(post.ref_counts.dom().contains(r));
            assert(pre.ref_counts.dom().contains(r));
            
            // Frame condition for IMap: only key r is modified
            assert(post.ref_counts == pre.ref_counts.remove(r).insert(r, pre.ref_counts.index(r) - 1));

            assert(post.ref_counts.index(r) == pre.ref_counts.index(r) - 1) by {
                // After remove(r), key r is not in domain
                // Then insert(r, _) adds it back with the new value
                let tmp = pre.ref_counts.remove(r);
                let tmp2 = tmp.insert(r, pre.ref_counts.index(r) - 1);
                assert(tmp.dom() == pre.ref_counts.dom().remove(r));
                assert(!tmp.dom().contains(r));
                assert(tmp2.dom() == tmp.dom().insert(r));
                assert(tmp2.dom().contains(r));
                assert(tmp2.index(r) == pre.ref_counts.index(r) - 1);
            };

            assert forall |r_prime: int|
                0 <= r_prime < post.rc_width && r_prime != r implies
                #[trigger] post.ref_counts.index(r_prime) == pre.ref_counts.index(r_prime)
            by {
                // Frame condition: ref_counts only changes at r
                // For r_prime != r, the value is unchanged after remove(r).insert(r, _)
                assert(pre.ref_counts.dom().contains(r_prime));
                assert(post.ref_counts.dom().contains(r_prime));
                let tmp = pre.ref_counts.remove(r);
                let tmp2 = tmp.insert(r, pre.ref_counts.index(r) - 1);
                assert(tmp.index(r_prime) == pre.ref_counts.index(r_prime));
                assert(tmp2.index(r_prime) == tmp.index(r_prime));
                assert(post.ref_counts.index(r_prime) == pre.ref_counts.index(r_prime));
            };

            // Step 6: Combine to show the invariant is preserved
            assert(post.ref_counts.index(r) ==
                post.shared_pending.count(r) as int +
                Self::filter_r(post.shared_guard, r).len() as int) by {
                // lhs = post.ref_counts[r] = pre.ref_counts[r] - 1
                // rhs = post.shared_pending[r] + filter_r(post.shared_guard, r).len()
                //     = pre.shared_pending[r] + (filter_r(pre.shared_guard, r).len() - 1)
                //     = (pre.shared_pending[r] + filter_r(pre.shared_guard, r).len()) - 1
                //     = pre.ref_counts[r] - 1
                assert(pre.shared_counts_agree());
                assert(0 <= r < pre.rc_width);
                assert(pre.ref_counts.index(r) == pre.shared_pending.count(r) as int + Self::filter_r(pre.shared_guard, r).len() as int);
                assert(post.ref_counts.index(r) == pre.ref_counts.index(r) - 1);
                assert(post.shared_pending.count(r) == pre.shared_pending.count(r));
                assert(Self::filter_r(post.shared_guard, r).len() == Self::filter_r(pre.shared_guard, r).len() - 1);
                assert(post.ref_counts.index(r) ==
                    post.shared_pending.count(r) as int + Self::filter_r(post.shared_guard, r).len() as int);
            };

            // Step 7: For other reader ids, the invariant is preserved
            assert forall |r_prime: int|
                0 <= r_prime < post.rc_width implies
                #[trigger] post.ref_counts.index(r_prime) ==
                    post.shared_pending.count(r_prime) as int +
                        Self::filter_r(post.shared_guard, r_prime).len() as int
            by {
                if r_prime == r {
                    // Already proved in Step 6
                } else {
                    // For r_prime != r, the values don't change
                    assert(post.ref_counts.index(r_prime) == pre.ref_counts.index(r_prime));
                    assert(post.shared_pending.count(r_prime) == pre.shared_pending.count(r_prime));
                    assert(Self::filter_r(post.shared_guard, r_prime).len() == Self::filter_r(pre.shared_guard, r_prime).len());
                    assert(pre.shared_counts_agree());
                    assert(0 <= r_prime < pre.rc_width);
                    assert(pre.ref_counts.index(r_prime) == pre.shared_pending.count(r_prime) as int + Self::filter_r(pre.shared_guard, r_prime).len() as int);
                    assert(post.ref_counts.index(r_prime) ==
                        post.shared_pending.count(r_prime) as int + Self::filter_r(post.shared_guard, r_prime).len() as int);
                }
            };

            // Step 8: The domain doesn't change (rc_width is constant)
            assert(0 < post.rc_width);
            assert(forall |i: int| 0 <= i < post.rc_width <==> post.ref_counts.dom().contains(i));
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
