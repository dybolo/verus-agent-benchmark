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
            assert forall |r| 0 <= r < rc_width implies
                post.ref_counts.index(r) == 0
                && post.shared_pending.count(r) == 0
                && Self::filter_r(post.shared_guard, r).len() == 0 by {
                assert(post.ref_counts.index(r) == 0);
                assert(post.shared_pending.count(r) == 0);
                assert forall |x: (int, T)| post.shared_guard.count(x) == 0 by {
                    assert(post.shared_guard == Multiset::empty());
                }
                filter_empty_len(post.shared_guard, |x: (int, T)| x.0 == r);
                assert(Self::filter_r(post.shared_guard, r).len() == 0);
            }
        }

        #[inductive(exc_start)]
        fn exc_start_inductive(pre: Self, post: Self) {

        }

        #[inductive(exc_check_count)]
        fn exc_check_count_inductive(pre: Self, post: Self) {
            let r = pre.exc_pending->0;
            assert(pre.ref_counts.index(r) == 0);
            assert(pre.shared_pending.count(r) == 0);
            assert(Self::filter_r(pre.shared_guard, r).len() == 0);
            assert forall |x: (int, T)| pre.shared_guard.count(x) > 0 implies x.0 != r by {
                if x.0 == r {
                    assert(Self::filter_r(pre.shared_guard, r).count(x) ==
                        pre.shared_guard.count(x));
                    assert(pre.shared_guard.count(x) <=
                        Self::filter_r(pre.shared_guard, r).len());
                }
            }
            assert forall |x: (int, T)| pre.shared_guard.count(x) > 0 implies
                !(0 <= x.0 < r + 1) by {
                if 0 <= x.0 < r + 1 {
                    if x.0 < r {
                        assert(! (0 <= x.0 < r));
                    } else {
                        assert(x.0 == r);
                        assert(x.0 != r);
                    }
                }
            }
            assert forall |r| 0 <= r < pre.rc_width implies
                post.ref_counts.index(r) == pre.ref_counts.index(r)
                && post.shared_pending.count(r) == pre.shared_pending.count(r)
                && Self::filter_r(post.shared_guard, r).len() == Self::filter_r(pre.shared_guard, r).len() by {
                assert(post.ref_counts.index(r) == pre.ref_counts.index(r));
                assert(post.shared_pending.count(r) == pre.shared_pending.count(r));
                assert(Self::filter_r(post.shared_guard, r).len() == Self::filter_r(pre.shared_guard, r).len());
            }
        }

        #[inductive(exc_finish)]
        fn exc_finish_inductive(pre: Self, post: Self) {
        }

        #[inductive(exc_release)]
        fn exc_release_inductive(pre: Self, post: Self, t: T) {

        }

        #[inductive(shared_start)]
        fn shared_start_inductive(pre: Self, post: Self, r: int) { }

        #[inductive(shared_finish)]
        fn shared_finish_inductive(pre: Self, post: Self, r: int) {
            let t = pre.storage->0;
            assert(post.shared_guard == pre.shared_guard.insert((r, t)));
            assert forall |r0| 0 <= r0 < pre.rc_width implies
                post.ref_counts.index(r0) == pre.ref_counts.index(r0)
                && if r0 == r {
                    post.shared_pending.count(r0) + 1nat == pre.shared_pending.count(r0)
                    && Self::filter_r(post.shared_guard, r0).len() ==
                        Self::filter_r(pre.shared_guard, r0).len() + 1nat
                } else {
                    post.shared_pending.count(r0) == pre.shared_pending.count(r0)
                    && Self::filter_r(post.shared_guard, r0).len() ==
                        Self::filter_r(pre.shared_guard, r0).len()
                } by {
                assert(post.ref_counts.index(r0) == pre.ref_counts.index(r0));
                if r0 == r {
                    assert(post.shared_pending.count(r0) + 1nat == pre.shared_pending.count(r0));
                    filter_insert_len(pre.shared_guard, (r, t),
                        |x: (int, T)| x.0 == r0);
                    assert(Self::filter_r(post.shared_guard, r0).len() ==
                        Self::filter_r(pre.shared_guard, r0).len() + 1nat);
                } else {
                    assert(post.shared_pending.count(r0) == pre.shared_pending.count(r0));
                    filter_insert_len(pre.shared_guard, (r, t),
                        |x: (int, T)| x.0 == r0);
                    assert(Self::filter_r(post.shared_guard, r0).len() ==
                        Self::filter_r(pre.shared_guard, r0).len());
                }
            }
        }

        #[inductive(shared_release)]
        fn shared_release_inductive(pre: Self, post: Self, val: (int, T)) {
            assert(pre.shared_guard == post.shared_guard.insert(val));
            assert forall |r| 0 <= r < pre.rc_width implies
                if r == val.0 {
                    post.ref_counts.index(r) + 1int == pre.ref_counts.index(r)
                    && post.shared_pending.count(r) == pre.shared_pending.count(r)
                    && Self::filter_r(post.shared_guard, r).len() + 1nat ==
                        Self::filter_r(pre.shared_guard, r).len()
                } else {
                    post.ref_counts.index(r) == pre.ref_counts.index(r)
                    && post.shared_pending.count(r) == pre.shared_pending.count(r)
                    && Self::filter_r(post.shared_guard, r).len() ==
                        Self::filter_r(pre.shared_guard, r).len()
                } by {
                if r == val.0 {
                    assert(post.ref_counts.index(r) + 1int == pre.ref_counts.index(r));
                    filter_insert_len(post.shared_guard, val,
                        |x: (int, T)| x.0 == r);
                    assert(Self::filter_r(post.shared_guard, r).len() + 1nat ==
                        Self::filter_r(pre.shared_guard, r).len());
                } else {
                    assert(post.ref_counts.index(r) == pre.ref_counts.index(r));
                    filter_insert_len(post.shared_guard, val,
                        |x: (int, T)| x.0 == r);
                    assert(Self::filter_r(post.shared_guard, r).len() ==
                        Self::filter_r(pre.shared_guard, r).len());
                }
                assert(post.shared_pending.count(r) == pre.shared_pending.count(r));
            }
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

} 
verus! {
proof fn filter_empty_len<V>(m: Multiset<V>, f: spec_fn(V) -> bool)
    requires forall |v: V| m.count(v) == 0
    ensures m.filter(f).len() == 0
{
    assert forall |v: V| #[trigger] m.filter(f).count(v) == 0 by {
        assert(m.filter(f).count(v) == if f(v) { m.count(v) } else { 0 });
    }
    assert(m.filter(f) =~= Multiset::empty());
    assert(m.filter(f).len() == 0);
}
proof fn filter_insert_len<V>(m: Multiset<V>, x: V, f: spec_fn(V) -> bool)
    ensures m.insert(x).filter(f).len() == m.filter(f).len() + (if f(x) { 1nat } else { 0nat })
{
    if f(x) {
        assert forall |v: V| #[trigger] m.insert(x).filter(f).count(v) == m.filter(f).insert(x).count(v) by {
            assert(m.insert(x).filter(f).count(v) == if f(v) { m.insert(x).count(v) } else { 0 });
            assert(m.filter(f).insert(x).count(v) == m.filter(f).count(v) + Multiset::singleton(x).count(v));
            if v == x { assert(m.insert(x).count(v) == m.count(v) + 1); assert(m.filter(f).count(v) == m.count(v)); assert(Multiset::singleton(x).count(v) == 1); }
            else { assert(m.insert(x).count(v) == m.count(v)); assert(Multiset::singleton(x).count(v) == 0); }
        }
        assert(m.insert(x).filter(f) =~= m.filter(f).insert(x));
        assert(m.insert(x).filter(f).len() == m.filter(f).insert(x).len());
        assert(m.filter(f).insert(x).len() == m.filter(f).len() + 1);
    } else {
        assert forall |v: V| #[trigger] m.insert(x).filter(f).count(v) == m.filter(f).count(v) by {
            assert(m.insert(x).filter(f).count(v) == if f(v) { m.insert(x).count(v) } else { 0 });
            if v == x { assert(!f(v)); } else { assert(m.insert(x).count(v) == m.count(v)); }
        }
        assert(m.insert(x).filter(f) =~= m.filter(f));
        assert(m.insert(x).filter(f).len() == m.filter(f).len());
    }
}
}
fn main() {}
