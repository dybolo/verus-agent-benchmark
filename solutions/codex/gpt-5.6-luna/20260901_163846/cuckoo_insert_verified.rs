#![verifier::loop_isolation(false)]
#![allow(non_snake_case)]

use verus_state_machines_macros::tokenized_state_machine;
use vstd::atomic::*;
use vstd::cell::CellId;
use vstd::cell::pcell as pc;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::tokens::*;
use core::marker::PhantomData;
use vstd::atomic_ghost::*;
use vstd::invariant::InvariantPredicate;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::set::*;

fn main() {}

verus! {

tokenized_state_machine!(
RwLockToks<K, V, Pred: InvariantPredicate<K, V>> {
    fields {
        #[sharding(constant)]
        pub k: K,

        #[sharding(constant)]
        pub pred: PhantomData<Pred>,

        #[sharding(variable)]
        pub flag_exc: bool,

        #[sharding(variable)]
        pub flag_rc: nat,

        #[sharding(storage_option)]
        pub storage: Option<V>,

        #[sharding(option)]
        pub pending_writer: Option<()>,

        #[sharding(option)]
        pub writer: Option<()>,

        #[sharding(multiset)]
        pub pending_reader: Multiset<()>,

        #[sharding(multiset)]
        pub reader: Multiset<V>,
    }

    init!{
        initialize_full(k: K, t: V) {
            require Pred::inv(k, t);
            init k = k;
            init pred = PhantomData;
            init flag_exc = false;
            init flag_rc = 0;
            init storage = Option::Some(t);
            init pending_writer = Option::None;
            init writer = Option::None;
            init pending_reader = Multiset::empty();
            init reader = Multiset::empty();
        }
    }

    #[inductive(initialize_full)]
    fn initialize_full_inductive(post: Self, k: K, t: V) {
        broadcast use group_multiset_axioms;
    }

    transition!{
        acquire_read_start() {
            update flag_rc = pre.flag_rc + 1;
            add pending_reader += {()};
        }
    }

    transition!{
        acquire_read_end() {
            require(pre.flag_exc == false);

            remove pending_reader -= {()};

            birds_eye let x: V = pre.storage->0;
            add reader += {x};

            assert Pred::inv(pre.k, x);
        }
    }

    transition!{
        acquire_read_abandon() {
            remove pending_reader -= {()};
            assert(pre.flag_rc >= 1);
            update flag_rc = (pre.flag_rc - 1) as nat;
        }
    }

    transition!{
        acquire_exc_start() {
            require(pre.flag_exc == false);
            update flag_exc = true;
            add pending_writer += Some(());
        }
    }

    transition!{
        acquire_exc_end() {
            require(pre.flag_rc == 0);

            remove pending_writer -= Some(());

            add writer += Some(());

            birds_eye let x = pre.storage->0;
            withdraw storage -= Some(x);

            assert Pred::inv(pre.k, x);
        }
    }

    transition!{
        release_exc(x: V) {
            require Pred::inv(pre.k, x);
            remove writer -= Some(());

            update flag_exc = false;

            deposit storage += Some(x);
        }
    }

    property!{
        read_guard(x: V) {
            have reader >= {x};
            guard storage >= Some(x);
        }
    }

    property!{
        read_match(x: V, y: V) {
            have reader >= {x};
            have reader >= {y};
            assert(equal(x, y));
        }
    }

    #[transition]
    transition!{
        release_shared(x: V) {
            remove reader -= {x};

            assert(pre.flag_rc >= 1) by {
                assert(equal(pre.storage, Option::Some(x)));
            };
            update flag_rc = (pre.flag_rc - 1) as nat;
        }
    }

    #[invariant]
    pub fn exc_bit_matches(&self) -> bool {
        (if self.flag_exc { 1 } else { 0 as int }) ==
            (if self.pending_writer is Some { 1 } else { 0 as int }) as int
            + (if self.writer is Some { 1 } else { 0 as int }) as int
    }

    #[invariant]
    pub fn count_matches(&self) -> bool {
        self.flag_rc == self.pending_reader.count(())
            + self.reader.count(self.storage->0)
    }

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |t: V| imply(#[trigger] self.reader.count(t) > 0,
            equal(self.storage, Option::Some(t)))
    }

    #[invariant]
    pub fn writer_agrees_storage(&self) -> bool {
        imply(self.writer is Some, self.storage is None)
    }

    #[invariant]
    pub fn writer_agrees_storage_rev(&self) -> bool {
        imply(self.storage is None, self.writer is Some)
    }

    #[invariant]
    pub fn sto_user_inv(&self) -> bool {
        self.storage.is_some() ==> Pred::inv(self.k, self.storage.unwrap())
    }

    #[inductive(acquire_read_start)]
    fn acquire_read_start_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
    }

    #[inductive(acquire_read_end)]
    fn acquire_read_end_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
    }

    #[inductive(acquire_read_abandon)]
    fn acquire_read_abandon_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
    }

    #[inductive(acquire_exc_start)]
    fn acquire_exc_start_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_exc_end)]
    fn acquire_exc_end_inductive(pre: Self, post: Self) { }

    #[inductive(release_exc)]
    fn release_exc_inductive(pre: Self, post: Self, x: V) { }

    #[inductive(release_shared)]
    fn release_shared_inductive(pre: Self, post: Self, x: V) {
        broadcast use group_multiset_axioms;
        assert(equal(pre.storage, Option::Some(x)));
    }
});


pub trait RwLockPredicate<V>: Sized {
    spec fn inv(self, v: V) -> bool;
}

impl<V> RwLockPredicate<V> for spec_fn(V) -> bool {
    open spec fn inv(self, v: V) -> bool {
        self(v)
    }
}

ghost struct InternalPred<V, Pred> {
    v: V,
    pred: Pred,
}

impl<V, Pred: RwLockPredicate<V>> InvariantPredicate<Pred, V> for InternalPred<V, Pred> {
    closed spec fn inv(k: Pred, v: V) -> bool {
        k.inv(v)
    }
}

struct_with_invariants!{

    pub struct RwLock<V, Pred: RwLockPredicate<V>> {
        exc: AtomicBool<_, RwLockToks::flag_exc<Pred, V, InternalPred<V, Pred>>, _>,
        rc: AtomicUsize<_, RwLockToks::flag_rc<Pred, V, InternalPred<V, Pred>>, _>,

        inst: Tracked<RwLockToks::Instance<Pred, V, InternalPred<V, Pred>>>,
        pred: Ghost<Pred>,
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        invariant on exc with (inst) is (v: bool, g: RwLockToks::flag_exc<Pred, V, InternalPred<V, Pred>>) {
            g.instance_id() == inst@.id()
                && g.value() == v
        }

        invariant on rc with (inst) is (v: usize, g: RwLockToks::flag_rc<Pred, V, InternalPred<V, Pred>>) {
            g.instance_id() == inst@.id()
                && g.value() == v
        }

        predicate {
            self.inst@.k() == self.pred@
        }
    }
}

pub struct WriteHandle<'a, V, Pred: RwLockPredicate<V>> {
    tracked handle: Tracked<RwLockToks::writer<Pred, V, InternalPred<V, Pred>>>,
    rwlock: &'a RwLock<V, Pred>,
}

pub struct ReadHandle<'a, V, Pred: RwLockPredicate<V>> {
    tracked handle: Tracked<RwLockToks::reader<Pred, V, InternalPred<V, Pred>>>,
    rwlock: &'a RwLock<V, Pred>,
}

impl<'a, V, Pred: RwLockPredicate<V>> WriteHandle<'a, V, Pred> {
    #[verifier::type_invariant]
    spec fn wf_write_handle(self) -> bool {
        equal(
            self.handle@.instance_id(),
            self.rwlock.inst@.id(),
        ) && self.rwlock.wf()
    }

    pub closed spec fn rwlock(self) -> RwLock<V, Pred> {
        *self.rwlock
    }

    pub fn release_write(self, Tracked(new_val): Tracked<V>)
        requires
            self.rwlock().inv(new_val),
    {
        proof {
            use_type_invariant(&self);
        }
        let WriteHandle { handle: Tracked(handle), rwlock } = self;

        atomic_with_ghost!(
            &rwlock.exc => store(false);
            ghost g =>
        {
            self.rwlock.inst.borrow().release_exc(new_val, &mut g, new_val, handle);
        });
    }
}

impl<'a, V, Pred: RwLockPredicate<V>> ReadHandle<'a, V, Pred> {
    #[verifier::type_invariant]
    spec fn wf_read_handle(self) -> bool {
        equal(self.handle@.instance_id(), self.rwlock.inst@.id())
            && self.rwlock.wf()
    }

    pub closed spec fn view(self) -> V {
        self.handle@.element()
    }

    pub closed spec fn rwlock(self) -> RwLock<V, Pred> {
        *self.rwlock
    }

    pub proof fn borrow<'b>(tracked &'b self) -> (tracked val: &'b V)
        ensures
            val == self.view(),
    {
        use_type_invariant(self);
        let tracked perm = self.rwlock.inst.borrow().read_guard(
            self.handle@.element(),
            self.handle.borrow(),
        );
        &perm
    }

    pub proof fn lemma_readers_match(
        tracked read_handle1: &ReadHandle<V, Pred>,
        tracked read_handle2: &ReadHandle<V, Pred>,
    )
        requires
            read_handle1.rwlock() == read_handle2.rwlock(),
        ensures
            (equal(read_handle1.view(), read_handle2.view())),
    {
        use_type_invariant(read_handle1);
        use_type_invariant(read_handle2);
        read_handle1.rwlock.inst.borrow().read_match(
            read_handle1.handle@.element(),
            read_handle2.handle@.element(),
            &read_handle1.handle.borrow(),
            &read_handle2.handle.borrow(),
        );
    }

    pub fn release_read(self) {
        proof { use_type_invariant(&self); }
        let ReadHandle { handle: Tracked(handle), rwlock } = self;

        let _ =
            atomic_with_ghost!(
            &rwlock.rc => fetch_sub(1);
            ghost g =>
        {
            rwlock.inst.borrow().release_shared(handle.element(), &mut g, handle);
        });
    }
}

impl<V, Pred: RwLockPredicate<V>> RwLock<V, Pred> {
    pub closed spec fn pred(&self) -> Pred {
        self.pred@
    }

    pub open spec fn inv(&self, val: V) -> bool {
        self.pred().inv(val)
    }

    pub fn new(Tracked(val): Tracked<V>, Ghost(pred): Ghost<Pred>) -> (s: Self)
        requires
            pred.inv(val),
        ensures
            s.pred() == pred,
    {
        let tracked (Tracked(inst), Tracked(flag_exc), Tracked(flag_rc), _, _, _, _) =
            RwLockToks::Instance::<Pred, V, InternalPred<V, Pred>>::initialize_full(pred, val, Some(val));
        let inst = Tracked(inst);

        let exc = AtomicBool::new(Ghost(inst), false, Tracked(flag_exc));
        let rc = AtomicUsize::new(Ghost(inst), 0, Tracked(flag_rc));

        RwLock { exc, rc, inst, pred: Ghost(pred) }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn acquire_write(&self) -> (ret: (Tracked<V>, WriteHandle<'_, V, Pred>))
        ensures
            ({
                let val = *ret.0;
                let write_handle = ret.1;
                &&& write_handle.rwlock() == *self
                &&& self.inv(val)
            }),
    {
        proof {
            use_type_invariant(self);
        }
        let mut done = false;
        let tracked mut token: Option<
            RwLockToks::pending_writer<Pred, V, InternalPred<V, Pred>>,
        > = Option::None;
        while !done
            invariant
                done ==> token.is_some() && equal(token->0.instance_id(), self.inst@.id()),
                self.wf(),
        {
            let result =
                atomic_with_ghost!(
                &self.exc => compare_exchange(false, true);
                returning res;
                ghost g =>
            {
                if res is Ok {
                    token = Option::Some(self.inst.borrow().acquire_exc_start(&mut g));
                }
            });

            done =
            match result {
                Result::Ok(_) => true,
                _ => false,
            };
        }
        loop
            invariant
                token is Some && equal(token->0.instance_id(), self.inst@.id()),
                self.wf(),
        {
            let tracked mut perm_opt: Option<V> = None;
            let tracked mut handle_opt: Option<
                RwLockToks::writer<Pred, V, InternalPred<V, Pred>>,
            > = None;

            let result =
                atomic_with_ghost!(
                &self.rc => load();
                returning res;
                ghost g =>
            {
                if res == 0 {
                    let tracked tok = match token { Option::Some(t) => t, Option::None => proof_from_false() };
                    let tracked x = self.inst.borrow().acquire_exc_end(&g, tok);
                    token = None;
                    let tracked (_, Tracked(perm), Tracked(exc_handle)) = x;
                    perm_opt = Some(perm);
                    handle_opt = Some(exc_handle);
                }
            });

            if result == 0 {
                let tracked mut perm = match perm_opt {
                    Option::Some(t) => t,
                    Option::None => proof_from_false(),
                };
                let tracked handle = match handle_opt {
                    Option::Some(t) => t,
                    Option::None => proof_from_false(),
                };
                let write_handle = WriteHandle {
                    handle: Tracked(handle),
                    rwlock: self,
                };
                return (Tracked(perm), write_handle);
            }
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn acquire_read(&self) -> (read_handle: ReadHandle<'_, V, Pred>)
        ensures
            read_handle.rwlock() == *self,
            self.inv(read_handle.view()),
    {
        proof {
            use_type_invariant(self);
        }
        loop
            invariant
                self.wf(),
        {
            let val = atomic_with_ghost!(&self.rc => load(); ghost g => { });

            let tracked mut token: Option<
                RwLockToks::pending_reader<Pred, V, InternalPred<V, Pred>>,
            > = Option::None;

            if val < usize::MAX {
                let result =
                    atomic_with_ghost!(
                    &self.rc => compare_exchange(val, val + 1);
                    returning res;
                    ghost g =>
                {
                    if res is Ok {
                        token = Option::Some(self.inst.borrow().acquire_read_start(&mut g));
                    }
                });

                match result {
                    Result::Ok(_) => {
                        let tracked mut handle_opt:
                            Option<RwLockToks::reader<Pred, V, InternalPred<V, Pred>>> = None;

                        let result =
                            atomic_with_ghost!(
                            &self.exc => load();
                            returning res;
                            ghost g =>
                        {
                            if res == false {
                                let tracked tok = match token { Option::Some(t) => t, Option::None => proof_from_false() };
                                let tracked x = self.inst.borrow().acquire_read_end(&g, tok);
                                token = None;
                                let tracked (_, Tracked(exc_handle)) = x;
                                handle_opt = Some(exc_handle);
                            }
                        });

                        if result == false {
                            let tracked handle = match handle_opt {
                                Option::Some(t) => t,
                                Option::None => proof_from_false(),
                            };
                            let read_handle = ReadHandle { handle: Tracked(handle), rwlock: self };
                            return read_handle;
                        } else {
                            let _ =
                                atomic_with_ghost!(
                                &self.rc => fetch_sub(1);
                                ghost g =>
                            {
                                let tracked tok = match token { Option::Some(t) => t, Option::None => proof_from_false() };
                                self.inst.borrow().acquire_read_abandon(&mut g, tok);
                            });
                        }
                    },
                    _ => {},
                }
            }
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn into_inner(self) -> (v: Tracked<V>)
        ensures
            self.inv(*v),
    {
        let (v, write_handle) = self.acquire_write();
        v
    }
}




type Key = u64;
type Value = u64;

type Row = nat;
type Col = nat;

pub const HEIGHT: usize = 1048576;
pub const WIDTH: usize = 4;

pub closed spec fn hash1(key: Key) -> nat {
    (key as int % HEIGHT as int) as nat
}
pub closed spec fn hash2(key: Key) -> nat {
    let j = (key as int % 1048579) % (HEIGHT - 1);
    ((hash1(key) + j + 1) % HEIGHT as int) as nat
}

#[verifier::external_body]
pub fn rand_u8() -> u8 {
    use std::hash::BuildHasher;
    use std::hash::Hasher;
    let s = std::collections::hash_map::RandomState::new();
    let hasher = s.build_hasher();
    (hasher.finish() & 0xFF) as u8
}


proof fn hash1_ne_hash2(key: Key)
    ensures hash1(key) != hash2(key)
{
}

fn compute_hash1(key: Key) -> (h: usize)
    ensures h == hash1(key) && h < HEIGHT
{
    (key % HEIGHT as u64) as usize
}

fn compute_hash2(key: Key) -> (h: usize)
    ensures h == hash2(key) && h < HEIGHT
{
    let j = (key % 1048579u64) % ((HEIGHT - 1) as u64);
    (compute_hash1(key) + j as usize + 1) % HEIGHT
}



tokenized_state_machine!{ Cuckoo {
    fields {
        #[sharding(imap)]
        pub frag: IMap<Key, Option<Value>>,

        #[sharding(imap)]
        pub matrix: IMap<Row, Seq<Option<(Key, Value)>>>,
    }

    init!{
        initialize() {
            init frag = IMap::new(|key| true, |key| None);
            init matrix = IMap::new(
                |p: Row| p < HEIGHT,
                |p: Row| Seq::new(WIDTH as nat, |col| None),
            );
        }
    }

    property!{
        query_none(key: Key) {
            have frag >= [key => let opt_val];
            have matrix >= [hash1(key) => let r1];
            have matrix >= [hash2(key) => let r2];
            require not_in_row(r1, key);
            require not_in_row(r2, key);
            assert opt_val === None;
        }
    }

    property!{
        query_some(key: Key, row: Row, col: Col) {
            have frag >= [key => let opt_val];
            require row < HEIGHT;
            require col < WIDTH;
            have matrix >= [row => let r];
            require let Some((entry_key, entry_value)) = r[col as int];
            require entry_key == key;
            assert opt_val === Some(entry_value);
        }
    }

    property!{
        hash_is_right(key: Key, row: Row, col: Col) {
            require row < HEIGHT;
            require col < WIDTH;
            have matrix >= [row => let r];
            require let Some((entry_key, entry_value)) = r[col as int];
            require entry_key == key;
            assert row == hash1(key) || row == hash2(key);
        }
    }

    transition!{
        delete_key_value(key: Key, row: Row, col: Col) {
            remove frag -= [key => let _];
            require row < HEIGHT;
            require col < WIDTH;
            remove matrix -= [row => let r];
            require let Some((entry_key, entry_value)) = r[col as int];
            require entry_key == key;
            add matrix += [row => r.update(col as int, None)];
            add frag += [key => None];
        }
    }

    transition!{
        update_key_value(key: Key, new_val: Value, row: Row, col: Col) {
            remove frag -= [key => let _];
            require row < HEIGHT;
            require col < WIDTH;
            remove matrix -= [row => let r];
            require let Some((entry_key, entry_value)) = r[col as int];
            require entry_key == key;
            add matrix += [row => r.update(col as int, Some((key, new_val)))];
            add frag += [key => Some(new_val)];
        }
    }

    transition!{
        insert_key_value(key: Key, new_val: Value, row: Row, col: Col) {
            remove frag -= [key => let _];
            require row < HEIGHT;
            require col < WIDTH;
            require row == hash1(key) || row == hash2(key);
            let other_row = if row == hash1(key) { hash2(key) } else { hash1(key) };
            remove matrix -= [row => let r];
            have matrix >= [other_row => let other_r];
            require not_in_row(r, key);
            require not_in_row(other_r, key);
            require r[col as int] === None;
            add matrix += [row => r.update(col as int, Some((key, new_val)))];
            add frag += [key => Some(new_val)];
        }
    }

    transition!{
        swing(key: Key, row: Row, col: Col, row2: Row, col2: Col) {
            require row < HEIGHT;
            require col < WIDTH;
            require row2 < HEIGHT;
            require col2 < WIDTH;
            require row == hash1(key) || row == hash2(key);
            require row2 == hash1(key) || row2 == hash2(key);

            remove matrix -= [row => let r];
            remove matrix -= [row2 => let r2];

            require r[col as int].is_some() && r[col as int].unwrap().0 == key;
            require r2[col2 as int].is_none();

            add matrix += [row => r.update(col as int, None)];
            add matrix += [row2 => r2.update(col2 as int, r[col as int])];
        }
    }

    #[invariant]
    pub spec fn domain_full(&self) -> bool {
        forall |x| self.frag.dom().contains(x)
    }

    #[invariant]
    pub spec fn matrix_domain(&self) -> bool {
        forall |row1| 0 <= row1 < HEIGHT <==> #[trigger] self.matrix.dom().contains(row1)
    }

    #[invariant]
    pub spec fn matrix_col_len(&self) -> bool {
        forall |row1| 0 <= row1 < HEIGHT ==> self.matrix[row1].len() == WIDTH
    }

    #[invariant]
    pub spec fn all_distinct(&self) -> bool {
        forall |row1, col1, row2, col2|
            0 <= row1 < HEIGHT ==>
            0 <= col1 < WIDTH ==>
            0 <= row2 < HEIGHT ==>
            0 <= col2 < WIDTH ==>
            (#[trigger] self.matrix[row1][col1]).is_some() ==>
            (#[trigger] self.matrix[row2][col2]).is_some() ==>
            self.matrix[row1][col1].unwrap().0 == self.matrix[row2][col2].unwrap().0 ==>
            row1 == row2 && col1 == col2
    }

    #[invariant]
    pub spec fn key_in_map_implies_key_in_matrix(&self) -> bool {
        forall |key| (#[trigger] self.frag[key]).is_some() ==>
            exists |row, col|
                0 <= row < HEIGHT && 0 <= col < WIDTH
                    && (#[trigger] self.matrix[row][col]).is_some()
                    && self.matrix[row][col].unwrap().0 == key
    }

    #[invariant]
    pub spec fn pair_in_matrix_implies_pair_in_map(&self) -> bool {
        forall |row, col|
            0 <= row < HEIGHT ==>
            0 <= col < WIDTH ==>
            self.matrix[row][col].is_some() ==>
            self.frag[self.matrix[row][col].unwrap().0]
                == Some(self.matrix[row][col].unwrap().1)
    }

    #[invariant]
    pub spec fn pair_in_matrix_implies_hash_correct(&self) -> bool {
        forall |row, col|
            0 <= row < HEIGHT ==>
            0 <= col < WIDTH ==>
            self.matrix[row][col].is_some() ==>
            (row == hash1(self.matrix[row][col].unwrap().0)
              || row == hash2(self.matrix[row][col].unwrap().0))
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    #[inductive(delete_key_value)]
    fn delete_key_value_inductive(pre: Self, post: Self, key: Key, row: Row, col: Col) {
        assert forall |key0| (#[trigger] post.frag[key0]).is_some() implies
            exists |row0, col0|
                0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                    && (#[trigger] post.matrix[row0][col0]).is_some()
                    && post.matrix[row0][col0].unwrap().0 == key0
        by {
            if key0 == key {
                assert(false);
            } else {
                assert(pre.frag[key0].is_some());
                let (row0, col0) = choose |row0, col0|
                    0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                        && (pre.matrix[row0][col0]).is_some()
                        && pre.matrix[row0][col0].unwrap().0 == key0;
                assert(post.matrix[row0][col0].is_some());
            }
        }
    }

    #[inductive(update_key_value)]
    fn update_key_value_inductive(pre: Self, post: Self, key: Key, new_val: Value, row: Row, col: Col) {
        assert forall |key0| (#[trigger] post.frag[key0]).is_some() implies
            exists |row0, col0|
                0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                    && (#[trigger] post.matrix[row0][col0]).is_some()
                    && post.matrix[row0][col0].unwrap().0 == key0
        by {
            if key0 == key {
                assert(post.matrix[row][col as int].is_some());
            } else {
                assert(pre.frag[key0].is_some());
                let (row0, col0) = choose |row0, col0|
                    0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                        && (pre.matrix[row0][col0]).is_some()
                        && pre.matrix[row0][col0].unwrap().0 == key0;
                assert(post.matrix[row0][col0].is_some());
            }
        }
    }

    #[inductive(insert_key_value)]
    fn insert_key_value_inductive(pre: Self, post: Self, key: Key, new_val: Value, row: Row, col: Col) {
        assert forall |key0| (#[trigger] post.frag[key0]).is_some() implies
            exists |row0, col0|
                0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                    && (#[trigger] post.matrix[row0][col0]).is_some()
                    && post.matrix[row0][col0].unwrap().0 == key0
        by {
            if key0 == key {
                assert(post.matrix[row][col as int].is_some());
            } else {
                assert(pre.frag[key0].is_some());
                let (row0, col0) = choose |row0, col0|
                    0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                        && (pre.matrix[row0][col0]).is_some()
                        && pre.matrix[row0][col0].unwrap().0 == key0;
                assert(post.matrix[row0][col0].is_some());
            }
        }
    }

    #[inductive(swing)]
    fn swing_inductive(pre: Self, post: Self, key: Key, row: Row, col: Col, row2: Row, col2: Col) {
        assert forall |key0| (#[trigger] post.frag[key0]).is_some() implies
            exists |row0, col0|
                0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                    && (#[trigger] post.matrix[row0][col0]).is_some()
                    && post.matrix[row0][col0].unwrap().0 == key0
        by {
            if key0 == key {
                assert(post.matrix[row2][col2 as int].is_some());
            } else {
                assert(pre.frag[key0].is_some());
                let (row0, col0) = choose |row0, col0|
                    0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                        && (pre.matrix[row0][col0]).is_some()
                        && pre.matrix[row0][col0].unwrap().0 == key0;
                assert(post.matrix[row0][col0].is_some());
            }
        }
    }
}}

pub open spec fn not_in_row(r: Seq<Option<(Key, Value)>>, key: Key) -> bool {
    forall |i| 0 <= i < r.len() ==> (#[trigger] r[i] matches Some((k, v)) ==> k != key)
}

closed spec fn places_ok(v: Seq<PlaceToFree>, i: int) -> bool {
    0 <= i && i+1 < v.len()
        && 0 <= v[i].row < HEIGHT
        && 0 <= v[i].col < WIDTH
        && v[i].row != v[i+1].row
        && (v[i].row == hash1(v[i].key) || v[i].row == hash2(v[i].key))
        && (v[i+1].row == hash1(v[i].key) || v[i+1].row == hash2(v[i].key))
}


pub const LOCKS_LEN: usize = 1048576;
type LockIdx = nat;

spec fn lock_for_row(row: Row) -> LockIdx {
    row
}

fn compute_lock_for_row(row: usize) -> (l: usize)
    ensures l == lock_for_row(row as nat)
{
    row
}

ghost struct Consts {
    pub ghost instance_id: InstanceId,
    pub ghost cell_ids: Seq<CellId>,
}

tracked struct RowStore {
    pub tracked pt: pc::PointsTo<[Option<(Key, Value)>; WIDTH]>,
    pub tracked token: Cuckoo::matrix,
}

tracked struct LockStore {
    pub tracked rows: IMap<Row, RowStore>,
}

ghost struct LockPred {
    consts: Consts,
    lock: nat,
}

spec fn row_store_wf(consts: Consts, store: RowStore, row: Row) -> bool {
    consts.cell_ids.len() == HEIGHT
    && 0 <= row < HEIGHT
    && store.pt.id() == consts.cell_ids[row as int]
    && store.token.instance_id() == consts.instance_id
    && store.token.value() == store.pt.value()@
    && store.token.key() == row
}

impl RwLockPredicate<LockStore> for LockPred {
    closed spec fn inv(self, store: LockStore) -> bool {
        0 <= self.lock < LOCKS_LEN
        && forall |row| 0 <= row < HEIGHT ==>
            self.lock == #[trigger] lock_for_row(row) ==>
                store.rows.dom().contains(row) &&
                    row_store_wf(self.consts, store.rows[row], row)
    }
}

struct TruePred;
impl<A> RwLockPredicate<A> for TruePred {
    closed spec fn inv(self, a: A) -> bool {
        true
    }
}
pub struct MyHashMap {
    consts: Ghost<Consts>,
    instance: Tracked<Cuckoo::Instance>,
    locks: Vec<RwLock<LockStore, LockPred>>,
    matrix: Vec<pc::PCell<[Option<(Key, Value)>; WIDTH]>>,
    main_write_lock: RwLock<(), TruePred>,
}

impl MyHashMap {
    pub closed spec fn wf(&self) -> bool {
        self.instance.id() == self.consts.instance_id
            && self.locks.len() == LOCKS_LEN
            && self.matrix.len() == HEIGHT
            && (forall |i| 0 <= i < self.locks.len() ==> self.locks[i].pred() == LockPred { consts: *self.consts, lock: i as nat })
            && (forall |i| 0 <= i < HEIGHT ==> self.matrix[i].id() == self.consts.cell_ids[i])
    }

    pub closed spec fn id(&self) -> InstanceId {
        self.consts.instance_id
    }
}

pub type MPointsTo = Cuckoo::frag;

proof fn initialize_lock_store_map(j: nat) -> (tracked m: IMap<LockIdx, LockStore>)
    ensures forall |i| 0 <= i < j ==> m.dom().contains(i)
        && m[i].rows =~= IMap::empty()
    decreases j
{
    if j == 0 {
        IMap::tracked_empty()
    } else {
        let tracked mut m = initialize_lock_store_map((j-1) as nat);
        m.tracked_insert((j-1) as nat, LockStore { rows: IMap::tracked_empty() });
        m
    }
}

struct PlaceToFree {
    row: usize,
    col: usize,
    key: Key,
}

enum Attempt {
    Free(usize),
    Unfree(usize, Key),
}

impl MyHashMap {
    pub fn new() -> (ret: (Self, Tracked<IMapToken<Key, Option<Value>, MPointsTo>>))
        ensures
            ret.0.wf(),
            ret.1.map() =~= IMap::new(|key: Key| true, |key: Key| None),
            ret.1.instance_id() == ret.0.id(),
    {
        let mut locks: Vec<RwLock<LockStore, LockPred>> = vec![];
        let mut matrix: Vec<pc::PCell<[Option<(Key, Value)>; WIDTH]>> = vec![];

        let tracked mut lock_stores = initialize_lock_store_map(LOCKS_LEN as nat);
        let ghost mut cell_ids: Seq<CellId> = seq![];
        let tracked (Tracked(instance), Tracked(frag), Tracked(mut matrix_toks)) =
            Cuckoo::Instance::initialize();

        let mut i = 0;
        while i < HEIGHT
            invariant
                0 <= i <= HEIGHT,
                cell_ids.len() == i,
                matrix.len() == i,
                forall |j| i <= j < HEIGHT ==> matrix_toks.map().dom().contains(j),
                forall |j| i <= j < HEIGHT ==>
                    matrix_toks.map()[j] === Seq::new(WIDTH as nat, |w| None),
                matrix_toks.instance_id() == instance.id(),
                forall |j| 0 <= j < LOCKS_LEN ==> lock_stores.dom().contains(j),
                forall |k: nat| 0 <= k < i ==>
                    lock_stores[#[trigger] lock_for_row(k)].rows.dom().contains(k)
                    && lock_stores[lock_for_row(k)].rows[k].pt.id() == cell_ids[k as int]
                    && lock_stores[lock_for_row(k)].rows[k].pt.value()@ ===
                       lock_stores[lock_for_row(k)].rows[k].token.value()
                    && lock_stores[lock_for_row(k)].rows[k].token.instance_id() == instance.id()
                    && lock_stores[lock_for_row(k)].rows[k].token.key() == k
                    && lock_stores[lock_for_row(k)].rows[k].token.value()
                        === Seq::new(WIDTH as nat, |w| None),
                forall |j| 0 <= j < i ==> cell_ids[j] == matrix[j].id(),
            decreases HEIGHT - i,
        {
            let (pcell, Tracked(pt)) = pc::PCell::new([None; WIDTH]);
            matrix.push(pcell);

            proof {
                let tracked token = matrix_toks.remove(i as nat);
                let tracked row_store = RowStore {
                    pt: pt,
                    token: token,
                };
                let ghost l = lock_for_row(i as nat);
                let tracked mut store = lock_stores.tracked_remove(l);
                store.rows.tracked_insert(i as nat, row_store);
                lock_stores.tracked_insert(l, store);
                cell_ids = cell_ids.push(pcell.id());

                assert(pt.value()@ =~= Seq::new(WIDTH as nat, |w| None));
            }

            i += 1;

        }

        let ghost consts = Consts {
            instance_id: instance.id(),
            cell_ids,
        };

        let mut i = 0;
        while i < LOCKS_LEN
            invariant
                0 <= i <= LOCKS_LEN,
                forall |j| i <= j < LOCKS_LEN ==> lock_stores.dom().contains(j),
                locks.len() == i,
                forall |j| 0 <= j < i ==> locks[j].pred() == (LockPred { consts, lock: j as nat }),
                forall |k: nat| 0 <= k < HEIGHT ==>
                    lock_stores.dom().contains(lock_for_row(k)) ==>
                    lock_stores[#[trigger] lock_for_row(k)].rows.dom().contains(k)
                    && lock_stores[lock_for_row(k)].rows[k].pt.id() == cell_ids[k as int]
                    && lock_stores[lock_for_row(k)].rows[k].pt.value()@ ===
                       lock_stores[lock_for_row(k)].rows[k].token.value()
                    && lock_stores[lock_for_row(k)].rows[k].token.instance_id() == instance.id()
                    && lock_stores[lock_for_row(k)].rows[k].token.key() == k
                    && lock_stores[lock_for_row(k)].rows[k].token.value()
                        === Seq::new(WIDTH as nat, |w| None),
            decreases LOCKS_LEN - i,
        {
            let tracked mut store = lock_stores.tracked_remove(i as nat);
            let ghost pred = LockPred { consts, lock: i as nat };
            locks.push(RwLock::new(Tracked(store), Ghost(pred)));
            i = i + 1;
        }

        let map = MyHashMap {
            consts: Ghost(consts),
            instance: Tracked(instance),
            locks,
            matrix,
            main_write_lock: RwLock::new(Tracked(()), Ghost(TruePred)),
        };

        (map, Tracked(frag))
    }

    pub fn read(&self, key: Key) -> (value: Option<Value>)
        atomically (au) {
            type ReadPred,
            (mpt: MPointsTo) -> (new_mpt: Commit<MPointsTo>),
            requires
                key == mpt.key(),
                self.id() == mpt.instance_id(),
            ensures
                new_mpt@ == mpt,

            outer_mask any,
            inner_mask none,
        }
        requires self.wf(),
        ensures value == mpt.value(),
    {
        let mut h1 = compute_hash1(key);
        let mut h2 = compute_hash2(key);
        let l1 = compute_lock_for_row(h1);
        let l2 = compute_lock_for_row(h2);

        let l1x = if l1 < l2 { l1 } else { l2 };
        let l2x = if l1 < l2 { l2 } else { l1 };
        let h1x = if l1 < l2 { h1 } else { h2 };
        let h2x = if l1 < l2 { h2 } else { h1 };

        let handle1x = self.locks[l1x].acquire_read();

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                row_store_wf(self.consts@, handle1x@.rows[h1x as nat], h1x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] handle1x@.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {

            let entry = self.matrix[h1x].borrow(
                Tracked(&handle1x.borrow().rows.tracked_borrow(h1x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                try_open_atomic_update!(au, mpt => {
                    proof {
                        self.instance.query_some(key, h1x as nat, i as nat,
                            &mpt,
                            &handle1x.borrow().rows.tracked_borrow(h1x as nat).token);
                    }
                    Tracked(Commit(mpt))
                });

                let value = entry.unwrap().1;
                handle1x.release_read();
                return Some(value);
            }

            i += 1;
        }

        let handle2x = self.locks[l2x].acquire_read();

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                row_store_wf(self.consts@, handle2x@.rows[h2x as nat], h2x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] handle2x@.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h2x].borrow(
                Tracked(&handle2x.borrow().rows.tracked_borrow(h2x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                try_open_atomic_update!(au, mpt => {
                    proof {
                        self.instance.query_some(key, h2x as nat, i as nat,
                            &mpt,
                            &handle2x.borrow().rows.tracked_borrow(h2x as nat).token);
                    }
                    Tracked(Commit(mpt))
                });

                let value = entry.unwrap().1;
                handle1x.release_read();
                handle2x.release_read();
                return Some(value);
            }

            i += 1;
        }

        try_open_atomic_update!(au, mpt => {
            proof {
                if l1 < l2 {
                    self.instance.query_none(key, &mpt,
                        &handle1x.borrow().rows.tracked_borrow(h1x as nat).token,
                        &handle2x.borrow().rows.tracked_borrow(h2x as nat).token);
                 } else {
                    self.instance.query_none(key, &mpt,
                        &handle2x.borrow().rows.tracked_borrow(h2x as nat).token,
                        &handle1x.borrow().rows.tracked_borrow(h1x as nat).token);
                 }
            }
            Tracked(Commit(mpt))
        });

        handle1x.release_read();
        handle2x.release_read();
        None
    }

    pub fn delete(&self, key: Key)
        atomically (au) {
            type DeletePred,
            (mpt: MPointsTo) -> (new_mpt: Commit<MPointsTo>),
            requires
                key == mpt.key(),
                self.id() == mpt.instance_id(),
            ensures
                new_mpt@.instance_id() == mpt.instance_id(),
                new_mpt@.key() == mpt.key(),
                new_mpt@.value() === None,

            outer_mask any,
            inner_mask none,
        }
        requires self.wf(),
    {
        let mut h1 = compute_hash1(key);
        let mut h2 = compute_hash2(key);
        let l1 = compute_lock_for_row(h1);
        let l2 = compute_lock_for_row(h2);

        let l1x = if l1 < l2 { l1 } else { l2 };
        let l2x = if l1 < l2 { l2 } else { l1 };
        let h1x = if l1 < l2 { h1 } else { h2 };
        let h2x = if l1 < l2 { h2 } else { h1 };

        let (Tracked(lock1x), handle1x) = self.locks[l1x].acquire_write();

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l1x as int].inv(lock1x),
                row_store_wf(self.consts@, lock1x.rows[h1x as nat], h1x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] lock1x.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h1x].borrow(
                Tracked(&lock1x.rows.tracked_borrow(h1x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                let tracked mut r;
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        r = lock1x.rows.tracked_remove(h1x as nat);
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.delete_key_value(key, h1x as nat, i as nat, mpt, r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(Commit(mpt))
                });

                let mut entry = *self.matrix[h1x].borrow(Tracked(&r.pt));
                entry[i] = None;
                self.matrix[h1x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock1x.rows.tracked_insert(h1x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                return;
            }

            i += 1;
        }

        let (Tracked(lock2x), handle2x) = self.locks[l2x].acquire_write();

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l2x as int].inv(lock2x),
                row_store_wf(self.consts@, lock2x.rows[h2x as nat], h2x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] lock2x.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h2x].borrow(
                Tracked(&lock2x.rows.tracked_borrow(h2x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                let tracked mut r;
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        r = lock2x.rows.tracked_remove(h2x as nat);
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.delete_key_value(key, h2x as nat, i as nat, mpt, r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(Commit(mpt))
                });

                let mut entry = *self.matrix[h2x].borrow(Tracked(&r.pt));
                entry[i] = None;
                self.matrix[h2x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock2x.rows.tracked_insert(h2x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                handle2x.release_write(Tracked(lock2x));
                return;
            }

            i += 1;
        }

        try_open_atomic_update!(au, mpt => {
            proof {
                if l1 < l2 {
                    self.instance.query_none(key, &mpt,
                        &lock1x.rows.tracked_borrow(h1x as nat).token,
                        &lock2x.rows.tracked_borrow(h2x as nat).token);
                 } else {
                    self.instance.query_none(key, &mpt,
                        &lock2x.rows.tracked_borrow(h2x as nat).token,
                        &lock1x.rows.tracked_borrow(h1x as nat).token);
                 }
            }
            Tracked(Commit(mpt))
        });

        handle1x.release_write(Tracked(lock1x));
        handle2x.release_write(Tracked(lock2x));
    }

    pub fn insert(&self, key: Key, new_val: Value) -> (success: bool)
        atomically (au) {
            type InsertPred,
            (mpt: MPointsTo) -> (new_mpt: Commit<MPointsTo>),
            requires
                key == mpt.key(),
                self.id() == mpt.instance_id(),
            ensures
                new_mpt@.instance_id() == mpt.instance_id(),
                new_mpt@.key() == mpt.key(),
                new_mpt@.value() === Some(new_val) || new_mpt@.value() == mpt.value()

            outer_mask any,
            inner_mask none,
        }
        requires self.wf(),
        ensures success ==> new_mpt@.value() === Some(new_val)
    {
        let mut h1 = compute_hash1(key);
        let mut h2 = compute_hash2(key);
        let l1 = compute_lock_for_row(h1);
        let l2 = compute_lock_for_row(h2);

        let l1x = if l1 < l2 { l1 } else { l2 };
        let l2x = if l1 < l2 { l2 } else { l1 };
        let h1x = if l1 < l2 { h1 } else { h2 };
        let h2x = if l1 < l2 { h2 } else { h1 };

        let (Tracked(_unused), main_handle) = self.main_write_lock.acquire_write();
        let (Tracked(lock1x), handle1x) = self.locks[l1x].acquire_write();


        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l1x as int].inv(lock1x),
                row_store_wf(self.consts@, lock1x.rows[h1x as nat], h1x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] lock1x.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h1x].borrow(
                Tracked(&lock1x.rows.tracked_borrow(h1x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                let tracked mut r = lock1x.rows.tracked_remove(h1x as nat);
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.update_key_value(key, new_val, h1x as nat, i as nat, mpt, r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(Commit(mpt))
                });

                let mut entry = *self.matrix[h1x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h1x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock1x.rows.tracked_insert(h1x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }

        let (Tracked(lock2x), handle2x) = self.locks[l2x].acquire_write();

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l2x as int].inv(lock2x),
                row_store_wf(self.consts@, lock2x.rows[h2x as nat], h2x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] lock2x.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h2x].borrow(
                Tracked(&lock2x.rows.tracked_borrow(h2x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                let tracked mut r = lock2x.rows.tracked_remove(h2x as nat);
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.update_key_value(key, new_val, h2x as nat, i as nat, mpt, r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(Commit(mpt))
                });

                let mut entry = *self.matrix[h2x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h2x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock2x.rows.tracked_insert(h2x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                handle2x.release_write(Tracked(lock2x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }


        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l1x as int].inv(lock1x),
                row_store_wf(self.consts@, lock1x.rows[h1x as nat], h1x as nat),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock1x.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock2x.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
                forall |j| 0 <= j < i ==> (#[trigger] lock1x.rows[h1x as nat].token.value()[j].is_some()),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h1x].borrow(
                Tracked(&lock1x.rows.tracked_borrow(h1x as nat).pt))[i];
            if entry.is_none() {
                let tracked mut r = lock1x.rows.tracked_remove(h1x as nat);
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.insert_key_value(key, new_val, h1x as nat, i as nat, mpt, r.token,
                                &lock2x.rows.tracked_borrow(h2x as nat).token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(Commit(mpt))
                });

                let mut entry = *self.matrix[h1x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h1x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock1x.rows.tracked_insert(h1x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                handle2x.release_write(Tracked(lock2x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l2x as int].inv(lock2x),
                row_store_wf(self.consts@, lock2x.rows[h2x as nat], h2x as nat),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock1x.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock2x.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
                forall |j| 0 <= j < i ==> (#[trigger] lock2x.rows[h2x as nat].token.value()[j].is_some()),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h2x].borrow(
                Tracked(&lock2x.rows.tracked_borrow(h2x as nat).pt))[i];
            if entry.is_none() {
                let tracked mut r = lock2x.rows.tracked_remove(h2x as nat);
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.insert_key_value(key, new_val, h2x as nat, i as nat, mpt, r.token,
                                &lock1x.rows.tracked_borrow(h1x as nat).token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(Commit(mpt))
                });

                let mut entry = *self.matrix[h2x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h2x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock2x.rows.tracked_insert(h2x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                handle2x.release_write(Tracked(lock2x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }


        let r = rand_u8();
        let first_row = if r % 2 == 0 { h1 } else { h2 };
        let first_col = (r >> 1) as usize % WIDTH;
        let first_key =
            self.matrix[first_row].borrow(
                Tracked(if first_row == h1x { &lock1x.rows.tracked_borrow(h1x as nat).pt } else { &lock2x.rows.tracked_borrow(h2x as nat).pt })
            )[first_col].unwrap().0;
        proof {
            self.instance.hash_is_right(first_key, first_row as nat, first_col as nat,
              if first_row == h1x { &lock1x.rows.tracked_borrow(h1x as nat).token } else { &lock2x.rows.tracked_borrow(h2x as nat).token });
        }

        handle1x.release_write(Tracked(lock1x));
        handle2x.release_write(Tracked(lock2x));

        let mut first_place = PlaceToFree { row: first_row, col: first_col, key: first_key };
        let mut path = vec![first_place];

        let mut free_r;
        let mut free_c;

        let mut i = HEIGHT;

        #[verifier::allow_complex_invariants]
        loop
            invariant path.len() > 0,
                forall |i: int| 0 <= i && i+1 < path.len() ==> places_ok(path@, i),
                0 <= path[path.len() - 1].row < HEIGHT,
                0 <= path[path.len() - 1].col < WIDTH,
                path[path.len() - 1].row == hash1(path[path.len() - 1].key)
                  || path[path.len() - 1].row == hash2(path[path.len() - 1].key),

            decreases i
        {
            let ghost old_path = path;
            let cur_place = path.last().unwrap();
            proof { hash1_ne_hash2(cur_place.key); }
            let h1 = compute_hash1(cur_place.key);
            let h2 = compute_hash2(cur_place.key);
            let h_other = if h1 == cur_place.row { h2 } else { h1 };
            match self.find_free_space(h_other) {
                Attempt::Free(c) => {
                    free_r = h_other;
                    free_c = c;

                    break;
                }
                Attempt::Unfree(c, next_key) => {
                    path.push(PlaceToFree { row: h_other, col: c, key: next_key });
                }
            }
            if i == 0 {
                main_handle.release_write(Tracked(()));
                try_open_atomic_update!(au, mpt => { Tracked(Commit(mpt)) });
                return false;
            }
            i -= 1;

            proof {
                assert(places_ok(path@, path.len() - 2));
                assert(forall |i: int| 0 <= i && i+1 < old_path.len() ==>
                    places_ok(old_path@, i) ==> places_ok(path@, i));
            }
        }

        while path.len() > 0
            invariant
                forall |i: int| 0 <= i && i+1 < path.len() ==> places_ok(path@, i),
                  path.len() > 0 ==> path[path.len() - 1].row != free_r,
                  path.len() > 0 ==> 0 <= path[path.len() - 1].row < HEIGHT,
                  path.len() > 0 ==> 0 <= path[path.len() - 1].col < WIDTH,
                  path.len() > 0 ==> 0 <= free_r < HEIGHT,
                  path.len() > 0 ==> 0 <= free_c < WIDTH,
                  path.len() > 0 ==>
                       path[path.len() - 1].row == hash1(path[path.len() - 1].key)
                    || path[path.len() - 1].row == hash2(path[path.len() - 1].key),
                  path.len() > 0 ==>
                       free_r == hash1(path[path.len() - 1].key)
                    || free_r == hash2(path[path.len() - 1].key),
            decreases path.len()
        {
            let ghost old_path = path;
            proof {
                assert(path@.len() >= 2 ==> places_ok(path@, path@.len() - 2));
            }
            let place = path.pop().unwrap();
            self.do_swing(place.key, place.row, place.col, free_r, free_c);
            free_r = place.row;
            free_c = place.col;
            proof {
                assert(forall |i: int| 0 <= i && i+1 < path.len() ==>
                    places_ok(old_path@, i) ==> places_ok(path@, i));
            }
        }


        let (Tracked(lock1x), handle1x) = self.locks[l1x].acquire_write();


        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l1x as int].inv(lock1x),
                row_store_wf(self.consts@, lock1x.rows[h1x as nat], h1x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] lock1x.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h1x].borrow(
                Tracked(&lock1x.rows.tracked_borrow(h1x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                let tracked mut r = lock1x.rows.tracked_remove(h1x as nat);
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.update_key_value(key, new_val, h1x as nat, i as nat, mpt, r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(Commit(mpt))
                });

                let mut entry = *self.matrix[h1x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h1x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock1x.rows.tracked_insert(h1x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }

        let (Tracked(lock2x), handle2x) = self.locks[l2x].acquire_write();

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l2x as int].inv(lock2x),
                row_store_wf(self.consts@, lock2x.rows[h2x as nat], h2x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] lock2x.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h2x].borrow(
                Tracked(&lock2x.rows.tracked_borrow(h2x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                let tracked mut r = lock2x.rows.tracked_remove(h2x as nat);
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.update_key_value(key, new_val, h2x as nat, i as nat, mpt, r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(Commit(mpt))
                });

                let mut entry = *self.matrix[h2x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h2x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock2x.rows.tracked_insert(h2x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                handle2x.release_write(Tracked(lock2x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }


        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l1x as int].inv(lock1x),
                row_store_wf(self.consts@, lock1x.rows[h1x as nat], h1x as nat),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock1x.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock2x.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h1x].borrow(
                Tracked(&lock1x.rows.tracked_borrow(h1x as nat).pt))[i];
            if entry.is_none() {
                let tracked mut r = lock1x.rows.tracked_remove(h1x as nat);
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.insert_key_value(key, new_val, h1x as nat, i as nat, mpt, r.token,
                                &lock2x.rows.tracked_borrow(h2x as nat).token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(Commit(mpt))
                });

                let mut entry = *self.matrix[h1x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h1x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock1x.rows.tracked_insert(h1x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                handle2x.release_write(Tracked(lock2x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l2x as int].inv(lock2x),
                row_store_wf(self.consts@, lock2x.rows[h2x as nat], h2x as nat),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock1x.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock2x.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
                forall |j| 0 <= j < i ==> (#[trigger] lock2x.rows[h2x as nat].token.value()[j].is_some()),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h2x].borrow(
                Tracked(&lock2x.rows.tracked_borrow(h2x as nat).pt))[i];
            if entry.is_none() {
                let tracked mut r = lock2x.rows.tracked_remove(h2x as nat);
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.insert_key_value(key, new_val, h2x as nat, i as nat, mpt, r.token,
                                &lock1x.rows.tracked_borrow(h1x as nat).token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(Commit(mpt))
                });

                let mut entry = *self.matrix[h2x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h2x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock2x.rows.tracked_insert(h2x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                handle2x.release_write(Tracked(lock2x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }

        try_open_atomic_update!(au, mpt => { Tracked(Commit(mpt)) });
        false
    }

    fn find_free_space(&self, row: usize) -> (a: Attempt)
        requires self.wf(), 0 <= row < HEIGHT,
        ensures (match a {
            Attempt::Free(c) => 0 <= c < WIDTH,
            Attempt::Unfree(c, key) => 0 <= c < WIDTH
                && (row == hash1(key) || row == hash2(key)),
        })
    {
        let l1x = compute_lock_for_row(row);
        let handle1x = self.locks[l1x].acquire_read();

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH,
                row_store_wf(self.consts@, handle1x@.rows[row as nat], row as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] handle1x@.rows[row as nat].token.value()[j]).is_some(),
            decreases WIDTH - i,
        {
            let entry = self.matrix[row].borrow(
                Tracked(&handle1x.borrow().rows.tracked_borrow(row as nat).pt))[i];
            if entry.is_none() {
                handle1x.release_read();
                return Attempt::Free(i);
            }
            i += 1;
        }

        let c = rand_u8() as usize % WIDTH;
        let key = self.matrix[row].borrow(
             Tracked(&handle1x.borrow().rows.tracked_borrow(row as nat).pt))[c].unwrap().0;
        proof {
            self.instance.hash_is_right(key, row as nat, c as nat,
              &handle1x.borrow().rows.tracked_borrow(row as nat).token);
        }

        handle1x.release_read();
        Attempt::Unfree(c, key)
    }

    fn do_swing(&self, key: Key, old_row: usize, old_col: usize, new_row: usize, new_col: usize)
        requires self.wf(),
            0 <= old_row < HEIGHT,
            0 <= new_row < HEIGHT,
            0 <= old_col < WIDTH,
            0 <= new_col < WIDTH,
            old_row != new_row,
            old_row == hash1(key) || old_row == hash2(key),
            new_row == hash1(key) || new_row == hash2(key),
    {

        let l1 = compute_lock_for_row(old_row);
        let l2 = compute_lock_for_row(new_row);

        let l1x = if l1 < l2 { l1 } else { l2 };
        let l2x = if l1 < l2 { l2 } else { l1 };

        let (Tracked(lock1x), handle1x) = self.locks[l1x].acquire_write();
        let (Tracked(lock2x), handle2x) = self.locks[l2x].acquire_write();

        let tracked mut lock1;
        let tracked mut lock2;
        let tracked mut r1;
        let tracked mut r2;
        proof {
            if l1 < l2 {
                lock1 = lock1x;
                lock2 = lock2x;
            } else {
                lock1 = lock2x;
                lock2 = lock1x;
            }
            r1 = lock1.rows.tracked_remove(old_row as nat);
            r2 = lock2.rows.tracked_remove(new_row as nat);
        }

        let mut entry1 = *self.matrix[old_row].borrow(Tracked(&r1.pt));
        let mut entry2 = *self.matrix[new_row].borrow(Tracked(&r2.pt));

        if entry1[old_col].is_some() && entry1[old_col].unwrap().0 == key && entry2[new_col].is_none() {
            entry2[new_col] = entry1[old_col];
            entry1[old_col] = None;

            self.matrix[old_row].write(Tracked(&mut r1.pt), entry1);
            self.matrix[new_row].write(Tracked(&mut r2.pt), entry2);

            proof {
                let tracked (Tracked(tok1), Tracked(tok2)) =
                    self.instance.swing(key, old_row as nat, old_col as nat, new_row as nat, new_col as nat, r1.token, r2.token);
                r1.token = tok1;
                r2.token = tok2;
            }
        }

        proof {
            lock1.rows.tracked_insert(old_row as nat, r1);
            lock2.rows.tracked_insert(new_row as nat, r2);
            if l1 < l2 {
                lock1x = lock1;
                lock2x = lock2;
            } else {
                lock1x = lock2;
                lock2x = lock1;
            }
        }

        handle1x.release_write(Tracked(lock1x));
        handle2x.release_write(Tracked(lock2x));
    }
}

pub type ReadAU = AtomicUpdate<MPointsTo, Commit<MPointsTo>, ReadPred>;
pub type InsertAU = AtomicUpdate<MPointsTo, Commit<MPointsTo>, InsertPred>;
pub type DeleteAU = AtomicUpdate<MPointsTo, Commit<MPointsTo>, DeletePred>;

}
