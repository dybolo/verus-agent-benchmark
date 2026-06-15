use vstd::prelude::*;

fn main() {}

verus!{

// File: defs.rs
pub struct Execution<T> {
    pub nat_to_state: spec_fn(nat) -> T,
}

impl<T> Execution<T> {

    pub open spec fn suffix(self, pos: nat) -> Self {
        Execution {
            nat_to_state: |i: nat| (self.nat_to_state)(i + pos),
        }
    }

}


#[verifier(reject_recursive_types(T))]
pub struct TempPred<T> {
    pub pred: spec_fn(Execution<T>) -> bool,
}

impl<T> TempPred<T> {

    pub open spec fn new(pred: spec_fn(Execution<T>) -> bool) -> Self {
        TempPred { pred: pred }
    }

    pub open spec fn satisfied_by(self, execution: Execution<T>) -> bool {
        (self.pred)(execution)
    }

    pub open spec fn implies(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) ==> other.satisfied_by(ex))
    }

    pub open spec fn entails(self, other: Self) -> bool {
        valid(self.implies(other))
    }

}

pub open spec fn always<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}

// File: rules.rs
#[verifier::external_body]
pub proof fn execution_equality<T>(ex1: Execution<T>, ex2: Execution<T>)
    requires forall |i: nat| #[trigger] (ex1.nat_to_state)(i) == (ex2.nat_to_state)(i),
    ensures ex1 == ex2,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn temp_pred_equality<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        p.entails(q),
        q.entails(p),
    ensures p == q,
{
    unimplemented!()
}

// --- Helper lemmas ---

proof fn execution_suffix_left_zero<T>(ex: Execution<T>, i: nat)
    ensures ex.suffix(0).suffix(i) == ex.suffix(i),
{
    // Discharge execution_equality precondition by unfolding suffix.
    assert(forall |k: nat| #[trigger]
        (ex.suffix(0).suffix(i).nat_to_state)(k)
            == (ex.suffix(i).nat_to_state)(k)) by {
        reveal(Execution::suffix);
        // both sides are ex.nat_to_state(k + i)
        assert(forall |k: nat| #[trigger]
            (ex.suffix(0).suffix(i).nat_to_state)(k)
                == (ex.nat_to_state)(k + (0 + i))) by {
            reveal(Execution::suffix);
        };
    }
    execution_equality::<T>(ex.suffix(0).suffix(i), ex.suffix(i));
}

proof fn execution_suffix_addition<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix(i + j),
{
    assert(forall |k: nat| #[trigger]
        (ex.suffix(i).suffix(j).nat_to_state)(k)
            == (ex.suffix(i + j).nat_to_state)(k)) by {
        reveal(Execution::suffix);
        // Unfold both suffix compositions.
        forall |k: nat| {
            assert((ex.suffix(i).suffix(j).nat_to_state)(k)
                == (ex.nat_to_state)((k + j) + i));
            assert((ex.suffix(i + j).nat_to_state)(k)
                == (ex.nat_to_state)(k + (i + j)));
            assert(((k + j) + i) == (k + (i + j)));
        };
    }
    execution_equality::<T>(ex.suffix(i).suffix(j), ex.suffix(i + j));
}

// --- Main lemma ---

proof fn always_double_equality<T>(p: TempPred<T>)
    ensures always(always(p)) == always(p),
{
    let q = always(p);
    let r = always(q); // always(always(p))

    // Prove r.entails(q)
    assert(r.entails(q)) by {
        reveal(TempPred::entails);
        reveal(valid);
        reveal(TempPred::implies);
        // r.entails(q) == forall ex, r.satisfied_by(ex) ==> q.satisfied_by(ex)
        assert(forall |ex: Execution<T>| #[trigger]
            r.satisfied_by(ex) ==> q.satisfied_by(ex)) by {
            forall |ex: Execution<T>| {
                if r.satisfied_by(ex) {
                    // r.satisfied_by(ex) = forall i, q.satisfied_by(ex.suffix(i))
                    reveal(always);
                    // Need q.satisfied_by(ex) = forall k, p.satisfied_by(ex.suffix(k))
                    assert(forall |k: nat| #[trigger] p.satisfied_by(ex.suffix(k))) by {
                        // choose i=k, then use q.satisfied_by(ex.suffix(k)) and j=0
                        reveal(always);
                        assert(q.satisfied_by(ex.suffix(k)));
                        reveal(always);
                        // q.satisfied_by(ex.suffix(k)) = forall j, p.satisfied_by(ex.suffix(k).suffix(j))
                        assert(p.satisfied_by(ex.suffix(k).suffix(0)));
                        execution_suffix_left_zero::<T>(ex, k);
                        assert(p.satisfied_by(ex.suffix(k)));
                    };
                }
            };
        };
    };

    // Prove q.entails(r)
    assert(q.entails(r)) by {
        reveal(TempPred::entails);
        reveal(valid);
        reveal(TempPred::implies);
        assert(forall |ex: Execution<T>| #[trigger]
            q.satisfied_by(ex) ==> r.satisfied_by(ex)) by {
            forall |ex: Execution<T>| {
                if q.satisfied_by(ex) {
                    reveal(always);
                    // Need r.satisfied_by(ex) = forall i, q.satisfied_by(ex.suffix(i))
                    assert(forall |i: nat| #[trigger] q.satisfied_by(ex.suffix(i))) by {
                        // q.satisfied_by(ex.suffix(i)) = forall j, p.satisfied_by(ex.suffix(i).suffix(j))
                        reveal(always);
                        assert(forall |j: nat| #[trigger] p.satisfied_by(ex.suffix(i).suffix(j))) by {
                            let t = i + j;
                            // From q.satisfied_by(ex), get p.satisfied_by(ex.suffix(t))
                            assert(p.satisfied_by(ex.suffix(t)));
                            execution_suffix_addition::<T>(ex, i, j);
                            assert(p.satisfied_by(ex.suffix(i).suffix(j)));
                        };
                    };
                }
            };
        };
    };

    temp_pred_equality::<T>(r, q);
}

}
