use vstd::prelude::*;

fn main() {}

verus!{

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
        TempPred { pred }
    }

    pub open spec fn satisfied_by(self, execution: Execution<T>) -> bool {
        (self.pred)(execution)
    }

    pub open spec fn and(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) && other.satisfied_by(ex))
    }

    pub open spec fn implies(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) ==> other.satisfied_by(ex))
    }
}

pub open spec fn always<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}

	#[verifier::external_body]
proof fn always_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires always(p).satisfied_by(ex),
    ensures forall |i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
{
    unimplemented!()
}

proof fn always_distributed_by_and<T>(p: TempPred<T>, q: TempPred<T>)
    ensures valid(always(p.and(q)).implies(always(p).and(always(q)))) ,
{
    // Show the implication for all executions.
    assert forall |ex: Execution<T>|
        always(p.and(q)).satisfied_by(ex)
        ==> (always(p).and(always(q))).satisfied_by(ex)
    by {
        if always(p.and(q)).satisfied_by(ex) {
            // Prove always(p)
            assert(always(p).satisfied_by(ex)) by {
                assert forall |i: nat| #[trigger] p.satisfied_by(ex.suffix(i)) by {
                    assert(p.satisfied_by(ex.suffix(i)) && q.satisfied_by(ex.suffix(i))) by {
                        assert((p.and(q)).satisfied_by(ex.suffix(i)));
                    };
                    assert(p.satisfied_by(ex.suffix(i))) by {
                        assert(p.satisfied_by(ex.suffix(i)) && q.satisfied_by(ex.suffix(i)));
                    };
                };
            };

            // Prove always(q)
            assert(always(q).satisfied_by(ex)) by {
                assert forall |i: nat| #[trigger] q.satisfied_by(ex.suffix(i)) by {
                    assert(p.satisfied_by(ex.suffix(i)) && q.satisfied_by(ex.suffix(i))) by {
                        assert((p.and(q)).satisfied_by(ex.suffix(i)));
                    };
                    assert(q.satisfied_by(ex.suffix(i))) by {
                        assert(p.satisfied_by(ex.suffix(i)) && q.satisfied_by(ex.suffix(i)));
                    };
                };
            };

            assert((always(p).and(always(q))).satisfied_by(ex)) by {
                assert(always(p).satisfied_by(ex) && always(q).satisfied_by(ex));
            };
        }
    };
}

}
