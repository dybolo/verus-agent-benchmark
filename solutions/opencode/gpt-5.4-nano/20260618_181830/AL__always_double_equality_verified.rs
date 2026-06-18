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
        TempPred {
            pred: pred,
        }
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

    proof fn execution_suffix_compose<T>(ex: Execution<T>, a: nat, b: nat)
        ensures ex.suffix(a).suffix(b) == ex.suffix(b + a)
    {
        execution_equality(ex.suffix(a).suffix(b), ex.suffix(b + a));
    }

proof fn always_double_equality<T>(p: TempPred<T>)
    ensures always(always(p)) == always(p),
{
    let aa = always(always(p));
    let a = always(p);

    // Prove aa.entails(a) and a.entails(aa), then use the extensionality lemma.
    assert(aa.entails(a)) by {
        assert forall |ex: Execution<T>| aa.satisfied_by(ex) implies a.satisfied_by(ex) by {
            if aa.satisfied_by(ex) {
                assert forall |i: nat| #[trigger] p.satisfied_by(ex.suffix(i)) by {
                    // From aa.satisfied_by(ex), instantiate the outer "always" at position 0.
                    assert(always(p).satisfied_by(ex.suffix(0))) by {
                        // Triggering on the `always(p).satisfied_by(ex.suffix(j))` term.
                    };

                    // From always(p).satisfied_by(ex.suffix(0)), instantiate the inner "always" at i.
                    assert(p.satisfied_by((ex.suffix(0)).suffix(i))) by {
                        // Triggering on the `p.satisfied_by((ex.suffix(0)).suffix(k))` term.
                    };

                    // (ex.suffix(0)).suffix(i) == ex.suffix(i)
                    execution_suffix_compose(ex, 0, i);
                }
            }
        };
    };

    assert(a.entails(aa)) by {
        assert forall |ex: Execution<T>| a.satisfied_by(ex) implies aa.satisfied_by(ex) by {
            if a.satisfied_by(ex) {
                assert forall |j: nat| #[trigger] always(p).satisfied_by(ex.suffix(j)) by {
                    assert forall |i: nat| #[trigger] p.satisfied_by((ex.suffix(j)).suffix(i)) by {
                        // From a.satisfied_by(ex), instantiate at (i + j).
                        assert(p.satisfied_by(ex.suffix(i + j))) by {
                            // Triggering on the `p.satisfied_by(ex.suffix(n))` term.
                        };

                        // (ex.suffix(j)).suffix(i) == ex.suffix(i + j)
                        execution_suffix_compose(ex, j, i);
                    }
                }
            }
        };
    };

    temp_pred_equality(aa, a);
}


}
