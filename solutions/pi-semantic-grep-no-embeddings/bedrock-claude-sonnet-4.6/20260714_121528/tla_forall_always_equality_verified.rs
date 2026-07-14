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

pub open spec fn tla_forall<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |a: A| #[trigger] a_to_temp_pred(a).satisfied_by(ex))
}

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}


// File: rules.rs
	#[verifier::external_body]
proof fn always_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires always(p).satisfied_by(ex),
    ensures forall |i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn tla_forall_unfold<T, A>(ex: Execution<T>, a_to_p: spec_fn(A) -> TempPred<T>)
    requires tla_forall(a_to_p).satisfied_by(ex),
    ensures forall |a| #[trigger] a_to_p(a).satisfied_by(ex),
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

pub proof fn tla_forall_always_equality<T, A>(a_to_p: spec_fn(A) -> TempPred<T>)
    ensures tla_forall(|a: A| always(a_to_p(a))) == always(tla_forall(a_to_p)),
{
    let lhs = tla_forall(|a: A| always(a_to_p(a)));
    let rhs = always(tla_forall(a_to_p));

    // Prove lhs.entails(rhs): tla_forall(|a| always(a_to_p(a))) |= always(tla_forall(a_to_p))
    assert(lhs.entails(rhs)) by {
        assert forall |ex: Execution<T>| lhs.satisfied_by(ex) implies rhs.satisfied_by(ex) by {
            // lhs.satisfied_by(ex) means: forall a, always(a_to_p(a)).satisfied_by(ex)
            // For each i, show tla_forall(a_to_p).satisfied_by(ex.suffix(i))
            assert forall |i: nat| tla_forall(a_to_p).satisfied_by(#[trigger] ex.suffix(i)) by {
                // For each a, show a_to_p(a).satisfied_by(ex.suffix(i))
                assert forall |a: A| #[trigger] a_to_p(a).satisfied_by(ex.suffix(i)) by {
                    // From lhs: always(a_to_p(a)).satisfied_by(ex)
                    // which means forall j, a_to_p(a).satisfied_by(ex.suffix(j))
                    assert(always(a_to_p(a)).satisfied_by(ex)) by {
                        // lhs is open spec, tla_forall is open spec, satisfied_by is open spec
                        // lhs.satisfied_by(ex) = forall a, (|a| always(a_to_p(a)))(a).satisfied_by(ex)
                        // beta reduction: (|a| always(a_to_p(a)))(a) == always(a_to_p(a))
                        assert((|a: A| always(a_to_p(a)))(a) == always(a_to_p(a)));
                    };
                    always_unfold(ex, a_to_p(a));
                };
            };
        };
    };

    // Prove rhs.entails(lhs): always(tla_forall(a_to_p)) |= tla_forall(|a| always(a_to_p(a)))
    assert(rhs.entails(lhs)) by {
        assert forall |ex: Execution<T>| rhs.satisfied_by(ex) implies lhs.satisfied_by(ex) by {
            // rhs.satisfied_by(ex) means: forall i, tla_forall(a_to_p).satisfied_by(ex.suffix(i))
            always_unfold(ex, tla_forall(a_to_p));
            // For each a, show always(a_to_p(a)).satisfied_by(ex)
            assert forall |a: A| #[trigger] always(a_to_p(a)).satisfied_by(ex) by {
                // For each i, show a_to_p(a).satisfied_by(ex.suffix(i))
                assert forall |i: nat| #[trigger] a_to_p(a).satisfied_by(ex.suffix(i)) by {
                    tla_forall_unfold(ex.suffix(i), a_to_p);
                };
            };
        };
    };

    temp_pred_equality(lhs, rhs);
}


}
