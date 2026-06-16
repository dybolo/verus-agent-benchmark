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

    pub open spec fn and(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) && other.satisfied_by(ex))
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
proof fn always_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires always(p).satisfied_by(ex),
    ensures forall |i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
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

pub proof fn always_and_equality<T>(p: TempPred<T>, q: TempPred<T>)
    ensures always(p.and(q)) == always(p).and(always(q)),
{
    let r1: TempPred<T> = always(p.and(q));
    let r2: TempPred<T> = always(p).and(always(q));

    // Prove r1 entails r2.
    assert forall|ex: Execution<T>| r1.satisfied_by(ex) ==> r2.satisfied_by(ex) by {
        if r1.satisfied_by(ex) {
            // Show both `always(p)` and `always(q)`.
            assert forall|i: nat| p.satisfied_by(ex.suffix(i)) by {
                assert((p.and(q)).satisfied_by(ex.suffix(i)));
                // unfold `and`: p.and(q) holds iff both p and q hold
                assert(p.satisfied_by(ex.suffix(i)));
            };
            assert forall|i: nat| q.satisfied_by(ex.suffix(i)) by {
                assert((p.and(q)).satisfied_by(ex.suffix(i)));
                assert(q.satisfied_by(ex.suffix(i)));
            };

            assert(r2.satisfied_by(ex));
        }
    };

    // Prove r2 entails r1.
    assert forall|ex: Execution<T>| r2.satisfied_by(ex) ==> r1.satisfied_by(ex) by {
        if r2.satisfied_by(ex) {
            assert forall|i: nat| p.satisfied_by(ex.suffix(i)) by {
            };
            assert forall|i: nat| q.satisfied_by(ex.suffix(i)) by {
            };

            assert forall|i: nat| (p.and(q)).satisfied_by(ex.suffix(i)) by {
                assert(p.satisfied_by(ex.suffix(i)));
                assert(q.satisfied_by(ex.suffix(i)));
                assert((p.and(q)).satisfied_by(ex.suffix(i)));
            };

            assert(r1.satisfied_by(ex));
        }
    };

    temp_pred_equality(r1, r2);
}


}
