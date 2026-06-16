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

proof fn execution_suffix_zero<T>(ex: Execution<T>)
    ensures ex.suffix(0) == ex,
{
    execution_equality(ex.suffix(0), ex);
}

proof fn execution_suffix_add<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix(i + j),
{
    execution_equality(ex.suffix(i).suffix(j), ex.suffix(i + j));
}

proof fn always_double_equality<T>(p: TempPred<T>)
    ensures always(always(p)) == always(p),
{
    let a: TempPred<T> = always(p);
    let b: TempPred<T> = always(a);

    // b.entails(a)
    assert forall|ex: Execution<T>| b.satisfied_by(ex) implies a.satisfied_by(ex) by {
        // We need: for all i, p(ex.suffix(i))
        assert forall|i: nat| #[trigger] p.satisfied_by(ex.suffix(i)) by {
            // From b.satisfied_by(ex), we get a.satisfied_by(ex.suffix(i))
            assert(a.satisfied_by(ex.suffix(i)));
            // From that, we get p((ex.suffix(i)).suffix(0))
            assert(p.satisfied_by(ex.suffix(i).suffix(0)));
            // And (ex.suffix(i)).suffix(0) == ex.suffix(i)
            execution_suffix_add(ex, i, 0);
            assert(p.satisfied_by(ex.suffix(i)));
        }
    };
    assert(b.entails(a));

    // a.entails(b)
    assert forall|ex: Execution<T>| a.satisfied_by(ex) implies b.satisfied_by(ex) by {
        // Need: for all j, a.satisfied_by(ex.suffix(j))
        assert forall|j: nat| #[trigger] a.satisfied_by(ex.suffix(j)) by {
            // Unfold a.satisfied_by(ex.suffix(j))
            assert forall|i: nat| #[trigger] p.satisfied_by(ex.suffix(j).suffix(i)) by {
                // From a.satisfied_by(ex), we get p(ex.suffix(j+i))
                execution_suffix_add(ex, j, i);
                assert(p.satisfied_by(ex.suffix(j + i)));
                assert(p.satisfied_by(ex.suffix(j).suffix(i)));
            }
        }
    };
    assert(a.entails(b));

    temp_pred_equality(b, a);
}


}
