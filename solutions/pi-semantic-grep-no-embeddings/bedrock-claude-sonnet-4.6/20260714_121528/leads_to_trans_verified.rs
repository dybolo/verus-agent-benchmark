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

    pub open spec fn leads_to(self, other: Self) -> Self {
        always(self.implies(eventually(other)))
    }

    pub open spec fn entails(self, other: Self) -> bool {
        valid(self.implies(other))
    }

}


pub open spec fn always<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn eventually<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| exists |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
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
proof fn eventually_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires eventually(p).satisfied_by(ex),
    ensures exists |i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn implies_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.implies(q).satisfied_by(ex),
        p.satisfied_by(ex),
    ensures q.satisfied_by(ex),
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn entails_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.entails(q),
        p.satisfied_by(ex),
    ensures q.satisfied_by(ex),
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn eventually_propagate_backwards<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires eventually(p).satisfied_by(ex.suffix(i)),
    ensures eventually(p).satisfied_by(ex),
	{
		unimplemented!()
	}

spec fn eventually_choose_witness<T>(ex: Execution<T>, p: TempPred<T>) -> nat
    recommends exists |i| p.satisfied_by(#[trigger] ex.suffix(i)),
{
    let witness = choose |i| p.satisfied_by(#[trigger] ex.suffix(i));
    witness
}

	#[verifier::external_body]
pub proof fn execution_equality<T>(ex1: Execution<T>, ex2: Execution<T>)
    requires forall |i: nat| #[trigger] (ex1.nat_to_state)(i) == (ex2.nat_to_state)(i),
    ensures ex1 == ex2,
	{
		unimplemented!()
	}

pub proof fn leads_to_trans<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(q)),
        spec.entails(q.leads_to(r)),
    ensures spec.entails(p.leads_to(r)),
{
    assert forall |ex: Execution<T>| spec.satisfied_by(ex) implies p.leads_to(r).satisfied_by(ex) by {
        // Extract the leads_to facts for this execution
        entails_apply(ex, spec, p.leads_to(q));
        entails_apply(ex, spec, q.leads_to(r));
        // Unfold: for all i, p.implies(eventually(q)) holds at ex.suffix(i)
        always_unfold(ex, p.implies(eventually(q)));
        // Unfold: for all i, q.implies(eventually(r)) holds at ex.suffix(i)
        always_unfold(ex, q.implies(eventually(r)));

        // Show: for all i, p.implies(eventually(r)) holds at ex.suffix(i)
        assert forall |i: nat| #[trigger] p.implies(eventually(r)).satisfied_by(ex.suffix(i)) by {
            if p.satisfied_by(ex.suffix(i)) {
                // From p leads_to q: eventually q holds at ex.suffix(i)
                implies_apply(ex.suffix(i), p, eventually(q));
                // Extract witness j such that q holds at ex.suffix(i).suffix(j)
                eventually_unfold(ex.suffix(i), q);
                let j = eventually_choose_witness(ex.suffix(i), q);
                // Key lemma: ex.suffix(i).suffix(j) == ex.suffix(i + j)
                assert(ex.suffix(i).suffix(j) == ex.suffix(i + j)) by {
                    execution_equality(ex.suffix(i).suffix(j), ex.suffix(i + j));
                };
                // q holds at ex.suffix(i+j), so by q leads_to r, eventually r holds there
                implies_apply(ex.suffix(i + j), q, eventually(r));
                // Propagate: eventually r at ex.suffix(i).suffix(j) implies eventually r at ex.suffix(i)
                eventually_propagate_backwards(ex.suffix(i), r, j);
            }
        };
    };
}


}
