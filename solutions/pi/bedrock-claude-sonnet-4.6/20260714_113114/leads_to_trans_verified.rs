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

proof fn suffix_suffix_eq<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix((i + j) as nat),
{
    assert forall |k: nat| #[trigger] (ex.suffix(i).suffix(j).nat_to_state)(k) == (ex.suffix((i + j) as nat).nat_to_state)(k) by {
        // ex.suffix(i).suffix(j).nat_to_state(k)
        //   = ex.suffix(i).nat_to_state(k + j)
        //   = ex.nat_to_state(k + j + i)
        // ex.suffix(i+j).nat_to_state(k)
        //   = ex.nat_to_state(k + (i+j))
        // k + j + i == k + i + j by commutativity -- Verus arithmetic should handle this
        assert((k + j + i) == (k + (i + j) as nat)) by (nonlinear_arith);
    };
    execution_equality(ex.suffix(i).suffix(j), ex.suffix((i + j) as nat));
}

pub proof fn leads_to_trans<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(q)),
        spec.entails(q.leads_to(r)),
    ensures spec.entails(p.leads_to(r)),
{
    assert forall |ex: Execution<T>| spec.satisfied_by(ex) implies p.leads_to(r).satisfied_by(ex) by {
        // Get p.leads_to(q) and q.leads_to(r) satisfied by ex
        entails_apply(ex, spec, p.leads_to(q));
        entails_apply(ex, spec, q.leads_to(r));

        // Unfold the always: for all i, p.implies(eventually(q)) holds at ex.suffix(i)
        // and q.implies(eventually(r)) holds at ex.suffix(i)
        always_unfold(ex, p.implies(eventually(q)));
        always_unfold(ex, q.implies(eventually(r)));

        // Now show: for all i, p.implies(eventually(r)) holds at ex.suffix(i)
        assert forall |i: nat| p.implies(eventually(r)).satisfied_by(#[trigger] ex.suffix(i)) by {
            if p.satisfied_by(ex.suffix(i)) {
                // Since p holds at suffix(i) and p ~> q holds, eventually(q) holds at suffix(i)
                implies_apply(ex.suffix(i), p, eventually(q));

                // Get witness j where q holds at suffix(i).suffix(j)
                eventually_unfold(ex.suffix(i), q);
                let j = eventually_choose_witness(ex.suffix(i), q);
                // q holds at ex.suffix(i).suffix(j)
                assert(q.satisfied_by(ex.suffix(i).suffix(j)));

                // Show suffix(i).suffix(j) == suffix(i+j)
                suffix_suffix_eq(ex, i, j);
                let ij: nat = (i + j) as nat;
                assert(ex.suffix(i).suffix(j) == ex.suffix(ij));

                // So q holds at ex.suffix(ij)
                assert(q.satisfied_by(ex.suffix(ij)));

                // Since q ~> r holds at all positions, q.implies(eventually(r)) holds at suffix(ij)
                // implies_apply gives eventually(r) at suffix(ij)
                implies_apply(ex.suffix(ij), q, eventually(r));

                // eventually(r) holds at ex.suffix(ij) = ex.suffix(i).suffix(j)
                assert(eventually(r).satisfied_by(ex.suffix(i).suffix(j)));

                // Propagate backwards: eventually(r) at suffix(i)
                eventually_propagate_backwards(ex.suffix(i), r, j);
            }
        };

        // Now always(p.implies(eventually(r))) is satisfied by ex, i.e., p.leads_to(r)
        assert(always(p.implies(eventually(r))).satisfied_by(ex));
    };
}


}
