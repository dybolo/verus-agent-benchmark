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
        // Unpack the hypotheses for this execution
        entails_apply(ex, spec, p.leads_to(q));
        entails_apply(ex, spec, q.leads_to(r));

        // p.leads_to(q) = always(p.implies(eventually(q)))
        always_unfold(ex, p.implies(eventually(q)));
        // q.leads_to(r) = always(q.implies(eventually(r)))
        always_unfold(ex, q.implies(eventually(r)));

        // We now prove: forall i, p.implies(eventually(r)).satisfied_by(ex.suffix(i))
        assert forall |i: nat| #[trigger] p.implies(eventually(r)).satisfied_by(ex.suffix(i)) by {
            if p.satisfied_by(ex.suffix(i)) {
                // From p ~> q: p.satisfied_by(ex.suffix(i)) => eventually(q).satisfied_by(ex.suffix(i))
                assert(p.implies(eventually(q)).satisfied_by(ex.suffix(i)));
                implies_apply(ex.suffix(i), p, eventually(q));

                // Unpack the existential to get witness j
                eventually_unfold(ex.suffix(i), q);
                let j = eventually_choose_witness(ex.suffix(i), q);
                assert(q.satisfied_by(ex.suffix(i).suffix(j)));

                // Prove ex.suffix(i).suffix(j) == ex.suffix(i + j)
                assert forall |k: nat| #[trigger] (ex.suffix(i).suffix(j).nat_to_state)(k)
                    == (ex.suffix(i + j).nat_to_state)(k) by {
                    assert((ex.suffix(i).suffix(j).nat_to_state)(k) == (ex.nat_to_state)(k + j + i));
                    assert((ex.suffix(i + j).nat_to_state)(k) == (ex.nat_to_state)(k + (i + j)));
                    assert(k + j + i == k + (i + j)) by (nonlinear_arith);
                };
                execution_equality(ex.suffix(i).suffix(j), ex.suffix(i + j));
                // Now q.satisfied_by(ex.suffix(i + j))
                assert(q.satisfied_by(ex.suffix(i + j)));

                // From q ~> r: q.satisfied_by(ex.suffix(i+j)) => eventually(r).satisfied_by(ex.suffix(i+j))
                assert(q.implies(eventually(r)).satisfied_by(ex.suffix(i + j)));
                implies_apply(ex.suffix(i + j), q, eventually(r));

                // eventually(r).satisfied_by(ex.suffix(i + j))
                // = eventually(r).satisfied_by(ex.suffix(i).suffix(j))
                assert(eventually(r).satisfied_by(ex.suffix(i).suffix(j)));

                // Propagate backwards to get eventually(r).satisfied_by(ex.suffix(i))
                eventually_propagate_backwards(ex.suffix(i), r, j);
            }
        };
        // From the forall: always(p.implies(eventually(r))).satisfied_by(ex)
        // = p.leads_to(r).satisfied_by(ex)
    };
}


}
