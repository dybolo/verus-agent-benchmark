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

    pub open spec fn or(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) || other.satisfied_by(ex))
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

pub open spec fn later<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| temp_pred.satisfied_by(ex.suffix(1)))
}

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}


// File: rules.rs
spec fn eventually_choose_witness<T>(ex: Execution<T>, p: TempPred<T>) -> nat
    recommends exists |i| p.satisfied_by(#[trigger] ex.suffix(i)),
{
    let witness = choose |i| p.satisfied_by(#[trigger] ex.suffix(i));
    witness
}


#[verifier::external_body]
proof fn always_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires always(p).satisfied_by(ex),
    ensures forall |i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
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
proof fn eventually_proved_by_witness<T>(ex: Execution<T>, p: TempPred<T>, witness_idx: nat)
    requires p.satisfied_by(ex.suffix(witness_idx)),
    ensures eventually(p).satisfied_by(ex)
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn always_p_or_eventually_q<T>(ex: Execution<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        always(p.and(next).implies(later(p).or(later(q)))).satisfied_by(ex),
        always(next).satisfied_by(ex),
    ensures always(p.implies(always(p).or(eventually(q)))).satisfied_by(ex),
	{
		unimplemented!()
	}

// Helper: extract a spec entails fact as a satisfied_by on a specific execution.
proof fn entails_apply<T>(spec: TempPred<T>, p: TempPred<T>, ex: Execution<T>)
    requires
        spec.entails(p),
        spec.satisfied_by(ex),
    ensures
        p.satisfied_by(ex),
{
    // spec.entails(p) = valid(spec.implies(p)) = forall ex', spec.implies(p).satisfied_by(ex')
    // Provide trigger to instantiate the forall at our specific ex:
    assert(spec.implies(p).satisfied_by(ex));
    // Now apply the implication
    implies_apply(ex, spec, p);
}

pub proof fn transform_leads_to_with_until<T>(spec: TempPred<T>, next: TempPred<T>, p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>)
    requires
        spec.entails(p1.leads_to(q1)),
        spec.entails(always(p2.and(next).implies(later(p2).or(later(q2))))),
        spec.entails(always(next)),
    ensures
        spec.entails(p1.and(p2).leads_to((q1.and(p2)).or(q2))),
{
    assert forall |ex: Execution<T>| spec.satisfied_by(ex) implies
        p1.and(p2).leads_to((q1.and(p2)).or(q2)).satisfied_by(ex) by
    {
        // Extract spec facts for this execution
        entails_apply(spec, p1.leads_to(q1), ex);
        entails_apply(spec, always(p2.and(next).implies(later(p2).or(later(q2)))), ex);
        entails_apply(spec, always(next), ex);

        // Apply always_p_or_eventually_q: get always(p2 => □p2 ∨ ◇q2)
        always_p_or_eventually_q(ex, next, p2, q2);

        // Unfold the two always facts we need
        always_unfold(ex, p1.implies(eventually(q1)));
        always_unfold(ex, p2.implies(always(p2).or(eventually(q2))));

        // Prove: ∀i, if p1∧p2 holds at suffix(i), then ◇((q1∧p2)∨q2) holds at suffix(i)
        assert forall |i: nat|
            p1.and(p2).implies(eventually((q1.and(p2)).or(q2))).satisfied_by(#[trigger] ex.suffix(i)) by
        {
            if p1.and(p2).satisfied_by(ex.suffix(i)) {
                // Extract p1 and p2 individually
                assert(p1.satisfied_by(ex.suffix(i)));
                assert(p2.satisfied_by(ex.suffix(i)));

                // Use p1 => ◇q1 to get a witness j0 where q1 holds
                implies_apply(ex.suffix(i), p1, eventually(q1));
                let j0 = eventually_choose_witness(ex.suffix(i), q1);
                assert(q1.satisfied_by(ex.suffix(i).suffix(j0)));

                // Use p2 => □p2 ∨ ◇q2
                implies_apply(ex.suffix(i), p2, always(p2).or(eventually(q2)));
                // Unfold the `or` to get a boolean disjunction
                assert(always(p2).satisfied_by(ex.suffix(i)) ||
                       eventually(q2).satisfied_by(ex.suffix(i)));

                if always(p2).satisfied_by(ex.suffix(i)) {
                    // p2 holds at all positions from suffix(i), including j0
                    always_unfold(ex.suffix(i), p2);
                    assert(p2.satisfied_by(ex.suffix(i).suffix(j0)));
                    // So q1 ∧ p2 holds at j0
                    assert(q1.and(p2).satisfied_by(ex.suffix(i).suffix(j0)));
                    // Therefore (q1∧p2)∨q2 holds at j0
                    assert((q1.and(p2)).or(q2).satisfied_by(ex.suffix(i).suffix(j0)));
                    eventually_proved_by_witness(ex.suffix(i), (q1.and(p2)).or(q2), j0);
                } else {
                    // q2 eventually holds at suffix(i)
                    assert(eventually(q2).satisfied_by(ex.suffix(i)));
                    let k0 = eventually_choose_witness(ex.suffix(i), q2);
                    assert(q2.satisfied_by(ex.suffix(i).suffix(k0)));
                    // Therefore (q1∧p2)∨q2 holds at k0
                    assert((q1.and(p2)).or(q2).satisfied_by(ex.suffix(i).suffix(k0)));
                    eventually_proved_by_witness(ex.suffix(i), (q1.and(p2)).or(q2), k0);
                }
            }
        };

        // The above forall is exactly always(p1.and(p2).implies(eventually(...))).satisfied_by(ex)
        assert(always(p1.and(p2).implies(eventually((q1.and(p2)).or(q2)))).satisfied_by(ex));
        // Which is the definition of leads_to
        assert(p1.and(p2).leads_to((q1.and(p2)).or(q2)).satisfied_by(ex));
    };

    // From the above, we have established spec.entails(p1.and(p2).leads_to(...))
    assert(spec.entails(p1.and(p2).leads_to((q1.and(p2)).or(q2))));
}


}
