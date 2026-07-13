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

pub proof fn transform_leads_to_with_until<T>(spec: TempPred<T>, next: TempPred<T>, p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>)
    requires
        spec.entails(p1.leads_to(q1)),
        spec.entails(always(p2.and(next).implies(later(p2).or(later(q2))))),
        spec.entails(always(next)),
    ensures
        spec.entails(p1.and(p2).leads_to((q1.and(p2)).or(q2))),
{
    assert forall |ex: Execution<T>| #[trigger] spec.satisfied_by(ex)
        implies p1.and(p2).leads_to((q1.and(p2)).or(q2)).satisfied_by(ex) by
    {
        // Extract conclusions for this specific execution from the entails hypotheses
        implies_apply(ex, spec, p1.leads_to(q1));
        implies_apply(ex, spec, always(p2.and(next).implies(later(p2).or(later(q2)))));
        implies_apply(ex, spec, always(next));

        // Use always_p_or_eventually_q to derive: always(p2 -> always(p2) or eventually(q2))
        always_p_or_eventually_q(ex, next, p2, q2);

        // Unfold: always(p1 -> eventually(q1)) for all positions
        always_unfold(ex, p1.implies(eventually(q1)));
        // Unfold: always(p2 -> always(p2) or eventually(q2)) for all positions
        always_unfold(ex, p2.implies(always(p2).or(eventually(q2))));

        // Now prove the inner always: forall i, (p1 and p2) -> eventually((q1 and p2) or q2) at ex.suffix(i)
        assert forall |i: nat|
            p1.and(p2).implies(eventually((q1.and(p2)).or(q2))).satisfied_by(#[trigger] ex.suffix(i)) by
        {
            if p1.and(p2).satisfied_by(ex.suffix(i)) {
                // Extract p1 and p2 from the conjunction
                assert(p1.satisfied_by(ex.suffix(i)));
                assert(p2.satisfied_by(ex.suffix(i)));

                // From p1 ~> q1: p1 at position i gives eventually(q1) at position i
                implies_apply(ex.suffix(i), p1, eventually(q1));

                // From always(p2 -> always(p2) or eventually(q2)): get the disjunction at position i
                implies_apply(ex.suffix(i), p2, always(p2).or(eventually(q2)));

                if always(p2).satisfied_by(ex.suffix(i)) {
                    // Case A: p2 holds forever from position i
                    // Unfold always(p2) to get p2 at every future position
                    always_unfold(ex.suffix(i), p2);
                    // Get witness j where q1 holds
                    assert(eventually(q1).satisfied_by(ex.suffix(i)));
                    assert(exists |j: nat| q1.satisfied_by(#[trigger] ex.suffix(i).suffix(j)));
                    let j: nat = choose |j: nat| q1.satisfied_by(ex.suffix(i).suffix(j));
                    assert(q1.satisfied_by(ex.suffix(i).suffix(j)));
                    // p2 also holds at j since always(p2) from i
                    assert(p2.satisfied_by(ex.suffix(i).suffix(j)));
                    // So q1 and p2 both hold at j
                    assert(q1.and(p2).satisfied_by(ex.suffix(i).suffix(j)));
                    // Therefore (q1 and p2) or q2 holds at j
                    assert((q1.and(p2)).or(q2).satisfied_by(ex.suffix(i).suffix(j)));
                    // So eventually((q1 and p2) or q2) holds from i
                    eventually_proved_by_witness(ex.suffix(i), (q1.and(p2)).or(q2), j);
                } else {
                    // Case B: eventually(q2) holds from position i
                    assert(eventually(q2).satisfied_by(ex.suffix(i)));
                    assert(exists |k: nat| q2.satisfied_by(#[trigger] ex.suffix(i).suffix(k)));
                    let k: nat = choose |k: nat| q2.satisfied_by(ex.suffix(i).suffix(k));
                    assert(q2.satisfied_by(ex.suffix(i).suffix(k)));
                    // Therefore (q1 and p2) or q2 holds at k
                    assert((q1.and(p2)).or(q2).satisfied_by(ex.suffix(i).suffix(k)));
                    // So eventually((q1 and p2) or q2) holds from i
                    eventually_proved_by_witness(ex.suffix(i), (q1.and(p2)).or(q2), k);
                }
            }
        };
    };
}


}
