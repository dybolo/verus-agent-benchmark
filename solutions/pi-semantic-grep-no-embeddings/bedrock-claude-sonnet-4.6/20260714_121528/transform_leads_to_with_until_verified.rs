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
    assert forall |ex: Execution<T>| spec.satisfied_by(ex) implies
        p1.and(p2).leads_to((q1.and(p2)).or(q2)).satisfied_by(ex) by {

        // Instantiate spec.entails(p1.leads_to(q1)) at ex
        implies_apply(ex, spec, p1.leads_to(q1));
        // p1.leads_to(q1).satisfied_by(ex) = always(p1.implies(eventually(q1))).satisfied_by(ex)
        always_unfold(ex, p1.implies(eventually(q1)));
        // forall i: nat, p1.implies(eventually(q1)).satisfied_by(ex.suffix(i))

        // Instantiate spec.entails(always(p2.and(next).implies(later(p2).or(later(q2))))) at ex
        implies_apply(ex, spec, always(p2.and(next).implies(later(p2).or(later(q2)))));
        // Instantiate spec.entails(always(next)) at ex
        implies_apply(ex, spec, always(next));

        // Apply always_p_or_eventually_q to get: always(p2.implies(always(p2).or(eventually(q2)))).satisfied_by(ex)
        always_p_or_eventually_q(ex, next, p2, q2);
        always_unfold(ex, p2.implies(always(p2).or(eventually(q2))));
        // forall i: nat, p2.implies(always(p2).or(eventually(q2))).satisfied_by(ex.suffix(i))

        // Show forall i, (p1.and(p2)).implies(eventually((q1.and(p2)).or(q2))).satisfied_by(ex.suffix(i))
        assert forall |i: nat|
            (p1.and(p2)).implies(eventually((q1.and(p2)).or(q2))).satisfied_by(#[trigger] ex.suffix(i)) by {

            if (p1.and(p2)).satisfied_by(ex.suffix(i)) {
                // p1 holds at i
                implies_apply(ex.suffix(i), p1, eventually(q1));
                // eventually(q1) holds at ex.suffix(i); get witness j
                let j = eventually_choose_witness(ex.suffix(i), q1);
                // q1.satisfied_by(ex.suffix(i).suffix(j))

                // p2 holds at i
                implies_apply(ex.suffix(i), p2, always(p2).or(eventually(q2)));
                // always(p2) or eventually(q2) holds at ex.suffix(i)

                if always(p2).satisfied_by(ex.suffix(i)) {
                    // p2 holds at all positions from i
                    always_unfold(ex.suffix(i), p2);
                    // p2.satisfied_by(ex.suffix(i).suffix(j))
                    // q1.satisfied_by(ex.suffix(i).suffix(j)) (from witness j above)
                    // Therefore (q1.and(p2)).or(q2) holds at ex.suffix(i).suffix(j)
                    eventually_proved_by_witness(ex.suffix(i), (q1.and(p2)).or(q2), j);
                } else {
                    // eventually(q2) holds at ex.suffix(i); get witness k
                    let k = eventually_choose_witness(ex.suffix(i), q2);
                    // q2.satisfied_by(ex.suffix(i).suffix(k))
                    // Therefore (q1.and(p2)).or(q2) holds at ex.suffix(i).suffix(k)
                    eventually_proved_by_witness(ex.suffix(i), (q1.and(p2)).or(q2), k);
                }
            }
        };
        // The above forall proves always((p1.and(p2)).implies(eventually((q1.and(p2)).or(q2)))).satisfied_by(ex)
        // which is p1.and(p2).leads_to((q1.and(p2)).or(q2)).satisfied_by(ex)
    }
}


}
