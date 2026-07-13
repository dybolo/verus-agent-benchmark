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
proof fn leads_to_unfold<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires p.leads_to(q).satisfied_by(ex),
    ensures forall |i: nat| p.implies(eventually(q)).satisfied_by(#[trigger] ex.suffix(i)),
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
proof fn always_propagate_forwards<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires always(p).satisfied_by(ex),
    ensures always(p).satisfied_by(ex.suffix(i)),
	{
		unimplemented!()
	}

pub proof fn pack_conditions_to_spec<T>(spec: TempPred<T>, c: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires spec.entails(p.and(c).leads_to(q)),
    ensures spec.and(always(c)).entails(p.leads_to(q)),
{
    // Unfold entails: show forall ex, (spec && always(c)) => p leads_to q
    assert forall |ex: Execution<T>| spec.and(always(c)).implies(p.leads_to(q)).satisfied_by(ex) by {
        if spec.and(always(c)).satisfied_by(ex) {
            // Extract spec.satisfied_by(ex) and always(c).satisfied_by(ex)
            assert(spec.satisfied_by(ex));
            assert(always(c).satisfied_by(ex));

            // From spec.entails(p.and(c).leads_to(q)) = valid(spec.implies(p.and(c).leads_to(q)))
            // we get spec.implies(p.and(c).leads_to(q)).satisfied_by(ex)
            assert(spec.implies(p.and(c).leads_to(q)).satisfied_by(ex));
            // By implies_apply: get p.and(c).leads_to(q).satisfied_by(ex)
            implies_apply(ex, spec, p.and(c).leads_to(q));

            // Unfold leads_to: forall i, (p.and(c)).implies(eventually(q)).satisfied_by(ex.suffix(i))
            leads_to_unfold(ex, p.and(c), q);

            // Show always(p.implies(eventually(q))).satisfied_by(ex)
            // i.e., forall i, p.implies(eventually(q)).satisfied_by(ex.suffix(i))
            assert forall |i: nat| p.implies(eventually(q)).satisfied_by(#[trigger] ex.suffix(i)) by {
                // c holds at ex.suffix(i) from always(c).satisfied_by(ex)
                assert(c.satisfied_by(ex.suffix(i)));
                // (p.and(c)).implies(eventually(q)) holds at ex.suffix(i)
                assert((p.and(c)).implies(eventually(q)).satisfied_by(ex.suffix(i)));
                // p.implies(eventually(q)) at ex.suffix(i):
                if p.satisfied_by(ex.suffix(i)) {
                    // p.and(c) holds at ex.suffix(i)
                    assert(p.and(c).satisfied_by(ex.suffix(i)));
                    // By implies_apply: eventually(q).satisfied_by(ex.suffix(i))
                    implies_apply(ex.suffix(i), p.and(c), eventually(q));
                }
            };
            // p.leads_to(q) = always(p.implies(eventually(q)))
            // Verus should see the forall equals always(...).satisfied_by(ex)
        }
    };
}


}
