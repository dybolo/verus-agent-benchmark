use vstd::prelude::*;

fn main() {}

verus!{

pub type StatePred<T> = spec_fn(T) -> bool;

pub type ActionPred<T> = spec_fn(T, T) -> bool;


// File: defs.rs
pub struct Execution<T> {
    pub nat_to_state: spec_fn(nat) -> T,
}

impl<T> Execution<T> {

    pub open spec fn head(self) -> T {
        (self.nat_to_state)(0)
    }

    pub open spec fn head_next(self) -> T {
        (self.nat_to_state)(1)
    }

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


pub open spec fn lift_state<T>(state_pred: StatePred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| state_pred(ex.head()))
}

pub open spec fn lift_action<T>(action_pred: ActionPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| action_pred(ex.head(), ex.head_next()))
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

pub open spec fn enabled<T>(action_pred: ActionPred<T>) -> StatePred<T> {
    |s: T| exists |s_prime: T| #[trigger] action_pred(s, s_prime)
}

pub open spec fn weak_fairness<T>(action_pred: ActionPred<T>) -> TempPred<T> {
    always(lift_state(enabled(action_pred))).leads_to(lift_action(action_pred))
}

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}


// File: rules.rs
	#[verifier::external_body]
proof fn weak_fairness_unfold<T>(ex: Execution<T>, p: ActionPred<T>)
    requires weak_fairness(p).satisfied_by(ex),
    ensures forall |i| always(lift_state(enabled(p))).implies(eventually(lift_action(p))).satisfied_by(#[trigger] ex.suffix(i)),
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
proof fn implies_apply_with_always<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        always(p.implies(q)).satisfied_by(ex),
        always(p).satisfied_by(ex),
    ensures always(q).satisfied_by(ex),
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn execution_equality<T>(ex1: Execution<T>, ex2: Execution<T>)
    requires forall |i: nat| #[trigger] (ex1.nat_to_state)(i) == (ex2.nat_to_state)(i),
    ensures ex1 == ex2,
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn wf1_variant_temp<T>(spec: TempPred<T>, next: TempPred<T>, forward: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(p.and(next).implies(later(p).or(later(q))))),
        spec.entails(always(p.and(next).and(forward).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(always(p).leads_to(forward)),
    ensures spec.entails(p.leads_to(q)),
	{
		unimplemented!()
	}

pub proof fn wf1<T>(spec: TempPred<T>, next: ActionPred<T>, forward: ActionPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        forall |s, s_prime: T| p(s) && #[trigger] next(s, s_prime) ==> p(s_prime) || q(s_prime),
        forall |s, s_prime: T| p(s) && #[trigger] next(s, s_prime) && forward(s, s_prime) ==> q(s_prime),
        forall |s: T| #[trigger] p(s) ==> enabled(forward)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(weak_fairness(forward)),
    ensures spec.entails(lift_state(p).leads_to(lift_state(q))),
{
    let p_temp = lift_state(p);
    let q_temp = lift_state(q);
    let next_temp = lift_action(next);
    let forward_temp = lift_action(forward);

    // -----------------------------------------------------------------------
    // Condition 1: spec |= always(p_temp ∧ next_temp → later(p_temp) ∨ later(q_temp))
    // -----------------------------------------------------------------------
    assert forall |ex: Execution<T>| spec.satisfied_by(ex) implies
        always(p_temp.and(next_temp).implies(later(p_temp).or(later(q_temp)))).satisfied_by(ex)
    by {
        assert forall |i: nat|
            (p_temp.and(next_temp).implies(later(p_temp).or(later(q_temp)))).satisfied_by(#[trigger] ex.suffix(i))
        by {
            if p_temp.and(next_temp).satisfied_by(ex.suffix(i)) {
                let s = ex.suffix(i).head();
                let s_prime = ex.suffix(i).head_next();
                // hypothesis 1
                assert(p(s) && next(s, s_prime));
                assert(p(s_prime) || q(s_prime));
                // s_prime == ex.suffix(i).suffix(1).head() definitionally
                assert(ex.suffix(i).suffix(1).head() == s_prime);
                // So later(p_temp) or later(q_temp) holds
                if p(s_prime) {
                    assert(later(p_temp).satisfied_by(ex.suffix(i)));
                } else {
                    assert(q(s_prime));
                    assert(later(q_temp).satisfied_by(ex.suffix(i)));
                }
            }
        };
    };
    assert(spec.entails(always(p_temp.and(next_temp).implies(later(p_temp).or(later(q_temp))))));

    // -----------------------------------------------------------------------
    // Condition 2: spec |= always(p_temp ∧ next_temp ∧ forward_temp → later(q_temp))
    // -----------------------------------------------------------------------
    assert forall |ex: Execution<T>| spec.satisfied_by(ex) implies
        always(p_temp.and(next_temp).and(forward_temp).implies(later(q_temp))).satisfied_by(ex)
    by {
        assert forall |i: nat|
            (p_temp.and(next_temp).and(forward_temp).implies(later(q_temp))).satisfied_by(#[trigger] ex.suffix(i))
        by {
            if p_temp.and(next_temp).and(forward_temp).satisfied_by(ex.suffix(i)) {
                let s = ex.suffix(i).head();
                let s_prime = ex.suffix(i).head_next();
                assert(p(s) && next(s, s_prime) && forward(s, s_prime));
                // hypothesis 2
                assert(q(s_prime));
                assert(ex.suffix(i).suffix(1).head() == s_prime);
                assert(later(q_temp).satisfied_by(ex.suffix(i)));
            }
        };
    };
    assert(spec.entails(always(p_temp.and(next_temp).and(forward_temp).implies(later(q_temp)))));

    // -----------------------------------------------------------------------
    // Condition 3: spec |= always(next_temp) — directly from hypothesis 4
    // -----------------------------------------------------------------------
    assert(spec.entails(always(next_temp)));

    // -----------------------------------------------------------------------
    // Condition 4: spec |= always(p_temp) ~> forward_temp
    // -----------------------------------------------------------------------
    assert forall |ex: Execution<T>| spec.satisfied_by(ex) implies
        always(p_temp).leads_to(forward_temp).satisfied_by(ex)
    by {
        if spec.satisfied_by(ex) {
            // From spec.entails(weak_fairness(forward)) and spec.satisfied_by(ex):
            // Introduce the trigger term to instantiate the valid-forall
            assert(spec.implies(weak_fairness(forward)).satisfied_by(ex));
            assert(weak_fairness(forward).satisfied_by(ex));
            // Unfold weak fairness: for all i, always(enabled(forward)) → eventually(forward_temp) at ex.suffix(i)
            weak_fairness_unfold(ex, forward);

            assert forall |i: nat|
                (always(p_temp).implies(eventually(forward_temp))).satisfied_by(#[trigger] ex.suffix(i))
            by {
                if always(p_temp).satisfied_by(ex.suffix(i)) {
                    // Show always(lift_state(enabled(forward))) at ex.suffix(i)
                    assert forall |j: nat|
                        lift_state(enabled(forward)).satisfied_by(#[trigger] ex.suffix(i).suffix(j))
                    by {
                        // p holds at suffix(i).suffix(j)
                        assert(p_temp.satisfied_by(ex.suffix(i).suffix(j)));
                        let s = ex.suffix(i).suffix(j).head();
                        assert(p(s));
                        // hypothesis 3: p(s) => enabled(forward)(s)
                        assert(enabled(forward)(s));
                    };
                    assert(always(lift_state(enabled(forward))).satisfied_by(ex.suffix(i)));
                    // Apply weak-fairness implication at position i
                    implies_apply(
                        ex.suffix(i),
                        always(lift_state(enabled(forward))),
                        eventually(forward_temp)
                    );
                }
            };
            assert(always(p_temp).leads_to(forward_temp).satisfied_by(ex));
        }
    };
    assert(spec.entails(always(p_temp).leads_to(forward_temp)));

    // -----------------------------------------------------------------------
    // Apply wf1_variant_temp
    // -----------------------------------------------------------------------
    wf1_variant_temp(spec, next_temp, forward_temp, p_temp, q_temp);
}


}
