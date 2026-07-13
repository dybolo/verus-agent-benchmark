use vstd::prelude::*;
use vstd::map_lib::*;

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

pub open spec fn tla_forall<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |a: A| #[trigger] a_to_temp_pred(a).satisfied_by(ex))
}

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}


// File: rules.rs
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

	#[verifier::external_body]
proof fn eventually_proved_by_witness<T>(ex: Execution<T>, p: TempPred<T>, witness_idx: nat)
    requires p.satisfied_by(ex.suffix(witness_idx)),
    ensures eventually(p).satisfied_by(ex)
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

// Helper spec: max of two nats
spec fn max_nat(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

// Helper lemma: suffix composition is additive: ex.suffix(a).suffix(b) == ex.suffix(a + b)
proof fn suffix_additive<T>(ex: Execution<T>, a: nat, b: nat)
    ensures ex.suffix(a).suffix(b) == ex.suffix(a + b)
{
    assert forall |k: nat|
        #[trigger] (ex.suffix(a).suffix(b).nat_to_state)(k) == (ex.suffix(a + b).nat_to_state)(k)
    by {
        // ex.suffix(a).suffix(b).nat_to_state(k) = (ex.suffix(a).nat_to_state)(k + b)
        //                                         = ex.nat_to_state(k + b + a)
        // ex.suffix(a + b).nat_to_state(k) = ex.nat_to_state(k + (a + b))
        // k + b + a == k + a + b == k + (a + b), all equal by nat arithmetic
        assert(k + b + a == k + (a + b)) by (nonlinear_arith);
    };
    execution_equality(ex.suffix(a).suffix(b), ex.suffix(a + b));
}

// Helper lemma: if always(p) holds at ex.suffix(j_a) and j_a <= j, then always(p) holds at ex.suffix(j)
proof fn always_extend<T>(ex: Execution<T>, p: TempPred<T>, j_a: nat, j: nat)
    requires
        always(p).satisfied_by(ex.suffix(j_a)),
        j_a <= j,
    ensures
        always(p).satisfied_by(ex.suffix(j))
{
    let diff: nat = j - j_a;
    // always_propagate_forwards: always(p) at ex.suffix(j_a) implies always(p) at ex.suffix(j_a).suffix(diff)
    always_propagate_forwards(ex.suffix(j_a), p, diff);
    // suffix_additive: ex.suffix(j_a).suffix(diff) == ex.suffix(j_a + diff)
    suffix_additive(ex, j_a, diff);
    // j_a + diff == j since diff = j - j_a (nat subtraction, valid since j_a <= j)
    assert(j_a + diff == j);
    // So always(p) holds at ex.suffix(j_a + diff) = ex.suffix(j)
}

// Key inductive lemma: for a finite set s, given individual witnesses for each a in s,
// find a single witness j that works for all a in s simultaneously
proof fn witnesses_combine<T, A>(
    ex: Execution<T>,
    a_to_p: spec_fn(A) -> TempPred<T>,
    s: Set<A>,
    i: nat,
)
    requires
        forall |a: A| #[trigger] s.contains(a) ==>
            exists |j: nat| always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)),
    ensures
        exists |j: nat| forall |a: A| #[trigger] s.contains(a) ==>
            always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)),
    decreases s.len(),
{
    broadcast use vstd::set::group_set_lemmas;
    if s.len() == 0 {
        // Empty set: the forall is vacuously true for j = 0
        // s.len() == 0 means no element is in s
        assert forall |a: A| #[trigger] s.contains(a) implies
            always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(0nat)) by {
            // s.contains(a) ==> s.len() != 0 (from lemma_set_contains_len in broadcast group)
            // But s.len() == 0, contradiction
        };
        // Close the existential with witness j = 0
    } else {
        // Non-empty set: pick one element and induct on the rest
        let a = s.choose();
        assert(s.contains(a));

        // Get witness for element a
        let j_a: nat = choose |j: nat| always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j));

        // Induct on s.remove(a): get a single witness for all elements in s.remove(a)
        let s_rest = s.remove(a);
        assert(s_rest.len() < s.len()) by {
            // s.contains(a), so s.remove(a).len() == s.len() - 1 < s.len()
            assert(s.contains(a));
        };
        assert forall |b: A| #[trigger] s_rest.contains(b) implies
            exists |j: nat| always(a_to_p(b)).satisfied_by(ex.suffix(i).suffix(j)) by {
            // s_rest.contains(b) ==> s.contains(b) (since s_rest = s.remove(a))
            assert(s.contains(b));
        };
        witnesses_combine(ex, a_to_p, s_rest, i);
        let j_rest: nat = choose |j: nat| forall |b: A| #[trigger] s_rest.contains(b) ==>
            always(a_to_p(b)).satisfied_by(ex.suffix(i).suffix(j));

        // Take j = max(j_a, j_rest) as the combined witness
        let j = max_nat(j_a, j_rest);

        // Show that j works for all elements of s
        assert forall |a_: A| #[trigger] s.contains(a_) implies
            always(a_to_p(a_)).satisfied_by(ex.suffix(i).suffix(j)) by {
            if a_ == a {
                // a_ is the chosen element; use j_a <= j to extend
                assert(j >= j_a);
                always_extend(ex.suffix(i), a_to_p(a), j_a, j);
            } else {
                // a_ is in s_rest; use j_rest <= j to extend
                assert(s_rest.contains(a_));
                assert(j >= j_rest);
                always_extend(ex.suffix(i), a_to_p(a_), j_rest, j);
            }
        };
        // Close the existential with witness j = max_nat(j_a, j_rest)
    }
}

// Helper: from individual always(a_to_p(a)) at ex (for all a), derive always(tla_forall(a_to_p)) at ex
proof fn always_tla_forall_from_always_each<T, A>(
    ex: Execution<T>,
    a_to_p: spec_fn(A) -> TempPred<T>,
)
    requires forall |a: A| #[trigger] always(a_to_p(a)).satisfied_by(ex),
    ensures always(tla_forall(a_to_p)).satisfied_by(ex)
{
    // always(tla_forall(a_to_p)).satisfied_by(ex) means:
    //   forall k, tla_forall(a_to_p).satisfied_by(ex.suffix(k))
    // tla_forall(a_to_p).satisfied_by(ex.suffix(k)) means:
    //   forall a, a_to_p(a).satisfied_by(ex.suffix(k))
    // This follows from always(a_to_p(a)).satisfied_by(ex):
    //   forall k, a_to_p(a).satisfied_by(ex.suffix(k))
    assert forall |k: nat| #[trigger] tla_forall(a_to_p).satisfied_by(ex.suffix(k)) by {
        assert forall |a: A| #[trigger] a_to_p(a).satisfied_by(ex.suffix(k)) by {
            assert(always(a_to_p(a)).satisfied_by(ex));
            // always(a_to_p(a)).satisfied_by(ex) unfolds to: forall i, a_to_p(a).satisfied_by(ex.suffix(i))
            // In particular at i = k: a_to_p(a).satisfied_by(ex.suffix(k)) ✓
        };
    };
}

pub proof fn leads_to_always_tla_forall<T, A>(spec: TempPred<T>, p: TempPred<T>, a_to_p: spec_fn(A)->TempPred<T>, domain: Set<A>)
    requires
        forall |a: A| spec.entails(p.leads_to(always(#[trigger] a_to_p(a)))),
        domain.finite(),
        domain.len() > 0,
        forall |a: A| #[trigger] domain.contains(a),
    ensures spec.entails(p.leads_to(always(tla_forall(a_to_p)))),
{
    // Unfold: spec.entails(p.leads_to(always(tla_forall(a_to_p))))
    // = valid(spec.implies(p.leads_to(always(tla_forall(a_to_p)))))
    // = forall ex, spec.satisfied_by(ex) ==> p.leads_to(always(tla_forall(a_to_p))).satisfied_by(ex)
    assert forall |ex: Execution<T>| #[trigger] spec.satisfied_by(ex) implies
        p.leads_to(always(tla_forall(a_to_p))).satisfied_by(ex) by {

        // p.leads_to(always(tla_forall(a_to_p)))
        //   = always(p.implies(eventually(always(tla_forall(a_to_p)))))
        // So: forall i, p.satisfied_by(ex.suffix(i)) ==> eventually(always(tla_forall(a_to_p))).satisfied_by(ex.suffix(i))
        assert forall |i: nat| #[trigger] p.implies(eventually(always(tla_forall(a_to_p)))).satisfied_by(ex.suffix(i)) by {

            if p.satisfied_by(ex.suffix(i)) {
                // For each a in domain, derive: exists j, always(a_to_p(a)) at ex.suffix(i).suffix(j)
                assert forall |a: A| #[trigger] domain.contains(a) implies
                    exists |j: nat| always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)) by {

                    // From precondition: spec.entails(p.leads_to(always(a_to_p(a))))
                    assert(spec.entails(p.leads_to(always(a_to_p(a)))));
                    // spec.entails(q) = valid(spec.implies(q)) = forall ex_, spec.implies(q).satisfied_by(ex_)
                    // Instantiate at ex to get: spec.implies(p.leads_to(always(a_to_p(a)))).satisfied_by(ex)
                    assert(spec.implies(p.leads_to(always(a_to_p(a)))).satisfied_by(ex));
                    // spec.implies(q).satisfied_by(ex) = spec.satisfied_by(ex) ==> q.satisfied_by(ex)
                    // Since spec holds at ex: p.leads_to(always(a_to_p(a))).satisfied_by(ex)
                    assert(p.leads_to(always(a_to_p(a))).satisfied_by(ex));
                    // p.leads_to(q) = always(p.implies(eventually(q)))
                    // always(...).satisfied_by(ex) = forall i_, p.implies(eventually(always(a_to_p(a)))).satisfied_by(ex.suffix(i_))
                    // In particular at i_:
                    assert(p.implies(eventually(always(a_to_p(a)))).satisfied_by(ex.suffix(i)));
                    // Since p holds at ex.suffix(i): eventually(always(a_to_p(a))).satisfied_by(ex.suffix(i))
                    assert(eventually(always(a_to_p(a))).satisfied_by(ex.suffix(i)));
                    // eventually(q).satisfied_by(ex.suffix(i)) = exists j, q.satisfied_by(ex.suffix(i).suffix(j))
                    // So: exists j, always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)) ✓
                };

                // Since domain contains ALL a: A (from precondition), the above holds for all a: A
                // witnesses_combine needs: forall a, domain.contains(a) ==> exists j, always(a_to_p(a)) at ...
                // This is exactly what we just proved. Call witnesses_combine on domain:
                witnesses_combine(ex, a_to_p, domain, i);

                // Get the single combined witness j_combined
                let j_combined: nat = choose |j: nat| forall |a: A| #[trigger] domain.contains(a) ==>
                    always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j));

                // For all a: A, domain.contains(a) (from precondition), so always(a_to_p(a)) holds at j_combined
                assert forall |a: A| #[trigger] always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j_combined)) by {
                    assert(domain.contains(a));
                };

                // Therefore always(tla_forall(a_to_p)) holds at ex.suffix(i).suffix(j_combined)
                always_tla_forall_from_always_each(ex.suffix(i).suffix(j_combined), a_to_p);

                // So eventually(always(tla_forall(a_to_p))) holds at ex.suffix(i)
                eventually_proved_by_witness(ex.suffix(i), always(tla_forall(a_to_p)), j_combined);
            }
        };
    };
}


}
