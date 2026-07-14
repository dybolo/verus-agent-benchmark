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

pub open spec fn later<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| temp_pred.satisfied_by(ex.suffix(1)))
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
proof fn next_preserves_inv_rec<T>(ex: Execution<T>, next: TempPred<T>, inv: TempPred<T>, i: nat)
    requires
        inv.satisfied_by(ex),
        forall |idx| next.satisfied_by(#[trigger] ex.suffix(idx)),
        forall |idx| inv.satisfied_by(#[trigger] ex.suffix(idx)) && next.satisfied_by(ex.suffix(idx))
            ==> inv.satisfied_by(ex.suffix(idx + 1)),
    ensures inv.satisfied_by(ex.suffix(i)),
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

/// Helper: suffix composition -- ex.suffix(i).suffix(j) == ex.suffix(i + j)
proof fn suffix_suffix<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix(i + j)
{
    assert forall |k: nat| #[trigger] (ex.suffix(i).suffix(j).nat_to_state)(k)
        == (ex.suffix(i + j).nat_to_state)(k) by {
        // (ex.suffix(i).suffix(j).nat_to_state)(k) = ex.nat_to_state(k + j + i)
        // (ex.suffix(i + j).nat_to_state)(k)        = ex.nat_to_state(k + (i + j))
        // Equal by nat arithmetic: k + j + i == k + (i + j)
    };
    execution_equality(ex.suffix(i).suffix(j), ex.suffix(i + j));
}

/// Helper: the preservation step: q.satisfied_by(ex.suffix(idx)) && next.satisfied_by(ex.suffix(idx))
/// implies q.satisfied_by(ex.suffix(idx + 1)), given the stability condition.
proof fn q_preservation_step<T>(
    ex: Execution<T>,
    next: TempPred<T>,
    q: TempPred<T>,
    idx: nat,
)
    requires
        q.satisfied_by(ex.suffix(idx)),
        next.satisfied_by(ex.suffix(idx)),
        always(q.and(next).implies(later(q))).satisfied_by(ex),
    ensures q.satisfied_by(ex.suffix(idx + 1))
{
    // The stability condition gives: (q.and(next)).implies(later(q)).satisfied_by(ex.suffix(idx))
    // Since q and next both hold at ex.suffix(idx), q.and(next) holds there.
    // By implies_apply, later(q) holds: q.satisfied_by(ex.suffix(idx).suffix(1))
    implies_apply(ex.suffix(idx), q.and(next), later(q));
    // ex.suffix(idx).suffix(1) == ex.suffix(idx + 1)
    suffix_suffix(ex, idx, 1);
    // So q.satisfied_by(ex.suffix(idx + 1))
}

/// Helper: once q holds at ex.suffix(base), it holds forever (always(q) at ex.suffix(base)),
/// provided q is stable under next.
proof fn q_stable_once_holds<T>(
    ex: Execution<T>,
    next: TempPred<T>,
    q: TempPred<T>,
    base: nat,
)
    requires
        q.satisfied_by(ex.suffix(base)),
        always(next).satisfied_by(ex),
        always(q.and(next).implies(later(q))).satisfied_by(ex),
    ensures always(q).satisfied_by(ex.suffix(base))
{
    let ex_base = ex.suffix(base);

    // Propagate always(next) and the stability condition to ex_base
    always_propagate_forwards(ex, next, base);
    always_propagate_forwards(ex, q.and(next).implies(later(q)), base);

    // Prove always(q) at ex_base using next_preserves_inv_rec
    // First show the preservation condition for ex_base
    assert forall |idx: nat|
        q.satisfied_by(#[trigger] ex_base.suffix(idx)) && next.satisfied_by(ex_base.suffix(idx))
        ==> q.satisfied_by(ex_base.suffix(idx + 1))
    by {
        if q.satisfied_by(ex_base.suffix(idx)) && next.satisfied_by(ex_base.suffix(idx)) {
            // ex_base.suffix(idx) = ex.suffix(base + idx)
            suffix_suffix(ex, base, idx);
            q_preservation_step(ex, next, q, base + idx);
            suffix_suffix(ex, base, idx + 1);
        }
    };

    // next always holds on ex_base
    assert forall |idx: nat| next.satisfied_by(#[trigger] ex_base.suffix(idx)) by {
        // from always(next).satisfied_by(ex_base)
    };

    // Apply next_preserves_inv_rec for each future index
    assert forall |k: nat| #[trigger] q.satisfied_by(ex_base.suffix(k)) by {
        next_preserves_inv_rec(ex_base, next, q, k);
    };
}

/// Helper: for a fixed execution satisfying spec, prove p.leads_to(always(q)) holds.
proof fn leads_to_stable_exec<T>(
    ex: Execution<T>,
    spec: TempPred<T>,
    next: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
)
    requires
        spec.satisfied_by(ex),
        spec.entails(always(q.and(next).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(p.leads_to(q)),
    ensures p.leads_to(always(q)).satisfied_by(ex)
{
    // Extract the properties for this execution using entails
    implies_apply(ex, spec, always(q.and(next).implies(later(q))));
    implies_apply(ex, spec, always(next));
    implies_apply(ex, spec, p.leads_to(q));

    // p.leads_to(always(q)).satisfied_by(ex)
    // = always(p.implies(eventually(always(q)))).satisfied_by(ex)
    // = forall i, p.implies(eventually(always(q))).satisfied_by(ex.suffix(i))
    assert forall |i: nat| #[trigger]
        p.implies(eventually(always(q))).satisfied_by(ex.suffix(i))
    by {
        if p.satisfied_by(ex.suffix(i)) {
            // From p.leads_to(q), at every suffix where p holds, eventually q holds.
            leads_to_unfold(ex, p, q);
            // p.implies(eventually(q)).satisfied_by(ex.suffix(i))
            implies_apply(ex.suffix(i), p, eventually(q));
            // eventually(q).satisfied_by(ex.suffix(i))
            // => exists j, q.satisfied_by(ex.suffix(i).suffix(j))
            let j = eventually_choose_witness(ex.suffix(i), q);
            // q.satisfied_by(ex.suffix(i).suffix(j))
            // ex.suffix(i).suffix(j) == ex.suffix(i + j)
            suffix_suffix(ex, i, j);
            // q.satisfied_by(ex.suffix(i + j))
            // By stability, always(q).satisfied_by(ex.suffix(i + j))
            q_stable_once_holds(ex, next, q, i + j);
            // always(q).satisfied_by(ex.suffix(i).suffix(j)) since ex.suffix(i).suffix(j) == ex.suffix(i+j)
            // Use j as witness for eventually(always(q)) at ex.suffix(i)
            assert(always(q).satisfied_by(ex.suffix(i).suffix(j)));
            eventually_proved_by_witness(ex.suffix(i), always(q), j);
        }
    };
}

pub proof fn leads_to_stable<T>(spec: TempPred<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(q.and(next).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(p.leads_to(q)),
    ensures spec.entails(p.leads_to(always(q))),
{
    // We need: valid(spec.implies(p.leads_to(always(q))))
    // = forall ex, spec.satisfied_by(ex) ==> p.leads_to(always(q)).satisfied_by(ex)
    assert forall |ex: Execution<T>| spec.satisfied_by(ex)
        implies p.leads_to(always(q)).satisfied_by(ex)
    by {
        leads_to_stable_exec(ex, spec, next, p, q);
    };
}


}
