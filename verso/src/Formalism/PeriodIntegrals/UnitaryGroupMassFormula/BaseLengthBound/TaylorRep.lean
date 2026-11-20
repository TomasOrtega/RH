import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

section Gen

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {d : ℕ} (g : Fin d → R)

def monSpan (k : ℕ) : Submodule R M where
  carrier := {x | ∃ cf : (Fin d → ℕ) → M, x = ∑ α ∈ Finset.Nat.antidiagonalTuple d k, (∏ i, g i ^ α i) • cf α}
  add_mem' := by
    rintro x y ⟨c1, rfl⟩ ⟨c2, rfl⟩
    exact ⟨c1 + c2, by simp [smul_add, Finset.sum_add_distrib]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro r x ⟨c1, rfl⟩
    exact ⟨r • c1, by simp [Finset.smul_sum, smul_comm r]⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem single_mem_monSpan {k : ℕ} {α : Fin d → ℕ} (hα : α ∈ Finset.Nat.antidiagonalTuple d k) (m : M) :
    (∏ i, g i ^ α i) • m ∈ monSpan (M := M) g k := by
  refine ⟨fun β => if β = α then m else 0, ?_⟩
  rw [Finset.sum_eq_single α]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hα h

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem prod_pow_add_single (α : Fin d → ℕ) (i : Fin d) :
    (∏ l, g l ^ (α + Pi.single i 1 : Fin d → ℕ) l) = g i * ∏ l, g l ^ α l := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Treat this case separately. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pow_smul_top_le_monSpan (k : ℕ) :
    (Ideal.span (Set.range g)) ^ k • (⊤ : Submodule R M) ≤ monSpan (M := M) g k := by
  induction k with
  | zero =>
    intro x _
    refine ⟨fun _ => x, ?_⟩
    simp [Finset.Nat.antidiagonalTuple_zero_right]
  | succ k ih =>
    rw [pow_succ', Submodule.mul_smul, Submodule.smul_le]
    intro r hr n hn
    obtain ⟨cf, rfl⟩ := ih hn
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hr
    rw [Finset.sum_smul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun β hβ => ?_
    have hβ' : β + Pi.single i 1 ∈ Finset.Nat.antidiagonalTuple d (k + 1) := by
      rw [Finset.Nat.mem_antidiagonalTuple] at hβ ⊢
      simp [Finset.sum_add_distrib, hβ]
    have e : (a i • g i) • ((∏ l, g l ^ β l) • cf β) =
        (∏ l, g l ^ (β + Pi.single i 1 : Fin d → ℕ) l) • (a i • cf β) := by
      rw [smul_smul, smul_smul, prod_pow_add_single g β i, smul_eq_mul]
      congr 1
      ring
    rw [e]
    exact single_mem_monSpan g hβ' _

end Gen

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem taylorRep_holds : TaylorRep := by
  intro D B P j X ka wL wF G la k x hx
  obtain ⟨cf, hcf⟩ := pow_smul_top_le_monSpan (M := ↥(HK X la G.w wF))
    (fun i : Fin (WeightFamilies.dimY D j) => sfr X la G.w i.succ) k hx
  refine ⟨cf, ?_⟩
  have : x - ∑ α ∈ mon D j k, ym G la α • cf α = 0 := by
    rw [sub_eq_zero]; exact hcf
  rw [this]
  exact Submodule.zero_mem _

end PoleLengthBounds
