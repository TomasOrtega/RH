import Mathlib
open NumberField Matrix

namespace GlobalTheory

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem det_one_add_smul_poly_eval {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    Polynomial.eval z (det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)) = det (1 + z • M) := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply]
  split_ifs <;> simp [mul_comm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem det_one_add_smul_poly_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C) ≠ 0 := by
  intro h
  have := det_one_add_smul_poly_eval M 0
  rw [h] at this
  simp at this

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem finite_det_one_add_smul_eq_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    {z : ℂ | det (1 + z • M) = 0}.Finite := by
  refine (Polynomial.rootSet_finite (det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)) ℂ).subset ?_
  intro z hz
  rw [Polynomial.mem_rootSet_of_ne (det_one_add_smul_poly_ne_zero M)]
  simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
  rw [det_one_add_smul_poly_eval]
  exact hz

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem exists_normOne_det_one_add_ne_zero : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ),
    ∃ a : L, a * (IsCMField.complexConj L : L →+* L) a = 1 ∧ ∀ σ : L →+* ℂ, (1 + σ a • X σ).det ≠ 0 := by
  intro L _ _ _ n X
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  have hcc : ∀ x, c (c x) = x := fun x => IsCMField.complexConj_apply_apply L x
  obtain ⟨μ, hμ⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  have hμ' : c μ ≠ μ := hμ
  have hne : ∀ t : ℚ, (t : L) + μ ≠ 0 := by
    intro t h
    apply hμ'
    have h1 : μ = -(t : L) := by linear_combination h
    rw [h1, map_neg, map_ratCast]
  have hne' : ∀ t : ℚ, (t : L) + c μ ≠ 0 := by
    intro t h
    apply hμ'
    have h1 : c μ = -(t : L) := by linear_combination h
    have h2 : μ = -(t : L) := by rw [← hcc μ, h1, map_neg, map_ratCast]
    rw [h1, h2]
  let a : ℚ → L := fun t => ((t : L) + μ) / ((t : L) + c μ)
  have hca : ∀ t, c (a t) = ((t : L) + c μ) / ((t : L) + μ) := by
    intro t
    simp only [a, map_div₀, map_add, map_ratCast, hcc]
  have hnorm : ∀ t, a t * c (a t) = 1 := by
    intro t
    rw [hca]
    simp only [a]
    field_simp [hne t, hne' t]
  have hinj : Function.Injective a := by
    intro t s h
    simp only [a] at h
    rw [div_eq_div_iff (hne' t) (hne' s)] at h
    have h3 : ((t : L) - s) * (c μ - μ) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact_mod_cast sub_eq_zero.mp h4
    · exact absurd (sub_eq_zero.mp h4) hμ'
  have hfin : (⋃ σ : L →+* ℂ, (fun t => σ (a t)) ⁻¹' {z : ℂ | det (1 + z • X σ) = 0}).Finite := by
    refine Set.finite_iUnion fun σ => ?_
    exact (finite_det_one_add_smul_eq_zero (X σ)).preimage
      (fun t _ s _ h => hinj (σ.injective h))
  obtain ⟨t, ht⟩ := (Set.infinite_univ (α := ℚ)).diff hfin |>.nonempty
  refine ⟨a t, hnorm t, fun σ hσ => ht.2 ?_⟩
  exact Set.mem_iUnion.mpr ⟨σ, hσ⟩

end GlobalTheory
