import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly

/- English proof (translation)
Unfold `degFl`. Rewrite using `[Finset.sum_eq_single (fun _ => 1)]`. Rewrite using `[coeff_monomial, if_pos rfl]`. Simplify using the standard rewrite rules. Introduce `σ _ hσ`.

Rewrite using `[coeff_monomial, if_neg]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `hσ (PermutationPointDegree.permExp_inj _ _ h).symm`. Simplify using the standard rewrite rules.
-/
theorem degFl_monomial_staircase (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) :
    degFl ι N (monomial (permExp (fun _ : ι => (1 : Equiv.Perm (Fin N)))) (1 : ℝ)) =
      (-1) ^ dimFl ι N := by
  unfold degFl
  rw [Finset.sum_eq_single (fun _ => 1)]
  · rw [coeff_monomial, if_pos rfl]
    simp
  · intro σ _ hσ
    rw [coeff_monomial, if_neg]
    · simp
    · intro h; exact hσ (PermutationPointDegree.permExp_inj _ _ h).symm
  · simp

/- English proof (translation)
Unfold `degFl`. Rewrite using `[Finset.sum_eq_zero, mul_zero]`. Introduce `σ _`. Rewrite using `[coeff_monomial, if_neg, mul_zero]`. Introduce `hm`.

Rewrite `h` using `[hm, PPowSum.permExp_apply, PPowSum.permExp_apply]`. Establish `h1` using `(σ τ a).isLt`. Establish `h2` using `(σ τ b).isLt`. Apply `hab` to reduce the goal to its premises. Apply `(σ τ).injective` to reduce the goal to its premises.

Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only at h`. Use linear arithmetic over natural numbers and integers.
-/
theorem degFl_monomial_eq_zero_of_repeat {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (m : (ι × Fin N) →₀ ℕ) (τ : ι) (a b : Fin N) (hab : a ≠ b) (h : m (τ, a) = m (τ, b)) :
    degFl ι N (monomial m (1 : ℝ)) = 0 := by
  unfold degFl
  rw [Finset.sum_eq_zero, mul_zero]
  intro σ _
  rw [coeff_monomial, if_neg, mul_zero]
  intro hm
  rw [hm, PPowSum.permExp_apply, PPowSum.permExp_apply] at h
  have h1 := (σ τ a).isLt
  have h2 := (σ τ b).isLt
  apply hab
  apply (σ τ).injective
  apply Fin.ext
  simp only at h
  omega

/- English proof (translation)
Introduce `ι _ _ N j τ h1 hN`. Use `set a : Fin N := ⟨j - 1, by omega⟩ with ha`. Use `set b : Fin N := ⟨j, hN⟩ with hb`. Use `set δ := permExp (fun _ : ι => (1 : Equiv.Perm (Fin N))) with hδ`. Use `set m : (ι × Fin N) →₀ ℕ := δ - Finsupp.single (τ, a) 1 with hm`.

Establish `hδa : δ (τ, a) = N - j`. Simplify using `only [hδ, PPowSum.permExp_apply, ha, Equiv.Perm.coe_one, id]`. Use linear arithmetic over natural numbers and integers. Establish `hδb : δ (τ, b) = N - 1 - j`. Simplify using `only [hδ, PPowSum.permExp_apply, hb, Equiv.Perm.coe_one, id]`.

Establish `hab : a ≠ b`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [ha, hb] at this`. Use linear arithmetic over natural numbers and integers.

Establish `hle : Finsupp.single (τ, a) 1 ≤ δ`. Rewrite using `[Finsupp.single_le_iff, hδa]`. Use linear arithmetic over natural numbers and integers. Establish `hadd : Finsupp.single (τ, a) 1 + m = δ`. Rewrite using `[hm]`.

Conclude with `add_tsub_cancel_of_le hle`. Establish `hdeg : m.degree = dimFl ι N - 1`. Use `congrArg Finsupp.degree hadd` as an intermediate fact. Rewrite `this` using `[map_add, Finsupp.degree_single, hδ, PPowSum.degree_permExp]`. Use linear arithmetic over natural numbers and integers.

Use `⟨C ((-1 : ℝ) ^ dimFl ι N) * monomial m 1, ?_, ?_⟩` and prove the remaining obligations. Use `(isHomogeneous_C (ι × Fin N) ((-1 : ℝ) ^ dimFl ι N)).mul (isHomogeneous_monomial (1 : ℝ) hdeg)` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis. Rewrite using `[mul_left_comm, PPowSum.degFl_C_mul, pLow, Finset.sum_mul, PPowSum.degFl_sum, Finset.sum_eq_single a]`. Rewrite using `[X_pow_eq_monomial, monomial_mul, hadd, one_mul, hδ, degFl_monomial_staircase, ← pow_add, ← two_mul, pow_mul]`.

Simplify using the standard rewrite rules. Introduce `i hi hia`. Rewrite using `[X_pow_eq_monomial, monomial_mul, one_mul]`. Establish `hij : (i : ℕ) < j` using `(Finset.mem_filter.mp hi).2`. Establish `hib : i ≠ b`.

Introduce `h`. Rewrite `hij` using `[h]`. Simplify using `[hb] at hij`. Use `degFl_monomial_eq_zero_of_repeat _ τ a b hab ?_` and prove the remaining obligations. Simplify using `only [hm, Finsupp.add_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, Prod.mk.injEq, true_and, if_neg hia, if_neg hib, if_neg hab, if_true, hδa, hδb]`.

Use linear arithmetic over natural numbers and integers. Introduce `h`. Conclude with `absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp only [ha]; omega⟩) h`.
-/
theorem exists_dual_pLow_one : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ) (τ : ι), 1 ≤ j → j < N →
    ∃ Q : Pol ι N, Q.IsHomogeneous (dimFl ι N - 1) ∧ degFl ι N (pLow j τ 1 * Q) = 1 := by
  intro ι _ _ N j τ h1 hN
  set a : Fin N := ⟨j - 1, by omega⟩ with ha
  set b : Fin N := ⟨j, hN⟩ with hb
  set δ := permExp (fun _ : ι => (1 : Equiv.Perm (Fin N))) with hδ
  set m : (ι × Fin N) →₀ ℕ := δ - Finsupp.single (τ, a) 1 with hm
  have hδa : δ (τ, a) = N - j := by
    simp only [hδ, PPowSum.permExp_apply, ha, Equiv.Perm.coe_one, id]; omega
  have hδb : δ (τ, b) = N - 1 - j := by
    simp only [hδ, PPowSum.permExp_apply, hb, Equiv.Perm.coe_one, id]
  have hab : a ≠ b := by
    intro h; have := congrArg Fin.val h; simp only [ha, hb] at this; omega
  have hle : Finsupp.single (τ, a) 1 ≤ δ := by
    rw [Finsupp.single_le_iff, hδa]; omega
  have hadd : Finsupp.single (τ, a) 1 + m = δ := by
    rw [hm]; exact add_tsub_cancel_of_le hle
  have hdeg : m.degree = dimFl ι N - 1 := by
    have := congrArg Finsupp.degree hadd
    rw [map_add, Finsupp.degree_single, hδ, PPowSum.degree_permExp] at this
    omega
  refine ⟨C ((-1 : ℝ) ^ dimFl ι N) * monomial m 1, ?_, ?_⟩
  · have := (isHomogeneous_C (ι × Fin N) ((-1 : ℝ) ^ dimFl ι N)).mul
      (isHomogeneous_monomial (1 : ℝ) hdeg)
    rwa [zero_add] at this
  · rw [mul_left_comm, PPowSum.degFl_C_mul, pLow, Finset.sum_mul, PPowSum.degFl_sum,
      Finset.sum_eq_single a]
    · rw [X_pow_eq_monomial, monomial_mul, hadd, one_mul, hδ, degFl_monomial_staircase,
        ← pow_add, ← two_mul, pow_mul]
      simp
    · intro i hi hia
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
      have hij : (i : ℕ) < j := (Finset.mem_filter.mp hi).2
      have hib : i ≠ b := by
        intro h; rw [h] at hij; simp [hb] at hij
      refine degFl_monomial_eq_zero_of_repeat _ τ a b hab ?_
      simp only [hm, Finsupp.add_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
        Prod.mk.injEq, true_and, if_neg hia, if_neg hib, if_neg hab, if_true, hδa, hδb]
      omega
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp only [ha]; omega⟩) h

end GlobalTheory.FlagPoly
