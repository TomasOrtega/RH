import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace MCMatrixDetDeriv

/- English proof (translation)
Establish `hd : HasFDerivAt (fun q => ∏ i ∈ s, g i q) (∑ i ∈ s, (∏ j ∈ s.erase i, g j p) • fderiv ℝ (g i) p) p` using `HasFDerivAt.finsetProd fun i hi => (h i hi).1.hasFDerivAt`. Use `⟨hd.differentiableAt, ?_⟩` and prove the remaining obligations. Rewrite using `[hd.fderiv]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `i hi`. Establish `hA : 0 ≤ A` using `(norm_nonneg _).trans (h i hi).2.1`. Establish `hprod : ‖∏ j ∈ s.erase i, g j p‖ ≤ A ^ (s.card - 1)`. Rewrite using `[norm_prod, ← Finset.card_erase_of_mem hi, ← Finset.prod_const]`. Conclude with `Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j hj => (h j (Finset.mem_of_mem_erase hj)).2.1)`.

Use `(ContinuousLinearMap.opNorm_smul_le _ _).trans ?_` and prove the remaining obligations. Conclude with `mul_le_mul hprod (h i hi).2.2 (norm_nonneg _) (pow_nonneg hA _)`. Use `_ = (s.card : ℝ) * A ^ (s.card - 1) * B := by`. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_fderiv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (g : ι → E → ℂ) (p : E) (A B : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (g i) p ∧ ‖g i p‖ ≤ A ∧ ‖fderiv ℝ (g i) p‖ ≤ B) :
    DifferentiableAt ℝ (fun q => ∏ i ∈ s, g i q) p ∧
      ‖fderiv ℝ (fun q => ∏ i ∈ s, g i q) p‖ ≤ (s.card : ℝ) * A ^ (s.card - 1) * B := by
  have hd : HasFDerivAt (fun q => ∏ i ∈ s, g i q)
      (∑ i ∈ s, (∏ j ∈ s.erase i, g j p) • fderiv ℝ (g i) p) p :=
    HasFDerivAt.finsetProd fun i hi => (h i hi).1.hasFDerivAt
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.fderiv]
  calc ‖∑ i ∈ s, (∏ j ∈ s.erase i, g j p) • fderiv ℝ (g i) p‖
      ≤ ∑ i ∈ s, ‖(∏ j ∈ s.erase i, g j p) • fderiv ℝ (g i) p‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, A ^ (s.card - 1) * B := by
        apply Finset.sum_le_sum
        intro i hi
        have hA : 0 ≤ A := (norm_nonneg _).trans (h i hi).2.1
        have hprod : ‖∏ j ∈ s.erase i, g j p‖ ≤ A ^ (s.card - 1) := by
          rw [norm_prod, ← Finset.card_erase_of_mem hi, ← Finset.prod_const]
          exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
            (fun j hj => (h j (Finset.mem_of_mem_erase hj)).2.1)
        refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
        exact mul_le_mul hprod (h i hi).2.2 (norm_nonneg _) (pow_nonneg hA _)
    _ = (s.card : ℝ) * A ^ (s.card - 1) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

end MCMatrixDetDeriv

/- English proof (translation)
Introduce `E _ _ k H p A B h`. Establish `hexp : (fun q => (H q).det) = fun q => ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, H q (σ i) i`. Use function extensionality and compare the values at `q`. Conclude with `Matrix.det_apply' (H q)`. Establish `hterm : ∀ σ : Equiv.Perm (Fin k), DifferentiableAt ℝ (fun q => ∏ i, H q (σ i) i) p ∧ ‖fderiv ℝ (fun q => ∏ i, H q (σ i) i) p‖ ≤ (k : ℝ) * A ^ (k - 1) * B`.

Introduce `σ`. Use `MCMatrixDetDeriv.prod_fderiv_le (Finset.univ : Finset (Fin k)) (fun i q => H q (σ i) i) p A B (fun i _ => h (σ i) i)` as an intermediate fact. Simplify `this` using `[Finset.card_univ, Fintype.card_fin]`. Establish `hd : HasFDerivAt (fun q => ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, H q (σ i) i) (∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) • fderiv ℝ (fun q => ∏ i, H q (σ i) i) p) p` using `HasFDerivAt.fun_sum fun σ _ => ((hterm σ).1.hasFDerivAt).const_mul _`. Rewrite using `[hexp]`.

Use `⟨hd.differentiableAt, ?_⟩` and prove the remaining obligations. Rewrite using `[hd.fderiv]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `σ _`.

Use `(ContinuousLinearMap.opNorm_smul_le _ _).trans ?_` and prove the remaining obligations. Establish `hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]`. Rewrite using `[hs, one_mul]`. Conclude with `(hterm σ).2`.

Use `_ = (k.factorial : ℝ) * k * A ^ (k - 1) * B := by`. Rewrite using `[Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem MatrixDetDeriv.proof : MatrixDetDeriv.Statement := by
  intro E _ _ k H p A B h
  classical
  have hexp : (fun q => (H q).det) =
      fun q => ∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, H q (σ i) i := by
    funext q
    exact Matrix.det_apply' (H q)
  have hterm : ∀ σ : Equiv.Perm (Fin k),
      DifferentiableAt ℝ (fun q => ∏ i, H q (σ i) i) p ∧
        ‖fderiv ℝ (fun q => ∏ i, H q (σ i) i) p‖ ≤ (k : ℝ) * A ^ (k - 1) * B := by
    intro σ
    have := MCMatrixDetDeriv.prod_fderiv_le (Finset.univ : Finset (Fin k))
      (fun i q => H q (σ i) i) p A B (fun i _ => h (σ i) i)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have hd : HasFDerivAt (fun q => ∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, H q (σ i) i)
      (∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        fderiv ℝ (fun q => ∏ i, H q (σ i) i) p) p :=
    HasFDerivAt.fun_sum fun σ _ => ((hterm σ).1.hasFDerivAt).const_mul _
  rw [hexp]
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.fderiv]
  calc ‖∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        fderiv ℝ (fun q => ∏ i, H q (σ i) i) p‖
      ≤ ∑ σ : Equiv.Perm (Fin k), ‖((Equiv.Perm.sign σ : ℤ) : ℂ) •
        fderiv ℝ (fun q => ∏ i, H q (σ i) i) p‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), (k : ℝ) * A ^ (k - 1) * B := by
        apply Finset.sum_le_sum
        intro σ _
        refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
        have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
        rw [hs, one_mul]
        exact (hterm σ).2
    _ = (k.factorial : ℝ) * k * A ^ (k - 1) * B := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin]
        ring

end GroundTheory.Heights₂.Heights
