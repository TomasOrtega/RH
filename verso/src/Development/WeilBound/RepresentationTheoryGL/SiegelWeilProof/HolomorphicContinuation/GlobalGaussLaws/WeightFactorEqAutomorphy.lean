import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLaw
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussO

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

/- English proof (translation)
Simplify using `only [F0, f0, jF, u1, u2, conj_I_smul_one, Matrix.mul_neg, mul_I_smul_one]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weight_factor_eq_automorphy (p q : ℕ) (e : ℤ) (y : GR n) : F0 p q e y = jF e p q y (Complex.I • 1) := by
  simp only [F0, f0, jF, u1, u2, conj_I_smul_one, Matrix.mul_neg, mul_I_smul_one]
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.GaussH

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

/- English proof (translation)
Introduce `hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL`. Take `⟨σ, hσ⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ`. Take `⟨k, ⟨j, hj⟩, hk⟩` from `LocLawH.chi_exp hC.hθ hC.hχ hC.hη τ`. Use `⟨k - j, fun y a ha hy f hf => ?_⟩` and prove the remaining obligations. Use `set A : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero a ha.ne_zero with hAdef`.

Establish `hAv : A.1 = a` using `rfl`. Establish `hAi : (A⁻¹).1 = a⁻¹` using `by rw [Matrix.coe_units_inv, hAv]`. Establish `hyA : y = LocLawH.mOf A`. Apply `GR_ext` to reduce the goal to its premises. Rewrite using `[hy, LocLawH.mR_mOf, hAv, hAi, Matrix.conjTranspose_nonsing_inv]`.

Both sides reduce to the same expression. Establish `hy0 : (mR (LocLawH.mOf A)).toBlocks₂₁ = 0` using `by simp [LocLawH.mR_mOf]`. Establish `haOf : LocLawH.aOf (LocLawH.mOf A) hy0 = A` using `Units.ext (by rw [LocLawH.aOf_val, LocLawH.mR_mOf]; simp)`. Establish `hsc` using `LocLawH.scal hC.hθ hσ k j hk hj (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) (cnt_add _) (LocLawH.mOf A) hy0`. Rewrite `hsc` using `[haOf]`.

Use `hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC _ _ fun Ψ hΨ => ?_` and prove the remaining obligations. Rewrite using `[← hL.2 y Ψ hΨ f hf]`. Use function extensionality and compare the values at `x`. Rewrite using `[hyA, hC.hω.levi _ (LocLawH.unitAt hσ τ A) (LocLawH.mat_mOf hσ hC.hι A), hsc, weight_factor_eq_automorphy, siegelP_jF _ hy0, cnt_add]`. Establish `hbl : (mR (LocLawH.mOf A)).toBlocks₁₁ = a` using `by rw [LocLawH.mR_mOf]; simp [hAv]`.

Rewrite using `[hbl]`. Establish `hΨx : Ψ (HMul.hMul x (LocLawH.unitAt hσ τ A).1 : Mx D V.rank n) = Ψ x`. Use `hΨ.1 _ _ (fun τ' h => ?_) ?_` and prove the remaining obligations. Rewrite using `[LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_ne hσ h, Matrix.mul_one]`. Rewrite using `[LocLawH.unitAt_val, Matrix.map_mul, LocLawH.finite_part_adelic_point_matrix hσ, Matrix.mul_one]`.

Simplify using `only [tens, hΨx, levF]`. Rewrite using `[LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_matrix hσ, hAv, ← Matrix.mul_assoc]`. Establish `hof : (Matrix.of (fr⁻¹ * compAt θ τ x) : Matrix (Fin V.rank) (Fin n) ℂ) = fr⁻¹ * compAt θ τ x` using `rfl`. Rewrite using `[hof]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lawM_of : TensInj → LawM := by
  intro hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  obtain ⟨k, ⟨j, hj⟩, hk⟩ := LocLawH.chi_exp hC.hθ hC.hχ hC.hη τ
  refine ⟨k - j, fun y a ha hy f hf => ?_⟩
  set A : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero a ha.ne_zero with hAdef
  have hAv : A.1 = a := rfl
  have hAi : (A⁻¹).1 = a⁻¹ := by rw [Matrix.coe_units_inv, hAv]
  have hyA : y = LocLawH.mOf A := by
    apply GR_ext
    rw [hy, LocLawH.mR_mOf, hAv, hAi, Matrix.conjTranspose_nonsing_inv]
    rfl
  have hy0 : (mR (LocLawH.mOf A)).toBlocks₂₁ = 0 := by simp [LocLawH.mR_mOf]
  have haOf : LocLawH.aOf (LocLawH.mOf A) hy0 = A := Units.ext (by rw [LocLawH.aOf_val, LocLawH.mR_mOf]; simp)
  have hsc := LocLawH.scal hC.hθ hσ k j hk hj (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false)
    (cnt_add _) (LocLawH.mOf A) hy0
  rw [haOf] at hsc
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC _ _ fun Ψ hΨ => ?_
  rw [← hL.2 y Ψ hΨ f hf]
  funext x
  rw [hyA, hC.hω.levi _ (LocLawH.unitAt hσ τ A) (LocLawH.mat_mOf hσ hC.hι A), hsc, weight_factor_eq_automorphy,
    siegelP_jF _ hy0, cnt_add]
  have hbl : (mR (LocLawH.mOf A)).toBlocks₁₁ = a := by rw [LocLawH.mR_mOf]; simp [hAv]
  rw [hbl]
  have hΨx : Ψ (HMul.hMul x (LocLawH.unitAt hσ τ A).1 : Mx D V.rank n) = Ψ x := by
    refine hΨ.1 _ _ (fun τ' h => ?_) ?_
    · rw [LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_ne hσ h, Matrix.mul_one]
    · rw [LocLawH.unitAt_val, Matrix.map_mul, LocLawH.finite_part_adelic_point_matrix hσ, Matrix.mul_one]
  simp only [tens, hΨx, levF]
  rw [LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_matrix hσ, hAv, ← Matrix.mul_assoc]
  have hof : (Matrix.of (fr⁻¹ * compAt θ τ x) : Matrix (Fin V.rank) (Fin n) ℂ) = fr⁻¹ * compAt θ τ x := rfl
  rw [hof]
  ring

end PositivityTheory.Rg.Sw.Glob
