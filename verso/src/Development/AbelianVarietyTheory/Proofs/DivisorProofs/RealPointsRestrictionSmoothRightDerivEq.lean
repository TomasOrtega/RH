import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic NormedSpace
open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory.HCA

/- English proof (translation)
Introduce `E _ _ _ a φ x`. Set `T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a` to `LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap`. Establish `hT : ∀ M, T M = toL M` using `fun _ => rfl`. Establish `key : ∀ (g : glG E a) (Y : glL E a), glRes φ.1 x (g * (glH E a).expG Y) = chart φ.1 x (T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E))))`. Introduce `g Y`.

Rewrite using `[hT]`. Conclude with `(chart_val φ.1 x ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) * ((glH E a).expG Y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ))).symm`. Establish `hs : (glH E a).IsSmoothFun (glRes φ.1 x)`. Rewrite using `[IsExpLieAlgebra.isSmoothFun_iff]`. Introduce `g`.

Establish `e : (fun Y : glL E a => glRes φ.1 x (g * (glH E a).expG Y)) = chart φ.1 x ∘ fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))`. Use function extensionality and compare the values at `(key g)`. Rewrite using `[e]`. Establish `h1 : ContDiff ℝ ∞ (fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E))))` using `T.contDiff.comp (contDiff_const.mul ((contDiff_exp ℝ _).comp (glL E a).subtypeL.contDiff))`. Conclude with `(φ.2 x).comp_contDiff h1 fun Y => ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) * ((glH E a).expG Y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)).isUnit`.

Use `⟨hs, fun X => funext fun g => ?_⟩` and prove the remaining obligations. Establish `h2` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (0 : ℝ)`. Rewrite `h2` using `[zero_smul, NormedSpace.exp_zero, one_mul]`. Establish `hc : HasDerivAt (fun t : ℝ => toL (((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Matrix (Fin a) (Fin a) (Cinf E))) (toL X.1) 0` using `T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2`. Establish `h0 : (((glH E a).expG ((0 : ℝ) • X) : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) = 1`.

Use extensionality with `: 1`. Simplify using the standard rewrite rules. Establish `h3` using `hasDerivAt_curve φ (x * infGL E a (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)) (fun t => ((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)) (toL X.1) h0 hc`. Establish `ef : (fun t : ℝ => glRes φ.1 x (g * (glH E a).expG (t • X))) = fun t : ℝ => φ.1 (x * infGL E a (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) * infGL E a ((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ))`. Use function extensionality and compare the values at `t`.

Simplify using `only [glRes, Subgroup.coe_mul, map_mul, mul_assoc]`. Establish `h4` using `(glH E a).hasDerivAt_rightDeriv hs X g`. Rewrite `h4` using `[ef]`. Conclude with `h4.unique h3`.
-/
theorem glRes_smooth_rightDeriv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    ∀ φ : Sm E a, ∀ x, (glH E a).IsSmoothFun (glRes φ.1 x) ∧
      ∀ X : glL E a, (glH E a).rightDeriv X (glRes φ.1 x) = glRes (lie E a (toL X.1) φ).1 x := by
  intro E _ _ _ a φ x
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  have hT : ∀ M, T M = toL M := fun _ => rfl
  have key : ∀ (g : glG E a) (Y : glL E a), glRes φ.1 x (g * (glH E a).expG Y) =
      chart φ.1 x (T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))) := by
    intro g Y
    rw [hT]
    exact (chart_val φ.1 x ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) * ((glH E a).expG Y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ))).symm
  have hs : (glH E a).IsSmoothFun (glRes φ.1 x) := by
    rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro g
    have e : (fun Y : glL E a => glRes φ.1 x (g * (glH E a).expG Y)) =
        chart φ.1 x ∘ fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E))) :=
      funext (key g)
    rw [e]
    have h1 : ContDiff ℝ ∞ (fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))) :=
      T.contDiff.comp (contDiff_const.mul ((contDiff_exp ℝ _).comp (glL E a).subtypeL.contDiff))
    exact (φ.2 x).comp_contDiff h1 fun Y =>
      ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) * ((glH E a).expG Y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)).isUnit
  refine ⟨hs, fun X => funext fun g => ?_⟩
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  have hc : HasDerivAt (fun t : ℝ => toL (((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Matrix (Fin a) (Fin a) (Cinf E)))
      (toL X.1) 0 := T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h0 : (((glH E a).expG ((0 : ℝ) • X) : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) = 1 := by
    ext : 1
    simp
  have h3 := hasDerivAt_curve φ (x * infGL E a (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ))
    (fun t => ((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)) (toL X.1) h0 hc
  have ef : (fun t : ℝ => glRes φ.1 x (g * (glH E a).expG (t • X))) = fun t : ℝ =>
      φ.1 (x * infGL E a (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) *
        infGL E a ((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)) := by
    funext t
    simp only [glRes, Subgroup.coe_mul, map_mul, mul_assoc]
  have h4 := (glH E a).hasDerivAt_rightDeriv hs X g
  rw [ef] at h4
  exact h4.unique h3

end GlobalTheory.HCA

end
