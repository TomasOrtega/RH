import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

open GlobalTheory.FockCompare
open scoped ContDiff

namespace GlobalTheory.FockCompare

/- English proof (translation)
Establish `hd : DifferentiableAt ℝ (fun x : R => f (w + ι x)) ((0 : ℝ) • u)` using `((hf w).differentiable (by simp)).differentiableAt`. Establish `hl : HasDerivAt (fun t : ℝ => t • u) u 0`. Simplify using `using (hasDerivAt_id (0 : ℝ)).smul_const u`. Establish `h2 : HasDerivAt (fun t : ℝ => f (w + ι (t • u))) (fderiv ℝ (fun x : R => f (w + ι x)) 0 u) 0`. Use `hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl` as an intermediate fact.

Rewrite `this` using `[zero_smul]`. Conclude with `this`. Establish `h0 : HasDerivAt (fun t : ℝ => -(Real.pi * Complex.I) * ((om (π w) (t • u) : ℝ) : ℂ)) (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ)) 0`. Use `HasDerivAt.const_mul _ (HasDerivAt.ofReal_comp ?_)` and prove the remaining obligations. Simplify using `using (hasDerivAt_id (0 : ℝ)).mul_const (om (π w) u)`.

Establish `h3` using `(h0.cexp.mul h2).deriv`. Unfold `hD`. Use `Eq.trans h3 ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem hD_eq_fderiv {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (f : G → ℂ) (hf : Sm ι f) (u : R) (w : G) :
    hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w +
      fderiv ℝ (fun x : R => f (w + ι x)) 0 u := by
  have hd : DifferentiableAt ℝ (fun x : R => f (w + ι x)) ((0 : ℝ) • u) :=
    ((hf w).differentiable (by simp)).differentiableAt
  have hl : HasDerivAt (fun t : ℝ => t • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have h2 : HasDerivAt (fun t : ℝ => f (w + ι (t • u)))
      (fderiv ℝ (fun x : R => f (w + ι x)) 0 u) 0 := by
    have := hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [zero_smul] at this
    exact this
  have h0 : HasDerivAt (fun t : ℝ => -(Real.pi * Complex.I) * ((om (π w) (t • u) : ℝ) : ℂ))
      (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ)) 0 := by
    refine HasDerivAt.const_mul _ (HasDerivAt.ofReal_comp ?_)
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (om (π w) u)
  have h3 := (h0.cexp.mul h2).deriv
  unfold hD
  refine Eq.trans h3 ?_
  simp

/- English proof (translation)
Introduce `G R _ _ _ _ ι π om hπ f hf u`. Use `⟨hD_eq_fderiv ι π om f hf u, fun w => ?_⟩` and prove the remaining obligations. Establish `e : (fun x : R => hD ι π om u f (w + ι x)) = fun x : R => -(Real.pi * Complex.I) * ((om.flip u (π w + x) : ℝ) : ℂ) * f (w + ι x) + fderiv ℝ (fun y : R => f (w + ι y)) x u`. Use function extensionality and compare the values at `x`. Rewrite using `[hD_eq_fderiv ι π om f hf, map_add π, hπ, LinearMap.flip_apply]`.

Use `congr 2`. Use `fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : R => f (w + ι y)) (x := 0) x` as an intermediate fact. Rewrite `this` using `[add_zero]`. Rewrite using `[← this]`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Rewrite using `[map_add, add_assoc]`. Rewrite using `[e]`. Establish `h1 : ContDiff ℝ ∞ fun x : R => (om.flip u (π w + x) : ℝ)` using `(LinearMap.toContinuousLinearMap (om.flip u)).contDiff.comp (contDiff_const.add contDiff_id)`. Use `ContDiff.add (ContDiff.mul (ContDiff.mul contDiff_const (Complex.ofRealCLM.contDiff.comp h1)) (hf w)) ?_` and prove the remaining obligations.

Conclude with `((hf w).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const`.
-/
theorem hD_formula_smooth : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) →
    ∀ (f : G → ℂ), Sm ι f → ∀ u : R,
      (∀ w, hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w +
        fderiv ℝ (fun x : R => f (w + ι x)) 0 u) ∧ Sm ι (hD ι π om u f) := by
  intro G R _ _ _ _ ι π om hπ f hf u
  refine ⟨hD_eq_fderiv ι π om f hf u, fun w => ?_⟩
  have e : (fun x : R => hD ι π om u f (w + ι x)) = fun x : R =>
      -(Real.pi * Complex.I) * ((om.flip u (π w + x) : ℝ) : ℂ) * f (w + ι x) +
        fderiv ℝ (fun y : R => f (w + ι y)) x u := by
    funext x
    rw [hD_eq_fderiv ι π om f hf, map_add π, hπ, LinearMap.flip_apply]
    congr 2
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : R => f (w + ι y)) (x := 0) x
    rw [add_zero] at this
    rw [← this]
    congr 1
    funext y
    rw [map_add, add_assoc]
  rw [e]
  have h1 : ContDiff ℝ ∞ fun x : R => (om.flip u (π w + x) : ℝ) :=
    (LinearMap.toContinuousLinearMap (om.flip u)).contDiff.comp (contDiff_const.add contDiff_id)
  refine ContDiff.add (ContDiff.mul (ContDiff.mul contDiff_const
    (Complex.ofRealCLM.contDiff.comp h1)) (hf w)) ?_
  exact ((hf w).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

end GlobalTheory.FockCompare
