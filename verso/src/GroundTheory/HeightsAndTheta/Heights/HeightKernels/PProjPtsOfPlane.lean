import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ProjProjApply
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

namespace ProjectivePointsOfPlane

/- English proof (translation)
Rewrite using `[eval₂_comp_left]`. Use `congr 1`. Conclude with `RingHom.ext_int _ _`.
-/
theorem map_eval₂_int {ι A B : Type*} [CommRing A] [CommRing B] (k : A →+* B) (c : ℤ →+* A) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (eval₂ c g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by
  rw [eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

/- English proof (translation)
Rewrite using `[aeval_def, map_eval₂_int]`.
-/
theorem map_aeval_int {ι A B : Type*} [CommRing A] {_ : Algebra ℤ A} [CommRing B] (k : A →+* B) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (aeval g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by
  rw [aeval_def, map_eval₂_int]

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def formPoly (p : Σ _ : Unit, ProjIdx K i) : MvPolynomial (Fin i) K :=
  C (integralBasis K p.2.1) * X p.2.2

/- English proof (translation)
Simplify using `[formPoly, projPlanePt]`.
-/
theorem eval₂_formPoly (σ : K →+* ℂ) (v : Fin i → ℂ) (p : Σ _ : Unit, ProjIdx K i) :
    eval₂Hom σ v (formPoly p) = projPlanePt σ v p := by
  simp [formPoly, projPlanePt]

end ProjectivePointsOfPlane

open ProjectivePointsOfPlane in

/- English proof (translation)
Introduce `K _ _ i σ v hv`. Use `⟨fun _ => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `Function.ne_iff.mp hv`. Take `⟨m⟩` from `(integralBasis K).index_nonempty`. Use `⟨(m, j), ?_⟩` and prove the remaining obligations.

Simplify using `only [projPlanePt]`. Conclude with `mul_ne_zero ((map_ne_zero σ).mpr ((integralBasis K).ne_zero m)) hj`. Establish `h0 : mConeMap (projSpaceCoord K i) f = 0` using `hf`. Establish `h1` using `congrArg (MvPolynomial.eval fun _ : Unit => (1 : ProjField K i)) h0`. Unfold `mConeMap at h1`.

Rewrite `h1` using `[map_zero, map_aeval_int]`. Establish `hy : (MvPolynomial.eval fun _ : Unit => (1 : ProjField K i)) ∘ (fun p => C (projSpaceCoord K i p) * X p.1) = (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)) ∘ formPoly`. Use function extensionality and compare the values at `p`. Simplify using `[projSpaceCoord, formPoly]`. Rewrite `h1` using `[hy, ← map_eval₂_int (c := Int.castRingHom _)]`.

Establish `h2 : eval₂ (Int.castRingHom _) formPoly f = 0` using `(map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h1`. Establish `h3` using `congrArg (eval₂Hom σ v) h2`. Rewrite `h3` using `[map_zero, map_eval₂_int]`. Establish `hz : (eval₂Hom σ v) ∘ formPoly = projPlanePt σ v` using `funext (eval₂_formPoly σ v)`. Rewrite `h3` using `[hz]`.

Rewrite using `[eval_map]`. Conclude with `h3`.
-/
theorem ProjPtsOfPlane.proof : ProjPtsOfPlane.Statement := by
  intro K _ _ i σ v hv
  classical
  refine ⟨fun _ => ?_, fun f hf => ?_⟩
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    obtain ⟨m⟩ := (integralBasis K).index_nonempty
    refine ⟨(m, j), ?_⟩
    simp only [projPlanePt]
    exact mul_ne_zero ((map_ne_zero σ).mpr ((integralBasis K).ne_zero m)) hj
  · have h0 : mConeMap (projSpaceCoord K i) f = 0 := hf
    have h1 := congrArg (MvPolynomial.eval fun _ : Unit => (1 : ProjField K i)) h0
    unfold mConeMap at h1
    rw [map_zero, map_aeval_int] at h1
    have hy : (MvPolynomial.eval fun _ : Unit => (1 : ProjField K i)) ∘
        (fun p => C (projSpaceCoord K i p) * X p.1) =
        (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)) ∘ formPoly := by
      funext p
      simp [projSpaceCoord, formPoly]
    rw [hy, ← map_eval₂_int (c := Int.castRingHom _)] at h1
    have h2 : eval₂ (Int.castRingHom _) formPoly f = 0 :=
      (map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h1
    have h3 := congrArg (eval₂Hom σ v) h2
    rw [map_zero, map_eval₂_int] at h3
    have hz : (eval₂Hom σ v) ∘ formPoly = projPlanePt σ v := funext (eval₂_formPoly σ v)
    rw [hz] at h3
    rw [eval_map]
    exact h3

end

end GroundTheory.Heights₂.Heights
