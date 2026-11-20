import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ProjProjApply
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

namespace ProjectivePointsOfPlane

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem map_eval₂_int {ι A B : Type*} [CommRing A] [CommRing B] (k : A →+* B) (c : ℤ →+* A) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (eval₂ c g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by
  rw [eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem map_aeval_int {ι A B : Type*} [CommRing A] {_ : Algebra ℤ A} [CommRing B] (k : A →+* B) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (aeval g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by
  rw [aeval_def, map_eval₂_int]

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def formPoly (p : Σ _ : Unit, ProjIdx K i) : MvPolynomial (Fin i) K :=
  C (integralBasis K p.2.1) * X p.2.2

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem eval₂_formPoly (σ : K →+* ℂ) (v : Fin i → ℂ) (p : Σ _ : Unit, ProjIdx K i) :
    eval₂Hom σ v (formPoly p) = projPlanePt σ v p := by
  simp [formPoly, projPlanePt]

end ProjectivePointsOfPlane

open ProjectivePointsOfPlane in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
