import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StandardLatticeVecIndep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ShortFamilyEquivSmallFamilyVec
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField TensorProduct

noncomputable section

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
The claim follows from `norm_pos_iff.mpr ((linearIndependent_fibreVec E.metric σ hs).ne_zero i)`.
-/
theorem norm_fibreVec_pos_of_linearIndependent {E : HermitianBundle.{0} K} {ι : Type*}
    {s : ι → E.carrier} (hs : LinearIndependent (𝓞 K) s) (σ : K →+* ℂ) (i : ι) :
    0 < ‖fibreVec E.metric σ (s i)‖ :=
  norm_pos_iff.mpr ((linearIndependent_fibreVec E.metric σ hs).ne_zero i)

/- English proof (translation)
Take `⟨x, hx⟩` from `exists_linearIndependent_cons_of_lt_finrank (R := 𝓞 K) (M := E.carrier) (v := Fin.elim0) (linearIndependent_empty_type) h`. Conclude with `⟨_, hx⟩`.
-/
theorem exists_linearIndependent_one (E : HermitianBundle.{0} K) (h : 0 < bundleRank E) :
    ∃ s : Fin 1 → E.carrier, LinearIndependent (𝓞 K) s := by
  obtain ⟨x, hx⟩ := exists_linearIndependent_cons_of_lt_finrank (R := 𝓞 K) (M := E.carrier)
    (v := Fin.elim0) (linearIndependent_empty_type) h
  exact ⟨_, hx⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_linearIndependent_one E' h`. Establish `hs' : LinearIndependent (𝓞 K) (α.toLinearMap ∘ s)` using `hs.map' α.toLinearMap (LinearMap.ker_eq_bot.mpr α.injective)`. Establish `h1` using `norm_fibreVec_pos_of_linearIndependent hs' σ 0`. Simplify using `only [Function.comp_apply] at h1`. Establish `h2` using `α.norm_le σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] s 0)`.

Rewrite `h2` using `[LinearMap.lTensor_tmul, fibreNorm_one_tmul, fibreNorm_one_tmul]`. Establish `h3` using `norm_nonneg (fibreVec E'.metric σ (s 0))`. Assume the negation of the conclusion as `hA`. Establish `hA'` using `not_lt.mp hA`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem BoundedInjection.pos {E' E : HermitianBundle.{0} K} {A : (K →+* ℂ) → ℝ}
    (α : BoundedInjection E' E A) (h : 0 < bundleRank E') (σ : K →+* ℂ) : 0 < A σ := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_one E' h
  have hs' : LinearIndependent (𝓞 K) (α.toLinearMap ∘ s) :=
    hs.map' α.toLinearMap (LinearMap.ker_eq_bot.mpr α.injective)
  have h1 := norm_fibreVec_pos_of_linearIndependent hs' σ 0
  simp only [Function.comp_apply] at h1
  have h2 := α.norm_le σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] s 0)
  rw [LinearMap.lTensor_tmul, fibreNorm_one_tmul, fibreNorm_one_tmul] at h2
  have h3 := norm_nonneg (fibreVec E'.metric σ (s 0))
  by_contra hA
  have hA' := not_lt.mp hA
  nlinarith

/- English proof (translation)
Establish `h1` using `norm_fibreVec_pos_of_linearIndependent F.linearIndependent σ ⟨0, h⟩`. Establish `h2` using `F.norm_le σ ⟨0, h⟩`. Rewrite `h2` using `[fibreNorm_one_tmul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ShortFamily.pos {E : HermitianBundle.{0} K} {lam : (K →+* ℂ) → ℝ}
    (F : ShortFamily E lam) (h : 0 < bundleRank E) (σ : K →+* ℂ) : 0 < lam σ := by
  have h1 := norm_fibreVec_pos_of_linearIndependent F.linearIndependent σ ⟨0, h⟩
  have h2 := F.norm_le σ ⟨0, h⟩
  rw [fibreNorm_one_tmul] at h2
  linarith

omit [NumberField K] in

def posOrOne (f : (K →+* ℂ) → ℝ) (σ : K →+* ℂ) : ℝ := if 0 < f σ then f σ else 1

omit [NumberField K] in
/- English proof (translation)
Unfold `posOrOne`. Use `split_ifs with hf`. Conclude with `h`. Establish `hf'` using `not_lt.mp hf`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_posOrOne {f : (K →+* ℂ) → ℝ} {σ : K →+* ℂ} {y : ℝ} (h : y ≤ f σ) :
    y ≤ posOrOne f σ := by
  unfold posOrOne
  split_ifs with hf
  · exact h
  · have hf' := not_lt.mp hf; linarith

def ShortFamily.posOrOne {E : HermitianBundle.{0} K} {lam : (K →+* ℂ) → ℝ}
    (F : ShortFamily E lam) : ShortFamily E (posOrOne lam) where
  vec := F.vec
  linearIndependent := F.linearIndependent
  norm_le σ i := le_posOrOne (F.norm_le σ i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
