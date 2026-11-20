import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsImEqLattice

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators ComplexOrder
open Matrix

namespace GlobalTheory.MomOne.ThetaLine

variable {g : ℕ}

/- English proof (translation)
Simplify using `only [dotProduct, mulVec, transpose_apply, hf, Pi.star_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dot_transpose_eq_hf (Hm : Matrix (Fin g) (Fin g) ℂ) (z a : Fin g → ℂ) :
    star a ⬝ᵥ Hmᵀ.mulVec z = hf Hm z a := by
  simp only [dotProduct, mulVec, transpose_apply, hf, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  ring

/- English proof (translation)
Take `⟨u, v, huv⟩` from `h`. Use `⟨v, ?_⟩` and prove the remaining obligations. Establish `hs : Real.sqrt d / 2 ≠ 0`. Establish `: (0 : ℝ) < Real.sqrt d` using `Real.sqrt_pos.mpr (by exact_mod_cast hd)`. Check the signs of the components of the expression.

Establish `key : (beta d Hm x y).im = Real.sqrt d / 2 * (hf Hm x y).im`. Rewrite using `[beta, Complex.im_ofReal_mul]`. Establish `hv : (beta d Hm x y).im = Real.sqrt d / 2 * v`. Rewrite using `[huv]`. Simplify using `[w0, rtd]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_left_cancel₀ hs (key.symm.trans hv)`.
-/
theorem im_hf_int {d : ℕ} (hd : 0 < d) (Hm : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ)
    (h : beta d Hm x y ∈ OK d) : ∃ k : ℤ, (hf Hm x y).im = k := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨v, ?_⟩
  have hs : Real.sqrt d / 2 ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    positivity
  have key : (beta d Hm x y).im = Real.sqrt d / 2 * (hf Hm x y).im := by
    rw [beta, Complex.im_ofReal_mul]
  have hv : (beta d Hm x y).im = Real.sqrt d / 2 * v := by
    rw [huv]
    simp [w0, rtd]
    ring
  exact mul_left_cancel₀ hs (key.symm.trans hv)

/- English proof (translation)
Establish `hz` using `congrFun h z`. Simplify using `only [opW, opU] at hz`. Establish `e1 : Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ))) * Complex.exp ((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ)) = 1`. Rewrite using `[← Complex.exp_add, neg_add_cancel, Complex.exp_zero]`. Establish `e2 : Complex.exp (Real.pi * hf Hm z x + Real.pi / 2 * hf Hm x x) * Complex.exp (-(Real.pi : ℂ) * hf Hm z x - (Real.pi : ℂ) / 2 * hf Hm x x) = 1`.

Rewrite using `[← Complex.exp_add]`. Use `Complex.exp_zero using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hz]`. Take the linear combination `(-(G (z + x) * Complex.exp (Real.pi * hf Hm z x + Real.pi / 2 * hf Hm x x) * Complex.exp (-(Real.pi : ℂ) * hf Hm z x - (Real.pi : ℂ) / 2 * hf Hm x x))) * e1 - G (z + x) * e2`.
-/
theorem transl_of_fixed {d : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {x : Fin g → ℂ}
    {G : (Fin g → ℂ) → ℂ} (h : opW d Hm x G = G) (z : Fin g → ℂ) :
    G (z + x) = Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ))) *
      Complex.exp (Real.pi * hf Hm z x + Real.pi / 2 * hf Hm x x) * G z := by
  have hz := congrFun h z
  simp only [opW, opU] at hz
  have e1 : Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ))) *
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ)) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have e2 : Complex.exp (Real.pi * hf Hm z x + Real.pi / 2 * hf Hm x x) *
      Complex.exp (-(Real.pi : ℂ) * hf Hm z x - (Real.pi : ℂ) / 2 * hf Hm x x) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  rw [← hz]
  linear_combination (-(G (z + x) * Complex.exp (Real.pi * hf Hm z x + Real.pi / 2 * hf Hm x x) *
      Complex.exp (-(Real.pi : ℂ) * hf Hm z x - (Real.pi : ℂ) / 2 * hf Hm x x))) * e1 - G (z + x) * e2

/- English proof (translation)
Introduce `g S e F hS he hF hF0`. Take `⟨hp, -, hH, hdisc, -, -, hβ, hdual⟩` from `hS`. Establish `: DiscreteTopology S.La.toAddSubgroup` using `hdisc`. Establish `hlaw : ∀ G : (Fin g → ℂ) → ℂ, S.IsTheta G → ∀ a ∈ S.La.toAddSubgroup, ∀ z, G (z + a) = Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta S.d S.Hm a a).re : ℂ))) * Complex.exp (Real.pi * (star a ⬝ᵥ S.Hmᵀ.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ S.Hmᵀ.mulVec a)) * G z`. Introduce `G hG a ha z`.

Rewrite using `[dot_transpose_eq_hf, dot_transpose_eq_hf]`. Conclude with `transl_of_fixed (hG.2 a ha) z`. Use `GlobalTheory.ThetaTranslSpan.exists_eq_smul hH.transpose S.La.toAddSubgroup ?_ (fun a => Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta S.d S.Hm a a).re : ℂ)))) F e ?_ (hF.1.differentiable (by simp)) hF0 (hlaw F hF) (he.1.differentiable (by simp)) (hlaw e he)` and prove the remaining obligations. Introduce `v`. Simplify using `only [dot_transpose_eq_hf]`.

Conclude with `⟨hdual v, fun hv a ha => im_hf_int hp.pos S.Hm a v (hβ a ha v hv)⟩`. Introduce `a _`. Simplify using `[Complex.norm_exp]`.
-/
theorem exists_eq_smul : ∀ (g : ℕ) (S : Setup g) (e F : (Fin g → ℂ) → ℂ), S.Ok → S.IsTheta e → S.IsTheta F → F ≠ 0 → ∃ c : ℂ, e = c • F := by
  intro g S e F hS he hF hF0
  obtain ⟨hp, -, hH, hdisc, -, -, hβ, hdual⟩ := hS
  have : DiscreteTopology S.La.toAddSubgroup := hdisc
  have hlaw : ∀ G : (Fin g → ℂ) → ℂ, S.IsTheta G → ∀ a ∈ S.La.toAddSubgroup, ∀ z,
      G (z + a) = Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta S.d S.Hm a a).re : ℂ))) *
        Complex.exp (Real.pi * (star a ⬝ᵥ S.Hmᵀ.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ S.Hmᵀ.mulVec a)) * G z := by
    intro G hG a ha z
    rw [dot_transpose_eq_hf, dot_transpose_eq_hf]
    exact transl_of_fixed (hG.2 a ha) z
  refine GlobalTheory.ThetaTranslSpan.exists_eq_smul hH.transpose S.La.toAddSubgroup ?_
    (fun a => Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta S.d S.Hm a a).re : ℂ)))) F e ?_
    (hF.1.differentiable (by simp)) hF0 (hlaw F hF) (he.1.differentiable (by simp)) (hlaw e he)
  · intro v
    simp only [dot_transpose_eq_hf]
    exact ⟨hdual v, fun hv a ha => im_hf_int hp.pos S.Hm a v (hβ a ha v hv)⟩
  · intro a _
    simp [Complex.norm_exp]

end GlobalTheory.MomOne.ThetaLine
