import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix

/- English proof (translation)
Introduce `H P hM z hz`. Take `⟨hP, hH, hdet, hPHP⟩` from `hM`. Use `set A := majInvolution H P with hAdef`. Establish `hA2 : A * A = 1`. Rewrite using `[hAdef, majInvolution, show H⁻¹ * P * (H⁻¹ * P) = H⁻¹ * (P * H⁻¹ * P) by`.

Simplify using `only [Matrix.mul_assoc], hPHP, nonsing_inv_mul H hdet]`. Establish `hPA : P * A = H`. Rewrite using `[hAdef, majInvolution, ← Matrix.mul_assoc, hPHP]`. Establish `hAA (v : ι → ℂ) : A *ᵥ (A *ᵥ v) = v`. Rewrite using `[mulVec_mulVec, hA2, one_mulVec]`.

Use `set a := plusPart H P z with hadef`. Use `set b := minusPart H P z with hbdef`. Establish `ha : A *ᵥ a = a`. Rewrite using `[hadef, plusPart, ← hAdef, mulVec_smul, mulVec_add, hAA, add_comm]`. Establish `hb : A *ᵥ b = -b`.

Rewrite using `[hbdef, minusPart, ← hAdef, mulVec_smul, mulVec_sub, hAA, ← smul_neg, neg_sub]`. Establish `hzab : z = a + b`. Rewrite using `[hadef, hbdef, plusPart, minusPart, ← smul_add]`. Use extensionality with `i`. Simplify using `only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hAzab : A *ᵥ z = a - b`. Rewrite using `[hadef, hbdef, plusPart, minusPart, ← hAdef, ← smul_sub]`. Use extensionality with `i`. Simplify using `only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hab : star a ⬝ᵥ (P *ᵥ b) = 0` using `h₁ H P ⟨hP, hH, hdet, hPHP⟩ a b ha hb`. Establish `hba : star b ⬝ᵥ (P *ᵥ a) = 0`. Rewrite using `[star_dotProduct, star_mulVec, ← dotProduct_mulVec, hP.1.eq, hab, star_zero]`. Use `⟨ha, hb, ?_⟩` and prove the remaining obligations.

Establish `h0 : star (a + b) ⬝ᵥ (P *ᵥ (a - b)) = 0`. Rewrite using `[← hAzab, ← hzab, mulVec_mulVec, hPA, hz]`. Rewrite `h0` using `[star_add, add_dotProduct, mulVec_sub, dotProduct_sub, dotProduct_sub, hab, hba]`. Take the linear combination `h0`.
-/
theorem IsotropicSplit.proof (ι : Type*) [Fintype ι] [DecidableEq ι]
    (h₁ : EigenspacesOrthogonal.Statement ι) : IsotropicSplit.Statement ι := by
  intro H P hM z hz
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  set A := majInvolution H P with hAdef
  have hA2 : A * A = 1 := by
    rw [hAdef, majInvolution, show H⁻¹ * P * (H⁻¹ * P) = H⁻¹ * (P * H⁻¹ * P) by
      simp only [Matrix.mul_assoc], hPHP, nonsing_inv_mul H hdet]
  have hPA : P * A = H := by
    rw [hAdef, majInvolution, ← Matrix.mul_assoc, hPHP]
  have hAA (v : ι → ℂ) : A *ᵥ (A *ᵥ v) = v := by
    rw [mulVec_mulVec, hA2, one_mulVec]
  set a := plusPart H P z with hadef
  set b := minusPart H P z with hbdef
  have ha : A *ᵥ a = a := by
    rw [hadef, plusPart, ← hAdef, mulVec_smul, mulVec_add, hAA, add_comm]
  have hb : A *ᵥ b = -b := by
    rw [hbdef, minusPart, ← hAdef, mulVec_smul, mulVec_sub, hAA, ← smul_neg, neg_sub]
  have hzab : z = a + b := by
    rw [hadef, hbdef, plusPart, minusPart, ← smul_add]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hAzab : A *ᵥ z = a - b := by
    rw [hadef, hbdef, plusPart, minusPart, ← hAdef, ← smul_sub]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hab : star a ⬝ᵥ (P *ᵥ b) = 0 := h₁ H P ⟨hP, hH, hdet, hPHP⟩ a b ha hb
  have hba : star b ⬝ᵥ (P *ᵥ a) = 0 := by
    rw [star_dotProduct, star_mulVec, ← dotProduct_mulVec, hP.1.eq, hab, star_zero]
  refine ⟨ha, hb, ?_⟩
  have h0 : star (a + b) ⬝ᵥ (P *ᵥ (a - b)) = 0 := by
    rw [← hAzab, ← hzab, mulVec_mulVec, hPA, hz]
  rw [star_add, add_dotProduct, mulVec_sub, dotProduct_sub, dotProduct_sub, hab, hba] at h0
  linear_combination h0

end GroundTheory.Heights₂.Heights.FiniteCovolume
