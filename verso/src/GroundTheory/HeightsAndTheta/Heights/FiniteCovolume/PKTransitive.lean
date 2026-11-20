import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open GroundTheory.Automorphic Matrix
open scoped ComplexOrder

noncomputable section

/- English proof (translation)
Introduce `H P hmaj z z' hz hz' hzH hz'H`. Take `⟨ha, hb, hab⟩` from `h₁ H P hmaj z hzH`. Take `⟨ha', hb', hab'⟩` from `h₁ H P hmaj z' hz'H`. Establish `hsplit : ∀ w : ι → ℂ, plusPart H P w + minusPart H P w = w`. Introduce `w`.

Use extensionality with `i`. Simplify using `only [plusPart, minusPart, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hPpos` using `hmaj.1`. Establish `hne : ∀ w : ι → ℂ, w ≠ 0 → star (plusPart H P w) ⬝ᵥ (P *ᵥ plusPart H P w) = star (minusPart H P w) ⬝ᵥ (P *ᵥ minusPart H P w) → plusPart H P w ≠ 0`.

Introduce `w hw heq h0`. Apply `hw` to reduce the goal to its premises. Rewrite `heq` using `[h0]`. Simplify using `only [star_zero, zero_dotProduct] at heq`. Establish `hm : minusPart H P w = 0`.

Assume the negation of the conclusion as `hm`. Conclude with `(hPpos.dotProduct_mulVec_pos hm).ne heq`. Rewrite using `[← hsplit w, h0, hm, add_zero]`. Use `set a := plusPart H P z with ha_def`. Use `set b := minusPart H P z with hb_def`.

Use `set a' := plusPart H P z' with ha'_def`. Use `set b' := minusPart H P z' with hb'_def`. Establish `ha0 : a ≠ 0` using `hne z hz hab`. Establish `ha'0 : a' ≠ 0` using `hne z' hz' hab'`. Establish `hp` using `hPpos.dotProduct_mulVec_pos ha0`.

Establish `hq` using `hPpos.dotProduct_mulVec_pos ha'0`. Use `set p := star a ⬝ᵥ (P *ᵥ a) with hp_def`. Use `set q := star a' ⬝ᵥ (P *ᵥ a') with hq_def`. Take `⟨hpr, hpi⟩` from `Complex.lt_def.mp hp`. Take `⟨hqr, hqi⟩` from `Complex.lt_def.mp hq`.

Simplify using `only [Complex.zero_re, Complex.zero_im] at hpr hpi hqr hqi`. Use `set t : ℝ := Real.sqrt (p.re / q.re) with ht_def`. Establish `ht : 0 < t` using `Real.sqrt_pos.mpr (div_pos hpr hqr)`. Establish `htt : t * t = p.re / q.re` using `Real.mul_self_sqrt (div_nonneg hpr.le hqr.le)`. Establish `ht2 : (t : ℂ) * t * q = p`.

Establish `key : t * t * q.re = p.re` using `by rw [htt, div_mul_cancel₀ _ hqr.ne']`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[Complex.mul_re, ← hqi, key]`. Simplify using `[Complex.mul_im, ← hqi, ← hpi]`. Establish `hscale : ∀ v : ι → ℂ, star ((t : ℂ) • v) ⬝ᵥ (P *ᵥ ((t : ℂ) • v)) = (t : ℂ) * t * (star v ⬝ᵥ (P *ᵥ v))`.

Introduce `v`. Rewrite using `[star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct]`. Simplify using `only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hA1 : majInvolution H P *ᵥ ((t : ℂ) • a') = (1 : ℂ) • ((t : ℂ) • a')`.

Rewrite using `[mulVec_smul, ha', one_smul]`. Establish `hAm : majInvolution H P *ᵥ ((t : ℂ) • b') = (-1 : ℂ) • ((t : ℂ) • b')`. Rewrite using `[mulVec_smul, hb', neg_one_smul, smul_neg]`. Take `⟨α, hα, Rp, hRpP, hRpH, hRpa, hRpfix⟩` from `h₂ H P hmaj 1 (Or.inl rfl) a ((t : ℂ) • a') (by rw [ha, one_smul]) hA1 (by rw [hscale, ht2])`. Take `⟨β, hβ, Rm, hRmP, hRmH, hRmb, hRmfix⟩` from `h₂ H P hmaj (-1) (Or.inr rfl) b ((t : ℂ) • b') (by rw [hb, neg_one_smul]) hAm (by rw [hscale, ← hab', ht2, hab])`.

Establish `hβ0 : β ≠ 0`. Introduce `h`. Rewrite `hβ` using `[h, norm_zero]`. Conclude with `zero_ne_one hβ`. Establish `hc : ‖α / β‖ = 1` using `by rw [norm_div, hα, hβ, div_one]`.

Take `⟨hDP, hDH, hDplus, hDminus⟩` from `h₃ H P hmaj (α / β) hc`. Use `set D := phaseOnMinus H P (α / β) with hD_def`. Use `set M := D * Rm * Rp with hM_def`. Establish `hunit : ∀ X : Matrix ι ι ℂ, Dᴴ * X * D = X → Rmᴴ * X * Rm = X → Rpᴴ * X * Rp = X → Mᴴ * X * M = X`. Introduce `X h1 h2 h3`.

Establish `e : Mᴴ * X * M = Rpᴴ * (Rmᴴ * (Dᴴ * X * D) * Rm) * Rp`. Simplify using `only [hM_def, conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[e, h1, h2, h3]`. Establish `hMH : Mᴴ * H * M = H` using `hunit H hDH hRmH hRpH`. Establish `hMP : Mᴴ * P * M = P` using `hunit P hDP hRmP hRpP`.

Establish `hct : ∀ X : Matrix ι ι ℂ, (X.map (starRingEnd ℂ))ᵀ = Xᴴ` using `fun X => by`. Use extensionality with `i j`. Simplify using `[conjTranspose_apply]`. Establish `hRma : Rm *ᵥ a = a` using `hRmfix a (by rw [ha, neg_neg, one_smul])`. Establish `hMz : M *ᵥ ((t : ℂ) • z') = α • z`.

Establish `hz'2 : (t : ℂ) • z' = (t : ℂ) • a' + (t : ℂ) • b'` using `by rw [← smul_add, hsplit z']`. Rewrite using `[hz'2, hM_def, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_add, hRpa, hRpfix _ hAm, mulVec_add, mulVec_smul, hRma, hRmb, mulVec_add, mulVec_smul, mulVec_smul, hDplus a ha, hDminus b hb, smul_smul, mul_div_cancel₀ _ hβ0, ← smul_add, hsplit z]`. Establish `htc : (t : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr ht.ne'`. Establish `hdet : IsUnit M.det` using `isUnit_det_of_unitary (starRingEnd ℂ) hmaj.2.2.1 (by rw [hct]; exact hMH)`. Use `⟨nonsingInvUnit M hdet, ?_, ?_, (t : ℂ)⁻¹ * α, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_unitaryGroupMatrix] show (M.map (starRingEnd ℂ))ᵀ * H * M = H`. Rewrite using `[hct]`. Conclude with `hMH`. Rewrite using `[mem_unitaryGroupMatrix] show (M.map (starRingEnd ℂ))ᵀ * P * M = P`. Rewrite using `[hct]`.

Conclude with `hMP`. Use `show M *ᵥ z' = ((t : ℂ)⁻¹ * α) • z`. Rewrite `hMz` using `[mulVec_smul]`. Rewrite using `[mul_smul, ← hMz, smul_smul, inv_mul_cancel₀ htc, one_smul]`.
-/
theorem KTransitive.proof (ι : Type*) [Fintype ι] [DecidableEq ι]
    (h₁ : IsotropicSplit.Statement ι) (h₂ : EigenReflectionMaps.Statement ι)
    (h₃ : PhaseOnMinus.Statement ι) (_h₄ : EigenspacesOrthogonal.Statement ι) :
    KTransitive.Statement ι := by
  intro H P hmaj z z' hz hz' hzH hz'H
  obtain ⟨ha, hb, hab⟩ := h₁ H P hmaj z hzH
  obtain ⟨ha', hb', hab'⟩ := h₁ H P hmaj z' hz'H
  have hsplit : ∀ w : ι → ℂ, plusPart H P w + minusPart H P w = w := by
    intro w; ext i; simp only [plusPart, minusPart, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul]; ring
  have hPpos := hmaj.1
  have hne : ∀ w : ι → ℂ, w ≠ 0 →
      star (plusPart H P w) ⬝ᵥ (P *ᵥ plusPart H P w) =
        star (minusPart H P w) ⬝ᵥ (P *ᵥ minusPart H P w) → plusPart H P w ≠ 0 := by
    intro w hw heq h0
    apply hw
    rw [h0] at heq
    simp only [star_zero, zero_dotProduct] at heq
    have hm : minusPart H P w = 0 := by
      by_contra hm
      exact (hPpos.dotProduct_mulVec_pos hm).ne heq
    rw [← hsplit w, h0, hm, add_zero]
  set a := plusPart H P z with ha_def
  set b := minusPart H P z with hb_def
  set a' := plusPart H P z' with ha'_def
  set b' := minusPart H P z' with hb'_def
  have ha0 : a ≠ 0 := hne z hz hab
  have ha'0 : a' ≠ 0 := hne z' hz' hab'
  have hp := hPpos.dotProduct_mulVec_pos ha0
  have hq := hPpos.dotProduct_mulVec_pos ha'0
  set p := star a ⬝ᵥ (P *ᵥ a) with hp_def
  set q := star a' ⬝ᵥ (P *ᵥ a') with hq_def
  obtain ⟨hpr, hpi⟩ := Complex.lt_def.mp hp
  obtain ⟨hqr, hqi⟩ := Complex.lt_def.mp hq
  simp only [Complex.zero_re, Complex.zero_im] at hpr hpi hqr hqi
  set t : ℝ := Real.sqrt (p.re / q.re) with ht_def
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hpr hqr)
  have htt : t * t = p.re / q.re := Real.mul_self_sqrt (div_nonneg hpr.le hqr.le)
  have ht2 : (t : ℂ) * t * q = p := by
    have key : t * t * q.re = p.re := by rw [htt, div_mul_cancel₀ _ hqr.ne']
    apply Complex.ext
    · simp [Complex.mul_re, ← hqi, key]
    · simp [Complex.mul_im, ← hqi, ← hpi]
  have hscale : ∀ v : ι → ℂ, star ((t : ℂ) • v) ⬝ᵥ (P *ᵥ ((t : ℂ) • v)) =
      (t : ℂ) * t * (star v ⬝ᵥ (P *ᵥ v)) := by
    intro v
    rw [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    ring
  have hA1 : majInvolution H P *ᵥ ((t : ℂ) • a') = (1 : ℂ) • ((t : ℂ) • a') := by
    rw [mulVec_smul, ha', one_smul]
  have hAm : majInvolution H P *ᵥ ((t : ℂ) • b') = (-1 : ℂ) • ((t : ℂ) • b') := by
    rw [mulVec_smul, hb', neg_one_smul, smul_neg]
  obtain ⟨α, hα, Rp, hRpP, hRpH, hRpa, hRpfix⟩ := h₂ H P hmaj 1 (Or.inl rfl) a ((t : ℂ) • a')
    (by rw [ha, one_smul]) hA1 (by rw [hscale, ht2])
  obtain ⟨β, hβ, Rm, hRmP, hRmH, hRmb, hRmfix⟩ := h₂ H P hmaj (-1) (Or.inr rfl) b ((t : ℂ) • b')
    (by rw [hb, neg_one_smul]) hAm (by rw [hscale, ← hab', ht2, hab])
  have hβ0 : β ≠ 0 := by
    intro h; rw [h, norm_zero] at hβ; exact zero_ne_one hβ
  have hc : ‖α / β‖ = 1 := by rw [norm_div, hα, hβ, div_one]
  obtain ⟨hDP, hDH, hDplus, hDminus⟩ := h₃ H P hmaj (α / β) hc
  set D := phaseOnMinus H P (α / β) with hD_def
  set M := D * Rm * Rp with hM_def
  have hunit : ∀ X : Matrix ι ι ℂ, Dᴴ * X * D = X → Rmᴴ * X * Rm = X → Rpᴴ * X * Rp = X →
      Mᴴ * X * M = X := by
    intro X h1 h2 h3
    have e : Mᴴ * X * M = Rpᴴ * (Rmᴴ * (Dᴴ * X * D) * Rm) * Rp := by
      simp only [hM_def, conjTranspose_mul, Matrix.mul_assoc]
    rw [e, h1, h2, h3]
  have hMH : Mᴴ * H * M = H := hunit H hDH hRmH hRpH
  have hMP : Mᴴ * P * M = P := hunit P hDP hRmP hRpP
  have hct : ∀ X : Matrix ι ι ℂ, (X.map (starRingEnd ℂ))ᵀ = Xᴴ := fun X => by
    ext i j; simp [conjTranspose_apply]
  have hRma : Rm *ᵥ a = a := hRmfix a (by rw [ha, neg_neg, one_smul])
  have hMz : M *ᵥ ((t : ℂ) • z') = α • z := by
    have hz'2 : (t : ℂ) • z' = (t : ℂ) • a' + (t : ℂ) • b' := by rw [← smul_add, hsplit z']
    rw [hz'2, hM_def, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_add, hRpa, hRpfix _ hAm,
      mulVec_add, mulVec_smul, hRma, hRmb, mulVec_add, mulVec_smul, mulVec_smul, hDplus a ha,
      hDminus b hb, smul_smul, mul_div_cancel₀ _ hβ0, ← smul_add, hsplit z]
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hdet : IsUnit M.det := isUnit_det_of_unitary (starRingEnd ℂ) hmaj.2.2.1 (by rw [hct]; exact hMH)
  refine ⟨nonsingInvUnit M hdet, ?_, ?_, (t : ℂ)⁻¹ * α, ?_⟩
  · rw [mem_unitaryGroupMatrix]
    show (M.map (starRingEnd ℂ))ᵀ * H * M = H
    rw [hct]; exact hMH
  · rw [mem_unitaryGroupMatrix]
    show (M.map (starRingEnd ℂ))ᵀ * P * M = P
    rw [hct]; exact hMP
  · show M *ᵥ z' = ((t : ℂ)⁻¹ * α) • z
    rw [mulVec_smul] at hMz
    rw [mul_smul, ← hMz, smul_smul, inv_mul_cancel₀ htc, one_smul]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
