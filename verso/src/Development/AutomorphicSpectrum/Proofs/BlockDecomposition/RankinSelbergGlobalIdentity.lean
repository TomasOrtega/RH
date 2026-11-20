import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.RankinSelberg

open Ad3 Ad3.R

/- English proof (translation)
Introduce `hB0 hA1 hG0 hG2a hG4 hG5 hGS hFT hF2 hF5 hF6 hF6c hE6 hG6`. Introduce `k N _ hk χ hχ f a hf ha ω φ hOm hL hP μ₁ μ₂ φ₀ hM m hm S hS c δ hc hδ hu x Ψ hΨ`. Take `⟨μ, 𝓕, mK, 𝓓, h0⟩` from `hG0`. Take `⟨C0, hC0⟩` from `hG2a μ 𝓕 mK 𝓓 h0`. Take `⟨hB1, -, -, -, hBun, -⟩` from `hB0`.

Take `⟨h, hh⟩` from `hBun S x`. Take `⟨γ, hγ⟩` from `hGS`. Use `haveI := h0.haarK`. Use `haveI := h0.probK`. Take `⟨C1, hC1, hE⟩` from `hE6 k N hk χ hχ f a hf ha ω φ hOm hL μ₁ μ₂ φ₀ hM mK m hm γ hγ`.

Take `⟨⟨Cb, hCb⟩, hDec⟩` from `hF5 k N hk χ hχ f a hf ha ω φ hOm hL`. Take `⟨hWc, -, -, -⟩` from `hF2 k N hk χ hχ f a hf ha ω φ hOm hL`. Establish `hcusp` using `hF6c k N hk χ hχ f a hf ha ω φ hOm hL`. Establish `hinf : ∀ w, infAt w h = 1` using `hh.2.2`. Establish `hDecH` using `hDec h hinf`.

Establish `hDec1 : Dec φ`. Use `hDec 1 (fun w => by simp)` as an intermediate fact. Simplify using `using this`. Establish `hcontR : Continuous fun g : G2 => φ (g * h)` using `hL.cont.comp (continuous_mul_right h)`. Establish `hleftR : LInv fun g : G2 => φ (g * h)` using `fun γ' g => by`.

Simplify using `only [mul_assoc]`. Conclude with `hL.left γ' (g * h)`. Establish `hWh : ∀ g, Wh (fun g : G2 => φ (g * h)) g = Wh φ (g * h)` using `fun g => by`. Simplify using `only [Wh, mul_assoc]`. Establish `hWhF : Wh (fun g : G2 => φ (g * h)) = fun g => Wh φ (g * h)` using `funext hWh`.

Establish `hWcR : Continuous (Wh fun g : G2 => φ (g * h))`. Rewrite using `[hWhF]`. Conclude with `hWc.comp (continuous_mul_right h)`. Establish `hPar : Par (fun g => φ g * conj (φ (g * h))) (fun g => Wh φ g * conj (Wh φ (g * h)))`. Use `hF6 φ (fun g => φ (g * h)) hL.cont hcontR hL.left hleftR hDec1 ⟨Cb, fun g => hCb _⟩ hcusp hWc hWcR` as an intermediate fact.

Rewrite `this` using `[hWhF]`. Conclude with `this`. Establish `hAut : Aut (fun g => φ g * conj (φ (g * h)))`. Use `⟨hL.cont.mul (Complex.continuous_conj.comp hcontR), ?_, ?_, ⟨Cb * Cb, fun g => ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `γ' g`.

Simplify using `only [mul_assoc]`. Rewrite using `[hL.left γ' g, hL.left γ' (g * h)]`. Introduce `z g`. Simplify using `only [mul_assoc]`. Rewrite using `[hL.cen z g, hL.cen z (g * h)]`.

Establish `: (ω.toIdele z : ℂ) * conj (ω.toIdele z : ℂ) = 1`. Rewrite using `[Complex.mul_conj, Circle.normSq_coe]`. Simplify using the standard rewrite rules. Simplify using `only [map_mul]`. Take the linear combination `(φ g * conj (φ (g * h))) * this`.

Establish `hb0 : 0 ≤ Cb` using `(norm_nonneg _).trans (hCb 1)`. Rewrite using `[norm_mul, RCLike.norm_conj]`. Conclude with `mul_le_mul (hCb _) (hCb _) (norm_nonneg _) hb0`. Introduce `M`. Take `⟨D, hD⟩` from `hDecH M`.

Establish `hb0 : 0 ≤ Cb` using `(norm_nonneg _).trans (hCb 1)`. Use `⟨Cb * D, fun x' a' κ => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, RCLike.norm_conj, mul_assoc Cb D]`. Conclude with `mul_le_mul (hCb _) (hD x' a' κ) (norm_nonneg _) hb0`. Take `⟨hΦ, hsFA⟩` from `hFT γ hγ S Ψ hΨ`.

Establish `hsΨ : ∀ v : S, SB (sF (localAdelicChar ℚ v.1) (Ψ v))` using `fun v => (hA1 (Qv v.1) (localAdelicChar ℚ v.1) (hB1 v.1).1 1 1 (Ψ v) 1 (hΨ v)).2.1`. Take `⟨hΦ', -⟩` from `hFT γ hγ S (fun v => sF (localAdelicChar ℚ v.1) (Ψ v)) hsΨ`. Establish `hci : IsOfFinOrder c⁻¹` using `hc.inv`. Establish `hδi : ∀ w : InfinitePlace ℚ, (c⁻¹.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1`. Introduce `w`.

Establish `h1 : (c⁻¹.infiniteComponent w (-1) : Circle) = (c.infiniteComponent w (-1))⁻¹` using `rfl`. Rewrite using `[h1, Circle.coe_inv, hδ w]`. Apply the tactic sequence `cases δ <;> simp`. Establish `hui : ∀ v ∉ S, IsUnramifiedChar (localChar c⁻¹ v)`. Introduce `v hv`.

Establish `h1 : localChar c⁻¹ v = (localChar c v)⁻¹`. Use extensionality with `a'`. Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `isUnramifiedChar_inv_iff.2 (hu v hv)`.

Take `⟨E, E', hd, hd', hEq, hfe, hnz⟩` from `hG4 μ 𝓕 mK 𝓓 h0 _ hAut _ hΦ c hc`. Apply the tactic sequence `have hsgn : (if δ then (-1 : ℂ) else 1) ≠ 0 := by cases δ <;> simp`. Use `⟨((C0 : ℝ) : ℂ) * C1 * (if δ then -1 else 1), E, E', ?_, hd, hd', ?_, hfe, ?_⟩` and prove the remaining obligations. Use `mul_ne_zero (mul_ne_zero ?_ hC1) hsgn` and prove the remaining obligations. Conclude with `hC0.1` after adjusting the coercions.

Introduce `s hs`. Take `⟨h1, h2⟩` from `hEq s hs`. Prove the components needed by the constructor for the conclusion. Rewrite using `[h1, hG5 μ 𝓕 mK 𝓓 C0 h0 hC0 _ _ hAut hPar _ hΦ c s hs, hE S hS c δ hc hδ hu x h hh Ψ hΨ s hs]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2, hsFA, hG5 μ 𝓕 mK 𝓓 C0 h0 hC0 _ _ hAut hPar _ hΦ' c⁻¹ s hs, hE S hS c⁻¹ δ hci hδi hui x h hh _ hsΨ s hs]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h1 hc1`. Conclude with `hG6 k N hk χ hχ f a hf ha ω φ hOm hL hP μ 𝓕 mK 𝓓 h0 S hS c hc hc1 hu x h hh (hnz h1)`.
-/
theorem globalIdentity : Ad3.R.B0 → Ad3.R.A1 → Ad3.R.G0 → Ad3.R.G2a → Ad3.R.G4 → Ad3.R.G5 → Ad3.R.GS →
    Ad3.R.FT → Ad3.R.F2 → Ad3.R.F5 → Ad3.R.F6 → Ad3.R.ConstantTermVanishingAlt → Ad3.R.E6 → Ad3.R.G6 → Ad3.R.X0 := by
  intro hB0 hA1 hG0 hG2a hG4 hG5 hGS hFT hF2 hF5 hF6 hF6c hE6 hG6
  intro k N _ hk χ hχ f a hf ha ω φ hOm hL hP μ₁ μ₂ φ₀ hM m hm S hS c δ hc hδ hu x Ψ hΨ
  obtain ⟨μ, 𝓕, mK, 𝓓, h0⟩ := hG0
  obtain ⟨C0, hC0⟩ := hG2a μ 𝓕 mK 𝓓 h0
  obtain ⟨hB1, -, -, -, hBun, -⟩ := hB0
  obtain ⟨h, hh⟩ := hBun S x
  obtain ⟨γ, hγ⟩ := hGS
  haveI := h0.haarK
  haveI := h0.probK
  obtain ⟨C1, hC1, hE⟩ := hE6 k N hk χ hχ f a hf ha ω φ hOm hL μ₁ μ₂ φ₀ hM mK m hm γ hγ
  obtain ⟨⟨Cb, hCb⟩, hDec⟩ := hF5 k N hk χ hχ f a hf ha ω φ hOm hL
  obtain ⟨hWc, -, -, -⟩ := hF2 k N hk χ hχ f a hf ha ω φ hOm hL
  have hcusp := hF6c k N hk χ hχ f a hf ha ω φ hOm hL
  have hinf : ∀ w, infAt w h = 1 := hh.2.2
  have hDecH := hDec h hinf
  have hDec1 : Dec φ := by
    have := hDec 1 (fun w => by simp)
    simpa using this
  have hcontR : Continuous fun g : G2 => φ (g * h) := hL.cont.comp (continuous_mul_right h)
  have hleftR : LInv fun g : G2 => φ (g * h) := fun γ' g => by
    simp only [mul_assoc]; exact hL.left γ' (g * h)
  have hWh : ∀ g, Wh (fun g : G2 => φ (g * h)) g = Wh φ (g * h) := fun g => by
    simp only [Wh, mul_assoc]
  have hWhF : Wh (fun g : G2 => φ (g * h)) = fun g => Wh φ (g * h) := funext hWh
  have hWcR : Continuous (Wh fun g : G2 => φ (g * h)) := by
    rw [hWhF]; exact hWc.comp (continuous_mul_right h)
  have hPar : Par (fun g => φ g * conj (φ (g * h))) (fun g => Wh φ g * conj (Wh φ (g * h))) := by
    have := hF6 φ (fun g => φ (g * h)) hL.cont hcontR hL.left hleftR hDec1
      ⟨Cb, fun g => hCb _⟩ hcusp hWc hWcR
    rw [hWhF] at this
    exact this
  have hAut : Aut (fun g => φ g * conj (φ (g * h))) := by
    refine ⟨hL.cont.mul (Complex.continuous_conj.comp hcontR), ?_, ?_, ⟨Cb * Cb, fun g => ?_⟩, ?_⟩
    · intro γ' g
      simp only [mul_assoc]
      rw [hL.left γ' g, hL.left γ' (g * h)]
    · intro z g
      simp only [mul_assoc]
      rw [hL.cen z g, hL.cen z (g * h)]
      have : (ω.toIdele z : ℂ) * conj (ω.toIdele z : ℂ) = 1 := by
        rw [Complex.mul_conj, Circle.normSq_coe]; simp
      simp only [map_mul]
      linear_combination (φ g * conj (φ (g * h))) * this
    · have hb0 : 0 ≤ Cb := (norm_nonneg _).trans (hCb 1)
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (hCb _) (hCb _) (norm_nonneg _) hb0
    · intro M
      obtain ⟨D, hD⟩ := hDecH M
      have hb0 : 0 ≤ Cb := (norm_nonneg _).trans (hCb 1)
      refine ⟨Cb * D, fun x' a' κ => ?_⟩
      rw [norm_mul, RCLike.norm_conj, mul_assoc Cb D]
      exact mul_le_mul (hCb _) (hD x' a' κ) (norm_nonneg _) hb0
  obtain ⟨hΦ, hsFA⟩ := hFT γ hγ S Ψ hΨ
  have hsΨ : ∀ v : S, SB (sF (localAdelicChar ℚ v.1) (Ψ v)) := fun v =>
    (hA1 (Qv v.1) (localAdelicChar ℚ v.1) (hB1 v.1).1 1 1 (Ψ v) 1 (hΨ v)).2.1
  obtain ⟨hΦ', -⟩ := hFT γ hγ S (fun v => sF (localAdelicChar ℚ v.1) (Ψ v)) hsΨ
  have hci : IsOfFinOrder c⁻¹ := hc.inv
  have hδi : ∀ w : InfinitePlace ℚ, (c⁻¹.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1 := by
    intro w
    have h1 : (c⁻¹.infiniteComponent w (-1) : Circle) = (c.infiniteComponent w (-1))⁻¹ := rfl
    rw [h1, Circle.coe_inv, hδ w]
    cases δ <;> simp
  have hui : ∀ v ∉ S, IsUnramifiedChar (localChar c⁻¹ v) := by
    intro v hv
    have h1 : localChar c⁻¹ v = (localChar c v)⁻¹ := by
      ext a'
      rfl
    rw [h1]
    exact isUnramifiedChar_inv_iff.2 (hu v hv)
  obtain ⟨E, E', hd, hd', hEq, hfe, hnz⟩ := hG4 μ 𝓕 mK 𝓓 h0 _ hAut _ hΦ c hc
  have hsgn : (if δ then (-1 : ℂ) else 1) ≠ 0 := by cases δ <;> simp
  refine ⟨((C0 : ℝ) : ℂ) * C1 * (if δ then -1 else 1), E, E', ?_, hd, hd', ?_, hfe, ?_⟩
  · refine mul_ne_zero (mul_ne_zero ?_ hC1) hsgn
    exact_mod_cast hC0.1
  · intro s hs
    obtain ⟨h1, h2⟩ := hEq s hs
    constructor
    · rw [h1, hG5 μ 𝓕 mK 𝓓 C0 h0 hC0 _ _ hAut hPar _ hΦ c s hs,
        hE S hS c δ hc hδ hu x h hh Ψ hΨ s hs]
      ring
    · rw [h2, hsFA, hG5 μ 𝓕 mK 𝓓 C0 h0 hC0 _ _ hAut hPar _ hΦ' c⁻¹ s hs,
        hE S hS c⁻¹ δ hci hδi hui x h hh _ hsΨ s hs]
      ring
  · intro h1 hc1
    exact hG6 k N hk χ hχ f a hf ha ω φ hOm hL hP μ 𝓕 mK 𝓓 h0 S hS c hc hc1 hu x h hh (hnz h1)

end GlobalTheory.CompanionTheory.RankinSelberg

end
