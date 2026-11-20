import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
open Filter Topology Set Metric MeasureTheory GlobalTheory.ChernReg
open scoped ContDiff

/- English proof (translation)
Introduce `d U Kc q hK hKU hc hhom hpos`. Establish `h0 : ∀ z ∈ U, q z 0 = 0` using `fun z hz => by simpa using hhom z hz 0 0`. Establish `hu : ∀ ξ : Fin d → ℂ, ξ ≠ 0 → ‖ξ‖⁻¹ • ξ ∈ sphere (0 : Fin d → ℂ) 1`. Introduce `ξ hξ`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)]`.

Establish `key : ∀ z ∈ U, ∀ ξ : Fin d → ℂ, ξ ≠ 0 → q z ξ = ‖ξ‖ ^ 2 * q z (‖ξ‖⁻¹ • ξ)`. Introduce `z hz ξ hξ`. Rewrite using `[← hhom z hz, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hξ), one_smul]`. Establish `hS : IsCompact (Kc ×ˢ sphere (0 : Fin d → ℂ) 1)` using `hK.prod (isCompact_sphere 0 1)`. Break down `(Kc ×ˢ sphere (0 : Fin d → ℂ) 1).eq_empty_or_nonempty with hE | hne` into its components or cases.

Use `⟨1, one_pos, fun z hz ξ => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hξ : ξ = 0`. Substitute `hξ` using the available equality. Simplify using `[h0 z (hKU hz)]`. It suffices to derive a contradiction.

Establish `: (z, ‖ξ‖⁻¹ • ξ) ∈ Kc ×ˢ sphere (0 : Fin d → ℂ) 1` using `⟨hz, hu ξ hξ⟩`. Rewrite `this` using `[hE]`. Conclude with `this`. Take `⟨p, hp, hmin⟩` from `hS.exists_isMinOn hne (hc.mono (Set.prod_mono hKU (Set.subset_univ _)))`. Establish `hp2 : p.2 ≠ 0`.

Introduce `h`. Use `hp.2` as an intermediate fact. Rewrite `this` using `[h, mem_sphere_zero_iff_norm, norm_zero]`. Conclude with `zero_ne_one this`. Use `⟨q p.1 p.2, hpos _ (hKU hp.1) _ hp2, fun z hz ξ => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hξ : ξ = 0`. Substitute `hξ` using the available equality. Simplify using `[h0 z (hKU hz)]`. Establish `hle : q p.1 p.2 ≤ q z (‖ξ‖⁻¹ • ξ)` using `isMinOn_iff.mp hmin (z, ‖ξ‖⁻¹ • ξ) ⟨hz, hu ξ hξ⟩`. Rewrite using `[key z (hKU hz) ξ hξ, mul_comm]`.

Conclude with `mul_le_mul_of_nonneg_left hle (by positivity)`.
-/
theorem GlobalTheory.uniformLowerBound_quadraticLike : ∀ (d : ℕ) (U Kc : Set (Fin d → ℂ)) (q : (Fin d → ℂ) → (Fin d → ℂ) → ℝ), IsCompact Kc → Kc ⊆ U → ContinuousOn (fun p : (Fin d → ℂ) × (Fin d → ℂ) => q p.1 p.2) (U ×ˢ Set.univ) → (∀ z ∈ U, ∀ (t : ℝ) ξ, q z (t • ξ) = t ^ 2 * q z ξ) → (∀ z ∈ U, ∀ ξ, ξ ≠ 0 → 0 < q z ξ) → ∃ m : ℝ, 0 < m ∧ ∀ z ∈ Kc, ∀ ξ, m * ‖ξ‖ ^ 2 ≤ q z ξ := by
  intro d U Kc q hK hKU hc hhom hpos
  have h0 : ∀ z ∈ U, q z 0 = 0 := fun z hz => by simpa using hhom z hz 0 0
  have hu : ∀ ξ : Fin d → ℂ, ξ ≠ 0 → ‖ξ‖⁻¹ • ξ ∈ sphere (0 : Fin d → ℂ) 1 := by
    intro ξ hξ
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)]
  have key : ∀ z ∈ U, ∀ ξ : Fin d → ℂ, ξ ≠ 0 → q z ξ = ‖ξ‖ ^ 2 * q z (‖ξ‖⁻¹ • ξ) := by
    intro z hz ξ hξ
    rw [← hhom z hz, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hξ), one_smul]
  have hS : IsCompact (Kc ×ˢ sphere (0 : Fin d → ℂ) 1) := hK.prod (isCompact_sphere 0 1)
  rcases (Kc ×ˢ sphere (0 : Fin d → ℂ) 1).eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, fun z hz ξ => ?_⟩
    by_cases hξ : ξ = 0
    · subst hξ; simp [h0 z (hKU hz)]
    · exfalso
      have : (z, ‖ξ‖⁻¹ • ξ) ∈ Kc ×ˢ sphere (0 : Fin d → ℂ) 1 := ⟨hz, hu ξ hξ⟩
      rw [hE] at this; exact this
  · obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hne
      (hc.mono (Set.prod_mono hKU (Set.subset_univ _)))
    have hp2 : p.2 ≠ 0 := by
      intro h
      have := hp.2
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at this
      exact zero_ne_one this
    refine ⟨q p.1 p.2, hpos _ (hKU hp.1) _ hp2, fun z hz ξ => ?_⟩
    by_cases hξ : ξ = 0
    · subst hξ; simp [h0 z (hKU hz)]
    · have hle : q p.1 p.2 ≤ q z (‖ξ‖⁻¹ • ξ) :=
        isMinOn_iff.mp hmin (z, ‖ξ‖⁻¹ • ξ) ⟨hz, hu ξ hξ⟩
      rw [key z (hKU hz) ξ hξ, mul_comm]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
