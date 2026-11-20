import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasCommonExponentDenominatorRingOperationsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesInvConvergesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveMulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesEqOfQExpansionSumAboveEventuallyEqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneEqZeroOfVanishAboveImStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNExp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem up_add (f f' : ℍ → ℂ) : up (f + f') = up f + up f' := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem up_sub (f f' : ℍ → ℂ) : up (f - f') = up f - up f' := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem up_mul (f f' : ℍ → ℂ) : up (f * f') = up f * up f' := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem up_inv (f : ℍ → ℂ) : up f⁻¹ = (up f)⁻¹ := rfl

/- English proof (translation)
Introduce `Ω _ ε`. Take `⟨hden, hsing⟩` from `GlobalTheory.T.hasCommonExponentDenominator_ring_operations Ω`. Take `⟨hmono, hadd, hmon, hcongr⟩` from `GlobalTheory.T.hasQExpansionSumAbove_basic_properties Ω ε`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `f f' h h' ⟨hd, C, hC⟩ ⟨hd', C', hC'⟩`.

Take `⟨d1, d2, d3⟩` from `hden h h' hd hd'`. Establish `e1 : HS ε (max C C') (up f) h` using `hmono _ _ _ _ (le_max_left _ _) hC`. Establish `e2 : HS ε (max C C') (up f') h'` using `hmono _ _ _ _ (le_max_right _ _) hC'`. Take `⟨s1, s2⟩` from `hadd _ _ _ _ _ e1 e2`. Use `⟨⟨d1, max C C', ?_⟩, ⟨d2, max C C', ?_⟩, ⟨d3, max C C', ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[up_add]`. Conclude with `s1`. Rewrite using `[up_sub]`. Conclude with `s2`. Rewrite using `[up_mul]`.

Conclude with `GlobalTheory.T.hasQExpansionSumAbove_mul Ω ε _ _ _ _ _ e1 e2`. Introduce and unpack `f h h' ⟨hd, C, hC⟩ ⟨hd', C', hC'⟩`. Conclude with `GlobalTheory.T.hahnSeries_eq_of_qExpansionSumAbove_eventually_eq Ω ε C C' 0 (up f) (up f) h h' hd hd' hC hC' (fun _ _ => rfl)`. Introduce `c`. Establish `hC : HahnSeries.C c = (HahnSeries.single (0 : ℚ) c : HahnSeries ℚ Ω)` using `HahnSeries.C_apply c`.

Rewrite using `[hC]`. Use `⟨hsing 0 c, 0, ?_⟩` and prove the remaining obligations. Use `hcongr 0 _ _ _ ?_ (hmon 0 0 c)` and prove the remaining obligations. Introduce `z _`. Simplify using `[up]`.

Introduce and unpack `f hf ⟨_, C, hC⟩`. Apply `GlobalTheory.T.upperHalfPlane_eq_zero_of_vanish_above_im f C hf` to reduce the goal to its premises. Introduce `τ hτ`. Establish `hz` using `hC (τ : ℂ) (by simpa using hτ)`. Establish `h0 : (fun r : ℚ => ε ((0 : HahnSeries ℚ Ω).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (τ : ℂ))) = fun _ => 0`.

Use function extensionality and compare the values at `r`. Simplify using the standard rewrite rules. Rewrite `hz` using `[h0]`. Use `hz.unique hasSum_zero` as an intermediate fact. Simplify `this` using `[up, UpperHalfPlane.ofComplex_apply]`.

Introduce and unpack `f h hne ⟨hd, C, hC⟩`. Take `⟨d, C', hC'⟩` from `GlobalTheory.T.den_inv_and_hs_inv_of_hs Ω ε C (up f) h hd hne hC`. Conclude with `⟨d, C', by rw [up_inv]; exact hC'⟩`.
-/
theorem exp_props : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), (∀ (f f' : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), IsExp ε f h → IsExp ε f' h' → IsExp ε (f + f') (h + h') ∧ IsExp ε (f - f') (h - h') ∧ IsExp ε (f * f') (h * h')) ∧ (∀ (f : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), IsExp ε f h → IsExp ε f h' → h = h') ∧ (∀ c : Ω, IsExp ε (fun _ => ε c) (HahnSeries.C c)) ∧ (∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → IsExp ε f (0 : HahnSeries ℚ Ω) → f = 0) ∧ ∀ (f : ℍ → ℂ) (h : HahnSeries ℚ Ω), h ≠ 0 → IsExp ε f h → IsExp ε f⁻¹ h⁻¹ := by
  intro Ω _ ε
  obtain ⟨hden, hsing⟩ := GlobalTheory.T.hasCommonExponentDenominator_ring_operations Ω
  obtain ⟨hmono, hadd, hmon, hcongr⟩ := GlobalTheory.T.hasQExpansionSumAbove_basic_properties Ω ε
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro f f' h h' ⟨hd, C, hC⟩ ⟨hd', C', hC'⟩
    obtain ⟨d1, d2, d3⟩ := hden h h' hd hd'
    have e1 : HS ε (max C C') (up f) h := hmono _ _ _ _ (le_max_left _ _) hC
    have e2 : HS ε (max C C') (up f') h' := hmono _ _ _ _ (le_max_right _ _) hC'
    obtain ⟨s1, s2⟩ := hadd _ _ _ _ _ e1 e2
    refine ⟨⟨d1, max C C', ?_⟩, ⟨d2, max C C', ?_⟩, ⟨d3, max C C', ?_⟩⟩
    · rw [up_add]; exact s1
    · rw [up_sub]; exact s2
    · rw [up_mul]; exact GlobalTheory.T.hasQExpansionSumAbove_mul Ω ε _ _ _ _ _ e1 e2
  · rintro f h h' ⟨hd, C, hC⟩ ⟨hd', C', hC'⟩
    exact GlobalTheory.T.hahnSeries_eq_of_qExpansionSumAbove_eventually_eq Ω ε C C' 0 (up f) (up f) h h' hd hd' hC hC' (fun _ _ => rfl)
  · intro c
    have hC : HahnSeries.C c = (HahnSeries.single (0 : ℚ) c : HahnSeries ℚ Ω) := HahnSeries.C_apply c
    rw [hC]
    refine ⟨hsing 0 c, 0, ?_⟩
    refine hcongr 0 _ _ _ ?_ (hmon 0 0 c)
    intro z _
    simp [up]
  · rintro f hf ⟨_, C, hC⟩
    apply GlobalTheory.T.upperHalfPlane_eq_zero_of_vanish_above_im f C hf
    intro τ hτ
    have hz := hC (τ : ℂ) (by simpa using hτ)
    have h0 : (fun r : ℚ => ε ((0 : HahnSeries ℚ Ω).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (τ : ℂ))) = fun _ => 0 := by
      funext r; simp
    rw [h0] at hz
    have := hz.unique hasSum_zero
    simpa [up, UpperHalfPlane.ofComplex_apply] using this
  · rintro f h hne ⟨hd, C, hC⟩
    obtain ⟨d, C', hC'⟩ := GlobalTheory.T.den_inv_and_hs_inv_of_hs Ω ε C (up f) h hd hne hC
    exact ⟨d, C', by rw [up_inv]; exact hC'⟩

end GlobalTheory.FNExp
