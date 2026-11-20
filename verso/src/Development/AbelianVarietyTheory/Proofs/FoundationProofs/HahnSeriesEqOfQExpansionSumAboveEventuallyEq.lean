import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasCommonExponentDenominatorRingOperationsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHasSumNeZeroStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Introduce `Ω _ ε C C' C'' φ φ' h h' hd hd' hs hs' heq`. Take `⟨hmono, hadd, -, hcongr⟩` from `GlobalTheory.T.hasQExpansionSumAbove_basic_properties Ω ε`. Use `set C₀ : ℝ := max C (max C' C'') with hC₀`. Establish `h1 : HS ε C₀ φ h` using `hmono C C₀ φ h (le_max_left _ _) hs`. Establish `h2 : HS ε C₀ φ' h'` using `hmono C' C₀ φ' h' (le_trans (le_max_left _ _) (le_max_right _ _)) hs'`.

Establish `h3 : HS ε C₀ (φ - φ') (h - h')` using `((hadd C₀ φ φ' h h') h1 h2).2`. Establish `h4 : HS ε C₀ (fun _ => (0 : ℂ)) (h - h')`. Use `hcongr C₀ (φ - φ') (fun _ => 0) (h - h') ?_ h3` and prove the remaining obligations. Introduce `z hz`. Establish `: C'' < z.im` using `lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hz`.

Simplify using `[heq z this]`. Establish `hdd : Den (h - h')` using `(((GlobalTheory.T.hasCommonExponentDenominator_ring_operations Ω).1 h h' hd hd').2.1)`. Assume the negation of the conclusion as `hne`. Establish `hne' : h - h' ≠ 0` using `sub_ne_zero.mpr hne`. Take `⟨D, hD⟩` from `GlobalTheory.T.exists_im_gt_ne_zero_of_hs Ω ε C₀ (fun _ => (0 : ℂ)) (h - h') hdd hne' h4`.

Conclude with `hD ((D + 1 : ℝ) * Complex.I) (by simp) rfl`.
-/
theorem hs_uniq : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C C' C'' : ℝ) (φ φ' : ℂ → ℂ) (h h' : HahnSeries ℚ Ω),
    Den h → Den h' → HS ε C φ h → HS ε C' φ' h' → (∀ z : ℂ, C'' < z.im → φ z = φ' z) → h = h' := by
  intro Ω _ ε C C' C'' φ φ' h h' hd hd' hs hs' heq
  obtain ⟨hmono, hadd, -, hcongr⟩ := GlobalTheory.T.hasQExpansionSumAbove_basic_properties Ω ε
  set C₀ : ℝ := max C (max C' C'') with hC₀
  have h1 : HS ε C₀ φ h := hmono C C₀ φ h (le_max_left _ _) hs
  have h2 : HS ε C₀ φ' h' := hmono C' C₀ φ' h' (le_trans (le_max_left _ _) (le_max_right _ _)) hs'
  have h3 : HS ε C₀ (φ - φ') (h - h') := ((hadd C₀ φ φ' h h') h1 h2).2
  have h4 : HS ε C₀ (fun _ => (0 : ℂ)) (h - h') := by
    refine hcongr C₀ (φ - φ') (fun _ => 0) (h - h') ?_ h3
    intro z hz
    have : C'' < z.im := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hz
    simp [heq z this]
  have hdd : Den (h - h') := (((GlobalTheory.T.hasCommonExponentDenominator_ring_operations Ω).1 h h' hd hd').2.1)
  by_contra hne
  have hne' : h - h' ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_im_gt_ne_zero_of_hs Ω ε C₀ (fun _ => (0 : ℂ)) (h - h') hdd hne' h4
  exact hD ((D + 1 : ℝ) * Complex.I) (by simp) rfl

end GlobalTheory.FN
