import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableIffOfLeOfLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthLocalizedModuleEqZeroOfNotAnnihilatorLe

namespace GlobalTheory

open Formalism.MainNotions.IntegralHeckeForms

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W]

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in

/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.relLength_ne_top_iff]`. Take `⟨hAfg, hAV, -⟩` from `hA`. Take `⟨-, -, hBV⟩` from `hB`. Establish `: Module.Finite O A` using `Module.Finite.iff_fg.mpr hAfg`. Apply `_root_.GlobalTheory.isFiniteLength_of_isTorsion` to reduce the goal to its premises.

Introduce `x`. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H a`. Take `⟨c, hc, hcB⟩` from `hBV a (hAV a.2)`. Use `⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `hcB`.
-/
theorem _root_.GlobalTheory.relLength_ne_top_of_isLatIn {V A B : Submodule O W} (hA : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn A V)
    (hB : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn B V) : _root_.GlobalTheory.relLength A B ≠ ⊤ := by
  rw [_root_.GlobalTheory.relLength_ne_top_iff]
  obtain ⟨hAfg, hAV, -⟩ := hA
  obtain ⟨-, -, hBV⟩ := hB
  have : Module.Finite O A := Module.Finite.iff_fg.mpr hAfg
  apply _root_.GlobalTheory.isFiniteLength_of_isTorsion
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    obtain ⟨c, hc, hcB⟩ := hBV a (hAV a.2)
    refine ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hcB

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨_root_.GlobalTheory.relLength_ne_top_of_isLatIn hA hB, _root_.GlobalTheory.relLength_ne_top_of_isLatIn hB hA⟩`.
-/
theorem _root_.GlobalTheory.lengthCommensurable_of_isLatIn {V A B : Submodule O W} (hA : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn A V)
    (hB : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn B V) : _root_.GlobalTheory.LengthCommensurable A B :=
  ⟨_root_.GlobalTheory.relLength_ne_top_of_isLatIn hA hB,
    _root_.GlobalTheory.relLength_ne_top_of_isLatIn hB hA⟩

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in

/- English proof (translation)
Unfold `_root_.Formalism.MainNotions.IntegralHeckeForms.sIdx _root_.Formalism.MainNotions.IntegralHeckeForms.lenR _root_.GlobalTheory.signedLength`. Rewrite using `[← _root_.GlobalTheory.relLength_eq_length_quotient_comap, ← _root_.GlobalTheory.relLength_eq_length_quotient_comap]`. Use `push_cast`. Rewrite using `[sub_div]`.
-/
theorem _root_.GlobalTheory.sIdx_eq_signedLength_div (l : ℕ) (A B : Submodule O W) :
    _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l A B = (_root_.GlobalTheory.signedLength A B : ℝ) /
      ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℝ) := by
  unfold _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx _root_.Formalism.MainNotions.IntegralHeckeForms.lenR _root_.GlobalTheory.signedLength
  rw [← _root_.GlobalTheory.relLength_eq_length_quotient_comap,
    ← _root_.GlobalTheory.relLength_eq_length_quotient_comap]
  push_cast
  rw [sub_div]

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in

/- English proof (translation)
Introduce `O _ _ _ W _ _ l V L₁ L₂ L₃ h₁ h₂ h₃`. Establish `hadd : _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃ = _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ + _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₂ L₃`. Simplify using `only [_root_.GlobalTheory.sIdx_eq_signedLength_div]`. Rewrite using `[(_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₁ h₂).signedLength_eq_add (_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₂ h₃)]`. Use `push_cast`.

Rewrite using `[add_div]`. Use `⟨hadd, fun hle => ?_⟩` and prove the remaining obligations. Rewrite using `[hadd, le_add_iff_nonneg_right, _root_.GlobalTheory.sIdx_eq_signedLength_div]`. Apply `div_nonneg _ (Nat.cast_nonneg _)` to reduce the goal to its premises. Conclude with `(_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₂ h₃).signedLength_nonneg hle` after adjusting the coercions.
-/
theorem _root_.GlobalTheory.sIdx_add_and_mono :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (W : Type)
      [AddCommGroup W] [Module O W] (l : ℕ) (V L₁ L₂ L₃ : Submodule O W),
      _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₁ V → _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₂ V → _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₃ V →
      _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃ = _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ + _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₂ L₃ ∧
        (L₃ ≤ L₂ → _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ ≤ _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃) := by
  intro O _ _ _ W _ _ l V L₁ L₂ L₃ h₁ h₂ h₃
  have hadd : _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃ = _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ + _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₂ L₃ := by
    simp only [_root_.GlobalTheory.sIdx_eq_signedLength_div]
    rw [(_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₁ h₂).signedLength_eq_add
      (_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₂ h₃)]
    push_cast
    rw [add_div]
  refine ⟨hadd, fun hle => ?_⟩
  rw [hadd, le_add_iff_nonneg_right, _root_.GlobalTheory.sIdx_eq_signedLength_div]
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact_mod_cast (_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₂ h₃).signedLength_nonneg hle

end GlobalTheory
