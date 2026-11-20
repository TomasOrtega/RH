import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocChar.weil_char_split` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FWeilCharacterSplitPlaceExistsContinuousNontrivia.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∃ ψk : AddChar k Circle, p.IsChar ψ ψk) ∧ (∀ ψk : AddChar k Circle, p.IsChar ψ ψk → Continuous ψk ∧ ψk ≠ 1) ∧ p.xi ≠ 0 ∧ (∀ x y, p.ι (x * y) = p.ι x * p.ι y) ∧ ∀ χ : (AE D)ˣ →* Circle, ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ := by
  first | exact @GlobalTheory.LocChar.weil_char_split | exact GlobalTheory.LocChar.weil_char_split | (intros; apply GlobalTheory.LocChar.weil_char_split <;> assumption)
