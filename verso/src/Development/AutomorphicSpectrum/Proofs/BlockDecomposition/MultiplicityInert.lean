import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers

noncomputable section

open NumberField IsDedekindDomain Polynomial
open GlobalTheory.BCT GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.MuInertPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem delta_indep {w : Pl E} (hw : ¬ IsSplitAt w) (μ μ' : (w.adicCompletion E)ˣ →* ℂˣ)
    (Q₁ Q₂ : (w.adicCompletion E)[X]) : delta w μ Q₁ Q₂ = delta w μ' Q₁ Q₂ := by
  simp only [delta, hw, if_false]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem match_indep {n a b : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (μ μ' : (w.adicCompletion E)ˣ →* ℂˣ)
    (f : UL n w → ℂ) (φ : GLw a w × GLw b w → ℂ) : Match n a b w μ f φ ↔ Match n a b w μ' f φ := by
  unfold Match
  simp only [delta_indep hw μ μ']

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem muInert : PositivityTheory.Rg.BcB.F.MLM.MuInert := by
  intro E _ _ _ n a b w hw μ μ' f φ
  exact match_indep hw μ μ' f φ

end GlobalTheory.CompanionTheory.MuInertPlace
