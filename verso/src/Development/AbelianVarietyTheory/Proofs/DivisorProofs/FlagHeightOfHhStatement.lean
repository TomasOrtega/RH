import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagHeightOfHh
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagHtObj.flagHt_obj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagHeightOfHh.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.flag_height_of_hh : Hypotheses2 → ∀ (ι : Type) [Fintype ι] (N : ℕ), GlobalTheory.FlagZ.HasHh ι N ∧ ∀ hh, GlobalTheory.FlagZ.IsHh ι N hh → FlagHt ι N hh := by
  first | exact @GlobalTheory.FlagHtObj.flagHt_obj | exact GlobalTheory.FlagHtObj.flagHt_obj | (intros; apply GlobalTheory.FlagHtObj.flagHt_obj <;> assumption)
