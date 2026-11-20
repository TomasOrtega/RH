import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateShiftCm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHodgeTateShiftCm.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.hodge_tate_shift_cm : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.FlatCM.PlaceShiftSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), HTShift Xo c := by
  first | exact @GlobalTheory.HTShiftPf.htShift | exact GlobalTheory.HTShiftPf.htShift | (intros; apply GlobalTheory.HTShiftPf.htShift <;> assumption)
