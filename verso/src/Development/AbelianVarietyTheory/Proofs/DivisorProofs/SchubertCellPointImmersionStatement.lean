import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellPointImmersion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagZ.isImmersion_plPt_cellGL` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchubertCellPointImmersion.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.schubert_cell_point_immersion : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)) (w : ι → Equiv.Perm (Fin N)), IsImmersion (plPt a l (cellGL a l w)) := by
  first | exact @GlobalTheory.FlagZ.isImmersion_plPt_cellGL | exact GlobalTheory.FlagZ.isImmersion_plPt_cellGL | (intros; apply GlobalTheory.FlagZ.isImmersion_plPt_cellGL <;> assumption)
