import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagZ.exists_mem_range_cell` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagPointInSomeCell.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.flag_point_in_some_cell : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)) (x : Part a l), ∃ w : ι → Equiv.Perm (Fin N), x ∈ Set.range (cell a l w) := by
  first | exact @GlobalTheory.FlagZ.exists_mem_range_cell | exact GlobalTheory.FlagZ.exists_mem_range_cell | (intros; apply GlobalTheory.FlagZ.exists_mem_range_cell <;> assumption)
