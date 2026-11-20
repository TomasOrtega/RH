import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularRowLatticeTriangularBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertZeta.RowSpan.spanEq_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FBlockTriangularRowLatticeTriangularBasis.lean&line=185#L185)
-/
theorem _root_.GlobalTheory.T.blockTriangular_row_lattice_triangular_basis : SpanEq := by
  first | exact @GlobalTheory.InertZeta.RowSpan.spanEq_holds | exact GlobalTheory.InertZeta.RowSpan.spanEq_holds | (intros; apply GlobalTheory.InertZeta.RowSpan.spanEq_holds <;> assumption)
