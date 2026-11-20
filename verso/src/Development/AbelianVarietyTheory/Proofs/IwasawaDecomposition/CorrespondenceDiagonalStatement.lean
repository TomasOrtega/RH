import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CorrespondenceDiagonal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocM.Diag.isDiag_diagCl` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCorrespondenceDiagonal.lean&line=323#L323)
-/
theorem _root_.GlobalTheory.T.correspondence_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), N2 Y → ∀ Z₁ Z₂ : Mdl Y i₀, GlobalTheory.LocM.Corr Z₁ Z₂ → IsDiag Z₁ Z₂ (diagCl Z₁ Z₂) := by
  first | exact @GlobalTheory.LocM.Diag.isDiag_diagCl | exact GlobalTheory.LocM.Diag.isDiag_diagCl | (intros; apply GlobalTheory.LocM.Diag.isDiag_diagCl <;> assumption)
