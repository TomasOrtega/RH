import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagClosure
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsFlagClosure.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.exists_flag_closure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z : Mdl Y i₀) (s : Finset (Step Y i₀)), (∀ t ∈ s, ∃ f, IsMap Z t.B f) → ∃ Z', IsFlagCl Z s Z' := by
  first | exact @GlobalTheory.GrCl.exists_isFlagCl | exact GlobalTheory.GrCl.exists_isFlagCl | (intros; apply GlobalTheory.GrCl.exists_isFlagCl <;> assumption)
