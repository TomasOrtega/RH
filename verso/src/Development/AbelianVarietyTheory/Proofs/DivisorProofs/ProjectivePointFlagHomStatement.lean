import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectivePointFlagHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagQ.exists_isHom_toPt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProjectivePointFlagHom.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.projective_point_flag_hom : ∀ (Y : GlobalTheory.ProjVar.Var ℚ), ∃ φ : (GlobalTheory.ProjVar.proj ℚ 0).Fn →ₐ[ℚ] Y.Fn, (GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)).IsHom (GlobalTheory.FlagBundle.ratOf Y) φ (GlobalTheory.FlagQ.toPt Y) := by
  first | exact @GlobalTheory.FlagQ.exists_isHom_toPt | exact GlobalTheory.FlagQ.exists_isHom_toPt | (intros; apply GlobalTheory.FlagQ.exists_isHom_toPt <;> assumption)
