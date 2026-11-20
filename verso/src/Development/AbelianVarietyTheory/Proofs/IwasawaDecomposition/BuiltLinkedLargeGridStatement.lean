import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BuiltLinkedLargeGrid
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.LiteralAutomorphy.exBL_NEa` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FBuiltLinkedLargeGrid.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.built_linked_large_grid : HypA → HypH → PrM → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (A : AtP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c)) → PositionMv (prmR N SExt.none Γ).s → ExBL KPx (IsBuiltE (prmR (NEa hL N A) SExt.none Γ).s) (IsGoodE (prmR (NEa hL N A) SExt.none Γ).s) (IsLinked (prmR (NEa hL N A) SExt.none Γ)) := by
  first | exact @GlobalTheory.Mem.LiteralAutomorphy.exBL_NEa | exact GlobalTheory.Mem.LiteralAutomorphy.exBL_NEa | (intros; apply GlobalTheory.Mem.LiteralAutomorphy.exBL_NEa <;> assumption)
