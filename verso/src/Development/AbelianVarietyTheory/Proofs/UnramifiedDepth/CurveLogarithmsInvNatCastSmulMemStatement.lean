import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CurveLogarithmsInvNatCastSmulMem
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RowLaw.cv_inv_natCast_smul_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FCurveLogarithmsInvNatCastSmulMem.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.curveLogarithms_inv_natCast_smul_mem : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (N : ℕ), V.v (N : C) = 0 → ∀ a ∈ Cv X V g, (N : C)⁻¹ • a ∈ Cv X V g := by
  first | exact @GlobalTheory.RowLaw.cv_inv_natCast_smul_mem | exact GlobalTheory.RowLaw.cv_inv_natCast_smul_mem | (intros; apply GlobalTheory.RowLaw.cv_inv_natCast_smul_mem <;> assumption)
