import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArakelovTopUnique
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TrueGeo.ArUniq.isArTop_unique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FArakelovTopUnique.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.arakelov_top_unique : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (t t' : ℝ), A.IsArTop t → A.IsArTop t' → t = t' := by
  first | exact @GlobalTheory.TrueGeo.ArUniq.isArTop_unique | exact GlobalTheory.TrueGeo.ArUniq.isArTop_unique | (intros; apply GlobalTheory.TrueGeo.ArUniq.isArTop_unique <;> assumption)
