import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombPowIsometric
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCombPowIsometric.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.comb_pow_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (L : HermLB p) (m : ℕ), (ArInt.comb (fun _ : Unit => L) (fun _ => (m : ℤ))).Isometric (L.pow m) := by
  first | exact @GlobalTheory.ArInt.isometric_comb_unit_pow | exact GlobalTheory.ArInt.isometric_comb_unit_pow | (intros; apply GlobalTheory.ArInt.isometric_comb_unit_pow <;> assumption)
