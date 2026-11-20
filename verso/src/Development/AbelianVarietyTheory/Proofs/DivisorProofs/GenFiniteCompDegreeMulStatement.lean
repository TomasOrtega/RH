import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFiniteCompDegreeMul
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGenFiniteCompDegreeMul.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.gen_finite_comp_degree_mul : ∀ (T'' T' T : Scheme.{0}) [IsIntegral T''] [IsIntegral T'] [IsIntegral T] (ρ' : T'' ⟶ T') (ρ : T' ⟶ T) (d' d : ℕ), IsGenFinite ρ' d' → IsGenFinite ρ d → IsGenFinite (ρ' ≫ ρ) (d' * d) := by
  first | exact @GlobalTheory.GenFiniteComp.isGenFinite_comp | exact GlobalTheory.GenFiniteComp.isGenFinite_comp | (intros; apply GlobalTheory.GenFiniteComp.isGenFinite_comp <;> assumption)
