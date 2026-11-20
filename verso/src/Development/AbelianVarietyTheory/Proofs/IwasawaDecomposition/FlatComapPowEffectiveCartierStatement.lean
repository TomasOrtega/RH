import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatComapPowEffectiveCartier
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFlatComapPowEffectiveCartier.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.flat_comap_pow_effective_cartier : ∀ (X Y : Scheme.{0}) (D : GlobalTheory.EffCartierData X) (g : Y ⟶ X), Flat g → ∀ n : ℕ, FinalTheorems.EffCartier ((D.idealSheaf ^ n).comap g) := by
  first | exact @GlobalTheory.effCartier_comap_pow_idealSheaf_of_flat | exact GlobalTheory.effCartier_comap_pow_idealSheaf_of_flat | (intros; apply GlobalTheory.effCartier_comap_pow_idealSheaf_of_flat <;> assumption)
