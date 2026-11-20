import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsOneTraitWeilPairingBijection
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabTors
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorsionLabelsOneTraitWeilPairingBijection.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.torsion_labels_one_trait_weil_pairing_bijection : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ k : ℕ, 1 ≤ k → LabTors D.toPre A k (lab k) := by
  first | exact @GlobalTheory.Mum.LabTorsTrait.labTors_of_oneTrait | exact GlobalTheory.Mum.LabTorsTrait.labTors_of_oneTrait | (intros; apply GlobalTheory.Mum.LabTorsTrait.labTors_of_oneTrait <;> assumption)
