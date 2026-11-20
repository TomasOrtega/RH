import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrreducibleFibreFst
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsIrreducibleFibreFst.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.isIrreducible_preimage_fst_of_isSemiAbelian : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, IsIrreducible ((fst G G).left ⁻¹' {x}) := by
  first | exact @GlobalTheory.MoverFibre.isIrreducible_fibre_fst | exact GlobalTheory.MoverFibre.isIrreducible_fibre_fst | (intros; apply GlobalTheory.MoverFibre.isIrreducible_fibre_fst <;> assumption)
