import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationTransferIsPullDegId
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUniformisationTransferIsPullDegId.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.uniformisation_transfer_isPullDeg_id : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I), Nonempty (IsPullDeg (RingHom.id R) D.toPre D'.toPre) → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∀ U' : Unif I D' A G, ∃ U : Unif I D A G, U.LG = U'.LG ∧ U.gen = U'.gen) ∧ ∀ U : Unif I D A G, ∃ U' : Unif I D' A G, U'.LG = U.LG ∧ U'.gen = U.gen := by
  first | exact @GlobalTheory.Mum.UnifMove.unif_move | exact GlobalTheory.Mum.UnifMove.unif_move | (intros; apply GlobalTheory.Mum.UnifMove.unif_move <;> assumption)
