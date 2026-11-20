import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionCompIso
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Member.isEtaleCompletion_stalkClosedPointTo_comp_iso` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FEtaleCompletionCompIso.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.etaleCompletion_comp_iso : ∀ {R : Type} [CommRing R] [IsLocalRing R] {X Y : Scheme.{0}} (ξ : Spec (CommRingCat.of R) ⟶ X) (g : X ⟶ Y) [IsIso g], IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → IsEtaleCompletion (Scheme.stalkClosedPointTo (ξ ≫ g)).hom := by
  first | exact @GlobalTheory.Member.isEtaleCompletion_stalkClosedPointTo_comp_iso | exact GlobalTheory.Member.isEtaleCompletion_stalkClosedPointTo_comp_iso | (intros; apply GlobalTheory.Member.isEtaleCompletion_stalkClosedPointTo_comp_iso <;> assumption)
