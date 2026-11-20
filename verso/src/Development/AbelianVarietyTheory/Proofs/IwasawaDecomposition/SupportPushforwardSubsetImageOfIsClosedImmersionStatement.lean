import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubsetImageOfIsClosedImmersion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConeVanishing
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSupportPushforwardSubsetImageOfIsClosedImmersion.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.support_pushforward_subset_image : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsClosedImmersion g] (E : Y.Modules), support ((Scheme.Modules.pushforward g).obj E) ⊆ g '' support E := by
  first | exact @GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion | exact GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion | (intros; apply GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion <;> assumption)
