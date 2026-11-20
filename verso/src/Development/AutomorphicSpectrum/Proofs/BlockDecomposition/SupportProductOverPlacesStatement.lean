import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportProductOverPlaces
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PlaneSA.ProdSupp.suppAt_subset_of_places` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSupportProductOverPlaces.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.support_product_over_places : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (N : Set (Q d β (AF F))), (1 : Q d β (AF F)) ∈ N →
  (∀ x ∈ N, ∀ y ∈ N, x * y ∈ N) → (∀ u : Pl F, SuppAt d β {u} ⊆ N) →
  ∀ T : Finset (Pl F), SuppAt d β (T : Set (Pl F)) ⊆ N := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.ProdSupp.suppAt_subset_of_places | exact GlobalTheory.CompanionTheory.PlaneSA.ProdSupp.suppAt_subset_of_places | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.ProdSupp.suppAt_subset_of_places <;> assumption)
