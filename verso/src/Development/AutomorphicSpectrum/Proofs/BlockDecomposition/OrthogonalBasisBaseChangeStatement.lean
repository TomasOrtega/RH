import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalBasisBaseChange
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SaGen.exists_rational_orth` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FOrthogonalBasisBaseChange.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.orthogonal_basis_base_change : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K], ∃ e : Fin M → Fin M → K ⊗[F] E, (∀ i j, i ≠ j → Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e j) = 0) ∧ (∀ i, IsUnit (Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e i))) ∧ IsUnit (Matrix.of e).det := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.exists_rational_orth | exact GlobalTheory.CompanionTheory.SaGen.exists_rational_orth | (intros; apply GlobalTheory.CompanionTheory.SaGen.exists_rational_orth <;> assumption)
