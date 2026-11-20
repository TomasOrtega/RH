import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinducedNerveAcyclic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCoinducedNerveAcyclic.lean&line=157#L157)
-/
theorem _root_.GlobalTheory.T.coinduced_nerve_acyclic : ∀ {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] (M : P → ModuleCat.{0} R) (n : ℕ),
    IsZero ((nerveCx.obj (coind M)).homology (n + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind | exact GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind | (intros; apply GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind <;> assumption)
