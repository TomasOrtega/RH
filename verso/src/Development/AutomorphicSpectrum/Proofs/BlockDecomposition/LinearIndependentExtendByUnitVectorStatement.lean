import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentExtendByUnitVector
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLinearIndependentExtendByUnitVector.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.linearIndependent_extend_by_unit_vector : ∀ (K : Type) [CommRing K] (M n : ℕ) (α : K), IsUnit α → ∀ (c : Fin n → K) (X : Fin n → Fin M → K), LinearIndependent K (vec α c X : Fin (n + 1) → Fin (M + 1) → K) ↔ LinearIndependent K X := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff <;> assumption)
