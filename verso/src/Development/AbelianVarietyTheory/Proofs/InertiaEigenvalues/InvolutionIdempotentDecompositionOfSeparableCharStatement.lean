import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutionIdempotentDecompositionOfSeparableChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FInvolutionIdempotentDecompositionOfSeparableChar.lean&line=200#L200)
-/
theorem _root_.GlobalTheory.T.involutionIdempotentDecomposition_of_separable_charpoly : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ (ι : Type) (_ : Fintype ι) (e : ι → B.A) (S : Finset ι), IsPre B e S := by
  first | exact @GlobalTheory.UnitLemma.Desc.isPre_of_separable | exact GlobalTheory.UnitLemma.Desc.isPre_of_separable | (intros; apply GlobalTheory.UnitLemma.Desc.isPre_of_separable <;> assumption)
