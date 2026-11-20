import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockSubquotientTensor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitImgMono
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfIrreducibleImageStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientOfExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSubquotientEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerTwoBlockSubquotientTensor.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.whittaker_two_block_subquotient_tensor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → ∀ S : IrrRep (GL (Fin (d 0)) k),
    IsSubquotient S.ρ (whit2 ψ d J) → ∃ s : ∀ a, IrrRep (GL (Fin (d a)) k),
      IsSubquotient (piTensor fun a => (s a).ρ) J ∧ Nonempty ((s 0).ρ.Equiv S.ρ) := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPair.exists_constituent_of_whit2 | exact GlobalTheory.CompanionTheory.BZNuPair.exists_constituent_of_whit2 | (intros; apply GlobalTheory.CompanionTheory.BZNuPair.exists_constituent_of_whit2 <;> assumption)
