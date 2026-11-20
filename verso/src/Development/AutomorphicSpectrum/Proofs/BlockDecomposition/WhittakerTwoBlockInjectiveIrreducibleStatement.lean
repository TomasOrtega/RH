import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockInjectiveIrreducible
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

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerTwoBlockInjectiveIrreducible.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.whittaker_two_block_injective_irreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → Nontrivial (X ⧸ whitKer ψ d J) →
    ∃ (S : IrrRep (GL (Fin (d 0)) k)) (f : S.ρ.IntertwiningMap (whit2 ψ d J)), Function.Injective f := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPair.WhitSub.exists_irr_sub | exact GlobalTheory.CompanionTheory.BZNuPair.WhitSub.exists_irr_sub | (intros; apply GlobalTheory.CompanionTheory.BZNuPair.WhitSub.exists_irr_sub <;> assumption)
