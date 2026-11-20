import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerUnipotentEquivariantHolds
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerUnipotentEquivariantHolds.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.whittaker_unipotent_equivariant_holds : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ (ν : Fˣ →* ℂˣ) (y : F) (g : GL (Fin 2) F),
  Ad3.LFS.s2 ψ ν (Ad3.uni2 y * g) = ((ψ y : Circle) : ℂ) * Ad3.LFS.s2 ψ ν g := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.whittaker_unipotent_left_equivariant | exact GlobalTheory.CompanionTheory.LFUDom.whittaker_unipotent_left_equivariant | (intros; apply GlobalTheory.CompanionTheory.LFUDom.whittaker_unipotent_left_equivariant <;> assumption)
