import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCharacterIntegralValue
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LFUDom.latchar1` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLatticeCharacterIntegralValue.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.lattice_character_integral_value : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ A : GL (Fin 2) F,
  (∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) →
  ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ =
    (((Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.latchar1 | exact GlobalTheory.CompanionTheory.LFUDom.latchar1 | (intros; apply GlobalTheory.CompanionTheory.LFUDom.latchar1 <;> assumption)
