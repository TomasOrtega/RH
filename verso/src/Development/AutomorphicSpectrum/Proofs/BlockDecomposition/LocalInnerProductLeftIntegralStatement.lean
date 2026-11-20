import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInnerProductLeftIntegral
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LFUDom.inn_Φ0_integral_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalInnerProductLeftIntegral.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.local_inner_product_left_integral : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (κ : GL (Fin 2) F), κ ∈ integralGL F 2 → ∀ (h : GL (Fin 2) F) (g : GL (Fin 3) F),
  Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) (κ * h) g = Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h g := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.inn_Φ0_integral_mul | exact GlobalTheory.CompanionTheory.LFUDom.inn_Φ0_integral_mul | (intros; apply GlobalTheory.CompanionTheory.LFUDom.inn_Φ0_integral_mul <;> assumption)
