import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusRowRepFactorization
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LFUDom.torusPow_mul_rowRep_inv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTorusRowRepFactorization.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.torus_row_rep_factorization : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a b : ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]),
  torusPow F 2 ![a, b] * (rowRep i j c)⁻¹ =
    Ad3.uni2 (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ (a - b - i)) * torusPow F 2 ![a - i, b - j] := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.torusPow_mul_rowRep_inv | exact GlobalTheory.CompanionTheory.LFUDom.torusPow_mul_rowRep_inv | (intros; apply GlobalTheory.CompanionTheory.LFUDom.torusPow_mul_rowRep_inv <;> assumption)
