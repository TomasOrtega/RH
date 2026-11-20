import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryZetaTermFunctionalEquation
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FBoundaryZetaTermFunctionalEquation.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.boundary_zeta_term_functional_equation : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G1a → Set0 μ 𝓕 mK 𝓓 → Aut H → IsOfFinOrder c → ∀ s : ℂ,
    GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c⁻¹ (-s) = 2 ^ (-s) * GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s := by
  first | exact @GlobalTheory.CompanionTheory.RSZeta.Bd_reflect | exact GlobalTheory.CompanionTheory.RSZeta.Bd_reflect | (intros; apply GlobalTheory.CompanionTheory.RSZeta.Bd_reflect <;> assumption)
