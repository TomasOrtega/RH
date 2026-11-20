import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductThetaLocallyConstantBounded
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ThetaFin.finitePart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FProductThetaLocallyConstantBounded.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.product_theta_locally_constant_bounded : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M →
  ∀ (Sv : Finset Pl) (m : Pl →₀ ℤ) (g₀ : G2), g₀ ∈ Gp M → ∃ (W : Set G2) (N : ℕ) (B : ℝ), W ∈ nhds g₀ ∧ N ≠ 0 ∧
    (∀ g ∈ W, g ∈ Gp M → ∀ u (ξ : K), ∏ᶠ v, (twM M Sv m u v).val (finAt v g) ξ = ∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ) ∧
    (∀ u, (∀ v : Sv, u v ∈ unQ v.1) → ∀ ξ : K, ‖∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ‖ ≤ B ∧
      (∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ ≠ 0 → ∃ a : 𝓞 K, (N : K) * ξ = a)) ∧
    ∀ ξ : K, Measurable (fun u => ∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaFin.finitePart | exact GlobalTheory.CompanionTheory.ThetaFin.finitePart | (intros; apply GlobalTheory.CompanionTheory.ThetaFin.finitePart <;> assumption)
