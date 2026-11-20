import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLocalThetaLocallyConstant
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTwistedLocalThetaLocallyConstant.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.twisted_local_theta_locally_constant : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ g₀ : GL (Fin 2) (Qv v), L.plus g₀ → ∃ U ∈ nhds g₀, ∀ g ∈ U, ∀ (τ : (Qv v)ˣ) (ξ : K),
    (L.tw τ).val g ξ = (L.tw τ).val g₀ ξ := by
  first | exact @GlobalTheory.CompanionTheory.ThetaStab.val_stab | exact GlobalTheory.CompanionTheory.ThetaStab.val_stab | (intros; apply GlobalTheory.CompanionTheory.ThetaStab.val_stab <;> assumption)
