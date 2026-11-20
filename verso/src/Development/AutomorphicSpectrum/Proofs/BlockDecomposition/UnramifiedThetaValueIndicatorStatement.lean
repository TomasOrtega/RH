import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedThetaValueIndicator
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

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnramifiedThetaValueIndicator.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.unramified_theta_value_indicator : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → L.std → Unr c v → ∀ k ∈ integralGL (Qv v) 2, ∀ ξ : K,
    ((∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w]) → L.val k ξ = 1) ∧
    (¬ (∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w]) → L.val k ξ = 0) := by
  first | exact @GlobalTheory.CompanionTheory.StdSphVal.val_std | exact GlobalTheory.CompanionTheory.StdSphVal.val_std | (intros; apply GlobalTheory.CompanionTheory.StdSphVal.val_std <;> assumption)
