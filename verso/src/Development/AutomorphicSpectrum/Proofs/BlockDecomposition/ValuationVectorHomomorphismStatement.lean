import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationVectorHomomorphism
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceEmbeddingPropertiesStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FValuationVectorHomomorphism.lean&line=159#L159)
-/
theorem _root_.GlobalTheory.T.valuation_vector_homomorphism : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
  ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M →
    (∀ (κ : Kˣ) (v : Pl), vK M κ v = ord ((k1 (M v) κ : (Qv v)ˣ) : Qv v)) ∧ (∀ κ : Kˣ, vK M κ ∈ Tm M) ∧
      ∀ a b : Kˣ, vK M (a * b) = vK M a + vK M b := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.VKMap.vK_valuation_map | exact GlobalTheory.CompanionTheory.FexTheta.VKMap.vK_valuation_map | (intros; apply GlobalTheory.CompanionTheory.FexTheta.VKMap.vK_valuation_map <;> assumption)
