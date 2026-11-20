import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSubmoduleChainBounded
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaGLRank.boundedChains_thetaGL` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FThetaSubmoduleChainBounded.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.theta_submodule_chain_bounded : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} →
    ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, GlobalTheory.ThetaGLSub.IsSub χ (N i)) → r ≤ L := by
  first | exact @GlobalTheory.ThetaGLRank.boundedChains_thetaGL | exact GlobalTheory.ThetaGLRank.boundedChains_thetaGL | (intros; apply GlobalTheory.ThetaGLRank.boundedChains_thetaGL <;> assumption)
