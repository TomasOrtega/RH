import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackOfTranslatedStandardLatticeMulIntegralGL
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPullbackOfTranslatedStandardLatticeMulIntegralGL.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.pullbackOfTranslatedStandardLattice_mul_integralGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g k : GLw n w), k ∈ GlobalTheory.LFun.KGL w n → pullLat w B ψ (g * k) = pullLat w B ψ g := by
  first | exact @GlobalTheory.KapOrb.pullLat_mul_of_mem_KGL | exact GlobalTheory.KapOrb.pullLat_mul_of_mem_KGL | (intros; apply GlobalTheory.KapOrb.pullLat_mul_of_mem_KGL <;> assumption)
