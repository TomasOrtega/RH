import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeMulEqMulLeftImage
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPullbackLatticeMulEqMulLeftImage.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.pullbackLattice_mul_eq_mulLeftImage : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (h g : GLw n w) (a : B.Aˣ), (∀ y, ψ ((a : B.A) * y) = h.val *ᵥ ψ y) → pullLat w B ψ (h * g) = GlobalTheory.UnitLemma.mulLat K.O (a : B.A) (pullLat w B ψ g) := by
  first | exact @GlobalTheory.KapOrb.pullLat_mul_eq_mulLat | exact GlobalTheory.KapOrb.pullLat_mul_eq_mulLat | (intros; apply GlobalTheory.KapOrb.pullLat_mul_eq_mulLat <;> assumption)
