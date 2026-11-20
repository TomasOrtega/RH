import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLiftOfReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
open GlobalTheory.RingChain
open scoped TensorProduct Pointwise ChangeOfRings
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProjectiveLiftOfReduction.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.projective_lift_of_reduction : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (a : A) (g : R), algebraMap A R a = g → ModIso R a → ∀ (s : R →+* R ⧸ Ideal.span {g}) (M M' P : Type) [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P] [Module.Projective R P] (Φ : M →ₛₗ[algebraMap A R] M'), Function.Bijective Φ → ∀ (lam : P →+ M') (e : (ModuleCat.extendScalars s).obj (ModuleCat.of R P) ≃+ M'), (∀ (r : R) (y : P), e ((Ideal.Quotient.mk _ r : R ⧸ Ideal.span {g}) ⊗ₜ[R, s] y) = r • lam y) → Module.Projective (A ⧸ Ideal.span {a}) ((A ⧸ Ideal.span {a}) ⊗[A] M) := by
  first | exact @GlobalTheory.RingChain.TwistProj.projective_of_twist | exact GlobalTheory.RingChain.TwistProj.projective_of_twist | (intros; apply GlobalTheory.RingChain.TwistProj.projective_of_twist <;> assumption)
