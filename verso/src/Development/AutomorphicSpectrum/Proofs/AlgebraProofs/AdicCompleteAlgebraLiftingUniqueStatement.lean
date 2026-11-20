import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AdicCompleteAlgebraLiftingUnique
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Relay.adic_complete_algebra_lifting_unique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FAdicCompleteAlgebraLiftingUnique.lean&line=4#L4)
-/
theorem _root_.GlobalTheory.T.adic_complete_algebra_lifting_unique : ∀ (R A B : Type) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Module.Finite R A] (I : Ideal R) [IsAdicComplete I R] (f : ∀ e : ℕ, B →ₐ[R] A ⧸ (I ^ (e + 1)).map (algebraMap R A)), (∀ e (b : B) (a : A), Ideal.Quotient.mk _ a = f (e + 1) b → Ideal.Quotient.mk _ a = f e b) → ∃! g : B →ₐ[R] A, ∀ e b, Ideal.Quotient.mk _ (g b) = f e b := by
  first | exact @GlobalTheory.CompanionTheory.Relay.adic_complete_algebra_lifting_unique | exact GlobalTheory.CompanionTheory.Relay.adic_complete_algebra_lifting_unique | (intros; apply GlobalTheory.CompanionTheory.Relay.adic_complete_algebra_lifting_unique <;> assumption)
