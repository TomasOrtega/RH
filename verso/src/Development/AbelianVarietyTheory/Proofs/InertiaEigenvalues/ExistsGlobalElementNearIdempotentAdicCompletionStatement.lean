import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalElementNearIdempotentAdicCompletion
import Mathlib
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_global_near_idempotent` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsGlobalElementNearIdempotentAdicCompletion.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_global_element_near_idempotent_adicCompletion : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [Algebra E E'] [FiniteDimensional E E'] (w : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι] (b : Module.Basis ι E E') (ψ : w.adicCompletion E ⊗[E] E' →ₐ[w.adicCompletion E] w.adicCompletion E) (e : w.adicCompletion E ⊗[E] E'), e * e = e → ψ e = 1 → ∀ (p q : w.adicCompletion E ⊗[E] E') (n : ℕ), ∃ ε : E', (∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) ∧ Valued.v (ψ ((1 : w.adicCompletion E) ⊗ₜ ε) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧ Valued.v (Algebra.norm (w.adicCompletion E) (p + q * ((1 : w.adicCompletion E) ⊗ₜ ε - e)) - Algebra.norm (w.adicCompletion E) p) ≤ WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.exists_global_near_idempotent | exact GlobalTheory.exists_global_near_idempotent | (intros; apply GlobalTheory.exists_global_near_idempotent <;> assumption)
