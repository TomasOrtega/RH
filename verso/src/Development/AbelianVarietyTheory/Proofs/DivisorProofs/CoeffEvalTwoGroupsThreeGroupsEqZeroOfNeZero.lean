import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem coeff_at2_x1_x2_eq_zero_of_third_ne_zero {R : Type} [CommRing R] {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ) (he : e ≠ 0) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := by
  classical
  let g : Fin d ⊕ Fin d → Fin d ⊕ (Fin d ⊕ Fin d) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  have hg : (Sum.elim x1 x2 : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = X ∘ g := by
    funext s; rcases s with s | s <;> rfl
  have h1 : at2 c x1 x2 = rename g c := by
    rw [rename_eq_subst, ← hg]; rfl
  rw [h1]
  apply coeff_rename_eq_zero
  rintro ⟨v, hv⟩
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra h; push_neg at h; exact he (Finsupp.ext h)
  apply hi
  have h2 := congrArg (fun w : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ => w (Sum.inr (Sum.inr i))) hv
  rw [Finsupp.mapDomain_notin_range] at h2
  · simpa using h2.symm
  · rintro ⟨s, hs⟩; rcases s with s | s <;> simp [g] at hs

end GlobalTheory
