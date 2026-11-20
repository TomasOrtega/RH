import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory

/- English proof (translation)
Set `g : Fin d ⊕ Fin d → Fin d ⊕ (Fin d ⊕ Fin d)` to `Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)`. Establish `hg : (Sum.elim x1 x2 : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = X ∘ g`. Apply the tactic sequence `funext s; rcases s with s | s <;> rfl`. Establish `h1 : at2 c x1 x2 = rename g c`. Rewrite using `[rename_eq_subst, ← hg]`.

Both sides reduce to the same expression. Rewrite using `[h1]`. Apply `coeff_rename_eq_zero` to reduce the goal to its premises. Introduce and unpack `⟨v, hv⟩`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, e i ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `he (Finsupp.ext h)`. Apply `hi` to reduce the goal to its premises. Establish `h2` using `congrArg (fun w : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ => w (Sum.inr (Sum.inr i))) hv`.

Rewrite `h2` using `[Finsupp.mapDomain_notin_range]`. Simplify using `using h2.symm`. Apply the tactic sequence `rintro ⟨s, hs⟩; rcases s with s | s <;> simp [g] at hs`.
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
