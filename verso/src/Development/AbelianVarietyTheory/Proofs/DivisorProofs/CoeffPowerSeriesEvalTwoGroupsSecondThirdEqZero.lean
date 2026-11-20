import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

open MvPowerSeries

set_option autoImplicit false

namespace GlobalTheory.Katz

/- English proof (translation)
Establish `hX : ∀ s, Sum.elim (x2 (R` using `R) (d := d)) x3 s = X (Sum.elim (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)) s) := by`. Apply the tactic sequence `intro s; cases s <;> rfl`. Establish `hs : HasSubst (Sum.elim (x2 (R` using `R) (d := d)) x3) := hasSubst_of_constantCoeff_zero fun s => by rw [hX]; exact constantCoeff_X _`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, a i ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `ha (Finsupp.ext h)`. Unfold `at2`. Rewrite using `[coeff_subst hs]`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises.

Introduce `α`. Establish `key : ∃ β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, β (Sum.inl i) = 0 ∧ (α.prod fun s k => (Sum.elim (x2 (R` using `R) (d := d)) x3 s) ^ k) = monomial β 1 := by`. Unfold `Finsupp.prod`. Use `Finset.prod_induction _ (fun f => ∃ β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, β (Sum.inl i) = 0 ∧ f = monomial β 1) ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `f g ⟨β, hβ, rfl⟩ ⟨γ, hγ, rfl⟩`.

Conclude with `⟨β + γ, by simp [hβ, hγ], by rw [monomial_mul_monomial, one_mul]⟩`. Conclude with `⟨0, rfl, (monomial_zero_one).symm⟩`. Introduce `s _`. Use `⟨Finsupp.single (Sum.elim (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)) s) (α s), ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `cases s <;> simp`.

Simplify using `only`. Rewrite using `[hX, X_pow_eq]`. Take `⟨β, hβ, hp⟩` from `key`. Rewrite using `[hp, coeff_monomial_ne, smul_zero]`. Introduce `h`.

Apply `hi` to reduce the goal to its premises. Use `congrArg (fun w => w (Sum.inl i)) h` as an intermediate fact. Simplify `this` using `[hβ]`.
-/
theorem coeff_at2_x2_x3_eq_zero_of_first_ne_zero {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (a b e : Fin d →₀ ℕ) (ha : a ≠ 0) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := by
  classical
  have hX : ∀ s, Sum.elim (x2 (R := R) (d := d)) x3 s
      = X (Sum.elim (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)) s) := by
    intro s; cases s <;> rfl
  have hs : HasSubst (Sum.elim (x2 (R := R) (d := d)) x3) :=
    hasSubst_of_constantCoeff_zero fun s => by rw [hX]; exact constantCoeff_X _
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha (Finsupp.ext h)
  unfold at2
  rw [coeff_subst hs]
  apply finsum_eq_zero_of_forall_eq_zero
  intro α
  have key : ∃ β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, β (Sum.inl i) = 0 ∧
      (α.prod fun s k => (Sum.elim (x2 (R := R) (d := d)) x3 s) ^ k) = monomial β 1 := by
    unfold Finsupp.prod
    refine Finset.prod_induction _ (fun f => ∃ β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ,
      β (Sum.inl i) = 0 ∧ f = monomial β 1) ?_ ?_ ?_
    · rintro f g ⟨β, hβ, rfl⟩ ⟨γ, hγ, rfl⟩
      exact ⟨β + γ, by simp [hβ, hγ], by rw [monomial_mul_monomial, one_mul]⟩
    · exact ⟨0, rfl, (monomial_zero_one).symm⟩
    · intro s _
      refine ⟨Finsupp.single (Sum.elim (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)) s) (α s), ?_, ?_⟩
      · cases s <;> simp
      · dsimp only
        rw [hX, X_pow_eq]
  obtain ⟨β, hβ, hp⟩ := key
  rw [hp, coeff_monomial_ne, smul_zero]
  intro h
  apply hi
  have := congrArg (fun w => w (Sum.inl i)) h
  simpa [hβ] using this

end GlobalTheory.Katz
