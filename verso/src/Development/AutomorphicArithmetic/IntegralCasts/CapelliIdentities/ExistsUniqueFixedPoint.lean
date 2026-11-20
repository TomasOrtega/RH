import Mathlib

open MvPowerSeries in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h d hd`. Establish `h0 : coeff d (f - g) = 0` using `coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Introduce `h`.

Use `nat_le_order fun d hd => ?_` and prove the remaining obligations. Rewrite using `[map_sub, h d hd, sub_self]`.
-/
private theorem UpperTheory.Reformulated.B.Ydb5.le_order_iff {σ R : Type*} [CommRing R]
    (f g : MvPowerSeries σ R) (n : ℕ) :
    (n : ℕ∞) ≤ (f - g).order ↔ ∀ d : σ →₀ ℕ, d.degree < n → coeff d f = coeff d g := by
  constructor
  · intro h d hd
    have h0 : coeff d (f - g) = 0 :=
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
    rwa [map_sub, sub_eq_zero] at h0
  · intro h
    refine nat_le_order fun d hd => ?_
    rw [map_sub, h d hd, sub_self]

/- English proof (translation)
Introduce `σ R _ Φ h`. Simplify using `only [UpperTheory.Reformulated.B.Ydb5.le_order_iff] at h`. Establish `step : ∀ (k : ℕ) (g : MvPowerSeries σ R) (d : σ →₀ ℕ), d.degree < k → MvPowerSeries.coeff d (Φ^[k] g) = MvPowerSeries.coeff d (Φ^[k] 0)`. Introduce `k g`. Proceed by induction on `k with`.

Consider the case `zero => intro d hd`. Conclude with `absurd hd (Nat.not_lt_zero _)`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply']`. Conclude with `h _ _ k ih`.

Set `f : MvPowerSeries σ R` to `fun d => MvPowerSeries.coeff d (Φ^[d.degree + 1] 0)`. Establish `hf : ∀ d : σ →₀ ℕ, MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[d.degree + 1] 0)` using `fun _ => rfl`. Establish `approx : ∀ (k : ℕ) (d : σ →₀ ℕ), d.degree < k → MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[k] 0)`. Introduce `k d hd`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hd)`.

Rewrite using `[hf, Function.iterate_add_apply Φ (Nat.succ _) m]`. Conclude with `(step _ _ d (Nat.lt_succ_self _)).symm`. Use `⟨f, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `d`. Rewrite using `[h f _ d.degree (approx _) d (Nat.lt_succ_self _), hf, Function.iterate_succ_apply']`.

Introduce `g hg`. Use extensionality with `d`. Rewrite using `[hf, ← step _ g d (Nat.lt_succ_self _), Function.iterate_fixed hg]`.
-/
theorem UpperTheory.Reformulated.B.Ydb5.existsUnique_fixedPoint.{u_1, u_2} :
    ∀ {σ : Type u_1} {R : Type u_2} [inst : CommRing R] (Φ : MvPowerSeries σ R → MvPowerSeries σ R),
      (∀ (f g : MvPowerSeries σ R) (n : ℕ), (↑n : ℕ∞) ≤ (f - g).order → (↑(n + (1 : ℕ)) : ℕ∞) ≤ (Φ f - Φ g).order) →
        ∃! f : MvPowerSeries σ R, Φ f = f := by
  intro σ R _ Φ h
  simp only [UpperTheory.Reformulated.B.Ydb5.le_order_iff] at h
  have step : ∀ (k : ℕ) (g : MvPowerSeries σ R) (d : σ →₀ ℕ), d.degree < k →
      MvPowerSeries.coeff d (Φ^[k] g) = MvPowerSeries.coeff d (Φ^[k] 0) := by
    intro k g
    induction k with
    | zero => intro d hd; exact absurd hd (Nat.not_lt_zero _)
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact h _ _ k ih
  let f : MvPowerSeries σ R := fun d => MvPowerSeries.coeff d (Φ^[d.degree + 1] 0)
  have hf : ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[d.degree + 1] 0) := fun _ => rfl
  have approx : ∀ (k : ℕ) (d : σ →₀ ℕ), d.degree < k →
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[k] 0) := by
    intro k d hd
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hd)
    rw [hf, Function.iterate_add_apply Φ (Nat.succ _) m]
    exact (step _ _ d (Nat.lt_succ_self _)).symm
  refine ⟨f, ?_, ?_⟩
  · ext d
    rw [h f _ d.degree (approx _) d (Nat.lt_succ_self _), hf, Function.iterate_succ_apply']
  · intro g hg
    ext d
    rw [hf, ← step _ g d (Nat.lt_succ_self _), Function.iterate_fixed hg]
