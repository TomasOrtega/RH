import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.InvNatCastMemWittIntegers

noncomputable section

namespace PI.ExpIntWProof

open PI

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro y hy _`. Simplify using `using hy`. Consider the case `succ k ih`.

Introduce `y hy hnorm`. Establish `hpos : (0 : ℝ) < (p : ℝ)⁻¹` using `inv_pos.mpr (by exact_mod_cast hp.out.pos)`. Establish `hpinv : (p : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)`. Establish `hlt : ‖y‖ < 1` using `lt_of_le_of_lt hnorm (pow_lt_one₀ hpos.le hpinv (Nat.succ_ne_zero k))`. Establish `h1 : y / (p : ℂ_[p]) ∈ PI.Wp p` using `h p y hy hlt`.

Establish `h2 : ‖y / (p : ℂ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ k`. Rewrite using `[norm_div, norm_p, div_le_iff₀ hpos, ← pow_succ]`. Conclude with `hnorm`. Establish `h3` using `ih _ h1 h2`. Rewrite `h3` using `[div_div, ← pow_succ']`. Then use the resulting hypothesis.
-/
theorem div_pow_mem (h : KeyW) (p : ℕ) [hp : Fact p.Prime] :
    ∀ k : ℕ, ∀ y : ℂ_[p], y ∈ Wp p → ‖y‖ ≤ ((p : ℝ)⁻¹) ^ k → y / (p : ℂ_[p]) ^ k ∈ Wp p := by
  intro k
  induction k with
  | zero => intro y hy _; simpa using hy
  | succ k ih =>
    intro y hy hnorm
    have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
    have hpinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    have hlt : ‖y‖ < 1 :=
      lt_of_le_of_lt hnorm (pow_lt_one₀ hpos.le hpinv (Nat.succ_ne_zero k))
    have h1 : y / (p : ℂ_[p]) ∈ PI.Wp p := h p y hy hlt
    have h2 : ‖y / (p : ℂ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ k := by
      rw [norm_div, norm_p, div_le_iff₀ hpos, ← pow_succ]
      exact hnorm
    have h3 := ih _ h1 h2
    rwa [div_div, ← pow_succ'] at h3

/- English proof (translation)
Introduce `p hp x hx hnorm`. Take `⟨k, hk⟩` from `hx`. Establish `hp0 : (p : ℂ_[p]) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Establish `hn : ‖(p : ℂ_[p]) ^ k * x‖ ≤ ((p : ℝ)⁻¹) ^ k`. Rewrite using `[norm_mul, norm_pow, norm_p]`.

Conclude with `mul_le_of_le_one_right (by positivity) hnorm`. Establish `h3` using `div_pow_mem h p k _ hk hn`. Rewrite `h3` using `[mul_div_cancel_left₀ _ (pow_ne_zero k hp0)]`. Then use the resulting hypothesis.
-/
theorem stepIII_of_key (h : KeyW) : StepIII := by
  intro p hp x hx hnorm
  obtain ⟨k, hk⟩ := hx
  have hp0 : (p : ℂ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hn : ‖(p : ℂ_[p]) ^ k * x‖ ≤ ((p : ℝ)⁻¹) ^ k := by
    rw [norm_mul, norm_pow, norm_p]
    exact mul_le_of_le_one_right (by positivity) hnorm
  have h3 := div_pow_mem h p k _ hk hn
  rwa [mul_div_cancel_left₀ _ (pow_ne_zero k hp0)] at h3

/- English proof (translation)
The claim follows from `expIntW_of_steps h1 (stepIII_of_key h)`.
-/
theorem expIntW_of_key (h1 : StepI) (h : KeyW) : ExpIntW :=
  expIntW_of_steps h1 (stepIII_of_key h)

end PI.ExpIntWProof

end
