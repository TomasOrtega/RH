import Mathlib

open Filter Topology

namespace GlobalTheory.CompanionTheory.Casselman

/- English proof (translation)
Introduce `δ r hδ hδ1 hr h`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `hx : 0 < Real.sqrt δ * r` using `mul_pos (Real.sqrt_pos.mpr hδ) (by linarith)`. Establish `hcont : ContinuousAt (fun ε : ℝ => δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε)) 0`.

Apply `ContinuousAt.mul continuousAt_const` to reduce the goal to its premises. Conclude with `(Real.continuousAt_const_rpow hx.ne').comp (continuous_const.add continuous_id).continuousAt`. Establish `h0 : δ⁻¹ * (Real.sqrt δ * r) ^ ((2 : ℝ) + 0) = r ^ 2`. Rewrite using `[add_zero, Real.rpow_two, mul_pow, Real.sq_sqrt hδ.le, inv_mul_cancel_left₀ hδ.ne']`. Establish `h1 : (1 : ℝ) < δ⁻¹ * (Real.sqrt δ * r) ^ ((2 : ℝ) + 0)`.

Rewrite using `[h0]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 1 < δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε)` using `hcont.eventually (lt_mem_nhds h1)`. Take `⟨ε, hε1, hε0⟩` from `((hev.filter_mono nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[Set.Ioi (0 : ℝ)] 0, x ∈ Set.Ioi (0 : ℝ))).exists`. Conclude with `lt_asymm (h ε hε0) hε1`.
-/
theorem le_one_of_forall_sqrt_mul_rpow_lt :
    ∀ (δ r : ℝ), 0 < δ → δ < 1 → 0 ≤ r →
      (∀ ε : ℝ, 0 < ε → δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) < 1) → r ≤ 1 := by
  intro δ r hδ hδ1 hr h
  by_contra hlt
  rw [not_le] at hlt
  have hx : 0 < Real.sqrt δ * r := mul_pos (Real.sqrt_pos.mpr hδ) (by linarith)
  have hcont : ContinuousAt (fun ε : ℝ => δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε)) 0 := by
    apply ContinuousAt.mul continuousAt_const
    exact (Real.continuousAt_const_rpow hx.ne').comp
      (continuous_const.add continuous_id).continuousAt
  have h0 : δ⁻¹ * (Real.sqrt δ * r) ^ ((2 : ℝ) + 0) = r ^ 2 := by
    rw [add_zero, Real.rpow_two, mul_pow, Real.sq_sqrt hδ.le, inv_mul_cancel_left₀ hδ.ne']
  have h1 : (1 : ℝ) < δ⁻¹ * (Real.sqrt δ * r) ^ ((2 : ℝ) + 0) := by
    rw [h0]
    nlinarith
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 1 < δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) :=
    hcont.eventually (lt_mem_nhds h1)
  obtain ⟨ε, hε1, hε0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[Set.Ioi (0 : ℝ)] 0, x ∈ Set.Ioi (0 : ℝ))).exists
  exact lt_asymm (h ε hε0) hε1

end GlobalTheory.CompanionTheory.Casselman
