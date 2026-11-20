import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNefAsymp

/- English proof (translation)
Establish `h` using `(Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop`. Use `h.congr' (Eventually.of_forall fun m => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem tendsto_log_nat_div : Tendsto (fun m : ℕ => Real.log m / m) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  refine h.congr' (Eventually.of_forall fun m => ?_)
  simp

/- English proof (translation)
Use `set C : ℝ := max (L + 1) 1 with hC`. Establish `hC1 : 1 ≤ C` using `le_max_right _ _`. Establish `hev : ∀ᶠ m : ℕ in atTop, X m / (m : ℝ) ^ (D + 1) < C` using `hX.eventually (gt_mem_nhds (lt_of_lt_of_le (lt_add_one L) (le_max_left _ _)))`. Establish `hup : Tendsto (fun m : ℕ => 2 * Real.log C / m + (2 * ((D : ℝ) + 1)) * (Real.log m / m)) atTop (𝓝 0)`. Establish `h1 : Tendsto (fun m : ℕ => 2 * Real.log C * (m : ℝ)⁻¹) atTop (𝓝 (2 * Real.log C * 0))` using `(tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul _`.

Establish `h2` using `tendsto_log_nat_div.const_mul (2 * ((D : ℝ) + 1))`. Use `h1.add h2` as an intermediate fact. Simplify using `only [mul_zero, add_zero] at this`. Use `this.congr' (Eventually.of_forall fun m => ?_)` and prove the remaining obligations. Simplify using `[div_eq_mul_inv]`.

Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_` and prove the remaining obligations. Use `Eventually.of_forall fun m => ?_` and prove the remaining obligations. Conclude with `div_nonneg (Real.log_nonneg (by nlinarith [h1 m])) (Nat.cast_nonneg m)`. Use `filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1`. Establish `hm0 : (0 : ℝ) < m` using `by exact_mod_cast hm1`.

Establish `hP : (0 : ℝ) < (m : ℝ) ^ (D + 1)` using `pow_pos hm0 _`. Establish `hXle : X m ≤ C * (m : ℝ) ^ (D + 1)`. Rewrite `hm` using `[div_lt_iff₀ hP]`. Conclude with `hm.le`. Establish `hX0 : 0 < X m` using `lt_of_lt_of_le one_pos (h1 m)`.

Establish `hlog : Real.log (X m) ≤ Real.log C + ((D : ℝ) + 1) * Real.log m`. Use `Real.log_le_log hX0 hXle` as an intermediate fact. Rewrite `this` using `[Real.log_mul (by positivity) hP.ne', Real.log_pow]`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[Real.log_pow]`. Rewrite using `[show 2 * Real.log C / m + (2 * ((D : ℝ) + 1)) * (Real.log m / m) = (2 * (Real.log C + ((D : ℝ) + 1) * Real.log m)) / m by ring]`. Apply `div_le_div_of_nonneg_right _ hm0.le` to reduce the goal to its premises. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tendsto_log_sq_div {X : ℕ → ℝ} {D : ℕ} {L : ℝ} (h1 : ∀ m, 1 ≤ X m)
    (hX : Tendsto (fun m : ℕ => X m / (m : ℝ) ^ (D + 1)) atTop (𝓝 L)) :
    Tendsto (fun m : ℕ => Real.log (X m ^ 2) / m) atTop (𝓝 0) := by
  set C : ℝ := max (L + 1) 1 with hC
  have hC1 : 1 ≤ C := le_max_right _ _
  have hev : ∀ᶠ m : ℕ in atTop, X m / (m : ℝ) ^ (D + 1) < C :=
    hX.eventually (gt_mem_nhds (lt_of_lt_of_le (lt_add_one L) (le_max_left _ _)))
  have hup : Tendsto (fun m : ℕ => 2 * Real.log C / m + (2 * ((D : ℝ) + 1)) * (Real.log m / m)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => 2 * Real.log C * (m : ℝ)⁻¹) atTop (𝓝 (2 * Real.log C * 0)) :=
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul _
    have h2 := tendsto_log_nat_div.const_mul (2 * ((D : ℝ) + 1))
    have := h1.add h2
    simp only [mul_zero, add_zero] at this
    refine this.congr' (Eventually.of_forall fun m => ?_)
    simp [div_eq_mul_inv]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · refine Eventually.of_forall fun m => ?_
    exact div_nonneg (Real.log_nonneg (by nlinarith [h1 m])) (Nat.cast_nonneg m)
  · filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hP : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos hm0 _
    have hXle : X m ≤ C * (m : ℝ) ^ (D + 1) := by
      rw [div_lt_iff₀ hP] at hm; exact hm.le
    have hX0 : 0 < X m := lt_of_lt_of_le one_pos (h1 m)
    have hlog : Real.log (X m) ≤ Real.log C + ((D : ℝ) + 1) * Real.log m := by
      have := Real.log_le_log hX0 hXle
      rw [Real.log_mul (by positivity) hP.ne', Real.log_pow] at this
      push_cast at this
      linarith
    rw [Real.log_pow]
    rw [show 2 * Real.log C / m + (2 * ((D : ℝ) + 1)) * (Real.log m / m)
        = (2 * (Real.log C + ((D : ℝ) + 1) * Real.log m)) / m by ring]
    apply div_le_div_of_nonneg_right _ hm0.le
    push_cast
    linarith

/- English proof (translation)
Use `set Δ : ℝ := Real.log ((q : ℝ) / 2) with hΔdef`. Use `set F : ℝ := ((D + 1).factorial : ℝ) with hFdef`. Establish `hΔ : 0 < Δ` using `Real.log_pos (by`. Establish `: (3 : ℝ) ≤ q` using `by exact_mod_cast hq`. Use the proof step `linarith)`.

Establish `hF : 0 < F` using `by rw [hFdef]; exact_mod_cast Nat.factorial_pos _`. Establish `hFΔ : 0 < F * Δ` using `mul_pos hF hΔ`. Use `set c1 : ℝ := ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2) with hc1`. Establish `hc1p : 0 ≤ c1` using `mul_nonneg (by positivity) (add_nonneg hΔ.le (div_nonneg (mul_nonneg (Nat.cast_nonneg D) (Real.log_nonneg one_le_two)) zero_le_two))`. Use `set A : ℕ → ℝ := fun m => (β m + c1 * g m) / (F * Δ) with hA`.

Use `set B : ℕ → ℝ := fun m => ((D : ℝ) + 1) * g m / (2 * (F * Δ)) with hB`. Establish `hunf : ∀ m, bound D q (β m) (g m) = Real.log q * (A m + B m * Real.log ((A m + 2 * B m + 1) ^ 2))` using `fun m => rfl`. Establish `hinv` using `(tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))`. Establish `hgP : Tendsto (fun m : ℕ => g m / (m : ℝ) ^ (D + 1)) atTop (𝓝 0)`. Use `hg.mul hinv` as an intermediate fact.

Rewrite `this` using `[mul_zero]`. Conclude with `this.congr' (Eventually.of_forall fun m => by ring)`. Establish `hAP : Tendsto (fun m : ℕ => A m / (m : ℝ) ^ (D + 1)) atTop (𝓝 (a / (F * Δ)))`. Use `(hβ.add (hgP.const_mul c1)).div_const (F * Δ)` as an intermediate fact. Rewrite `this` using `[mul_zero, add_zero]`.

Conclude with `this.congr' (Eventually.of_forall fun m => by simp only [hA]; ring)`. Establish `hBP : Tendsto (fun m : ℕ => B m / (m : ℝ) ^ (D + 1)) atTop (𝓝 0)`. Use `hgP.const_mul (((D : ℝ) + 1) / (2 * (F * Δ)))` as an intermediate fact. Rewrite `this` using `[mul_zero]`. Conclude with `this.congr' (Eventually.of_forall fun m => by simp only [hB]; ring)`.

Establish `hA0 : ∀ m, 0 ≤ A m` using `fun m => div_nonneg (add_nonneg (hβ0 m) (mul_nonneg hc1p (hg0 m))) hFΔ.le`. Establish `hB0 : ∀ m, 0 ≤ B m` using `fun m => div_nonneg (mul_nonneg (by positivity) (hg0 m)) (by positivity)`. Establish `hX1 : ∀ m, 1 ≤ A m + 2 * B m + 1` using `fun m => by linarith [hA0 m, hB0 m]`. Establish `hXP : Tendsto (fun m : ℕ => (A m + 2 * B m + 1) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (a / (F * Δ) + 2 * 0 + 0 ^ (D + 1)))`. Use `(hAP.add (hBP.const_mul 2)).add (hinv.pow (D + 1))` as an intermediate fact.

Conclude with `this.congr' (Eventually.of_forall fun m => by ring)`. Establish `hlog` using `tendsto_log_sq_div hX1 hXP`. Establish `h2 : Tendsto (fun m : ℕ => B m * Real.log ((A m + 2 * B m + 1) ^ 2) / (m : ℝ) ^ (D + 1)) atTop (𝓝 0)`. Use `((hg.const_mul (((D : ℝ) + 1) / (2 * (F * Δ)))).mul hlog)` as an intermediate fact. Rewrite `this` using `[mul_zero]`.

Conclude with `this.congr' (Eventually.of_forall fun m => by simp only [hB]; ring)`. Use `(hAP.add h2).const_mul (Real.log q)` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `this.congr' (Eventually.of_forall fun m => by show _ = bound D q (β m) (g m) / _; rw [hunf]; ring)`.
-/
theorem tendsto_bound_div (D q : ℕ) (hq : 3 ≤ q) {β g : ℕ → ℝ} {a γ : ℝ} (hβ0 : ∀ m, 0 ≤ β m)
    (hg0 : ∀ m, 0 ≤ g m) (hβ : Tendsto (fun m : ℕ => β m / (m : ℝ) ^ (D + 1)) atTop (𝓝 a))
    (hg : Tendsto (fun m : ℕ => g m / (m : ℝ) ^ D) atTop (𝓝 γ)) :
    Tendsto (fun m : ℕ => bound D q (β m) (g m) / (m : ℝ) ^ (D + 1)) atTop
      (𝓝 (Real.log q * (a / (((D + 1).factorial : ℝ) * Real.log ((q : ℝ) / 2))))) := by
  set Δ : ℝ := Real.log ((q : ℝ) / 2) with hΔdef
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hΔ : 0 < Δ := Real.log_pos (by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith)
  have hF : 0 < F := by rw [hFdef]; exact_mod_cast Nat.factorial_pos _
  have hFΔ : 0 < F * Δ := mul_pos hF hΔ
  set c1 : ℝ := ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2) with hc1
  have hc1p : 0 ≤ c1 := mul_nonneg (by positivity)
    (add_nonneg hΔ.le (div_nonneg (mul_nonneg (Nat.cast_nonneg D) (Real.log_nonneg one_le_two)) zero_le_two))
  set A : ℕ → ℝ := fun m => (β m + c1 * g m) / (F * Δ) with hA
  set B : ℕ → ℝ := fun m => ((D : ℝ) + 1) * g m / (2 * (F * Δ)) with hB
  have hunf : ∀ m, bound D q (β m) (g m) = Real.log q * (A m + B m * Real.log ((A m + 2 * B m + 1) ^ 2)) :=
    fun m => rfl
  have hinv := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hgP : Tendsto (fun m : ℕ => g m / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
    have := hg.mul hinv
    rw [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by ring)
  have hAP : Tendsto (fun m : ℕ => A m / (m : ℝ) ^ (D + 1)) atTop (𝓝 (a / (F * Δ))) := by
    have := (hβ.add (hgP.const_mul c1)).div_const (F * Δ)
    rw [mul_zero, add_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by simp only [hA]; ring)
  have hBP : Tendsto (fun m : ℕ => B m / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
    have := hgP.const_mul (((D : ℝ) + 1) / (2 * (F * Δ)))
    rw [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by simp only [hB]; ring)
  have hA0 : ∀ m, 0 ≤ A m := fun m => div_nonneg (add_nonneg (hβ0 m) (mul_nonneg hc1p (hg0 m))) hFΔ.le
  have hB0 : ∀ m, 0 ≤ B m := fun m => div_nonneg (mul_nonneg (by positivity) (hg0 m)) (by positivity)
  have hX1 : ∀ m, 1 ≤ A m + 2 * B m + 1 := fun m => by linarith [hA0 m, hB0 m]
  have hXP : Tendsto (fun m : ℕ => (A m + 2 * B m + 1) / (m : ℝ) ^ (D + 1)) atTop
      (𝓝 (a / (F * Δ) + 2 * 0 + 0 ^ (D + 1))) := by
    have := (hAP.add (hBP.const_mul 2)).add (hinv.pow (D + 1))
    exact this.congr' (Eventually.of_forall fun m => by ring)
  have hlog := tendsto_log_sq_div hX1 hXP
  have h2 : Tendsto (fun m : ℕ => B m * Real.log ((A m + 2 * B m + 1) ^ 2) / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
    have := ((hg.const_mul (((D : ℝ) + 1) / (2 * (F * Δ)))).mul hlog)
    rw [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by simp only [hB]; ring)
  have := (hAP.add h2).const_mul (Real.log q)
  rw [add_zero] at this
  exact this.congr' (Eventually.of_forall fun m => by show _ = bound D q (β m) (g m) / _; rw [hunf]; ring)

/- English proof (translation)
Introduce `D u β g a γ hβ0 hg0 hβ hg hu ε hε`. Use `set F : ℝ := ((D + 1).factorial : ℝ) with hFdef`. Establish `hF : 0 < F` using `by rw [hFdef]; exact_mod_cast Nat.factorial_pos _`. Establish `ha : 0 ≤ a` using `ge_of_tendsto' hβ (fun m => div_nonneg (hβ0 m) (by positivity))`. Use `set K : ℝ := Real.log 2 * a / (F * ε) with hK`.

Take `⟨n, hn⟩` from `exists_nat_gt (2 * Real.exp K)`. Use `set q : ℕ := max n 3 with hqdef`. Establish `hq3 : 3 ≤ q` using `le_max_right _ _`. Establish `hqn : (n : ℝ) ≤ q` using `by exact_mod_cast le_max_left n 3`. Establish `hq3r : (3 : ℝ) ≤ q` using `by exact_mod_cast hq3`.

Establish `hq0 : (0 : ℝ) < q` using `by linarith`. Establish `hKΔ : K < Real.log ((q : ℝ) / 2)`. Rewrite using `[Real.lt_log_iff_exp_lt (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hΔ : 0 < Real.log ((q : ℝ) / 2)` using `Real.log_pos (by linarith)`.

Establish `hlogq : Real.log q = Real.log ((q : ℝ) / 2) + Real.log 2`. Rewrite using `[Real.log_div hq0.ne' two_ne_zero]`. Expand and normalize the polynomial expressions, which then agree. Establish `hL : Real.log q * (a / (F * Real.log ((q : ℝ) / 2))) < a / F + ε`. Establish `e : Real.log q * (a / (F * Real.log ((q : ℝ) / 2))) = a / F + Real.log 2 * a / (F * Real.log ((q : ℝ) / 2))`.

Rewrite using `[hlogq]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Establish `h1 : Real.log 2 * a < Real.log ((q : ℝ) / 2) * (F * ε)`. Rewrite `hKΔ` using `[hK, div_lt_iff₀ (mul_pos hF hε)]`.

Conclude with `hKΔ`. Establish `h2 : Real.log 2 * a / (F * Real.log ((q : ℝ) / 2)) < ε`. Rewrite using `[div_lt_iff₀ (mul_pos hF hΔ)]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `ht` using `tendsto_bound_div D q hq3 hβ0 hg0 hβ hg`. Use `filter_upwards [ht.eventually (gt_mem_nhds hL), eventually_ge_atTop 1] with m hm hm1`. Establish `hP : (0 : ℝ) < (m : ℝ) ^ (D + 1)` using `pow_pos (by exact_mod_cast hm1) _`. Rewrite `hm` using `[div_lt_iff₀ hP]`. Conclude with `(hu m q hq3).trans hm.le`.
-/
theorem eventually_le_of_bound : ∀ (D : ℕ) (u β g : ℕ → ℝ) (a γ : ℝ), (∀ m, 0 ≤ β m) → (∀ m, 0 ≤ g m) →
    Tendsto (fun m : ℕ => β m / (m : ℝ) ^ (D + 1)) atTop (𝓝 a) →
    Tendsto (fun m : ℕ => g m / (m : ℝ) ^ D) atTop (𝓝 γ) →
    (∀ m q, 3 ≤ q → u m ≤ bound D q (β m) (g m)) → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ m : ℕ in atTop, u m ≤ (a / (D + 1).factorial + ε) * (m : ℝ) ^ (D + 1) := by
  intro D u β g a γ hβ0 hg0 hβ hg hu ε hε
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hF : 0 < F := by rw [hFdef]; exact_mod_cast Nat.factorial_pos _
  have ha : 0 ≤ a := ge_of_tendsto' hβ (fun m => div_nonneg (hβ0 m) (by positivity))
  set K : ℝ := Real.log 2 * a / (F * ε) with hK
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * Real.exp K)
  set q : ℕ := max n 3 with hqdef
  have hq3 : 3 ≤ q := le_max_right _ _
  have hqn : (n : ℝ) ≤ q := by exact_mod_cast le_max_left n 3
  have hq3r : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hKΔ : K < Real.log ((q : ℝ) / 2) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    linarith
  have hΔ : 0 < Real.log ((q : ℝ) / 2) := Real.log_pos (by linarith)
  have hlogq : Real.log q = Real.log ((q : ℝ) / 2) + Real.log 2 := by
    rw [Real.log_div hq0.ne' two_ne_zero]; ring
  have hL : Real.log q * (a / (F * Real.log ((q : ℝ) / 2))) < a / F + ε := by
    have e : Real.log q * (a / (F * Real.log ((q : ℝ) / 2)))
        = a / F + Real.log 2 * a / (F * Real.log ((q : ℝ) / 2)) := by
      rw [hlogq]; field_simp
    rw [e]
    have h1 : Real.log 2 * a < Real.log ((q : ℝ) / 2) * (F * ε) := by
      rw [hK, div_lt_iff₀ (mul_pos hF hε)] at hKΔ; exact hKΔ
    have h2 : Real.log 2 * a / (F * Real.log ((q : ℝ) / 2)) < ε := by
      rw [div_lt_iff₀ (mul_pos hF hΔ)]; nlinarith
    linarith
  have ht := tendsto_bound_div D q hq3 hβ0 hg0 hβ hg
  filter_upwards [ht.eventually (gt_mem_nhds hL), eventually_ge_atTop 1] with m hm hm1
  have hP : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos (by exact_mod_cast hm1) _
  rw [div_lt_iff₀ hP] at hm
  exact (hu m q hq3).trans hm.le

end GlobalTheory.HSNefAsymp
