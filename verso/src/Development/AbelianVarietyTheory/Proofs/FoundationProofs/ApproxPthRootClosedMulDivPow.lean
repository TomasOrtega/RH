import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

variable {L : Type} [Field L] (v : Valuation L ℝ≥0) {p : ℕ} {θ : ℝ≥0}

/- English proof (translation)
Establish `e : w ^ p = u - (u - w ^ p)` using `by ring`. Rewrite using `[e]`. Use `(Valuation.map_sub v _ _).trans (max_le le_rfl (h.trans ?_))` and prove the remaining obligations. Simplify using `using mul_le_mul' hθ (le_refl (v u))`.
-/
theorem approxRoot_pow_le (hθ : θ ≤ 1) {u w : L} (h : v (u - w ^ p) ≤ θ * v u) :
    v (w ^ p) ≤ v u := by
  have e : w ^ p = u - (u - w ^ p) := by ring
  rw [e]
  refine (Valuation.map_sub v _ _).trans (max_le le_rfl (h.trans ?_))
  simpa using mul_le_mul' hθ (le_refl (v u))

/- English proof (translation)
Establish `e : u * u' - (w * w') ^ p = u * (u' - w' ^ p) + w' ^ p * (u - w ^ p)` using `by ring`. Rewrite using `[e, map_mul]`. Use `(Valuation.map_add v _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem approxRoot_mul (hθ : θ ≤ 1) {u u' w w' : L} (h : v (u - w ^ p) ≤ θ * v u)
    (h' : v (u' - w' ^ p) ≤ θ * v u') : v (u * u' - (w * w') ^ p) ≤ θ * v (u * u') := by
  have e : u * u' - (w * w') ^ p = u * (u' - w' ^ p) + w' ^ p * (u - w ^ p) := by ring
  rw [e, map_mul]
  refine (Valuation.map_add v _ _).trans (max_le ?_ ?_)
  · rw [map_mul]
    calc v u * v (u' - w' ^ p) ≤ v u * (θ * v u') := mul_le_mul' le_rfl h'
      _ = θ * (v u * v u') := by ring
  · rw [map_mul]
    calc v (w' ^ p) * v (u - w ^ p) ≤ v u' * (θ * v u) :=
          mul_le_mul' (approxRoot_pow_le v hθ h') h
      _ = θ * (v u * v u') := by ring

/- English proof (translation)
Establish `hvu : 0 < v u`. Rewrite using `[pos_iff_ne_zero]`. Conclude with `(Valuation.ne_zero_iff v).mpr hu`. Establish `hlt : v (w ^ p - u) < v u`. Rewrite using `[Valuation.map_sub_swap]`.

Conclude with `h.trans_lt (by simpa using mul_lt_mul_of_pos_right hθ hvu)`. Establish `heq : v (w ^ p) = v u` using `Valuation.map_eq_of_sub_lt v hlt`. Establish `hw : w ^ p ≠ 0`. Introduce `h0`. Rewrite `heq` using `[h0, map_zero]`.

Conclude with `hvu.ne' heq.symm`. Establish `e : u⁻¹ - (w⁻¹) ^ p = (w ^ p - u) * (u⁻¹ * (w ^ p)⁻¹)`. Rewrite using `[inv_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, map_mul, map_mul, map_inv₀, map_inv₀, heq, Valuation.map_sub_swap]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem approxRoot_inv (hθ : θ < 1) {u w : L} (hu : u ≠ 0) (h : v (u - w ^ p) ≤ θ * v u) :
    v (u⁻¹ - (w⁻¹) ^ p) ≤ θ * v u⁻¹ := by
  have hvu : 0 < v u := by
    rw [pos_iff_ne_zero]; exact (Valuation.ne_zero_iff v).mpr hu
  have hlt : v (w ^ p - u) < v u := by
    rw [Valuation.map_sub_swap]
    exact h.trans_lt (by simpa using mul_lt_mul_of_pos_right hθ hvu)
  have heq : v (w ^ p) = v u := Valuation.map_eq_of_sub_lt v hlt
  have hw : w ^ p ≠ 0 := by
    intro h0; rw [h0, map_zero] at heq; exact hvu.ne' heq.symm
  have e : u⁻¹ - (w⁻¹) ^ p = (w ^ p - u) * (u⁻¹ * (w ^ p)⁻¹) := by
    rw [inv_pow]; field_simp
  rw [e, map_mul, map_mul, map_inv₀, map_inv₀, heq, Valuation.map_sub_swap]
  calc v (u - w ^ p) * ((v u)⁻¹ * (v u)⁻¹) ≤ θ * v u * ((v u)⁻¹ * (v u)⁻¹) :=
        mul_le_mul' h le_rfl
    _ = θ * (v u)⁻¹ := by field_simp

/- English proof (translation)
Introduce `L _ v p F θ hθ u u' ⟨w, hwF, hw⟩ ⟨w', hw'F, hw'⟩`. Establish `hθ1 : θ ≤ 1` using `hθ.le`. Use `⟨⟨w * w', F.mul_mem hwF hw'F, approxRoot_mul v hθ1 hw hw'⟩, fun hu' => ?_, fun k => ?_⟩` and prove the remaining obligations. Use `⟨w * w'⁻¹, F.mul_mem hwF (F.inv_mem hw'F), ?_⟩` and prove the remaining obligations. Rewrite using `[div_eq_mul_inv]`.

Conclude with `approxRoot_mul v hθ1 hw (approxRoot_inv v hθ hu' hw')`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨1, F.one_mem, by simp⟩`. Consider the case `succ k ih`. Take `⟨x, hxF, hx⟩` from `ih`.

Use `⟨x * w, F.mul_mem hxF hwF, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ]`. Conclude with `approxRoot_mul v hθ1 hx hw`.
-/
theorem approxRoot_closed : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (F : Subfield L) (θ : ℝ≥0), θ < 1 → ∀ u u' : L, (∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → (∃ w ∈ F, v (u' - w ^ p) ≤ θ * v u') → (∃ w ∈ F, v (u * u' - w ^ p) ≤ θ * v (u * u')) ∧ (u' ≠ 0 → ∃ w ∈ F, v (u / u' - w ^ p) ≤ θ * v (u / u')) ∧ ∀ k : ℕ, ∃ w ∈ F, v (u ^ k - w ^ p) ≤ θ * v (u ^ k) := by
  intro L _ v p F θ hθ u u' ⟨w, hwF, hw⟩ ⟨w', hw'F, hw'⟩
  have hθ1 : θ ≤ 1 := hθ.le
  refine ⟨⟨w * w', F.mul_mem hwF hw'F, approxRoot_mul v hθ1 hw hw'⟩, fun hu' => ?_, fun k => ?_⟩
  · refine ⟨w * w'⁻¹, F.mul_mem hwF (F.inv_mem hw'F), ?_⟩
    rw [div_eq_mul_inv]
    exact approxRoot_mul v hθ1 hw (approxRoot_inv v hθ hu' hw')
  · induction k with
    | zero => exact ⟨1, F.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨x, hxF, hx⟩ := ih
      refine ⟨x * w, F.mul_mem hxF hwF, ?_⟩
      rw [pow_succ]
      exact approxRoot_mul v hθ1 hx hw

end GlobalTheory.AlmostEt
