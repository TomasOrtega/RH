import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.LocCharAnn

/- English proof (translation)
Establish `hk' : k s₀ - 1 ≠ 0` using `sub_ne_zero.mpr hk`. Establish `hpos : 0 < ‖k s₀ - 1‖` using `norm_pos_iff.mpr hk'`. Use `set X₀ := a s₀ / (k s₀ - 1)`. Establish `hX : X₀ - X = (a s₀ - (k s₀ * X - X)) / (k s₀ - 1)`. Simplify using `only [X₀]`.

Clear the denominators using the available nonvanishing facts. Establish `hXn : ‖X₀ - X‖ ≤ ε / ‖k s₀ - 1‖`. Rewrite using `[hX, norm_div]`. Conclude with `div_le_div_of_nonneg_right h0 hpos.le`. Establish `hid : a s - (k s * X₀ - X₀) = (a s - (k s * X - X)) - (k s - 1) * (X₀ - X)` using `by ring`.

Rewrite using `[hid]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`. Use `gcongr`. Use `_ = (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) * ε := by field_simp`.
-/
theorem approx_candidate {K : Type} [NormedField K] {Γ : Type} (k a : Γ → K) {s₀ : Γ}
    (hk : k s₀ ≠ 1) {X : K} {ε : ℝ}
    (h0 : ‖a s₀ - (k s₀ * X - X)‖ ≤ ε) (s : Γ) (hs : ‖a s - (k s * X - X)‖ ≤ ε) :
    ‖a s - (k s * (a s₀ / (k s₀ - 1)) - a s₀ / (k s₀ - 1))‖ ≤
      (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) * ε := by
  have hk' : k s₀ - 1 ≠ 0 := sub_ne_zero.mpr hk
  have hpos : 0 < ‖k s₀ - 1‖ := norm_pos_iff.mpr hk'
  set X₀ := a s₀ / (k s₀ - 1)
  have hX : X₀ - X = (a s₀ - (k s₀ * X - X)) / (k s₀ - 1) := by
    simp only [X₀]; field_simp
  have hXn : ‖X₀ - X‖ ≤ ε / ‖k s₀ - 1‖ := by
    rw [hX, norm_div]; exact div_le_div_of_nonneg_right h0 hpos.le
  have hid : a s - (k s * X₀ - X₀) = (a s - (k s * X - X)) - (k s - 1) * (X₀ - X) := by ring
  rw [hid]
  calc ‖(a s - (k s * X - X)) - (k s - 1) * (X₀ - X)‖
      ≤ ‖a s - (k s * X - X)‖ + ‖(k s - 1) * (X₀ - X)‖ := norm_sub_le _ _
    _ ≤ ε + ‖k s - 1‖ * (ε / ‖k s₀ - 1‖) := by
        rw [norm_mul]; gcongr
    _ = (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) * ε := by field_simp

/- English proof (translation)
Introduce `l _ Γ H k a ⟨s₀, hs₀, hk⟩ hna`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `set q : ℝ := ‖((l : ℕ) : Qbar l)‖ with hq`. Establish `hq1 : q < 1` using `GlobalTheory.CoefEmbed.norm_prime_lt_one`.

Establish `hq0 : 0 ≤ q` using `norm_nonneg _`. Establish `happrox : ∀ r : ℕ, ∃ X : Qbar l, ∀ t ∈ H, ‖a t - (k t * X - X)‖ ≤ q ^ r`. Introduce `r`. Take `⟨n, x, y, hx1, hb, hx⟩` from `hcon r`. Rewrite `hx`, `hb` using `[norm_pow]`.

Distinguish the cases in `hnr : n < r`. Rewrite `hx` using `[Nat.sub_eq_zero_of_le hnr.le, pow_zero]`. Conclude with `absurd hx (not_lt.mpr hx1)`. Use `push_neg at hnr`. Establish `hxpos : 0 < ‖x‖` using `lt_of_le_of_lt (pow_nonneg hq0 _) hx`.

Establish `hx0 : x ≠ 0` using `norm_pos_iff.mp hxpos`. Use `⟨y / x, fun t ht => ?_⟩` and prove the remaining obligations. Establish `hid : x * a t - (k t * y - y) = x * (a t - (k t * (y / x) - y / x))`. Clear the denominators using the available nonvanishing facts. Establish `h1` using `hb t ht`.

Rewrite `h1` using `[hid, norm_mul]`. Establish `hsplit : q ^ n = q ^ (n - r) * q ^ r`. Rewrite using `[← pow_add, Nat.sub_add_cancel hnr]`. Rewrite `h1` using `[hsplit]`. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Establish `: q ^ (n - r) * q ^ r < ‖x‖ * ‖a t - (k t * (y / x) - y / x)‖` using `mul_lt_mul'' hx hlt (pow_nonneg hq0 _) (pow_nonneg hq0 _)`. Combine the linear equalities and inequalities to obtain the conclusion. Apply `hna` to reduce the goal to its premises. Use `⟨a s₀ / (k s₀ - 1), fun s hs => ?_⟩` and prove the remaining obligations.

Use `set C : ℝ := 1 + ‖k s - 1‖ / ‖k s₀ - 1‖`. Establish `hbound : ∀ r : ℕ, ‖a s - (k s * (a s₀ / (k s₀ - 1)) - a s₀ / (k s₀ - 1))‖ ≤ C * q ^ r`. Introduce `r`. Take `⟨X, hX⟩` from `happrox r`. Conclude with `approx_candidate k a hk (hX s₀ hs₀) s (hX s hs)`.

Establish `hlim : Filter.Tendsto (fun r : ℕ => C * q ^ r) Filter.atTop (nhds 0)`. Simplify using `using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C`. Establish `hle` using `ge_of_tendsto' hlim hbound`. Establish `h0 : ‖a s - (k s * (a s₀ / (k s₀ - 1)) - a s₀ / (k s₀ - 1))‖ = 0` using `le_antisymm hle (norm_nonneg _)`. Conclude with `sub_eq_zero.mp (norm_eq_zero.mp h0)`.
-/
theorem exists_depth_of_not_coboundary : ∀ (l : ℕ) [Fact l.Prime] {Γ : Type} (H : Set Γ) (k a : Γ → Qbar l), (∃ s ∈ H, k s ≠ 1) → (¬ ∃ X : Qbar l, ∀ s ∈ H, a s = k s * X - X) → ∃ r : ℕ, ∀ (n : ℕ) (x y : Qbar l), ‖x‖ ≤ 1 → (∀ s ∈ H, ‖x * a s - (k s * y - y)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) → ‖x‖ ≤ ‖((l : ℕ) : Qbar l) ^ (n - r)‖ := by
  intro l _ Γ H k a ⟨s₀, hs₀, hk⟩ hna
  by_contra hcon
  push_neg at hcon
  set q : ℝ := ‖((l : ℕ) : Qbar l)‖ with hq
  have hq1 : q < 1 := GlobalTheory.CoefEmbed.norm_prime_lt_one
  have hq0 : 0 ≤ q := norm_nonneg _
  have happrox : ∀ r : ℕ, ∃ X : Qbar l, ∀ t ∈ H, ‖a t - (k t * X - X)‖ ≤ q ^ r := by
    intro r
    obtain ⟨n, x, y, hx1, hb, hx⟩ := hcon r
    rw [norm_pow] at hx hb
    by_cases hnr : n < r
    · rw [Nat.sub_eq_zero_of_le hnr.le, pow_zero] at hx
      exact absurd hx (not_lt.mpr hx1)
    push_neg at hnr
    have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (pow_nonneg hq0 _) hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
    refine ⟨y / x, fun t ht => ?_⟩
    have hid : x * a t - (k t * y - y) = x * (a t - (k t * (y / x) - y / x)) := by
      field_simp
    have h1 := hb t ht
    rw [hid, norm_mul] at h1
    have hsplit : q ^ n = q ^ (n - r) * q ^ r := by
      rw [← pow_add, Nat.sub_add_cancel hnr]
    rw [hsplit] at h1
    by_contra hlt
    push_neg at hlt
    have : q ^ (n - r) * q ^ r < ‖x‖ * ‖a t - (k t * (y / x) - y / x)‖ :=
      mul_lt_mul'' hx hlt (pow_nonneg hq0 _) (pow_nonneg hq0 _)
    linarith
  apply hna
  refine ⟨a s₀ / (k s₀ - 1), fun s hs => ?_⟩
  set C : ℝ := 1 + ‖k s - 1‖ / ‖k s₀ - 1‖
  have hbound : ∀ r : ℕ, ‖a s - (k s * (a s₀ / (k s₀ - 1)) - a s₀ / (k s₀ - 1))‖ ≤ C * q ^ r := by
    intro r
    obtain ⟨X, hX⟩ := happrox r
    exact approx_candidate k a hk (hX s₀ hs₀) s (hX s hs)
  have hlim : Filter.Tendsto (fun r : ℕ => C * q ^ r) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
  have hle := ge_of_tendsto' hlim hbound
  have h0 : ‖a s - (k s * (a s₀ / (k s₀ - 1)) - a s₀ / (k s₀ - 1))‖ = 0 :=
    le_antisymm hle (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

end GlobalTheory.LocCharAnn
