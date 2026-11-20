import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.TorsionNormIteration.InverseIntegralClasses.MemSpanOfNormLe
open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

variable {K : Type} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Rewrite using `[← Commute.geom_sum₂_mul (Commute.all _ _), add_sub_cancel_left, norm_mul]`. Establish `hs : ‖∑ k ∈ Finset.range n, (c + e) ^ k * c ^ (n - 1 - k)‖ ≤ 1`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[norm_mul, norm_pow, norm_pow]`.

Conclude with `mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hce) (by positivity) (pow_le_one₀ (norm_nonneg _) hc)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_add_pow_sub_pow_le (c e : K) {r : ℝ} (hc : ‖c‖ ≤ 1) (hce : ‖c + e‖ ≤ 1) (he : ‖e‖ ≤ r)
    (n : ℕ) : ‖(c + e) ^ n - c ^ n‖ ≤ r := by
  rw [← Commute.geom_sum₂_mul (Commute.all _ _), add_sub_cancel_left, norm_mul]
  have hs : ‖∑ k ∈ Finset.range n, (c + e) ^ k * c ^ (n - 1 - k)‖ ≤ 1 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro k _
    rw [norm_mul, norm_pow, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hce) (by positivity) (pow_le_one₀ (norm_nonneg _) hc)
  calc _ ≤ 1 * r := mul_le_mul hs he (norm_nonneg _) zero_le_one
    _ = r := one_mul r

/- English proof (translation)
Take `⟨_, _, hl1, hmax, hiso, hfr⟩` from `hU`. Proceed by induction on `i with`. Consider the case `zero => exact ⟨fun a _ => by simp, fun x => by simp⟩`. Consider the case `succ i ih`. Take `⟨ih1, ih2⟩` from `ih`.

Use `⟨fun a ha => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ', RingHom.mul_def, RingHom.comp_apply] set b := (σ ^ i) a`. Establish `hb : ‖b‖ ≤ 1` using `(ih2 a).le.trans ha`. Establish `h1 : ‖σ b - b ^ l‖ ≤ ‖(l : K)‖` using `hmax _ (hfr b hb)`. Establish `hc : ‖a ^ l ^ i‖ ≤ 1` using `by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha`.

Establish `h2 : ‖b ^ l - (a ^ l ^ i) ^ l‖ ≤ ‖(l : K)‖`. Use `norm_add_pow_sub_pow_le (a ^ l ^ i) (b - a ^ l ^ i) hc (by simpa using hb) (ih1 a ha) l` as an intermediate fact. Simplify using `using this`. Establish `: σ b - a ^ l ^ (i + 1) = (σ b - b ^ l) + (b ^ l - (a ^ l ^ i) ^ l)` using `by ring`. Rewrite using `[this]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)`. Rewrite using `[pow_succ', RingHom.mul_def, RingHom.comp_apply, hiso, ih2]`.
-/
theorem isFrobLift_pow (l : ℕ) (σ : K →+* K) (hU : Unr K l σ) (i : ℕ) :
    Formalism.G.IsFrobLift l (l ^ i) (σ ^ i) ∧ ∀ x : K, ‖(σ ^ i) x‖ = ‖x‖ := by
  obtain ⟨_, _, hl1, hmax, hiso, hfr⟩ := hU
  induction i with
  | zero => exact ⟨fun a _ => by simp, fun x => by simp⟩
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun a ha => ?_, fun x => ?_⟩
    · rw [pow_succ', RingHom.mul_def, RingHom.comp_apply]
      set b := (σ ^ i) a
      have hb : ‖b‖ ≤ 1 := (ih2 a).le.trans ha
      have h1 : ‖σ b - b ^ l‖ ≤ ‖(l : K)‖ := hmax _ (hfr b hb)
      have hc : ‖a ^ l ^ i‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
      have h2 : ‖b ^ l - (a ^ l ^ i) ^ l‖ ≤ ‖(l : K)‖ := by
        have := norm_add_pow_sub_pow_le (a ^ l ^ i) (b - a ^ l ^ i) hc (by simpa using hb) (ih1 a ha) l
        simpa using this
      have : σ b - a ^ l ^ (i + 1) = (σ b - b ^ l) + (b ^ l - (a ^ l ^ i) ^ l) := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
    · rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, hiso, ih2]

/- English proof (translation)
Introduce `K _ _ _ l σ hU s A hA i h m`. Establish `hpr : l.Prime` using `hU.1`. Establish `hl1 : ‖(l : K)‖ < 1` using `hU.2.2.1`. Establish `hp0 : (l : K) ≠ 0` using `Nat.cast_ne_zero.mpr hpr.ne_zero`. Conclude with `Formalism.LT.FrobP.main l i hpr (σ ^ i) hp0 hl1 (isFrobLift_pow l σ hU i).1 A hA m`.
-/
theorem pow_frob_sub_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (s : Type) (A : MvPowerSeries s K), (∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1) → ∀ (i : ℕ) (h : l ^ i ≠ 0) (m : s →₀ ℕ), ‖MvPowerSeries.coeff m (A ^ (l ^ i) - MvPowerSeries.expand (l ^ i) h (MvPowerSeries.map (σ ^ i) A))‖ ≤ ‖(l : K)‖ := by
  intro K _ _ _ l σ hU s A hA i h m
  have hpr : l.Prime := hU.1
  have hl1 : ‖(l : K)‖ < 1 := hU.2.2.1
  have hp0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  exact Formalism.LT.FrobP.main l i hpr (σ ^ i) hp0 hl1 (isFrobLift_pow l σ hU i).1 A hA m

end GlobalTheory.Honda
