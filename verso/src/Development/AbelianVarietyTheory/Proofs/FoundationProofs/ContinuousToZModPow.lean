import Mathlib

namespace GlobalTheory.ContinuousZModPow

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Establish `hpos : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ))` using `zpow_pos (by exact_mod_cast hl.out.pos) _`. Establish `hev : ∀ᶠ y in nhds x, PadicInt.toZModPow n y = PadicInt.toZModPow n x` using `by filter_upwards [Metric.closedBall_mem_nhds x hpos] with y hy`. Rewrite `hy` using `[Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]`. Conclude with `hy`.

Conclude with `tendsto_nhds_of_eventually_eq hev`.
-/
theorem continuous_toZModPow (l : ℕ) [hl : Fact (Nat.Prime l)] (n : ℕ) :
    Continuous (⇑(PadicInt.toZModPow n) : ℤ_[l] → ZMod (l ^ n)) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast hl.out.pos) _
  have hev : ∀ᶠ y in nhds x, PadicInt.toZModPow n y = PadicInt.toZModPow n x := by
    filter_upwards [Metric.closedBall_mem_nhds x hpos] with y hy
    rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
      ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hy
    exact hy
  exact tendsto_nhds_of_eventually_eq hev

/- English proof (translation)
Introduce `l _ n`. Conclude with `continuous_toZModPow l n`.
-/
theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (n : ℕ),
    Continuous (⇑(PadicInt.toZModPow n) : ℤ_[l] → ZMod (l ^ n)) := by
  intro l _ n
  exact continuous_toZModPow l n

end GlobalTheory.ContinuousZModPow
