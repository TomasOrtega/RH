import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [h0]`. Consider the case `succ n ih`. Establish `h` using `congrArg (coeff n) hd`. Rewrite `h` using `[PowerSeries.coeff_derivative, ih]`.

Establish `hn : ((n : S) + 1) = algebraMap ℚ S ((n : ℚ) + 1)` using `by simp`. Rewrite `h` using `[hn]`. Establish `hu : coeff (n + 1) E = coeff (n + 1) E * algebraMap ℚ S ((n : ℚ) + 1) * algebraMap ℚ S (1 / ((n : ℚ) + 1))`. Rewrite using `[mul_assoc, ← map_mul, mul_one_div_cancel (by positivity), map_one, mul_one]`. Rewrite using `[hu, h, ← map_mul, Nat.factorial_succ]`.

Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem expRescale_coeff (S : Type) [CommRing S] [Algebra ℚ S] (E : PowerSeries S)
    (h0 : constantCoeff E = 1) (hd : derivative S E = E) (n : ℕ) :
    coeff n E = algebraMap ℚ S (1 / (n.factorial : ℚ)) := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have h := congrArg (coeff n) hd
    rw [PowerSeries.coeff_derivative, ih] at h
    have hn : ((n : S) + 1) = algebraMap ℚ S ((n : ℚ) + 1) := by simp
    rw [hn] at h
    have hu : coeff (n + 1) E =
        coeff (n + 1) E * algebraMap ℚ S ((n : ℚ) + 1) * algebraMap ℚ S (1 / ((n : ℚ) + 1)) := by
      rw [mul_assoc, ← map_mul, mul_one_div_cancel (by positivity), map_one, mul_one]
    rw [hu, h, ← map_mul, Nat.factorial_succ]
    congr 1
    push_cast
    field_simp

/- English proof (translation)
Introduce `S _ _ E h0 hd`. Establish `hE : E = PowerSeries.exp S`. Use extensionality with `n`. Rewrite using `[expRescale_coeff S E h0 hd n, PowerSeries.coeff_exp]`. Use `⟨hE, fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[hE, PowerSeries.exp_pow_eq_rescale_exp]`.
-/
theorem expRescale : ExpRescaleStatement := by
  intro S _ _ E h0 hd
  have hE : E = PowerSeries.exp S := by
    ext n
    rw [expRescale_coeff S E h0 hd n, PowerSeries.coeff_exp]
  refine ⟨hE, fun a => ?_⟩
  rw [hE, PowerSeries.exp_pow_eq_rescale_exp]

end LevelStatements.Lv
