import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.Calc

/- English proof (translation)
Take `⟨m, hm, ha⟩` from `ha`. Take `⟨n, hn, hb⟩` from `hb`. Use `⟨m * n, Nat.mul_pos hm hn, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, ← pow_mul, mul_comm m n, pow_mul b, hb, ← pow_mul]`.
-/
theorem ph_mul {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, ← pow_mul, mul_comm m n,
    pow_mul b, hb, ← pow_mul]

/- English proof (translation)
Take `⟨m, hm, ha⟩` from `ha`. Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_pow, ha, norm_inv, Complex.ofReal_inv, inv_pow]`.
-/
theorem ph_inv {a : ℂ} (ha : Ph a) : Ph a⁻¹ := by
  obtain ⟨m, hm, ha⟩ := ha
  refine ⟨m, hm, ?_⟩
  rw [inv_pow, ha, norm_inv, Complex.ofReal_inv, inv_pow]

/- English proof (translation)
Take `⟨m, hm, ha⟩` from `ha`. Conclude with `⟨m, hm, by rw [ha, h]; simp⟩`.
-/
theorem isMu_of_ph {a : ℂ} (ha : Ph a) (h : ‖a‖ = 1) : IsMu a := by
  obtain ⟨m, hm, ha⟩ := ha
  exact ⟨m, hm, by rw [ha, h]; simp⟩

/- English proof (translation)
Establish `h` using `ph_mul hab (ph_inv hb)`. Rewrite `h` using `[mul_assoc, mul_inv_cancel₀ hb0, mul_one]`. Then use the resulting hypothesis.
-/
theorem ph_cancel {a b : ℂ} (hb0 : b ≠ 0) (hb : Ph b) (hab : Ph (a * b)) : Ph a := by
  have h := ph_mul hab (ph_inv hb)
  rwa [mul_assoc, mul_inv_cancel₀ hb0, mul_one] at h

open Matrix Complex in
open scoped ComplexConjugate Real in

/- English proof (translation)
Use `⟨fun a b ha hb => ha.mul hb, fun a ha => ⟨?_, ha.inv⟩, fun t => ?_, fun a ha => ?_, fun a ha h1 => ?_, fun a b ha hb => ⟨?_, ?_, ?_⟩, fun a k hk => ⟨?_, ?_⟩, fun q => ?_, fun a b hb0 hb hab => ?_⟩` and prove the remaining obligations. Take `⟨m, hm, h⟩` from `ha`. Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, h, Complex.norm_conj, map_pow, Complex.conj_ofReal]`. Use `⟨2, two_pos, ?_⟩` and prove the remaining obligations.

Rewrite using `[Complex.norm_real, Real.norm_eq_abs, ← ofReal_pow, ← ofReal_pow, sq_abs]`. Take `⟨m, hm, h⟩` from `ha`. Establish `hn : ‖a‖ = 1`. Establish `h' : ‖a‖ ^ m = 1` using `by rw [← norm_pow, h, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg a) hm.ne').1 h'`.

Conclude with `⟨⟨m, hm, by rw [h, hn, ofReal_one, one_pow]⟩, hn⟩`. Take `⟨m, hm, h⟩` from `ha`. Conclude with `⟨m, hm, by rw [h, h1, ofReal_one, one_pow]⟩`. Take `⟨m, hm, h⟩` from `ha`. Take `⟨n, hn, h'⟩` from `hb`.

Use `⟨m * n, Nat.mul_pos hm hn, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, pow_mul, h, pow_mul', h', one_pow, one_pow, one_mul]`. Take `⟨m, hm, h⟩` from `ha`. Conclude with `⟨m, hm, by rw [inv_pow, h, inv_one]⟩`. Take `⟨m, hm, h⟩` from `ha`.

Conclude with `⟨m, hm, by rw [← map_pow, h, map_one]⟩`. Introduce and unpack `⟨m, hm, h⟩`. Conclude with `⟨k * m, Nat.mul_pos hk hm, by rw [pow_mul, h]⟩`. Introduce and unpack `⟨m, hm, h⟩`. Use `⟨k * m, Nat.mul_pos hk hm, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_mul, h, norm_pow, ofReal_pow, ← pow_mul]`. Use `⟨2 * q.den, by positivity, ?_⟩` and prove the remaining obligations. Rewrite using `[← Complex.exp_nat_mul, Complex.exp_eq_one_iff]`. Use `⟨q.num, ?_⟩` and prove the remaining obligations. Establish `hq : (q : ℂ) = q.num / q.den` using `by exact_mod_cast (Rat.num_div_den q).symm`.

Establish `hd : (q.den : ℂ) ≠ 0` using `by exact_mod_cast q.den_nz`. Rewrite using `[hq]`. Clear the denominators using the available nonvanishing facts. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `hab.mul hb.inv` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_right₀ hb0]`. Then use the resulting hypothesis.
-/
theorem _root_.GlobalTheory.Phase.Calc.calculus : (∀ a b : ℂ, _root_.GlobalTheory.Phase.Ph a → _root_.GlobalTheory.Phase.Ph b → _root_.GlobalTheory.Phase.Ph (a * b)) ∧ (∀ a : ℂ, _root_.GlobalTheory.Phase.Ph a → _root_.GlobalTheory.Phase.Ph (conj a) ∧ _root_.GlobalTheory.Phase.Ph a⁻¹) ∧
    (∀ t : ℝ, _root_.GlobalTheory.Phase.Ph (t : ℂ)) ∧ (∀ a : ℂ, _root_.GlobalTheory.Phase.IsMu a → _root_.GlobalTheory.Phase.Ph a ∧ ‖a‖ = 1) ∧ (∀ a : ℂ, _root_.GlobalTheory.Phase.Ph a → ‖a‖ = 1 → _root_.GlobalTheory.Phase.IsMu a) ∧
    (∀ a b : ℂ, _root_.GlobalTheory.Phase.IsMu a → _root_.GlobalTheory.Phase.IsMu b → _root_.GlobalTheory.Phase.IsMu (a * b) ∧ _root_.GlobalTheory.Phase.IsMu a⁻¹ ∧ _root_.GlobalTheory.Phase.IsMu (conj a)) ∧
    (∀ (a : ℂ) (k : ℕ), 0 < k → (_root_.GlobalTheory.Phase.IsMu (a ^ k) → _root_.GlobalTheory.Phase.IsMu a) ∧ (_root_.GlobalTheory.Phase.Ph (a ^ k) → _root_.GlobalTheory.Phase.Ph a)) ∧
    (∀ q : ℚ, _root_.GlobalTheory.Phase.IsMu (cexp (π * I * (q : ℂ)))) ∧ ∀ a b : ℂ, b ≠ 0 → _root_.GlobalTheory.Phase.Ph b → _root_.GlobalTheory.Phase.Ph (a * b) → _root_.GlobalTheory.Phase.Ph a := by
  refine ⟨fun a b ha hb => ha.mul hb, fun a ha => ⟨?_, ha.inv⟩, fun t => ?_, fun a ha => ?_,
    fun a ha h1 => ?_, fun a b ha hb => ⟨?_, ?_, ?_⟩, fun a k hk => ⟨?_, ?_⟩, fun q => ?_,
    fun a b hb0 hb hab => ?_⟩
  · obtain ⟨m, hm, h⟩ := ha
    refine ⟨m, hm, ?_⟩
    rw [← map_pow, h, Complex.norm_conj, map_pow, Complex.conj_ofReal]
  · refine ⟨2, two_pos, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, ← ofReal_pow, ← ofReal_pow, sq_abs]
  · obtain ⟨m, hm, h⟩ := ha
    have hn : ‖a‖ = 1 := by
      have h' : ‖a‖ ^ m = 1 := by rw [← norm_pow, h, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) hm.ne').1 h'
    exact ⟨⟨m, hm, by rw [h, hn, ofReal_one, one_pow]⟩, hn⟩
  · obtain ⟨m, hm, h⟩ := ha
    exact ⟨m, hm, by rw [h, h1, ofReal_one, one_pow]⟩
  · obtain ⟨m, hm, h⟩ := ha
    obtain ⟨n, hn, h'⟩ := hb
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [mul_pow, pow_mul, h, pow_mul', h', one_pow, one_pow, one_mul]
  · obtain ⟨m, hm, h⟩ := ha
    exact ⟨m, hm, by rw [inv_pow, h, inv_one]⟩
  · obtain ⟨m, hm, h⟩ := ha
    exact ⟨m, hm, by rw [← map_pow, h, map_one]⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨k * m, Nat.mul_pos hk hm, by rw [pow_mul, h]⟩
  · rintro ⟨m, hm, h⟩
    refine ⟨k * m, Nat.mul_pos hk hm, ?_⟩
    rw [pow_mul, h, norm_pow, ofReal_pow, ← pow_mul]
  · refine ⟨2 * q.den, by positivity, ?_⟩
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨q.num, ?_⟩
    have hq : (q : ℂ) = q.num / q.den := by exact_mod_cast (Rat.num_div_den q).symm
    have hd : (q.den : ℂ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [hq]
    field_simp
    push_cast
    ring
  · have := hab.mul hb.inv
    rwa [mul_inv_cancel_right₀ hb0] at this

end GlobalTheory.Phase.Calc
