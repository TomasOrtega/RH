import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodOfComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAddValuationFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDeRhamFiltrationOfForallAinfLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormedAway
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffTensorAcrisWithFrobeniusGaloisStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.BanachModel

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ', mul_assoc, hm, ih, pow_succ', mul_assoc]`.
-/
theorem norm_pow_mul {p : ℕ} {N : Type} [NormedRing N] (hm : ∀ x : N, ‖(p : N) * x‖ = (p : ℝ)⁻¹ * ‖x‖)
    (n : ℕ) (x : N) : ‖(p : N) ^ n * x‖ = ((p : ℝ)⁻¹) ^ n * ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, hm, ih, pow_succ', mul_assoc]

/- English proof (translation)
Establish `: (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Check the signs of the components of the expression.
-/
theorem inv_pos' {p : ℕ} (hp : 2 ≤ p) : (0 : ℝ) < (p : ℝ)⁻¹ := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  positivity

/- English proof (translation)
Establish `: (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Conclude with `inv_lt_one_of_one_lt₀ (by linarith)`.
-/
theorem inv_lt_one' {p : ℕ} (hp : 2 ≤ p) : (p : ℝ)⁻¹ < 1 := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  exact inv_lt_one_of_one_lt₀ (by linarith)

/- English proof (translation)
Establish `h0` using `inv_pos' hp`. Establish `hlt` using `inv_lt_one' hp`. Establish `hp0 : (0 : ℝ) < p` using `inv_pos.mp h0`. Establish `hpL : (p : L) ≠ 0`. Introduce `h`.

Rewrite `hL` using `[h, norm_zero]`. Conclude with `h0.ne hL`. Establish `hLm : ∀ x : L, ‖(p : L) * x‖ = (p : ℝ)⁻¹ * ‖x‖` using `fun x => by rw [norm_mul, hL]`. Establish `key : ∀ y : L, ‖y‖ ≤ 1 → ‖c y‖ ≤ p * ‖y‖`. Introduce `y hy`.

Break down `eq_or_ne y 0 with rfl | hy0` into its components or cases. Simplify using the standard rewrite rules. Take `⟨n, hn1, hn2⟩` from `exists_nat_pow_near_of_lt_one (norm_pos_iff.mpr hy0) hy h0 hlt`. Establish `e : y = (p : L) ^ n * (y / (p : L) ^ n)` using `by field_simp`. Establish `hz : ‖y / (p : L) ^ n‖ ≤ 1`.

Rewrite using `[norm_div, norm_pow, hL]`. Conclude with `(div_le_one (pow_pos h0 n)).mpr hn2`. Establish `e2 : ‖c y‖ ≤ ((p : ℝ)⁻¹) ^ n`. Rewrite using `[e, map_mul, map_pow, map_natCast, norm_pow_mul hm]`. Conclude with `mul_le_of_le_one_right (pow_pos h0 n).le (h1 _ hz)`.

Use `e2.trans ?_` and prove the remaining obligations. Establish `: ((p : ℝ)⁻¹) ^ n = p * ((p : ℝ)⁻¹) ^ (n + 1)` using `by rw [pow_succ]; field_simp`. Rewrite using `[this]`. Conclude with `mul_le_mul_of_nonneg_left hn1.le hp0.le`. Take `⟨m, hm'⟩` from `exists_pow_lt_of_lt_one (show (0 : ℝ) < (‖x‖ + 1)⁻¹ by positivity) hlt`.

Establish `hx : ‖(p : L) ^ m * x‖ ≤ 1`. Rewrite using `[norm_pow_mul hLm]`. Combine the equalities or inequalities in the displayed calculation. Use `key _ hx` as an intermediate fact. Rewrite `this` using `[map_mul, map_pow, map_natCast, norm_pow_mul hm, norm_pow_mul hLm, mul_left_comm]`.

Conclude with `le_of_mul_le_mul_left this (pow_pos h0 m)`.
-/
theorem bounded {p : ℕ} (hp : 2 ≤ p) {L N : Type} [NormedField L] [NormedRing N]
    (hL : ‖(p : L)‖ = (p : ℝ)⁻¹) (hm : ∀ x : N, ‖(p : N) * x‖ = (p : ℝ)⁻¹ * ‖x‖) (c : L →+* N)
    (h1 : ∀ x, ‖x‖ ≤ 1 → ‖c x‖ ≤ 1) (x : L) : ‖c x‖ ≤ p * ‖x‖ := by
  have h0 := inv_pos' hp
  have hlt := inv_lt_one' hp
  have hp0 : (0 : ℝ) < p := inv_pos.mp h0
  have hpL : (p : L) ≠ 0 := by
    intro h; rw [h, norm_zero] at hL; exact h0.ne hL
  have hLm : ∀ x : L, ‖(p : L) * x‖ = (p : ℝ)⁻¹ * ‖x‖ := fun x => by rw [norm_mul, hL]
  have key : ∀ y : L, ‖y‖ ≤ 1 → ‖c y‖ ≤ p * ‖y‖ := by
    intro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one (norm_pos_iff.mpr hy0) hy h0 hlt
    have e : y = (p : L) ^ n * (y / (p : L) ^ n) := by field_simp
    have hz : ‖y / (p : L) ^ n‖ ≤ 1 := by
      rw [norm_div, norm_pow, hL]
      exact (div_le_one (pow_pos h0 n)).mpr hn2
    have e2 : ‖c y‖ ≤ ((p : ℝ)⁻¹) ^ n := by
      rw [e, map_mul, map_pow, map_natCast, norm_pow_mul hm]
      exact mul_le_of_le_one_right (pow_pos h0 n).le (h1 _ hz)
    refine e2.trans ?_
    have : ((p : ℝ)⁻¹) ^ n = p * ((p : ℝ)⁻¹) ^ (n + 1) := by rw [pow_succ]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hn1.le hp0.le
  obtain ⟨m, hm'⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (‖x‖ + 1)⁻¹ by positivity) hlt
  have hx : ‖(p : L) ^ m * x‖ ≤ 1 := by
    rw [norm_pow_mul hLm]
    calc _ ≤ (‖x‖ + 1)⁻¹ * (‖x‖ + 1) := by gcongr; linarith
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have := key _ hx
  rw [map_mul, map_pow, map_natCast, norm_pow_mul hm, norm_pow_mul hLm, mul_left_comm] at this
  exact le_of_mul_le_mul_left this (pow_pos h0 m)

section
variable {p : ℕ} {A N : Type} [CommRing A] [NormedCommRing N] [Algebra A N]

/- English proof (translation)
Use `continuous_of_continuousAt_zero f ?_` and prove the remaining obligations. Rewrite using `[Metric.continuousAt_iff]`. Introduce `ε hε`. Take `⟨r, hr⟩` from `exists_pow_lt_of_lt_one hε (inv_lt_one' hp)`. Use `⟨_, pow_pos (inv_pos' hp) r, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite `hx` using `[dist_zero_right]`. Take `⟨y, rfl⟩` from `(hn x r).mp hx.le`. Rewrite using `[map_zero, dist_zero_right]`. Use `lt_of_le_of_lt ((hn _ r).mpr ⟨f₀ y, ?_⟩) hr` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, map_natCast, hf]`.
-/
theorem continuous_of_alg (hp : 2 ≤ p)
    (hn : ∀ (x : N) (r : ℕ), ‖x‖ ≤ ((p : ℝ)⁻¹) ^ r ↔ ∃ y : A, x = (p : N) ^ r * algebraMap A N y)
    (f : N →+* N) (f₀ : A →+* A) (hf : ∀ y, f (algebraMap A N y) = algebraMap A N (f₀ y)) :
    Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one' hp)
  refine ⟨_, pow_pos (inv_pos' hp) r, fun x hx => ?_⟩
  rw [dist_zero_right] at hx
  obtain ⟨y, rfl⟩ := (hn x r).mp hx.le
  rw [map_zero, dist_zero_right]
  refine lt_of_le_of_lt ((hn _ r).mpr ⟨f₀ y, ?_⟩) hr
  rw [map_mul, map_pow, map_natCast, hf]

/- English proof (translation)
Establish `h0` using `inv_pos' hp`. Establish `hlt` using `inv_lt_one' hp`. Establish `hp0 : (0 : ℝ) < p` using `inv_pos.mp h0`. Use `set r : ℝ := ((p : ℝ)⁻¹) ^ ((d : ℝ)⁻¹) with hr`. Establish `hr0 : 0 < r` using `Real.rpow_pos_of_pos h0 _`.

Establish `hr1 : r < 1` using `Real.rpow_lt_one h0.le hlt (by positivity)`. Establish `hrd : r ^ d = (p : ℝ)⁻¹` using `Real.rpow_inv_natCast_pow h0.le hd.ne'`. Use `⟨p, r, hr0, hr1, fun k => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `h`. Establish `e : ‖algebraMap A N a ^ k‖ ≤ ((p : ℝ)⁻¹) ^ (k / d)`.

Use `(hn _ _).mpr ⟨y ^ (k / d) * a ^ (k % d), ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← Nat.div_add_mod k d, ← map_pow, pow_add, pow_mul, hy]`. Simplify using `only [map_mul, map_pow, map_natCast, mul_pow, mul_assoc]`. Use `e.trans ?_` and prove the remaining obligations. Establish `e2 : ((p : ℝ)⁻¹) ^ (k / d) = p * r ^ (d * (k / d) + d)`.

Rewrite using `[pow_add, pow_mul, hrd]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e2]`. Use `mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1.le ?_) hp0.le` and prove the remaining obligations. Use `Nat.div_add_mod k d` as an intermediate fact.

Use `Nat.mod_lt k hd` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem pow_decay (hp : 2 ≤ p)
    (hn : ∀ (x : N) (r : ℕ), ‖x‖ ≤ ((p : ℝ)⁻¹) ^ r ↔ ∃ y : A, x = (p : N) ^ r * algebraMap A N y)
    (a : A) (d : ℕ) (hd : 0 < d) (h : (p : A) ∣ a ^ d) :
    ∃ C r : ℝ, 0 < r ∧ r < 1 ∧ ∀ k : ℕ, ‖algebraMap A N a ^ k‖ ≤ C * r ^ k := by
  have h0 := inv_pos' hp
  have hlt := inv_lt_one' hp
  have hp0 : (0 : ℝ) < p := inv_pos.mp h0
  set r : ℝ := ((p : ℝ)⁻¹) ^ ((d : ℝ)⁻¹) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos h0 _
  have hr1 : r < 1 := Real.rpow_lt_one h0.le hlt (by positivity)
  have hrd : r ^ d = (p : ℝ)⁻¹ := Real.rpow_inv_natCast_pow h0.le hd.ne'
  refine ⟨p, r, hr0, hr1, fun k => ?_⟩
  obtain ⟨y, hy⟩ := h
  have e : ‖algebraMap A N a ^ k‖ ≤ ((p : ℝ)⁻¹) ^ (k / d) := by
    refine (hn _ _).mpr ⟨y ^ (k / d) * a ^ (k % d), ?_⟩
    conv_lhs => rw [← Nat.div_add_mod k d, ← map_pow, pow_add, pow_mul, hy]
    simp only [map_mul, map_pow, map_natCast, mul_pow, mul_assoc]
  refine e.trans ?_
  have e2 : ((p : ℝ)⁻¹) ^ (k / d) = p * r ^ (d * (k / d) + d) := by
    rw [pow_add, pow_mul, hrd]; field_simp
  rw [e2]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1.le ?_) hp0.le
  have := Nat.div_add_mod k d
  have := Nat.mod_lt k hd
  omega

/- English proof (translation)
Rewrite using `[← Filter.tendsto_add_atTop_iff_nat 1, Metric.tendsto_atTop]`. Introduce `ε hε`. Take `⟨r, hr⟩` from `exists_pow_lt_of_lt_one hε (inv_lt_one' hp)`. Take `⟨M, hM⟩` from `h r`. Use `⟨M, fun n hnM => ?_⟩` and prove the remaining obligations.

Take `⟨u, z, hu, hz⟩` from `hM n hnM`. Establish `hf : ((n.factorial : ℕ) : L) ≠ 0` using `Nat.cast_ne_zero.mpr n.factorial_ne_zero`. Establish `e : ∑ k ∈ Finset.range (n + 1), c ((-1 : L) ^ (k + 1) / (k : L)) * algebraMap A N μ ^ k = algebraMap A N u`. Establish `h1 : c ((n.factorial : L)⁻¹) * ((n.factorial : ℕ) : N) = 1`. Rewrite using `[← map_natCast c, ← map_mul, inv_mul_cancel₀ hf, map_one]`.

Establish `h2` using `congrArg (algebraMap A N) hu`. Rewrite `h2` using `[map_mul, map_natCast, map_sum]`. Rewrite using `[← one_mul (algebraMap A N u), ← h1, mul_assoc, h2, Finset.mul_sum, Finset.sum_range_succ']`. Simplify using `only [Nat.cast_zero, div_zero, map_zero, zero_mul, add_zero]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations.

Establish `hk' : k + 1 ∣ n.factorial` using `Nat.dvd_factorial (Nat.succ_pos k) (Finset.mem_range.mp hk)`. Establish `hk0 : ((k + 1 : ℕ) : L) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)`. Establish `h3 : (-1 : L) ^ (k + 1 + 1) / ((k + 1 : ℕ) : L) = (n.factorial : L)⁻¹ * ((-1) ^ k * ((n.factorial / (k + 1) : ℕ) : L))`. Rewrite using `[Nat.cast_div hk' hk0, pow_succ, pow_succ]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[h3]`. Simplify using `only [map_mul, map_pow, map_neg, map_one, map_natCast, mul_assoc]`. Rewrite using `[e, dist_comm, dist_eq_norm, ← map_sub, hz]`. Use `lt_of_le_of_lt ((hn _ r).mpr ⟨z, ?_⟩) hr` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, map_natCast]`.
-/
theorem log_tendsto (hp : 2 ≤ p)
    (hn : ∀ (x : N) (r : ℕ), ‖x‖ ≤ ((p : ℝ)⁻¹) ^ r ↔ ∃ y : A, x = (p : N) ^ r * algebraMap A N y)
    {L : Type} [Field L] [CharZero L] (c : L →+* N) (μ t : A)
    (h : ∀ r : ℕ, ∃ M : ℕ, ∀ n ≥ M, ∃ u z : A, ((n.factorial : ℕ) : A) * u =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : A) * μ ^ (k + 1) ∧
        t - u = (p : A) ^ r * z) :
    Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      c ((-1 : L) ^ (k + 1) / (k : L)) * algebraMap A N μ ^ k) Filter.atTop (nhds (algebraMap A N t)) := by
  rw [← Filter.tendsto_add_atTop_iff_nat 1, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one' hp)
  obtain ⟨M, hM⟩ := h r
  refine ⟨M, fun n hnM => ?_⟩
  obtain ⟨u, z, hu, hz⟩ := hM n hnM
  have hf : ((n.factorial : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have e : ∑ k ∈ Finset.range (n + 1), c ((-1 : L) ^ (k + 1) / (k : L)) * algebraMap A N μ ^ k
      = algebraMap A N u := by
    have h1 : c ((n.factorial : L)⁻¹) * ((n.factorial : ℕ) : N) = 1 := by
      rw [← map_natCast c, ← map_mul, inv_mul_cancel₀ hf, map_one]
    have h2 := congrArg (algebraMap A N) hu
    rw [map_mul, map_natCast, map_sum] at h2
    rw [← one_mul (algebraMap A N u), ← h1, mul_assoc, h2, Finset.mul_sum, Finset.sum_range_succ']
    simp only [Nat.cast_zero, div_zero, map_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k + 1 ∣ n.factorial := Nat.dvd_factorial (Nat.succ_pos k) (Finset.mem_range.mp hk)
    have hk0 : ((k + 1 : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    have h3 : (-1 : L) ^ (k + 1 + 1) / ((k + 1 : ℕ) : L) =
        (n.factorial : L)⁻¹ * ((-1) ^ k * ((n.factorial / (k + 1) : ℕ) : L)) := by
      rw [Nat.cast_div hk' hk0, pow_succ, pow_succ]
      field_simp
    rw [h3]
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, mul_assoc]
  rw [e, dist_comm, dist_eq_norm, ← map_sub, hz]
  refine lt_of_le_of_lt ((hn _ r).mpr ⟨z, ?_⟩) hr
  rw [map_mul, map_pow, map_natCast]

/- English proof (translation)
Use `isClosed_of_closure_subset fun x hx => h2 _ fun n => ?_` and prove the remaining obligations. Take `⟨x', hx', hd⟩` from `Metric.mem_closure_iff.mp hx _ (pow_pos (inv_pos' hp) (n + C))`. Rewrite `hd` using `[dist_eq_norm]`. Take `⟨y, hy⟩` from `(hn _ _).mp hd.le`. Establish `e : F x = F x' + (p : B) ^ n * ((p : B) ^ C * F (algebraMap A N y))`.

Rewrite using `[← mul_assoc, ← pow_add, ← map_natCast F, ← map_pow, ← map_mul, ← hy, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `add_mem (h1 n _ hx') (h3 n _ (hC y))`.
-/
theorem closed_of_lat (hp : 2 ≤ p)
    (hn : ∀ (x : N) (r : ℕ), ‖x‖ ≤ ((p : ℝ)⁻¹) ^ r ↔ ∃ y : A, x = (p : N) ^ r * algebraMap A N y)
    {B : Type} [CommRing B] (F : N →+* B) (S : Set B) (Λ : ℕ → AddSubgroup B)
    (h1 : ∀ n, ∀ b ∈ S, b ∈ Λ n) (h2 : ∀ b, (∀ n, b ∈ Λ n) → b ∈ S)
    (h3 : ∀ n, ∀ b ∈ Λ 0, (p : B) ^ n * b ∈ Λ n) (C : ℕ)
    (hC : ∀ y : A, (p : B) ^ C * F (algebraMap A N y) ∈ Λ 0) : IsClosed {x : N | F x ∈ S} := by
  refine isClosed_of_closure_subset fun x hx => h2 _ fun n => ?_
  obtain ⟨x', hx', hd⟩ := Metric.mem_closure_iff.mp hx _ (pow_pos (inv_pos' hp) (n + C))
  rw [dist_eq_norm] at hd
  obtain ⟨y, hy⟩ := (hn _ _).mp hd.le
  have e : F x = F x' + (p : B) ^ n * ((p : B) ^ C * F (algebraMap A N y)) := by
    rw [← mul_assoc, ← pow_add, ← map_natCast F, ← map_pow, ← map_mul, ← hy, map_sub]
    ring
  rw [e]
  exact add_mem (h1 n _ hx') (h3 n _ (hC y))

end

/- English proof (translation)
Express the relevant statement in the definitionally equal form `‖(LL.1.val (l : ↥LL.1))‖ = _`. Rewrite using `[map_natCast, ← map_natCast (algebraMap ℚ_[l] (Om l)) l, norm_algebraMap', Padic.norm_p]`.
-/
theorem norm_l {l : ℕ} [Fact l.Prime] (LL : FinExt l) : ‖(l : ↥LL.1)‖ = (l : ℝ)⁻¹ := by
  change ‖(LL.1.val (l : ↥LL.1))‖ = _
  rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Om l)) l, norm_algebraMap', Padic.norm_p]

/- English proof (translation)
Take `⟨m, hm'⟩` from `exists_pow_lt_of_lt_one (show (0 : ℝ) < (‖x‖ + 1)⁻¹ by positivity) (inv_lt_one' hp)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow, hL, mul_comm]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_scale {p : ℕ} (hp : 2 ≤ p) {L : Type} [NormedField L]
    (hL : ‖(p : L)‖ = (p : ℝ)⁻¹) (x : L) : ∃ m : ℕ, ‖x * (p : L) ^ m‖ ≤ 1 := by
  obtain ⟨m, hm'⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (‖x‖ + 1)⁻¹ by positivity) (inv_lt_one' hp)
  refine ⟨m, ?_⟩
  rw [norm_mul, norm_pow, hL, mul_comm]
  calc _ ≤ (‖x‖ + 1)⁻¹ * (‖x‖ + 1) := by gcongr; linarith
    _ = 1 := inv_mul_cancel₀ (by positivity)

/- English proof (translation)
Use `IsLocalization.Away.mk _ ?_ (fun x => ?_) (fun a b h => ⟨0, ?_⟩)` and prove the remaining obligations. Rewrite using `[map_natCast]`. Conclude with `h0.isUnit`. Take `⟨m, hx⟩` from `h x`. Conclude with `⟨m, ⟨_, hx⟩, by rw [map_natCast]; rfl⟩`.

Rewrite using `[Subtype.val_injective h]`.
-/
theorem away_sub {p : ℕ} {Z L : Type} [CommRing Z] [Field L] [Algebra Z L] (O : Subalgebra Z L)
    (h0 : (p : L) ≠ 0) (h : ∀ x : L, ∃ m : ℕ, x * (p : L) ^ m ∈ O) :
    IsLocalization.Away ((p : ℕ) : ↥O) L := by
  refine IsLocalization.Away.mk _ ?_ (fun x => ?_) (fun a b h => ⟨0, ?_⟩)
  · rw [map_natCast]
    exact h0.isUnit
  · obtain ⟨m, hx⟩ := h x
    exact ⟨m, ⟨_, hx⟩, by rw [map_natCast]; rfl⟩
  · rw [Subtype.val_injective h]

/- English proof (translation)
Use `away_sub (OL LL) (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) fun x => ?_` and prove the remaining obligations. Take `⟨m, hm⟩` from `exists_scale (Fact.out : l.Prime).two_le (norm_l LL) x`. Conclude with `⟨m, (GlobalTheory.Per.Val.mem_OL_iff LL _).mpr hm⟩`.
-/
theorem away_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    IsLocalization.Away ((l : ℕ) : ↥(OL LL)) ↥LL.1 := by
  refine away_sub (OL LL) (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) fun x => ?_
  obtain ⟨m, hm⟩ := exists_scale (Fact.out : l.Prime).two_le (norm_l LL) x
  exact ⟨m, (GlobalTheory.Per.Val.mem_OL_iff LL _).mpr hm⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsLocalization.Away.lift (p : A) (g := f) (by rwa [map_natCast]), fun y => IsLocalization.Away.lift_eq _ _ y⟩`.
-/
theorem exists_ext {p : ℕ} {A N B : Type} [CommRing A] [CommRing N] [CommRing B] [Algebra A N]
    [IsLocalization.Away (p : A) N] (f : A →+* B) (h : IsUnit (p : B)) :
    ∃ g : N →+* B, ∀ y, g (algebraMap A N y) = f y :=
  ⟨IsLocalization.Away.lift (p : A) (g := f) (by rwa [map_natCast]), fun y =>
    IsLocalization.Away.lift_eq _ _ y⟩

/- English proof (translation)
The claim follows from `RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (p : A)) (RingHom.ext h)) x`.
-/
theorem ext_away {p : ℕ} {A N B : Type} [CommRing A] [CommRing N] [CommRing B] [Algebra A N]
    [IsLocalization.Away (p : A) N] (f g : N →+* B)
    (h : ∀ y, f (algebraMap A N y) = g (algebraMap A N y)) (x : N) : f x = g x :=
  RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (p : A)) (RingHom.ext h)) x

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `l _ P AI T LL β hβ`. Establish `hp : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Take `⟨A, iA, b, κ, φ, γ, t, hG, ⟨h1, h2, h3, h4, h5, h6⟩, hnil, hlog, hbd⟩` from `GlobalTheory.T.exists_coeffTensorAcris_with_frobenius_galois l P AI T LL β hβ`. Take `⟨N, iN, cN, aN, hloc, hn, hm⟩` from `GlobalTheory.AwayNorm.exists_normed_away l A hp hG`. Use `haveI := away_OL LL`.

Establish `uN : IsUnit (l : N)`. Use `IsLocalization.Away.algebraMap_isUnit (S := N) (l : A)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `uB : IsUnit (l : ↥LL.1 ⊗[ℚ_[l]] P.R.B)`. Establish `: IsUnit (l : ℚ_[l])` using `(Nat.cast_ne_zero.mpr (by omega)).isUnit`.

Use `this.map (algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B))` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Take `⟨κ', hκ⟩` from `exists_ext (p := l) (N := N) κ uB`. Take `⟨φ', hφ⟩` from `exists_ext (p := l) (N := N) ((algebraMap A N).comp φ) uN`. Use `choose γ' hγ using fun g => exists_ext (p := l) (N := N) ((algebraMap A N).comp (γ g)) uN`.

Take `⟨c, hc⟩` from `exists_ext (p := l) (N := ↥LL.1) ((algebraMap A N).comp (b.comp (Algebra.TensorProduct.includeLeftRingHom : ↥(OL LL) →+* ↥(OL LL) ⊗[ℤ_[l]] Ainf l))) uN`. Establish `hc' : ∀ o : ↥(OL LL), c (algebraMap ↥(OL LL) ↥LL.1 o) = algebraMap A N (b (o ⊗ₜ[ℤ_[l]] (1 : Ainf l)))` using `hc`. Establish `hφ' : ∀ y, φ' (algebraMap A N y) = algebraMap A N (φ y)` using `hφ`. Establish `hγ' : ∀ g y, γ' g (algebraMap A N y) = algebraMap A N (γ g y)` using `hγ`. Establish `hone : ∀ y : A, ‖algebraMap A N y‖ ≤ 1` using `fun y => by`.

Simplify using `using (hn (algebraMap A N y) 0).mpr ⟨y, by simp⟩`. Use `⟨N, iN, cN, c, (algebraMap A N).comp b, κ', φ', γ', algebraMap A N t, ⟨fun y => ?_, fun o w => ?_, fun x => ?_, fun g o w => ?_, fun g x => ?_, ?_⟩, ⟨l, bounded hp (norm_l LL) hm c fun x hx => ?_⟩, fun y => hone _, fun o => (hc' o).symm, fun x => ?_, ⟨continuous_of_alg hp hn φ' φ …` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, hκ, h1]`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, hφ', h2]`. Use `ext_away (p := l) (A := A) (κ'.comp φ') ((Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB).toRingHom.comp κ') (fun y => ?_) x` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, hφ', hκ, hκ, h3]`. Both sides reduce to the same expression. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, hγ', h4]`. Use `ext_away (p := l) (A := A) (κ'.comp (γ' g)) ((Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ g).toAlgHom).toRingHom.comp κ') (fun y => ?_) x` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, hγ', hκ, hκ, h5]`.

Both sides reduce to the same expression. Rewrite using `[hκ, h6]`. Use `hc' ⟨x, (GlobalTheory.Per.Val.mem_OL_iff LL x).mpr hx⟩` as an intermediate fact. Conclude with `(congrArg norm this).trans_le (hone _)`. Use `ext_away (p := l) (A := ↥(OL LL)) (κ'.comp c) (Algebra.TensorProduct.includeLeftRingHom : ↥LL.1 →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (fun o => ?_) x` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply, hc', hκ, h1, hβ, map_one]`. Both sides reduce to the same expression. Use `ext_away (p := l) (A := ↥(OL LL)) (φ'.comp c) c (fun o => ?_) x` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, hc', hφ', h2, map_one]`. Use `ext_away (p := l) (A := ↥(OL LL)) ((γ' g).comp c) c (fun o => ?_) x` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply, hc', hγ', h4, map_one]`. Take `⟨d, hd, hdv⟩` from `hnil s`. Conclude with `pow_decay hp hn _ d hd hdv`. Simplify using `only [logS, PowerSeries.coeff_mk]`. Conclude with `log_tendsto hp hn c _ t hlog`.

Take `⟨C, hC⟩` from `hbd ι m`. Use `closed_of_lat hp hn ((Algebra.TensorProduct.productMap ι P.ιB).toRingHom.comp κ') (GlobalTheory.ExpImage.FilB P (m : ℤ)) (fun n => GlobalTheory.ExpImage.Lat AI m n) (fun n b hb => GlobalTheory.ExpImage.FilB_le_Lat AI hb) (fun b hb => GlobalTheory.ExpImage.mem_FilB_of_forall_Lat l …` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, hκ]`. Conclude with `hC y`.
-/
theorem exists_banach_model : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B), IsBeta AI β → ∃ (N : Type) (_ : NormedCommRing N) (_ : CompleteSpace N) (c : ↥LL.1 →+* N) (b : RA LL →+* N) (κ : N →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (φ : N →+* N) (γ : GQ l → (N →+* N)) (t : N), ((∀ y, κ (b y) = β y) ∧ (∀ o w, φ (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) ∧ (∀ x, κ (φ x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB (κ x)) ∧ (∀ g o w, γ g (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] AI.actW g w)) ∧ (∀ g x, κ (γ g x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ g).toAlgHom (κ x)) ∧ κ t = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] P.tB) ∧ (∃ C : ℝ, ∀ x : ↥LL.1, ‖c x‖ ≤ C * ‖x‖) ∧ (∀ y, ‖b y‖ ≤ 1) ∧ (∀ o : ↥(OL LL), b (o ⊗ₜ[ℤ_[l]] (1 : Ainf l)) = c (o : ↥LL.1)) ∧ (∀ x, κ (c x) = x ⊗ₜ[ℚ_[l]] (1 : P.R.B)) ∧ (Continuous φ ∧ ∀ x, φ (c x) = c x) ∧ (∀ g, Continuous (γ g) ∧ ∀ x, γ g (c x) = c x) ∧ (∀ s : ℕ, ∃ C r : ℝ, 0 < r ∧ r < 1 ∧ ∀ k : ℕ, ‖b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) ^ k‖ ≤ C * r ^ k) ∧ Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, c (PowerSeries.coeff k (logS LL)) * b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.μ) ^ k) Filter.atTop (nhds t) ∧ ∀ (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (m : ℕ), IsClosed {x : N | Algebra.TensorProduct.productMap ι P.ιB (κ x) ∈ GlobalTheory.ExpImage.FilB P (m : ℤ)} := by
  intro l _ P AI T LL β hβ
  have hp : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨A, iA, b, κ, φ, γ, t, hG, ⟨h1, h2, h3, h4, h5, h6⟩, hnil, hlog, hbd⟩ :=
    GlobalTheory.T.exists_coeffTensorAcris_with_frobenius_galois l P AI T LL β hβ
  obtain ⟨N, iN, cN, aN, hloc, hn, hm⟩ := GlobalTheory.AwayNorm.exists_normed_away l A hp hG
  haveI := away_OL LL
  have uN : IsUnit (l : N) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := N) (l : A)
    rwa [map_natCast] at this
  have uB : IsUnit (l : ↥LL.1 ⊗[ℚ_[l]] P.R.B) := by
    have : IsUnit (l : ℚ_[l]) := (Nat.cast_ne_zero.mpr (by omega)).isUnit
    have := this.map (algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B))
    rwa [map_natCast] at this
  obtain ⟨κ', hκ⟩ := exists_ext (p := l) (N := N) κ uB
  obtain ⟨φ', hφ⟩ := exists_ext (p := l) (N := N) ((algebraMap A N).comp φ) uN
  choose γ' hγ using fun g => exists_ext (p := l) (N := N) ((algebraMap A N).comp (γ g)) uN
  obtain ⟨c, hc⟩ := exists_ext (p := l) (N := ↥LL.1) ((algebraMap A N).comp (b.comp
    (Algebra.TensorProduct.includeLeftRingHom : ↥(OL LL) →+* ↥(OL LL) ⊗[ℤ_[l]] Ainf l))) uN
  have hc' : ∀ o : ↥(OL LL), c (algebraMap ↥(OL LL) ↥LL.1 o) =
      algebraMap A N (b (o ⊗ₜ[ℤ_[l]] (1 : Ainf l))) := hc
  have hφ' : ∀ y, φ' (algebraMap A N y) = algebraMap A N (φ y) := hφ
  have hγ' : ∀ g y, γ' g (algebraMap A N y) = algebraMap A N (γ g y) := hγ
  have hone : ∀ y : A, ‖algebraMap A N y‖ ≤ 1 := fun y => by
    simpa using (hn (algebraMap A N y) 0).mpr ⟨y, by simp⟩
  refine ⟨N, iN, cN, c, (algebraMap A N).comp b, κ', φ', γ', algebraMap A N t,
    ⟨fun y => ?_, fun o w => ?_, fun x => ?_, fun g o w => ?_, fun g x => ?_, ?_⟩,
    ⟨l, bounded hp (norm_l LL) hm c fun x hx => ?_⟩, fun y => hone _, fun o => (hc' o).symm, fun x => ?_,
    ⟨continuous_of_alg hp hn φ' φ hφ', fun x => ?_⟩,
    fun g => ⟨continuous_of_alg hp hn (γ' g) (γ g) (hγ' g), fun x => ?_⟩, fun s => ?_, ?_, fun ι m => ?_⟩
  · rw [RingHom.comp_apply, hκ, h1]
  · rw [RingHom.comp_apply, RingHom.comp_apply, hφ', h2]
  · refine ext_away (p := l) (A := A) (κ'.comp φ')
      ((Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB).toRingHom.comp κ') (fun y => ?_) x
    rw [RingHom.comp_apply, RingHom.comp_apply, hφ', hκ, hκ, h3]
    rfl
  · rw [RingHom.comp_apply, RingHom.comp_apply, hγ', h4]
  · refine ext_away (p := l) (A := A) (κ'.comp (γ' g))
      ((Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ g).toAlgHom).toRingHom.comp κ')
      (fun y => ?_) x
    rw [RingHom.comp_apply, RingHom.comp_apply, hγ', hκ, hκ, h5]
    rfl
  · rw [hκ, h6]
  · have := hc' ⟨x, (GlobalTheory.Per.Val.mem_OL_iff LL x).mpr hx⟩
    exact (congrArg norm this).trans_le (hone _)
  · refine ext_away (p := l) (A := ↥(OL LL)) (κ'.comp c)
      (Algebra.TensorProduct.includeLeftRingHom : ↥LL.1 →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (fun o => ?_) x
    rw [RingHom.comp_apply, hc', hκ, h1, hβ, map_one]
    rfl
  · refine ext_away (p := l) (A := ↥(OL LL)) (φ'.comp c) c (fun o => ?_) x
    rw [RingHom.comp_apply, hc', hφ', h2, map_one]
  · refine ext_away (p := l) (A := ↥(OL LL)) ((γ' g).comp c) c (fun o => ?_) x
    rw [RingHom.comp_apply, hc', hγ', h4, map_one]
  · obtain ⟨d, hd, hdv⟩ := hnil s
    exact pow_decay hp hn _ d hd hdv
  · simp only [logS, PowerSeries.coeff_mk]
    exact log_tendsto hp hn c _ t hlog
  · obtain ⟨C, hC⟩ := hbd ι m
    refine closed_of_lat hp hn ((Algebra.TensorProduct.productMap ι P.ιB).toRingHom.comp κ')
      (GlobalTheory.ExpImage.FilB P (m : ℤ)) (fun n => GlobalTheory.ExpImage.Lat AI m n)
      (fun n b hb => GlobalTheory.ExpImage.FilB_le_Lat AI hb)
      (fun b hb => GlobalTheory.ExpImage.mem_FilB_of_forall_Lat l P AI T m b hb)
      (fun n b hb => (GlobalTheory.ExpImage.pow_mul_mem_Lat_iff AI (n := 0)).mpr hb) C fun y => ?_
    rw [RingHom.comp_apply, hκ]
    exact hC y

end GlobalTheory.HWL.BanachModel
