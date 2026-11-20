import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
import Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPosConstLagrangeCondition
import Formalism.GaussValuationBounds.NokLemmaCVal

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs

open Formalism.BasicNotions

/- English proof (translation)
Introduce `O _ _ _ l _ ϖ e h1 h2 h3 ε u hε hu b y t hb hy hmem`. Conclude with `Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ramified_coefficient_chain_bounds.2.2.2.2.2.2.1 O l ϖ e h1 h2 h3 ε u hε hu b y t hb hy hmem`.
-/
theorem power_series_dvr_factorisation : PowerSeriesDVRFactorisation := by
  intro O _ _ _ l _ ϖ e h1 h2 h3 ε u hε hu b y t hb hy hmem
  exact Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ramified_coefficient_chain_bounds.2.2.2.2.2.2.1 O l ϖ e h1 h2 h3 ε u hε hu b y t hb hy hmem

/- English proof (translation)
The claim follows from `power_series_dvr_factorisation`.
-/
theorem content_bound_clause (D : D7) : adm17 D := power_series_dvr_factorisation

section Alg

variable {R : Type} [CommRing R]

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Take `⟨r, s, rfl⟩` from `Ideal.mem_span_pair.1 hx`. Conclude with `Ideal.mem_span_pair.2 ⟨r * c, s, by ring⟩`.
-/
theorem span_pair_mono_left {a a' f x : R} (h : a' ∣ a) (hx : x ∈ Ideal.span {a, f}) :
    x ∈ Ideal.span {a', f} := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨r, s, rfl⟩ := Ideal.mem_span_pair.1 hx
  exact Ideal.mem_span_pair.2 ⟨r * c, s, by ring⟩

/- English proof (translation)
Establish `hQ` using `Formalism.KernelCokernelLengths.length_theorems_all_hold.2.2.2.2.2.2.2.2.2.2.1`. Take `⟨k, rfl⟩ : ∃ k, l = k + 1` from `⟨l - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Use `set q : R := π₀ + ((k + 1 : ℕ) : R) with hq`. Establish `hc' : c + η + M ≤ k * y + y`.

Establish `: (k + 1) * y = k * y + y` using `by ring`. Use linear arithmetic over natural numbers and integers. Rewrite using `[mul_pow, ← pow_mul]`. Distinguish the cases in `hM : M ≤ y`. Distinguish the cases in `hη : η ≤ k * y`.

Use `Ideal.mem_span_pair.2 ⟨0, π₀ ^ (y - M) * q ^ (k * y - η), ?_⟩` and prove the remaining obligations. Establish `e1 : π₀ ^ y = π₀ ^ (y - M) * π₀ ^ M` using `by rw [← pow_add]; congr 1; omega`. Establish `e2 : q ^ (k * y) = q ^ (k * y - η) * q ^ η` using `by rw [← pow_add]; congr 1; omega`. Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h` using `hQ R q (-((k + 1 : ℕ) : R)) (η - k * y) (y - M - (η - k * y) + 1)`. Establish `e0 : q + -((k + 1 : ℕ) : R) = π₀` using `by rw [hq]; ring`. Establish `e1 : η - k * y + (y - M - (η - k * y) + 1) - 1 = y - M` using `by omega`. Rewrite `h` using `[e0, e1]`. Take `⟨r, s, hrs⟩` from `Ideal.mem_span_pair.1 h`.

Establish `e2 : π₀ ^ y = π₀ ^ (y - M) * π₀ ^ M` using `by rw [← pow_add]; congr 1; omega`. Establish `e3 : q ^ η = q ^ (η - k * y) * q ^ (k * y)` using `by rw [← pow_add]; congr 1; omega`. Take `⟨j, hj⟩ : ∃ j, y - M - (η - k * y) + 1 = c + j` from `⟨y - M - (η - k * y) + 1 - c, by omega⟩`. Use `Ideal.mem_span_pair.2 ⟨s * (-1) ^ (c + j) * ((k + 1 : ℕ) : R) ^ j * π₀ ^ M * q ^ (k * y), r, ?_⟩` and prove the remaining obligations. Rewrite using `[e2, ← hrs, e3, hj, neg_pow ((k + 1 : ℕ) : R) (c + j), pow_add ((k + 1 : ℕ) : R) c j]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h` using `hQ R π₀ ((k + 1 : ℕ) : R) (M - y) (k * y - η - (M - y) + 1)`. Establish `e1 : M - y + (k * y - η - (M - y) + 1) - 1 = k * y - η` using `by omega`. Rewrite `h` using `[e1, ← hq]`. Take `⟨r, s, hrs⟩` from `Ideal.mem_span_pair.1 h`.

Establish `e2 : π₀ ^ M = π₀ ^ (M - y) * π₀ ^ y` using `by rw [← pow_add]; congr 1; omega`. Establish `e3 : q ^ (k * y) = q ^ (k * y - η) * q ^ η` using `by rw [← pow_add]; congr 1; omega`. Take `⟨j, hj⟩ : ∃ j, k * y - η - (M - y) + 1 = c + j` from `⟨k * y - η - (M - y) + 1 - c, by omega⟩`. Use `Ideal.mem_span_pair.2 ⟨s * ((k + 1 : ℕ) : R) ^ j * π₀ ^ y * q ^ η, r, ?_⟩` and prove the remaining obligations. Rewrite using `[e3, ← hrs, e2, hj, pow_add ((k + 1 : ℕ) : R) c j]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem rem_M (l : ℕ) (hl : 1 ≤ l) (π₀ : R) (y M η c : ℕ) (hc : c + η + M ≤ l * y) :
    (π₀ * (π₀ + (l : R)) ^ (l - 1)) ^ y ∈
      Ideal.span {(l : R) ^ c, π₀ ^ M * (π₀ + (l : R)) ^ η} := by
  have hQ := Formalism.KernelCokernelLengths.length_theorems_all_hold.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set q : R := π₀ + ((k + 1 : ℕ) : R) with hq
  have hc' : c + η + M ≤ k * y + y := by
    have : (k + 1) * y = k * y + y := by ring
    omega
  rw [mul_pow, ← pow_mul]
  by_cases hM : M ≤ y
  · by_cases hη : η ≤ k * y
    ·
      refine Ideal.mem_span_pair.2 ⟨0, π₀ ^ (y - M) * q ^ (k * y - η), ?_⟩
      have e1 : π₀ ^ y = π₀ ^ (y - M) * π₀ ^ M := by rw [← pow_add]; congr 1; omega
      have e2 : q ^ (k * y) = q ^ (k * y - η) * q ^ η := by rw [← pow_add]; congr 1; omega
      rw [e1, e2]; ring
    ·
      have h := hQ R q (-((k + 1 : ℕ) : R)) (η - k * y) (y - M - (η - k * y) + 1)
      have e0 : q + -((k + 1 : ℕ) : R) = π₀ := by rw [hq]; ring
      have e1 : η - k * y + (y - M - (η - k * y) + 1) - 1 = y - M := by omega
      rw [e0, e1] at h
      obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.1 h
      have e2 : π₀ ^ y = π₀ ^ (y - M) * π₀ ^ M := by rw [← pow_add]; congr 1; omega
      have e3 : q ^ η = q ^ (η - k * y) * q ^ (k * y) := by rw [← pow_add]; congr 1; omega
      obtain ⟨j, hj⟩ : ∃ j, y - M - (η - k * y) + 1 = c + j :=
        ⟨y - M - (η - k * y) + 1 - c, by omega⟩
      refine Ideal.mem_span_pair.2
        ⟨s * (-1) ^ (c + j) * ((k + 1 : ℕ) : R) ^ j * π₀ ^ M * q ^ (k * y), r, ?_⟩
      rw [e2, ← hrs, e3, hj, neg_pow ((k + 1 : ℕ) : R) (c + j), pow_add ((k + 1 : ℕ) : R) c j]
      ring
  ·
    have h := hQ R π₀ ((k + 1 : ℕ) : R) (M - y) (k * y - η - (M - y) + 1)
    have e1 : M - y + (k * y - η - (M - y) + 1) - 1 = k * y - η := by omega
    rw [e1, ← hq] at h
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.1 h
    have e2 : π₀ ^ M = π₀ ^ (M - y) * π₀ ^ y := by rw [← pow_add]; congr 1; omega
    have e3 : q ^ (k * y) = q ^ (k * y - η) * q ^ η := by rw [← pow_add]; congr 1; omega
    obtain ⟨j, hj⟩ : ∃ j, k * y - η - (M - y) + 1 = c + j :=
      ⟨k * y - η - (M - y) + 1 - c, by omega⟩
    refine Ideal.mem_span_pair.2 ⟨s * ((k + 1 : ℕ) : R) ^ j * π₀ ^ y * q ^ η, r, ?_⟩
    rw [e3, ← hrs, e2, hj, pow_add ((k + 1 : ℕ) : R) c j]
    ring

/- English proof (translation)
Establish `hP` using `Formalism.KernelCokernelLengths.length_theorems_all_hold.2.2.2.2.2.2.2.2.1`. Establish `e1 : π₀ ^ y = π₀ * π₀ ^ (y - 1)` using `by rw [← pow_succ']; congr 1; omega`. Rewrite using `[mul_pow, mul_pow, ← pow_mul, ← pow_mul, e1]`. Break down `Nat.eq_zero_or_pos X with rfl | hX` into its components or cases. Conclude with `Ideal.mem_span_pair.2 ⟨0, π₀ ^ (y - 1) * q ^ ((l - 1) * y) * (u * q ^ l + (l : R) * ε) ^ ((l - 1) * y), by ring⟩`.

Take `⟨α, β, hab, -⟩` from `hP R l u ε q ((l - 1) * y) X hl hX`. Take `⟨j, hj⟩ : ∃ j, (l - 1) * y - (X - 1) / l = c + j` from `⟨(l - 1) * y - (X - 1) / l - c, by omega⟩`. Rewrite using `[hab, hj, pow_add]`. Conclude with `Ideal.mem_span_pair.2 ⟨π₀ * π₀ ^ (y - 1) * q ^ ((l - 1) * y) * (l : R) ^ j * α, π₀ ^ (y - 1) * q ^ ((l - 1) * y) * β, by ring⟩`.
-/
theorem rem_2 (l : ℕ) (hl : 1 ≤ l) (π₀ q u ε : R) (y X c : ℕ) (hy : 1 ≤ y)
    (hc : c + (X - 1) / l ≤ (l - 1) * y) :
    (π₀ * q ^ (l - 1) * (u * q ^ l + (l : R) * ε) ^ (l - 1)) ^ y ∈
      Ideal.span {(l : R) ^ c, π₀ * q ^ X} := by
  have hP := Formalism.KernelCokernelLengths.length_theorems_all_hold.2.2.2.2.2.2.2.2.1
  have e1 : π₀ ^ y = π₀ * π₀ ^ (y - 1) := by rw [← pow_succ']; congr 1; omega
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, e1]
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · exact Ideal.mem_span_pair.2 ⟨0, π₀ ^ (y - 1) * q ^ ((l - 1) * y) *
      (u * q ^ l + (l : R) * ε) ^ ((l - 1) * y), by ring⟩
  · obtain ⟨α, β, hab, -⟩ := hP R l u ε q ((l - 1) * y) X hl hX
    obtain ⟨j, hj⟩ : ∃ j, (l - 1) * y - (X - 1) / l = c + j :=
      ⟨(l - 1) * y - (X - 1) / l - c, by omega⟩
    rw [hab, hj, pow_add]
    exact Ideal.mem_span_pair.2 ⟨π₀ * π₀ ^ (y - 1) * q ^ ((l - 1) * y) * (l : R) ^ j * α,
      π₀ ^ (y - 1) * q ^ ((l - 1) * y) * β, by ring⟩

end Alg

/- English proof (translation)
Establish `h1 : ϖ ^ t ∣ (l : O) ^ c`. Establish `: ϖ ^ (e * c) ∣ (l : O) ^ c`. Rewrite using `[pow_mul]`. Conclude with `pow_dvd_pow_of_dvd h.symm.dvd c`. Conclude with `(pow_dvd_pow ϖ ht).trans this`.

Establish `h2` using `(PowerSeries.C (R := O)).map_dvd h1`. Simplify using `using h2`.
-/
theorem C_pow_dvd {O : Type} [CommRing O] {l : ℕ} {ϖ : O} {e t c : ℕ}
    (h : Associated (l : O) (ϖ ^ e)) (ht : t ≤ e * c) :
    PowerSeries.C (ϖ ^ t) ∣ ((l : ℕ) : PowerSeries O) ^ c := by
  have h1 : ϖ ^ t ∣ (l : O) ^ c := by
    have : ϖ ^ (e * c) ∣ (l : O) ^ c := by
      rw [pow_mul]; exact pow_dvd_pow_of_dvd h.symm.dvd c
    exact (pow_dvd_pow ϖ ht).trans this
  have h2 := (PowerSeries.C (R := O)).map_dvd h1
  simpa using h2

/- English proof (translation)
Establish `h1 : max 0 x ≤ (c : ℝ)` using `max_le (Nat.cast_nonneg c) hx`. Establish `h2 : (t : ℝ) ≤ (e : ℝ) * c` using `ht.trans (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg e))`. Conclude with `h2` after adjusting the coercions.
-/
theorem nat_le_of_real {e t c : ℕ} {x : ℝ} (ht : (t : ℝ) ≤ e * max 0 x) (hx : x ≤ c) :
    t ≤ e * c := by
  have h1 : max 0 x ≤ (c : ℝ) := max_le (Nat.cast_nonneg c) hx
  have h2 : (t : ℝ) ≤ (e : ℝ) * c := ht.trans (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg e))
  exact_mod_cast h2

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `O _ _ _ l hlp ϖ e _ _ hass u₁ u₂ u ε _ _ _ _ y X M η t`. Establish `hl : 1 ≤ l` using `hlp.out.one_lt.le`. Establish `hC : (PowerSeries.C (l : O) : PowerSeries O) = ((l : ℕ) : PowerSeries O)` using `by simp`. Rewrite using `[hC]`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `ht`. Establish `htc : t ≤ e * (l * y - X)` using `nat_le_of_real ht (by`. Establish `: ((l * y : ℕ) : ℝ) ≤ ((l * y - X : ℕ) : ℝ) + X`. Conclude with `(by omega : l * y ≤ (l * y - X) + X)` after adjusting the coercions.

Move the coercions through the operations in `at this ⊢`. Use the proof step `linarith)`. Establish `e1 : (u₁ * PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ (l - 1)) ^ y = u₁ ^ y * (PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ (l - 1)) ^ y`. Rewrite using `[← mul_pow]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1]`. Distinguish the cases in `hle : X ≤ l * y`. Establish `hR` using `Formalism.TruncatedSeriesCounting.X.pX_conditions.2.2.1 (PowerSeries O) l hl PowerSeries.X y X (l * y - X) (by omega)`. Conclude with `Ideal.mul_mem_left _ _ (span_pair_mono_left (C_pow_dvd hass htc) hR)`. Establish `h0 : l * y - X = 0` using `by omega`.

Establish `ht0 : t = 0` using `by rw [h0] at htc; omega`. Substitute `ht0` using the available equality. Establish `: (1 : PowerSeries O) ∈ Ideal.span {PowerSeries.C (ϖ ^ 0), PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ X}` using `Ideal.subset_span (by simp)`. Rewrite using `[(Ideal.eq_top_iff_one _).2 this]`. Discharge the goal by the elementary cases of `trivial`.

Introduce `ht`. Establish `hR` using `rem_M (R := PowerSeries O) l hl PowerSeries.X y M η (l * y - η - M)`. Establish `htc : t ≤ e * (l * y - η - M)` using `nat_le_of_real ht (by`. Establish `: ((l * y : ℕ) : ℝ) ≤ ((l * y - η - M : ℕ) : ℝ) + η + M`. Conclude with `(by omega : l * y ≤ (l * y - η - M) + η + M)` after adjusting the coercions.

Move the coercions through the operations in `at this ⊢`. Use the proof step `linarith)`. Establish `e1 : (u₁ * PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ (l - 1)) ^ y = u₁ ^ y * (PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ (l - 1)) ^ y`. Rewrite using `[← mul_pow]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1]`. Distinguish the cases in `hle : η + M ≤ l * y`. Conclude with `Ideal.mul_mem_left _ _ (span_pair_mono_left (C_pow_dvd hass htc) (hR (by omega)))`. Establish `h0 : l * y - η - M = 0` using `by omega`. Establish `ht0 : t = 0` using `by rw [h0] at htc; omega`.

Substitute `ht0` using the available equality. Establish `: (1 : PowerSeries O) ∈ Ideal.span {PowerSeries.C (ϖ ^ 0), PowerSeries.X ^ M * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ η}` using `Ideal.subset_span (by simp)`. Rewrite using `[(Ideal.eq_top_iff_one _).2 this]`. Discharge the goal by the elementary cases of `trivial`. Introduce `ht set c : ℕ := (l - 1) * y - (X - 1) / l with hcdef`.

Establish `htc : t ≤ e * c` using `nat_le_of_real ht (by`. Establish `hlpos : (0 : ℝ) < l` using `by exact_mod_cast hl`. Establish `h1 : (l - 1) * y ≤ c + (X - 1) / l` using `by omega`. Establish `h2 : (((X - 1) / l : ℕ) : ℝ) ≤ (X : ℝ) / l`. Establish `: (((X - 1) / l : ℕ) : ℝ) ≤ ((X - 1 : ℕ) : ℝ) / l` using `Nat.cast_div_le`.

Establish `h3 : ((X - 1 : ℕ) : ℝ) ≤ X` using `by exact_mod_cast Nat.sub_le X 1`. Conclude with `this.trans (div_le_div_of_nonneg_right h3 hlpos.le)`. Establish `h4 : (((l - 1) * y : ℕ) : ℝ) ≤ (c : ℝ) + (((X - 1) / l : ℕ) : ℝ)` using `by exact_mod_cast h1`. Establish `h5 : (((l - 1) * y : ℕ) : ℝ) = ((l : ℝ) - 1) * y`. Rewrite using `[Nat.cast_mul, Nat.cast_sub hl, Nat.cast_one]`.

Use the proof step `linarith)`. Establish `e1 : (u₂ * PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ (l - 1) * (u * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ l + ((l : ℕ) : PowerSeries O) * ε) ^ (l - 1)) ^ y = u₂ ^ y * (PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ (l - 1) * (u * (PowerS …`. Rewrite using `[← mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`.

Break down `Nat.eq_zero_or_pos y with rfl | hy` into its components or cases. Establish `ht0 : t = 0`. Establish `: c = 0` using `by simp [hcdef]`. Rewrite `htc` using `[this]`. Use linear arithmetic over natural numbers and integers.

Substitute `ht0` using the available equality. Establish `: (1 : PowerSeries O) ∈ Ideal.span {PowerSeries.C (ϖ ^ 0), PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ X}` using `Ideal.subset_span (by simp)`. Rewrite using `[(Ideal.eq_top_iff_one _).2 this]`. Discharge the goal by the elementary cases of `trivial`. Distinguish the cases in `hle : (X - 1) / l ≤ (l - 1) * y`.

Conclude with `Ideal.mul_mem_left _ _ (span_pair_mono_left (C_pow_dvd hass htc) (rem_2 l hl PowerSeries.X _ u ε y X c hy (by omega)))`. Establish `ht0 : t = 0`. Establish `: c = 0` using `by omega`. Rewrite `htc` using `[this]`. Use linear arithmetic over natural numbers and integers.

Substitute `ht0` using the available equality. Establish `: (1 : PowerSeries O) ∈ Ideal.span {PowerSeries.C (ϖ ^ 0), PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ X}` using `Ideal.subset_span (by simp)`. Rewrite using `[(Ideal.eq_top_iff_one _).2 this]`. Discharge the goal by the elementary cases of `trivial`. Introduce `l y X M η hl`.

Conclude with `Formalism.TruncatedSeriesCounting.X.pX_conditions.2.1 l (by omega) y X M η`.
-/
theorem TToolAlg_holds : TToolAlg := by
  refine ⟨?_, ?_⟩
  · intro O _ _ _ l hlp ϖ e _ _ hass u₁ u₂ u ε _ _ _ _ y X M η t
    have hl : 1 ≤ l := hlp.out.one_lt.le
    have hC : (PowerSeries.C (l : O) : PowerSeries O) = ((l : ℕ) : PowerSeries O) := by simp
    rw [hC]
    refine ⟨?_, ?_, ?_⟩
    · intro ht
      have htc : t ≤ e * (l * y - X) := nat_le_of_real ht (by
        have : ((l * y : ℕ) : ℝ) ≤ ((l * y - X : ℕ) : ℝ) + X := by
          exact_mod_cast (by omega : l * y ≤ (l * y - X) + X)
        push_cast at this ⊢; linarith)
      have e1 : (u₁ * PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ (l - 1)) ^ y =
          u₁ ^ y * (PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ (l - 1)) ^ y := by
        rw [← mul_pow]; ring
      rw [e1]
      by_cases hle : X ≤ l * y
      · have hR := Formalism.TruncatedSeriesCounting.X.pX_conditions.2.2.1 (PowerSeries O) l hl PowerSeries.X y X (l * y - X)
          (by omega)
        exact Ideal.mul_mem_left _ _ (span_pair_mono_left (C_pow_dvd hass htc) hR)
      · have h0 : l * y - X = 0 := by omega
        have ht0 : t = 0 := by rw [h0] at htc; omega
        subst ht0
        have : (1 : PowerSeries O) ∈ Ideal.span {PowerSeries.C (ϖ ^ 0),
            PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ X} :=
          Ideal.subset_span (by simp)
        rw [(Ideal.eq_top_iff_one _).2 this]; trivial
    · intro ht
      have hR := rem_M (R := PowerSeries O) l hl PowerSeries.X y M η (l * y - η - M)
      have htc : t ≤ e * (l * y - η - M) := nat_le_of_real ht (by
        have : ((l * y : ℕ) : ℝ) ≤ ((l * y - η - M : ℕ) : ℝ) + η + M := by
          exact_mod_cast (by omega : l * y ≤ (l * y - η - M) + η + M)
        push_cast at this ⊢; linarith)
      have e1 : (u₁ * PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ (l - 1)) ^ y =
          u₁ ^ y * (PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ (l - 1)) ^ y := by
        rw [← mul_pow]; ring
      rw [e1]
      by_cases hle : η + M ≤ l * y
      · exact Ideal.mul_mem_left _ _ (span_pair_mono_left (C_pow_dvd hass htc) (hR (by omega)))
      · have h0 : l * y - η - M = 0 := by omega
        have ht0 : t = 0 := by rw [h0] at htc; omega
        subst ht0
        have : (1 : PowerSeries O) ∈ Ideal.span {PowerSeries.C (ϖ ^ 0),
            PowerSeries.X ^ M * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ η} :=
          Ideal.subset_span (by simp)
        rw [(Ideal.eq_top_iff_one _).2 this]; trivial
    · intro ht
      set c : ℕ := (l - 1) * y - (X - 1) / l with hcdef
      have htc : t ≤ e * c := nat_le_of_real ht (by
        have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
        have h1 : (l - 1) * y ≤ c + (X - 1) / l := by omega
        have h2 : (((X - 1) / l : ℕ) : ℝ) ≤ (X : ℝ) / l := by
          have : (((X - 1) / l : ℕ) : ℝ) ≤ ((X - 1 : ℕ) : ℝ) / l := Nat.cast_div_le
          have h3 : ((X - 1 : ℕ) : ℝ) ≤ X := by exact_mod_cast Nat.sub_le X 1
          exact this.trans (div_le_div_of_nonneg_right h3 hlpos.le)
        have h4 : (((l - 1) * y : ℕ) : ℝ) ≤ (c : ℝ) + (((X - 1) / l : ℕ) : ℝ) := by exact_mod_cast h1
        have h5 : (((l - 1) * y : ℕ) : ℝ) = ((l : ℝ) - 1) * y := by
          rw [Nat.cast_mul, Nat.cast_sub hl, Nat.cast_one]
        linarith)
      have e1 : (u₂ * PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ (l - 1) *
          (u * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ l + ((l : ℕ) : PowerSeries O) * ε)
            ^ (l - 1)) ^ y =
          u₂ ^ y * (PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ (l - 1) *
          (u * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ l + ((l : ℕ) : PowerSeries O) * ε)
            ^ (l - 1)) ^ y := by
        rw [← mul_pow]; ring
      rw [e1]
      rcases Nat.eq_zero_or_pos y with rfl | hy
      · have ht0 : t = 0 := by
          have : c = 0 := by simp [hcdef]
          rw [this] at htc; omega
        subst ht0
        have : (1 : PowerSeries O) ∈ Ideal.span {PowerSeries.C (ϖ ^ 0),
            PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ X} :=
          Ideal.subset_span (by simp)
        rw [(Ideal.eq_top_iff_one _).2 this]; trivial
      · by_cases hle : (X - 1) / l ≤ (l - 1) * y
        · exact Ideal.mul_mem_left _ _ (span_pair_mono_left (C_pow_dvd hass htc)
            (rem_2 l hl PowerSeries.X _ u ε y X c hy (by omega)))
        · have ht0 : t = 0 := by
            have : c = 0 := by omega
            rw [this] at htc; omega
          subst ht0
          have : (1 : PowerSeries O) ∈ Ideal.span {PowerSeries.C (ϖ ^ 0),
              PowerSeries.X * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ X} :=
            Ideal.subset_span (by simp)
          rw [(Ideal.eq_top_iff_one _).2 this]; trivial
  · intro l y X M η hl
    exact Formalism.TruncatedSeriesCounting.X.pX_conditions.2.1 l (by omega) y X M η

section Core

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

/- English proof (translation)
Take `⟨r, s, rfl⟩` from `Ideal.mem_span_pair.1 hx`. Introduce `y hy`. Rewrite using `[add_smul, mul_smul, mul_smul]`. Conclude with `(Formalism.MainNotions.LiftingTheory.Nimg W F i).add_mem ((Formalism.MainNotions.LiftingTheory.Nimg W F i).smul_mem r (ha y hy)) ((Formalism.MainNotions.LiftingTheory.Nimg W F i).smul_mem s (hb y hy))`.
-/
theorem kills_of_mem_span (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (i : ZMod n) {a b x : LetA O n} (ha : Formalism.MainNotions.LiftingTheory.Kills W F i a)
    (hb : Formalism.MainNotions.LiftingTheory.Kills W F i b) (hx : x ∈ Ideal.span {a, b}) : Formalism.MainNotions.LiftingTheory.Kills W F i x := by
  obtain ⟨r, s, rfl⟩ := Ideal.mem_span_pair.1 hx
  intro y hy
  rw [add_smul, mul_smul, mul_smul]
  exact (Formalism.MainNotions.LiftingTheory.Nimg W F i).add_mem ((Formalism.MainNotions.LiftingTheory.Nimg W F i).smul_mem r (ha y hy))
    ((Formalism.MainNotions.LiftingTheory.Nimg W F i).smul_mem s (hb y hy))

/- English proof (translation)
Establish `hl' : (3 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `h0 : 0 ≤ (H' : ℝ) * l / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l ((H' : ℝ) + 1)`. Establish `h1 : 0 ≤ Real.logb l ((H' : ℝ) + 1)` using `Real.logb_nonneg (by linarith) (by have : (0 : ℝ) ≤ H' := Nat.cast_nonneg H'; linarith)`. Establish `h2 : 0 ≤ (H' : ℝ) * l / ((l : ℝ) - 1) ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1` using `Formalism.TruncatedSeriesCounting.X.pX_conditions.1 l hl H' H (Formalism.MainNotions.LiftingTheory.eWA l H' : ℝ) hH (Nat.floor_le h0)`. Use `Nat.le_floor ?_` and prove the remaining obligations. Rewrite using `[Formalism.MainNotions.RamifiedCoefficientChains.aR_eq, Nat.cast_sub (Nat.le_add_right_of_le (Nat.le_add_left 1 _)), Nat.cast_add]`. Simplify using `using h1`.
-/
theorem q_exp_le_floor (l H' H : ℕ) (hl : 3 ≤ l) (hH : H' ≤ H) :
    H' / (l - 1) + 1 + Formalism.MainNotions.LiftingTheory.eWA l H' - 1 ≤ ⌊Formalism.MainNotions.RamifiedCoefficientChains.aR l H⌋₊ := by
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have h0 : 0 ≤ (H' : ℝ) * l / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l ((H' : ℝ) + 1) := by
    have h1 : 0 ≤ Real.logb l ((H' : ℝ) + 1) :=
      Real.logb_nonneg (by linarith) (by have : (0 : ℝ) ≤ H' := Nat.cast_nonneg H'; linarith)
    have h2 : 0 ≤ (H' : ℝ) * l / ((l : ℝ) - 1) ^ 2 := by positivity
    linarith
  have h1 := Formalism.TruncatedSeriesCounting.X.pX_conditions.1 l hl H' H (Formalism.MainNotions.LiftingTheory.eWA l H' : ℝ) hH (Nat.floor_le h0)
  refine Nat.le_floor ?_
  rw [Formalism.MainNotions.RamifiedCoefficientChains.aR_eq, Nat.cast_sub (Nat.le_add_right_of_le (Nat.le_add_left 1 _)), Nat.cast_add]
  simpa using h1

/- English proof (translation)
Establish `hQ` using `Formalism.KernelCokernelLengths.length_theorems_all_hold.2.2.2.2.2.2.2.2.2.2.1 (LetA O n) W.π₀ ((PD.p : ℕ) : LetA O n) A r`. Establish `h1 : Formalism.MainNotions.LiftingTheory.Kills W F i (Formalism.MainNotions.LiftingTheory.qp W ^ (A + r - 1))` using `kills_of_mem_span W F i ha hb hQ`. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hN`. Introduce `y hy`. Rewrite using `[pow_add, mul_comm, mul_smul]`.

Conclude with `(Formalism.MainNotions.LiftingTheory.Nimg W F i).smul_mem _ (h1 y hy)`.
-/
theorem kills_q (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (i : ZMod n) (A r N : ℕ) (hN : A + r - 1 ≤ N) (ha : Formalism.MainNotions.LiftingTheory.Kills W F i (W.π₀ ^ A))
    (hb : Formalism.MainNotions.LiftingTheory.Kills W F i (Formalism.MainNotions.LiftingTheory.lp W r)) :
    Formalism.MainNotions.LiftingTheory.Kills W F i (Formalism.MainNotions.LiftingTheory.qp W ^ N) := by
  have hQ := Formalism.KernelCokernelLengths.length_theorems_all_hold.2.2.2.2.2.2.2.2.2.2.1 (LetA O n) W.π₀ ((PD.p : ℕ) : LetA O n) A r
  have h1 : Formalism.MainNotions.LiftingTheory.Kills W F i (Formalism.MainNotions.LiftingTheory.qp W ^ (A + r - 1)) :=
    kills_of_mem_span W F i ha hb hQ
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
  intro y hy
  rw [pow_add, mul_comm, mul_smul]
  exact (Formalism.MainNotions.LiftingTheory.Nimg W F i).smul_mem _ (h1 y hy)

def boxM (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) : ℕ :=
  if (i.val + d) % 2 = 0 then b i + S else η

def boxh (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) : ℕ :=
  if (i.val + d) % 2 = 0 then η else b i + S

/- English proof (translation)
Introduce `i τ hτ a ha`. Establish `h` using `hS.2.2.2.2.2.2.1 i τ hτ a ha`. Establish `hη : 2 * ⌊Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η)⌋₊ + η + 1 ≤ b i` using `Formalism.MainNotions.RamifiedCoefficientChains.floor_a_le _ _ _ _ (by have := hS.2.1; omega) (hS.2.2.2.2.2.2.2.2.1 i)`. Unfold `Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at h`. Unfold `boxM boxh`.

Distinguish the cases in `hi : (i.val + d) % 2 = 0`. Simplify using `only [hi, if_true] at h ⊢`. Break down `h with h | h` into its components or cases. Take `⟨h1, h2⟩` from `h`. Conclude with `⟨h1, by omega⟩`.

Take `⟨h1, h2⟩` from `h`. Conclude with `⟨by push_cast at h1 ⊢; omega, h2⟩`. Simplify using `only [hi, if_false] at h ⊢`. Break down `h with h | h` into its components or cases. Take `⟨h1, h2⟩` from `h`.

Conclude with `⟨by omega, h2⟩`. Take `⟨h1, h2⟩` from `h`. Conclude with `⟨h1, by push_cast at h2 ⊢; omega⟩`.
-/
theorem jumpsLet_box [NeZero n] (W : LocWach PD LL O v n) {d : ℕ} {T₁ T₂ : LocLat G Qp LL O}
    {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ}
    (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) :
    Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ (boxM d b S η) (boxh d b S η) := by
  intro i τ hτ a ha
  have h := hS.2.2.2.2.2.2.1 i τ hτ a ha
  have hη : 2 * ⌊Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η)⌋₊ + η + 1 ≤ b i :=
    Formalism.MainNotions.RamifiedCoefficientChains.floor_a_le _ _ _ _ (by have := hS.2.1; omega) (hS.2.2.2.2.2.2.2.2.1 i)
  unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at h
  unfold boxM boxh
  by_cases hi : (i.val + d) % 2 = 0
  · simp only [hi, if_true] at h ⊢
    rcases h with h | h
    · obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega⟩
    · obtain ⟨h1, h2⟩ := h
      exact ⟨by push_cast at h1 ⊢; omega, h2⟩
  · simp only [hi, if_false] at h ⊢
    rcases h with h | h
    · obtain ⟨h1, h2⟩ := h
      exact ⟨by omega, h2⟩
    · obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by push_cast at h2 ⊢; omega⟩

/- English proof (translation)
Use `Finset.sup_le fun k _ => ?_` and prove the remaining obligations. Establish `h` using `Formalism.MainNotions.RamifiedCoefficientChains.add_le_hpar n b S (k : ZMod n)`. Unfold `boxM boxh`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem Hmax_box [NeZero n] (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) :
    Formalism.MainNotions.LiftingTheory.Hmax n (boxM d b S η) (boxh d b S η) ≤ Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η := by
  refine Finset.sup_le fun k _ => ?_
  have h := Formalism.MainNotions.RamifiedCoefficientChains.add_le_hpar n b S (k : ZMod n)
  unfold boxM boxh
  split_ifs <;> omega

def QToolOpen [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ)
    (Mi hi : ZMod n → ℕ),
    Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m → Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi →
    (∀ i : ZMod n,
      Formalism.MainNotions.LiftingTheory.Kills W F i (W.π₀ ^ (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi / (PD.p - 1) + 1))) ∧
    ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (G := G) (Qp := Qp) (LL := LL) (O := O) ι π → IsCrys PD Y.ρ →
      ∀ i : ZMod n,
        Formalism.MainNotions.LiftingTheory.Kills W π i (W.π₀ ^ (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi / (PD.p - 1) + 1)) ∧
        Formalism.MainNotions.LiftingTheory.Kills W π i (Formalism.MainNotions.LiftingTheory.lp W (Formalism.MainNotions.LiftingTheory.eWA PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi)))

/- English proof (translation)
Introduce `d T₁ T₂ F b S η m Mi hi hS hJ`. Establish `hbox` using `jumpsLet_box W hS`. Take `⟨h1, h2⟩` from `h d T₁ T₂ F b S η m Mi hi hS hJ`. Take `⟨h1', h2'⟩` from `h d T₁ T₂ F b S η m _ _ hS hbox`. Establish `hCA` using `hS.1`.

Establish `h11` using `hS.2.1`. Establish `hSur` using `hS.2.2.2.2.2.1`. Establish `hN : Formalism.MainNotions.LiftingTheory.Hmax n (boxM d b S η) (boxh d b S η) / (PD.p - 1) + 1 + Formalism.MainNotions.LiftingTheory.eWA PD.p (Formalism.MainNotions.LiftingTheory.Hmax n (boxM d b S η) (boxh d b S η)) - 1 ≤ ⌈Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p …` using `(q_exp_le_floor PD.p _ _ (by omega) (Hmax_box d b S η)).trans (Nat.floor_le_ceil _)`. Use `⟨fun i => ⟨h1 i, hWA hCA T₁ T₂ F Mi hi hSur hJ i, kills_q W F i _ _ _ hN (h1' i) (hWA hCA T₁ T₂ F _ _ hSur hbox i)⟩, fun Y ι π hses hY i => ⟨(h2 Y ι π hses hY i).1, (h2 Y ι π hses hY i).2, kills_q W π i _ _ _ hN (h2' Y ι π hses hY i).1 (h2' Y ι π hses hY i).2⟩⟩` and prove the remaining obligations.
-/
theorem QTool_of_open [NeZero n] (W : LocWach PD LL O v n) (hWA : Formalism.MainNotions.LiftingTheory.coreWA W)
    (h : QToolOpen W) : QTool W := by
  intro d T₁ T₂ F b S η m Mi hi hS hJ
  have hbox := jumpsLet_box W hS
  obtain ⟨h1, h2⟩ := h d T₁ T₂ F b S η m Mi hi hS hJ
  obtain ⟨h1', h2'⟩ := h d T₁ T₂ F b S η m _ _ hS hbox
  have hCA := hS.1
  have h11 := hS.2.1
  have hSur := hS.2.2.2.2.2.1
  have hN : Formalism.MainNotions.LiftingTheory.Hmax n (boxM d b S η) (boxh d b S η) / (PD.p - 1) + 1 +
      Formalism.MainNotions.LiftingTheory.eWA PD.p (Formalism.MainNotions.LiftingTheory.Hmax n (boxM d b S η) (boxh d b S η)) - 1 ≤
      ⌈Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η)⌉₊ :=
    (q_exp_le_floor PD.p _ _ (by omega) (Hmax_box d b S η)).trans (Nat.floor_le_ceil _)
  refine ⟨fun i => ⟨h1 i, hWA hCA T₁ T₂ F Mi hi hSur hJ i,
    kills_q W F i _ _ _ hN (h1' i) (hWA hCA T₁ T₂ F _ _ hSur hbox i)⟩,
    fun Y ι π hses hY i => ⟨(h2 Y ι π hses hY i).1, (h2 Y ι π hses hY i).2,
      kills_q W π i _ _ _ hN (h2' Y ι π hses hY i).1 (h2' Y ι π hses hY i).2⟩⟩

end Core

/- English proof (translation)
Introduce `l _ K LL hg _`. Conclude with `QTool_of_open _ (h6.2.2.1 l K 1 LL hg) (h l K LL hg)`.
-/
theorem level_clause_of_open_tool' (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h6 : adm6 D HW F)
    (h : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], QToolOpen ((HW l).W K 1 LL hg)) :
    adm13 D HW F Cm := by
  intro l _ K LL hg _
  exact QTool_of_open _ (h6.2.2.1 l K 1 LL hg) (h l K LL hg)

/- English proof (translation)
Assemble the required witnesses or components as `⟨TToolAlg_holds, h⟩`.
-/
theorem truncation_clause_of_tools (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))],
      TTool1 ((HW l).W K 1 LL hg) ∧ TTool2 ((HW l).W K 1 LL hg)) : adm15 D HW F Cm :=
  ⟨TToolAlg_holds, h⟩

/- English proof (translation)
The claim follows from `Formalism.MainNotions.RamifiedCoefficientChains.exists_pos_const_Lagrange_condition D HW F`.
-/
theorem exists_pos_const_Lagrange_condition (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : adm5 D HW F := Formalism.MainNotions.RamifiedCoefficientChains.exists_pos_const_Lagrange_condition D HW F

/- English proof (translation)
The claim follows from `Formalism.MainNotions.RamifiedCoefficientChains.Theorem_C_range_of_open D HW F _ C CA CB CK h10 h`.
-/
theorem Theorem_C_of_open (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h10 : adm10 D HW F CA CB CK)
    (h : Formalism.MainNotions.RamifiedCoefficientChains.openKR D HW F (fun m => 1 ≤ m) C) : aux₃ D HW F C :=
  Formalism.MainNotions.RamifiedCoefficientChains.Theorem_C_range_of_open D HW F _ C CA CB CK h10 h

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions.Loc

section RNum

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)

/- English proof (translation)
Establish `h1 : 0 ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l]))` using `(P.v_O LL _).2 ((OL LL).algebraMap_mem _)`. Establish `h2 : 0 ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]))` using `(P.v_O LL _).2 ((OL LL).algebraMap_mem _)`. Establish `h3 : P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) + P.v LL (algebraMap ℤ_[l] ↥LL.1 ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) = 0`. Rewrite using `[← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]`. Conclude with `((add_eq_zero_iff_of_nonneg h1 h2).1 h3).1`.
-/
theorem v_unit (u : ℤ_[l]ˣ) : P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) = 0 := by
  have h1 : 0 ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) :=
    (P.v_O LL _).2 ((OL LL).algebraMap_mem _)
  have h2 : 0 ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) :=
    (P.v_O LL _).2 ((OL LL).algebraMap_mem _)
  have h3 : P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) +
      P.v LL (algebraMap ℤ_[l] ↥LL.1 ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) = 0 := by
    rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
  exact ((add_eq_zero_iff_of_nonneg h1 h2).1 h3).1

/- English proof (translation)
Use `conv_lhs => rw [PadicInt.unitCoeff_spec hx]`. Rewrite using `[map_mul, AddValuation.map_mul, v_unit, zero_add, map_pow, map_natCast]`. Conclude with `Formalism.MainNotions.RamifiedCoefficientChains.v_pow_nat (P.v LL) (P.v_l LL) _`.
-/
theorem v_padicInt (x : ℤ_[l]) (hx : x ≠ 0) :
    P.v LL (algebraMap ℤ_[l] ↥LL.1 x) = ((x.valuation : ℕ) : WithTop ℚ) := by
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [map_mul, AddValuation.map_mul, v_unit, zero_add, map_pow, map_natCast]
  exact Formalism.MainNotions.RamifiedCoefficientChains.v_pow_nat (P.v LL) (P.v_l LL) _

end RNum

section RDef

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def RToolNum (W : LocWach PD LL O v n) : Prop :=
  cR W 0 = 0 ∧ ∀ j j' : ℤ, j ≠ j' →
    v (cR W j - cR W j') = ((padicValInt PD.p (j - j') : ℚ) : WithTop ℚ)

def RToolMod [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W →
    ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ →
    ∀ (i : ZMod n) (y y' : ℤ) (Bd : ℕ), y' < y →
      (∀ τ, Formalism.MainNotions.LiftingTheory.Over W τ i → JumpsInV PD T.ρ τ (Set.Icc (-(Bd : ℤ)) Bd)) →
      (∀ x, InQN W T i y x → InQN W T i y (dOp W T x)) ∧
      (∀ x, InQN W T i y' x → InQN W T i y' (dOp W T x)) ∧
      (∀ x, InQN W T i y x → InQN W T i y' (((PD.p : ℕ) : O) • x) → InQN W T i y' x) ∧
      ∃ k : ℕ, ∀ x, InQN W T i y x →
        InQN W T i y' (((PD.p : ℕ) : O) ^ k •
          dProd W T ((rootsR W T i y y' Bd).sort (· ≤ ·)) x)

/- English proof (translation)
Introduce `hCA` and use `⟨h1 hCA, h2 hCA⟩`.
-/
theorem RTool_of [NeZero n] (W : LocWach PD LL O v n) (h1 : Formalism.MainNotions.LiftingTheory.CaseA W → RToolNum W)
    (h2 : RToolMod W) : RTool W := fun hCA => ⟨h1 hCA, h2 hCA⟩

end RDef

/- English proof (translation)
Establish `hp : (P.PD K).p = l` using `P.PD_p K`. Take `⟨-, hs, hp2⟩` from `hCA`. Establish `hl2 : l ≠ 2` using `hp ▸ hp2`. Establish `hl0 : (l : ↥LL.1) ≠ 0`. Introduce `h`.

Use `P.v_l LL` as an intermediate fact. Rewrite `this` using `[h, AddValuation.map_zero]`. Conclude with `WithTop.top_ne_one this`. Take `⟨g, hgg⟩` from `(H.W K 1 LL hg).resΓ_onto (H.W K 1 LL hg).gam`. Establish `hχ` using `(H.W K 1 LL hg).χΓ_res g`.

Rewrite `hχ` using `[hgg]`. Establish `hint : IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g : ℚ_[l]))`. Rewrite using `[← hχ]`. Conclude with `(((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam : (↥(OL LL))ˣ) : ↥(OL LL)).2`. Establish `hint' : IsIntegral ℤ_[l] ((P.PD K).χ g : ℚ_[l])` using `(isIntegral_algebraMap_iff (algebraMap ℚ_[l] ↥LL.1).injective).1 hint`.

Take `⟨z, hz⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint'`. Establish `hzLL : algebraMap ℤ_[l] ↥LL.1 z = algebraMap ↥(OL LL) ↥LL.1 (((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam : (↥(OL LL))ˣ) : ↥(OL LL))`. Rewrite using `[hχ, ← hz, ← IsScalarTower.algebraMap_apply]`. Establish `hgen` using `(H.W K 1 LL hg).gam_gen`. Rewrite `hgen` using `[hs, ← hzLL]`.

Establish `hz1 : z - 1 ≠ 0`. Introduce `h0`. Establish `: algebraMap ℤ_[l] ↥LL.1 z - 1 = 0`. Rewrite using `[← map_one (algebraMap ℤ_[l] ↥LL.1), ← map_sub, h0, map_zero]`. Rewrite `hgen` using `[this, AddValuation.map_zero]`.

Conclude with `WithTop.top_ne_natCast 1 hgen`. Establish `hval : (z - 1).valuation = 1`. Establish `h1` using `v_padicInt P LL (z - 1) hz1`. Rewrite `h1` using `[map_sub, map_one, hgen]`. Conclude with `le_antisymm (Formalism.MainNotions.RamifiedCoefficientChains.natCast_le_withTop h1.ge) (Formalism.MainNotions.RamifiedCoefficientChains.natCast_le_withTop h1.le)`.

Establish `hzu : IsUnit z`. Break down `IsLocalRing.isUnit_or_isUnit_of_add_one (show z + (1 - z) = 1 by ring) with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Take `⟨u, hu⟩` from `h`.

Establish `h1` using `v_unit P LL u`. Establish `h2 : algebraMap ℤ_[l] ↥LL.1 (1 - z) = -(algebraMap ℤ_[l] ↥LL.1 z - 1)`. Rewrite using `[map_sub, map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[hu, h2, AddValuation.map_neg, hgen]`.

Establish `h3 : (1 : ℕ) ≤ 0` using `Formalism.MainNotions.RamifiedCoefficientChains.natCast_le_withTop (by rw [h1]; simp)`. Use linear arithmetic over natural numbers and integers. Take `⟨χ, rfl⟩` from `hzu`. Take `⟨c, hc1, hc0, hc2⟩` from `Formalism.NOK.cjExist_proof l hl2 χ hval`. Establish `hpow : ∀ k : ℤ, algebraMap ↥(OL LL) ↥LL.1 ((((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam) ^ k : (↥(OL LL))ˣ) : ↥(OL LL)) = algebraMap ℤ_[l] ↥LL.1 ((χ ^ k : ℤ_[l]ˣ) : ℤ_[l])`.

Introduce `k`. Establish `e1 : Units.map (algebraMap ↥(OL LL) ↥LL.1 : ↥(OL LL) →* ↥LL.1) ((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam) = Units.map (algebraMap ℤ_[l] ↥LL.1 : ℤ_[l] →* ↥LL.1) χ` using `Units.ext hzLL.symm`. Establish `e2 : Units.map (algebraMap ↥(OL LL) ↥LL.1 : ↥(OL LL) →* ↥LL.1) (((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam) ^ k) = Units.map (algebraMap ℤ_[l] ↥LL.1 : ℤ_[l] →* ↥LL.1) (χ ^ k)`. Rewrite using `[map_zpow, map_zpow, e1]`. Conclude with `congrArg Units.val e2`.

Establish `key : ∀ j : ℤ, cR (H.W K 1 LL hg) j = algebraMap ℤ_[l] ↥LL.1 (c j)`. Introduce `j`. Establish `h1 : algebraMap ℤ_[l] ↥LL.1 ((χ ^ (-j) : ℤ_[l]ˣ) : ℤ_[l]) - 1 = -(l : ↥LL.1) * algebraMap ℤ_[l] ↥LL.1 (c j)`. Rewrite using `[← map_one (algebraMap ℤ_[l] ↥LL.1), ← map_sub, ← hc1 j, map_mul, map_neg, map_natCast]`. Unfold `cR`.

Rewrite using `[hpow, h1, hp]`. Clear the denominators using the available nonvanishing facts. Use `⟨by rw [key, hc0, map_zero], fun j j' hjj => ?_⟩` and prove the remaining obligations. Rewrite using `[key, key, ← map_sub, v_padicInt P LL _ (hc2 j j' hjj).1, (hc2 j j' hjj).2, hp]`. Simplify using the standard rewrite rules.
-/
theorem RToolNum_holds {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K LL : FinExt l)
    (hg : Good K 1 LL) (hCA : Formalism.MainNotions.LiftingTheory.CaseA (H.W K 1 LL hg)) : RToolNum (H.W K 1 LL hg) := by
  have hp : (P.PD K).p = l := P.PD_p K
  obtain ⟨-, hs, hp2⟩ := hCA
  have hl2 : l ≠ 2 := hp ▸ hp2
  have hl0 : (l : ↥LL.1) ≠ 0 := by
    intro h
    have := P.v_l LL
    rw [h, AddValuation.map_zero] at this
    exact WithTop.top_ne_one this
  obtain ⟨g, hgg⟩ := (H.W K 1 LL hg).resΓ_onto (H.W K 1 LL hg).gam
  have hχ := (H.W K 1 LL hg).χΓ_res g
  rw [hgg] at hχ
  have hint : IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g : ℚ_[l])) := by
    rw [← hχ]
    exact (((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam : (↥(OL LL))ˣ) : ↥(OL LL)).2
  have hint' : IsIntegral ℤ_[l] ((P.PD K).χ g : ℚ_[l]) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ_[l] ↥LL.1).injective).1 hint
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
  have hzLL : algebraMap ℤ_[l] ↥LL.1 z = algebraMap ↥(OL LL) ↥LL.1
      (((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam : (↥(OL LL))ˣ) : ↥(OL LL)) := by
    rw [hχ, ← hz, ← IsScalarTower.algebraMap_apply]
  have hgen := (H.W K 1 LL hg).gam_gen
  rw [hs, ← hzLL] at hgen
  have hz1 : z - 1 ≠ 0 := by
    intro h0
    have : algebraMap ℤ_[l] ↥LL.1 z - 1 = 0 := by
      rw [← map_one (algebraMap ℤ_[l] ↥LL.1), ← map_sub, h0, map_zero]
    rw [this, AddValuation.map_zero] at hgen
    exact WithTop.top_ne_natCast 1 hgen
  have hval : (z - 1).valuation = 1 := by
    have h1 := v_padicInt P LL (z - 1) hz1
    rw [map_sub, map_one, hgen] at h1
    exact le_antisymm (Formalism.MainNotions.RamifiedCoefficientChains.natCast_le_withTop h1.ge) (Formalism.MainNotions.RamifiedCoefficientChains.natCast_le_withTop h1.le)
  have hzu : IsUnit z := by
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one (show z + (1 - z) = 1 by ring) with h | h
    · exact h
    · exfalso
      obtain ⟨u, hu⟩ := h
      have h1 := v_unit P LL u
      have h2 : algebraMap ℤ_[l] ↥LL.1 (1 - z) = -(algebraMap ℤ_[l] ↥LL.1 z - 1) := by
        rw [map_sub, map_one]; ring
      rw [hu, h2, AddValuation.map_neg, hgen] at h1
      have h3 : (1 : ℕ) ≤ 0 := Formalism.MainNotions.RamifiedCoefficientChains.natCast_le_withTop (by rw [h1]; simp)
      omega
  obtain ⟨χ, rfl⟩ := hzu
  obtain ⟨c, hc1, hc0, hc2⟩ := Formalism.NOK.cjExist_proof l hl2 χ hval
  have hpow : ∀ k : ℤ, algebraMap ↥(OL LL) ↥LL.1
      ((((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam) ^ k : (↥(OL LL))ˣ) : ↥(OL LL)) =
      algebraMap ℤ_[l] ↥LL.1 ((χ ^ k : ℤ_[l]ˣ) : ℤ_[l]) := by
    intro k
    have e1 : Units.map (algebraMap ↥(OL LL) ↥LL.1 : ↥(OL LL) →* ↥LL.1)
        ((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam) =
        Units.map (algebraMap ℤ_[l] ↥LL.1 : ℤ_[l] →* ↥LL.1) χ := Units.ext hzLL.symm
    have e2 : Units.map (algebraMap ↥(OL LL) ↥LL.1 : ↥(OL LL) →* ↥LL.1)
        (((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam) ^ k) =
        Units.map (algebraMap ℤ_[l] ↥LL.1 : ℤ_[l] →* ↥LL.1) (χ ^ k) := by
      rw [map_zpow, map_zpow, e1]
    exact congrArg Units.val e2
  have key : ∀ j : ℤ, cR (H.W K 1 LL hg) j = algebraMap ℤ_[l] ↥LL.1 (c j) := by
    intro j
    have h1 : algebraMap ℤ_[l] ↥LL.1 ((χ ^ (-j) : ℤ_[l]ˣ) : ℤ_[l]) - 1 =
        -(l : ↥LL.1) * algebraMap ℤ_[l] ↥LL.1 (c j) := by
      rw [← map_one (algebraMap ℤ_[l] ↥LL.1), ← map_sub, ← hc1 j, map_mul, map_neg, map_natCast]
    unfold cR
    rw [hpow, h1, hp]
    field_simp
  refine ⟨by rw [key, hc0, map_zero], fun j j' hjj => ?_⟩
  rw [key, key, ← map_sub, v_padicInt P LL _ (hc2 j j' hjj).1, (hc2 j j' hjj).2, hp]
  simp

/- English proof (translation)
Introduce `l _ K LL hg _`. Conclude with `RTool_of _ (RToolNum_holds (D.loc l) (HW l) K LL hg) (h l K LL hg)`.
-/
theorem module_clause_of_tools (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], RToolMod ((HW l).W K 1 LL hg)) :
    adm14 D HW F Cm := by
  intro l _ K LL hg _
  exact RTool_of _ (RToolNum_holds (D.loc l) (HW l) K LL hg) (h l K LL hg)

/- English proof (translation)
Establish `hl : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hl' : (2 : ℝ) ≤ l` using `by exact_mod_cast hl`. Take `⟨E, hE, hmem⟩` from `Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ramified_coefficient_chain_bounds.2.2.2.2.2.1 l R c hc h η S b ⌊Formalism.MainNotions.RamifiedCoefficientChains.aR l (h + η)⌋₊ S₂ (Formalism.MainNotions.RamifiedCoefficientChains.floor_a_le l (h + η) η b hl hb) hbh hS₂`. Use `⟨E, hE.trans ?_, hmem⟩` and prove the remaining obligations. Establish `ha : ((⌊Formalism.MainNotions.RamifiedCoefficientChains.aR l (h + η)⌋₊ : ℕ) : ℝ) ≤ Formalism.MainNotions.RamifiedCoefficientChains.aR l (h + η)` using `Nat.floor_le (Formalism.MainNotions.RamifiedCoefficientChains.aR_nonneg l (h + η) hl)`.

Establish `h1 : (3 * ((⌊Formalism.MainNotions.RamifiedCoefficientChains.aR l (h + η)⌋₊ : ℕ) : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((l : ℝ) - 1) ≤ (3 * Formalism.MainNotions.RamifiedCoefficientChains.aR l (h + η) + S + 2 * η) / ((l : ℝ) - 1)` using `div_le_div_of_nonneg_right (by linarith) (by linarith)`. Rewrite using `[Formalism.MainNotions.RamifiedCoefficientChains.lam_eq]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem LemmaG_E (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [IsDomain R] (c : ℤ → R)
    (hc : ∀ j j' : ℤ, j ≠ j' → Associated (c j - c j') ((l : R) ^ padicValInt l (j - j')))
    (h η S b : ℕ) (hb : 2 * Formalism.MainNotions.RamifiedCoefficientChains.aR l (h + η) + (η : ℝ) + 1 ≤ (b : ℝ)) (hbh : b + S ≤ h)
    (S₂ : Finset ℤ)
    (hS₂ : S₂ ⊆ Finset.Icc ((b : ℤ) + 1) ((b : ℤ) + S + ⌊Formalism.MainNotions.RamifiedCoefficientChains.aR l (h + η)⌋₊) ∪
      Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + ⌊Formalism.MainNotions.RamifiedCoefficientChains.aR l (h + η)⌋₊)) :
    ∃ E : ℕ, (E : ℝ) ≤ (3 * Formalism.MainNotions.RamifiedCoefficientChains.aR l (h + η) + S + 2 * η) / ((l : ℝ) - 1) +
        3 * Formalism.MainNotions.RamifiedCoefficientChains.lam l (h + η) ∧
      Polynomial.C ((l : R) ^ E) ∈
        Ideal.span ({∏ j ∈ Finset.Icc ((b : ℤ) - ⌊Formalism.MainNotions.RamifiedCoefficientChains.aR l (h + η)⌋₊ + 1) (b : ℤ),
            (Polynomial.X - Polynomial.C (c j)),
          ∏ j ∈ S₂, (Polynomial.X - Polynomial.C (c j))} : Set (Polynomial R)) := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨E, hE, hmem⟩ := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ramified_coefficient_chain_bounds.2.2.2.2.2.1 l R c hc h η S b
    ⌊Formalism.MainNotions.RamifiedCoefficientChains.aR l (h + η)⌋₊ S₂ (Formalism.MainNotions.RamifiedCoefficientChains.floor_a_le l (h + η) η b hl hb) hbh hS₂
  refine ⟨E, hE.trans ?_, hmem⟩
  have ha : ((⌊Formalism.MainNotions.RamifiedCoefficientChains.aR l (h + η)⌋₊ : ℕ) : ℝ) ≤ Formalism.MainNotions.RamifiedCoefficientChains.aR l (h + η) :=
    Nat.floor_le (Formalism.MainNotions.RamifiedCoefficientChains.aR_nonneg l (h + η) hl)
  have h1 : (3 * ((⌊Formalism.MainNotions.RamifiedCoefficientChains.aR l (h + η)⌋₊ : ℕ) : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((l : ℝ) - 1) ≤
      (3 * Formalism.MainNotions.RamifiedCoefficientChains.aR l (h + η) + S + 2 * η) / ((l : ℝ) - 1) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  rw [Formalism.MainNotions.RamifiedCoefficientChains.lam_eq]
  linarith

/- English proof (translation)
Establish `hl' : (3 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `h0 : 0 ≤ ((M : ℝ) + η) / ((l : ℝ) - 1)` using `div_nonneg (by positivity) (by linarith)`. Rewrite using `[Nat.floor_add_one h0]`. Conclude with `Formalism.KernelCokernelLengths.length_theorems_with_earlier.2.2.2.2.1 A l hl X u M η y hM`.
-/
theorem trunc_floor_one (A : Type) [CommRing A] (l : ℕ) [Fact l.Prime] (hl : 3 ≤ l) (X u : A)
    (M η y : ℕ) (hM : 1 ≤ M) :
    (l : A) ^ ⌊((M : ℝ) + η) / ((l : ℝ) - 1) + 1⌋₊ * (u * X * (X + (l : A)) ^ (l - 1)) ^ y ∈
      Ideal.span {(l : A) ^ eY l y, X ^ M * (X + (l : A)) ^ η} := by
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have h0 : 0 ≤ ((M : ℝ) + η) / ((l : ℝ) - 1) := div_nonneg (by positivity) (by linarith)
  rw [Nat.floor_add_one h0]
  exact Formalism.KernelCokernelLengths.length_theorems_with_earlier.2.2.2.2.1 A l hl X u M η y hM

/- English proof (translation)
Establish `h0 : 0 ≤ (X : ℝ) / ((l : ℝ) - 1) ^ 2` using `by positivity`. Rewrite using `[Nat.floor_add_one h0]`. Conclude with `Formalism.KernelCokernelLengths.length_theorems_with_earlier.2.2.2.2.2.1 O l hl ε u' w X y`.
-/
theorem trunc_floor_two (O : Type) [CommRing O] (l : ℕ) [Fact l.Prime] (hl : 3 ≤ l)
    (ε u' w : PowerSeries O) (X y : ℕ) :
    PowerSeries.C ((l : O) ^ ⌊(X : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌋₊) *
        (w * (PowerSeries.X - PowerSeries.C (l : O)) * PowerSeries.X ^ (l - 1) *
          (PowerSeries.C (l : O) * ε + u' * PowerSeries.X ^ l) ^ (l - 1)) ^ y ∈
      Ideal.span {PowerSeries.C ((l : O) ^ eY l y),
        (PowerSeries.X - PowerSeries.C (l : O)) * PowerSeries.X ^ X} := by
  have h0 : 0 ≤ (X : ℝ) / ((l : ℝ) - 1) ^ 2 := by positivity
  rw [Nat.floor_add_one h0]
  exact Formalism.KernelCokernelLengths.length_theorems_with_earlier.2.2.2.2.2.1 O l hl ε u' w X y

end Formalism.MainNotions.CrystallineLiftingInputs
