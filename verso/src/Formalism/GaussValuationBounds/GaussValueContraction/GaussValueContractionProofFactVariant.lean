import Formalism.GaussValuationBounds.Statement
import Formalism.WindowSums.PowerSeriesRelationList
import Formalism.WachModuleLifts.WachModuleProofs.LemmaHLift

noncomputable section

namespace Formalism.NOK

/- English proof (translation)
Take `⟨s, t, rfl⟩` from `Ideal.mem_span_pair.mp hp`. Rewrite using `[add_pow]`. Use `Ideal.sum_mem _ (fun i hi => ?_)` and prove the remaining obligations. Establish `hiz : i ≤ z` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Distinguish the cases in `hci : c ≤ i`.

Establish `e : (s * a) ^ i * (t * b) ^ (z - i) * (z.choose i : R) = (s ^ i * a ^ (i - c) * (t * b) ^ (z - i) * (z.choose i : R)) * a ^ c`. Rewrite using `[mul_pow]`. Use `conv_lhs => rw [show a ^ i = a ^ (i - c) * a ^ c by rw [← pow_add, Nat.sub_add_cancel hci]]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))`. Establish `hm : m ≤ z - i` using `by omega`. Establish `e : (s * a) ^ i * (t * b) ^ (z - i) * (z.choose i : R) = ((s * a) ^ i * t ^ (z - i) * b ^ (z - i - m) * (z.choose i : R)) * b ^ m`. Rewrite using `[mul_pow t b]`. Use `conv_lhs => rw [show b ^ (z - i) = b ^ (z - i - m) * b ^ m by`.

Rewrite using `[← pow_add, Nat.sub_add_cancel hm]]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))`.
-/
theorem pow_mem_span_pair_pow {R : Type} [CommRing R] (a b p : R) (z c m : ℕ)
    (hp : p ∈ Ideal.span {a, b}) (h : c + m ≤ z + 1) :
    p ^ z ∈ Ideal.span {a ^ c, b ^ m} := by
  obtain ⟨s, t, rfl⟩ := Ideal.mem_span_pair.mp hp
  rw [add_pow]
  refine Ideal.sum_mem _ (fun i hi => ?_)
  have hiz : i ≤ z := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hci : c ≤ i
  · have e : (s * a) ^ i * (t * b) ^ (z - i) * (z.choose i : R)
        = (s ^ i * a ^ (i - c) * (t * b) ^ (z - i) * (z.choose i : R)) * a ^ c := by
      rw [mul_pow]
      conv_lhs => rw [show a ^ i = a ^ (i - c) * a ^ c by rw [← pow_add, Nat.sub_add_cancel hci]]
      ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · have hm : m ≤ z - i := by omega
    have e : (s * a) ^ i * (t * b) ^ (z - i) * (z.choose i : R)
        = ((s * a) ^ i * t ^ (z - i) * b ^ (z - i - m) * (z.choose i : R)) * b ^ m := by
      rw [mul_pow t b]
      conv_lhs => rw [show b ^ (z - i) = b ^ (z - i - m) * b ^ m by
        rw [← pow_add, Nat.sub_add_cancel hm]]
      ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

/- English proof (translation)
Introduce `A _ ℓ hℓ h3 X u B r`. Establish `hLeg` using `Formalism.CL.legendreBound ℓ r`. Establish `h3R : (3 : ℝ) ≤ ℓ` using `by exact_mod_cast h3`. Establish `hd : (0 : ℝ) < (ℓ : ℝ) - 1` using `by linarith`. Use `set v := r + padicValNat ℓ r.factorial with hv`.

Use `set σ := ⌊(B : ℝ) / ((ℓ : ℝ) - 1)⌋₊ + 1 with hσ`. Establish `hσB : (B : ℝ) / ((ℓ : ℝ) - 1) < σ`. Rewrite using `[hσ]`. Use `push_cast`. Conclude with `Nat.lt_floor_add_one _`.

Establish `hvR : (v : ℝ) * ((ℓ : ℝ) - 1) ≤ r * ℓ`. Rewrite using `[hv]`. Use `push_cast`. Rewrite `hLeg` using `[le_div_iff₀ hd]`. Then use the resulting hypothesis. Establish `hσR : (B : ℝ) < σ * ((ℓ : ℝ) - 1)` using `by rwa [div_lt_iff₀ hd] at hσB`.

Establish `hmul : (ℓ - 1) * r + r = ℓ * r`. Rewrite using `[← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ ℓ)]`. Distinguish the cases in `h1 : v ≤ σ`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Rewrite using `[show (ℓ : A) ^ σ = (ℓ : A) ^ (σ - v) * (ℓ : A) ^ v by`.

Rewrite using `[← pow_add, Nat.sub_add_cancel h1]]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))`. Establish `hr : 1 ≤ r`. Break down `Nat.eq_zero_or_pos r with h0 | h0` into its components or cases. It suffices to derive a contradiction.

Apply `h1` to reduce the goal to its premises. Rewrite using `[hv, h0]`. Simplify using the standard rewrite rules. Conclude with `h0`. Distinguish the cases in `h2 : B ≤ (ℓ - 1) * r`.

Apply `Ideal.mul_mem_left` to reduce the goal to its premises. Establish `e : (u * X * (X + (ℓ : A)) ^ (ℓ - 1)) ^ r = (u ^ r * X ^ (r - 1) * (X + (ℓ : A)) ^ ((ℓ - 1) * r - B)) * (X * (X + (ℓ : A)) ^ B)`. Rewrite using `[mul_pow, mul_pow, ← pow_mul]`. Use `conv_lhs => rw [show X ^ r = X ^ (r - 1) * X by rw [← pow_succ, Nat.sub_add_cancel hr], show (X + (ℓ : A)) ^ ((ℓ - 1) * r) = (X + (ℓ : A)) ^ ((ℓ - 1) * r - B) * (X + (ℓ : A)) ^ B by`. Rewrite using `[← pow_add, Nat.sub_add_cancel h2]]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))`. Use `push Not at h1 h2`. Establish `hlB : B < ℓ * r`.

Assume the negation of the conclusion as `hh`. Use `push Not at hh`. Establish `hh' : (ℓ : ℝ) * r ≤ B` using `by exact_mod_cast hh`. Establish `hlt : (v : ℝ) * ((ℓ : ℝ) - 1) < σ * ((ℓ : ℝ) - 1)` using `by nlinarith`. Establish `: (v : ℝ) < σ` using `lt_of_mul_lt_mul_right hlt hd.le`.

Establish `: v < σ` using `by exact_mod_cast this`. Use linear arithmetic over natural numbers and integers. Establish `hkey : v ≤ σ + (ℓ * r - B)`. Establish `hlr : (B : ℝ) < ℓ * r` using `by exact_mod_cast hlB`. Establish `hlt : (v : ℝ) * ((ℓ : ℝ) - 1) < (σ + ((ℓ : ℝ) * r - B)) * ((ℓ : ℝ) - 1)`.

Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hlr.le) (by linarith : (0 : ℝ) ≤ ℓ - 2)]`. Establish `hcast : ((σ + (ℓ * r - B) : ℕ) : ℝ) = (σ : ℝ) + ((ℓ : ℝ) * r - B)`. Move the coercions through the operations in `[Nat.cast_sub hlB.le]`. Expand and normalize the polynomial expressions, which then agree. Establish `h' : (v : ℝ) < ((σ + (ℓ * r - B) : ℕ) : ℝ)`.

Rewrite using `[hcast]`. Conclude with `lt_of_mul_lt_mul_right hlt hd.le`. Conclude with `h'.le` after adjusting the coercions. Establish `hXmem : X ∈ Ideal.span {(ℓ : A), X + (ℓ : A)}` using `Ideal.mem_span_pair.mpr ⟨-1, 1, by ring⟩`. Establish `hpow` using `pow_mem_span_pair_pow (ℓ : A) (X + (ℓ : A)) X (r - 1) (ℓ * r - B) (B - (ℓ - 1) * r) hXmem (by omega)`.

Take `⟨s, t, hst⟩` from `Ideal.mem_span_pair.mp hpow`. Establish `hx : (u * X * (X + (ℓ : A)) ^ (ℓ - 1)) ^ r = u ^ r * X * (X + (ℓ : A)) ^ ((ℓ - 1) * r) * X ^ (r - 1)`. Rewrite using `[mul_pow, mul_pow, ← pow_mul]`. Use `conv_lhs => rw [show X ^ r = X ^ (r - 1) * X by rw [← pow_succ, Nat.sub_add_cancel hr]]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hx, ← hst]`. Establish `e1 : (ℓ : A) ^ σ * (ℓ : A) ^ (ℓ * r - B) = (ℓ : A) ^ (σ + (ℓ * r - B) - v) * (ℓ : A) ^ v`. Rewrite using `[← pow_add, ← pow_add, Nat.sub_add_cancel hkey]`. Establish `e2 : (X + (ℓ : A)) ^ ((ℓ - 1) * r) * (X + (ℓ : A)) ^ (B - (ℓ - 1) * r) = (X + (ℓ : A)) ^ B`. Rewrite using `[← pow_add, Nat.add_sub_cancel' h2.le]`.

Establish `e : (ℓ : A) ^ σ * (u ^ r * X * (X + (ℓ : A)) ^ ((ℓ - 1) * r) * (s * (ℓ : A) ^ (ℓ * r - B) + t * (X + (ℓ : A)) ^ (B - (ℓ - 1) * r))) = (u ^ r * X * s * (X + (ℓ : A)) ^ ((ℓ - 1) * r) * (ℓ : A) ^ (σ + (ℓ * r - B) - v)) * (ℓ : A) ^ v + ((ℓ : A) ^ σ * u ^ r * t) * (X * (X + (ℓ : A)) ^ …`. Take the linear combination `(u ^ r * X * s * (X + (ℓ : A)) ^ ((ℓ - 1) * r)) * e1 + ((ℓ : A) ^ σ * u ^ r * t * X) * e2`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))) (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))`.
-/
theorem gaussValueContraction_proof_fact_form : Rel1 := by
  intro A _ ℓ hℓ h3 X u B r
  have hLeg := Formalism.CL.legendreBound ℓ r
  have h3R : (3 : ℝ) ≤ ℓ := by exact_mod_cast h3
  have hd : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  set v := r + padicValNat ℓ r.factorial with hv
  set σ := ⌊(B : ℝ) / ((ℓ : ℝ) - 1)⌋₊ + 1 with hσ
  have hσB : (B : ℝ) / ((ℓ : ℝ) - 1) < σ := by
    rw [hσ]; push_cast; exact Nat.lt_floor_add_one _
  have hvR : (v : ℝ) * ((ℓ : ℝ) - 1) ≤ r * ℓ := by
    rw [hv]; push_cast; rwa [le_div_iff₀ hd] at hLeg
  have hσR : (B : ℝ) < σ * ((ℓ : ℝ) - 1) := by rwa [div_lt_iff₀ hd] at hσB
  have hmul : (ℓ - 1) * r + r = ℓ * r := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ ℓ)]
  by_cases h1 : v ≤ σ
  · apply Ideal.mul_mem_right
    rw [show (ℓ : A) ^ σ = (ℓ : A) ^ (σ - v) * (ℓ : A) ^ v by
      rw [← pow_add, Nat.sub_add_cancel h1]]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso; apply h1; rw [hv, h0]; simp
    · exact h0
  by_cases h2 : B ≤ (ℓ - 1) * r
  · apply Ideal.mul_mem_left
    have e : (u * X * (X + (ℓ : A)) ^ (ℓ - 1)) ^ r
        = (u ^ r * X ^ (r - 1) * (X + (ℓ : A)) ^ ((ℓ - 1) * r - B)) * (X * (X + (ℓ : A)) ^ B) := by
      rw [mul_pow, mul_pow, ← pow_mul]
      conv_lhs => rw [show X ^ r = X ^ (r - 1) * X by rw [← pow_succ, Nat.sub_add_cancel hr],
        show (X + (ℓ : A)) ^ ((ℓ - 1) * r) = (X + (ℓ : A)) ^ ((ℓ - 1) * r - B) * (X + (ℓ : A)) ^ B by
          rw [← pow_add, Nat.sub_add_cancel h2]]
      ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  push Not at h1 h2
  have hlB : B < ℓ * r := by
    by_contra hh
    push Not at hh
    have hh' : (ℓ : ℝ) * r ≤ B := by exact_mod_cast hh
    have hlt : (v : ℝ) * ((ℓ : ℝ) - 1) < σ * ((ℓ : ℝ) - 1) := by nlinarith
    have : (v : ℝ) < σ := lt_of_mul_lt_mul_right hlt hd.le
    have : v < σ := by exact_mod_cast this
    omega
  have hkey : v ≤ σ + (ℓ * r - B) := by
    have hlr : (B : ℝ) < ℓ * r := by exact_mod_cast hlB
    have hlt : (v : ℝ) * ((ℓ : ℝ) - 1) < (σ + ((ℓ : ℝ) * r - B)) * ((ℓ : ℝ) - 1) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hlr.le) (by linarith : (0 : ℝ) ≤ ℓ - 2)]
    have hcast : ((σ + (ℓ * r - B) : ℕ) : ℝ) = (σ : ℝ) + ((ℓ : ℝ) * r - B) := by
      push_cast [Nat.cast_sub hlB.le]; ring
    have h' : (v : ℝ) < ((σ + (ℓ * r - B) : ℕ) : ℝ) := by
      rw [hcast]; exact lt_of_mul_lt_mul_right hlt hd.le
    exact_mod_cast h'.le
  have hXmem : X ∈ Ideal.span {(ℓ : A), X + (ℓ : A)} :=
    Ideal.mem_span_pair.mpr ⟨-1, 1, by ring⟩
  have hpow := pow_mem_span_pair_pow (ℓ : A) (X + (ℓ : A)) X (r - 1) (ℓ * r - B)
    (B - (ℓ - 1) * r) hXmem (by omega)
  obtain ⟨s, t, hst⟩ := Ideal.mem_span_pair.mp hpow
  have hx : (u * X * (X + (ℓ : A)) ^ (ℓ - 1)) ^ r
      = u ^ r * X * (X + (ℓ : A)) ^ ((ℓ - 1) * r) * X ^ (r - 1) := by
    rw [mul_pow, mul_pow, ← pow_mul]
    conv_lhs => rw [show X ^ r = X ^ (r - 1) * X by rw [← pow_succ, Nat.sub_add_cancel hr]]
    ring
  rw [hx, ← hst]
  have e1 : (ℓ : A) ^ σ * (ℓ : A) ^ (ℓ * r - B) = (ℓ : A) ^ (σ + (ℓ * r - B) - v) * (ℓ : A) ^ v := by
    rw [← pow_add, ← pow_add, Nat.sub_add_cancel hkey]
  have e2 : (X + (ℓ : A)) ^ ((ℓ - 1) * r) * (X + (ℓ : A)) ^ (B - (ℓ - 1) * r) = (X + (ℓ : A)) ^ B := by
    rw [← pow_add, Nat.add_sub_cancel' h2.le]
  have e : (ℓ : A) ^ σ * (u ^ r * X * (X + (ℓ : A)) ^ ((ℓ - 1) * r) *
      (s * (ℓ : A) ^ (ℓ * r - B) + t * (X + (ℓ : A)) ^ (B - (ℓ - 1) * r)))
      = (u ^ r * X * s * (X + (ℓ : A)) ^ ((ℓ - 1) * r) * (ℓ : A) ^ (σ + (ℓ * r - B) - v)) *
          (ℓ : A) ^ v + ((ℓ : A) ^ σ * u ^ r * t) * (X * (X + (ℓ : A)) ^ B) := by
    linear_combination (u ^ r * X * s * (X + (ℓ : A)) ^ ((ℓ - 1) * r)) * e1 +
      ((ℓ : A) ^ σ * u ^ r * t * X) * e2
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

/- English proof (translation)
Introduce `O _ ℓ hℓ h3 ε u' w b r`. Establish `hLeg` using `Formalism.CL.legendreBound ℓ r`. Establish `h3R : (3 : ℝ) ≤ ℓ` using `by exact_mod_cast h3`. Establish `hd : (0 : ℝ) < (ℓ : ℝ) - 1` using `by linarith`. Establish `hL : (0 : ℝ) < ℓ` using `by linarith`.

Use `set v := r + padicValNat ℓ r.factorial with hv`. Use `set σ := ⌊(b : ℝ) / ((ℓ : ℝ) - 1) ^ 2⌋₊ + 1 with hσ`. Establish `hσb : (b : ℝ) / ((ℓ : ℝ) - 1) ^ 2 < σ`. Rewrite using `[hσ]`. Use `push_cast`.

Conclude with `Nat.lt_floor_add_one _`. Establish `hvR : (v : ℝ) * ((ℓ : ℝ) - 1) ≤ r * ℓ`. Rewrite using `[hv]`. Use `push_cast`. Rewrite `hLeg` using `[le_div_iff₀ hd]`. Then use the resulting hypothesis.

Establish `hσR : (b : ℝ) < σ * ((ℓ : ℝ) - 1) ^ 2` using `by rwa [div_lt_iff₀ (by positivity)] at hσb`. Establish `hx : (w * (PowerSeries.X - PowerSeries.C (ℓ : O)) * PowerSeries.X ^ (ℓ - 1) * (Formalism.WindowSums.p1 ℓ ε u') ^ (ℓ - 1)) ^ r = (w * (PowerSeries.X - PowerSeries.C (ℓ : O)) * PowerSeries.X ^ (ℓ - 1)) ^ r * (Formalism.WindowSums.p1 ℓ ε u') ^ ((ℓ - 1) * r)`. Rewrite using `[mul_pow, ← pow_mul]`. Unfold `Formalism.WindowSums.IdLQ`. Distinguish the cases in `h1 : v ≤ σ`.

Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Rewrite using `[show (ℓ : O) ^ σ = (ℓ : O) ^ (σ - v) * (ℓ : O) ^ v by`. Rewrite using `[← pow_add, Nat.sub_add_cancel h1], map_mul]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))`. Use `push Not at h1`.

Establish `hnum : ((v - σ : ℕ) : ℝ) ≤ (((ℓ - 1) * r : ℕ) : ℝ) + 1 - (b : ℝ) / (ℓ : ℝ)`. Rewrite using `[Nat.cast_sub h1.le, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]`. Use `set β := (b : ℝ) / (ℓ : ℝ) with hβdef`. Establish `hβ : β * ℓ = b` using `by rw [hβdef]; field_simp`. Establish `h1R : (σ : ℝ) < v` using `by exact_mod_cast h1`.

Establish `hv2 : (v : ℝ) * ((ℓ : ℝ) - 1) ^ 2 ≤ r * ℓ * ((ℓ : ℝ) - 1)`. Use `mul_le_mul_of_nonneg_right hvR hd.le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Distinguish the cases in `hc : ((ℓ : ℝ) - 1) * r * ℓ < b`. It suffices to derive a contradiction.

Establish `hlt : (v : ℝ) * ((ℓ : ℝ) - 1) ^ 2 < σ * ((ℓ : ℝ) - 1) ^ 2` using `by nlinarith`. Use `lt_of_mul_lt_mul_right hlt (by positivity)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `push Not at hc`. Establish `hβr : β ≤ ((ℓ : ℝ) - 1) * r`.

Assume the negation of the conclusion as `hh`. Use `push Not at hh`. Use `mul_lt_mul_of_pos_right hh hL` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA : ((ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2) * (((ℓ : ℝ) - 1) * r - β) ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (by linarith)`.

Establish `hlt : (v : ℝ) * ((ℓ : ℝ) - 1) ^ 2 < (σ + ((ℓ : ℝ) - 1) * r - β) * ((ℓ : ℝ) - 1) ^ 2` using `by nlinarith`. Use `lt_of_mul_lt_mul_right hlt (by positivity)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hC2` using `Formalism.WindowSums.arc_C2Lower O ℓ ε u' ((ℓ - 1) * r) b (v - σ) hnum`. Unfold `Formalism.WindowSums.IdLQ at hC2`.

Take `⟨s, t, hst⟩` from `Ideal.mem_span_pair.mp hC2`. Rewrite using `[hx, ← hst]`. Establish `e1 : PowerSeries.C ((ℓ : O) ^ σ) * PowerSeries.C ((ℓ : O) ^ (v - σ)) = PowerSeries.C ((ℓ : O) ^ v)`. Rewrite using `[← map_mul, ← pow_add, Nat.add_sub_cancel' h1.le]`. Use `set W := (w * (PowerSeries.X - PowerSeries.C (ℓ : O)) * PowerSeries.X ^ (ℓ - 1)) ^ r`.

Establish `e : PowerSeries.C ((ℓ : O) ^ σ) * (W * (s * PowerSeries.C ((ℓ : O) ^ (v - σ)) + t * PowerSeries.X ^ b)) = (W * s) * PowerSeries.C ((ℓ : O) ^ v) + (PowerSeries.C ((ℓ : O) ^ σ) * W * t) * PowerSeries.X ^ b`. Take the linear combination `(W * s) * e1`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))) (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))`.
-/
theorem gaussValueContraction_proof_fact_variant : Rel2 := by
  intro O _ ℓ hℓ h3 ε u' w b r
  have hLeg := Formalism.CL.legendreBound ℓ r
  have h3R : (3 : ℝ) ≤ ℓ := by exact_mod_cast h3
  have hd : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hL : (0 : ℝ) < ℓ := by linarith
  set v := r + padicValNat ℓ r.factorial with hv
  set σ := ⌊(b : ℝ) / ((ℓ : ℝ) - 1) ^ 2⌋₊ + 1 with hσ
  have hσb : (b : ℝ) / ((ℓ : ℝ) - 1) ^ 2 < σ := by
    rw [hσ]; push_cast; exact Nat.lt_floor_add_one _
  have hvR : (v : ℝ) * ((ℓ : ℝ) - 1) ≤ r * ℓ := by
    rw [hv]; push_cast; rwa [le_div_iff₀ hd] at hLeg
  have hσR : (b : ℝ) < σ * ((ℓ : ℝ) - 1) ^ 2 := by rwa [div_lt_iff₀ (by positivity)] at hσb
  have hx : (w * (PowerSeries.X - PowerSeries.C (ℓ : O)) * PowerSeries.X ^ (ℓ - 1) *
      (Formalism.WindowSums.p1 ℓ ε u') ^ (ℓ - 1)) ^ r
      = (w * (PowerSeries.X - PowerSeries.C (ℓ : O)) * PowerSeries.X ^ (ℓ - 1)) ^ r *
        (Formalism.WindowSums.p1 ℓ ε u') ^ ((ℓ - 1) * r) := by
    rw [mul_pow, ← pow_mul]
  unfold Formalism.WindowSums.IdLQ
  by_cases h1 : v ≤ σ
  · apply Ideal.mul_mem_right
    rw [show (ℓ : O) ^ σ = (ℓ : O) ^ (σ - v) * (ℓ : O) ^ v by
      rw [← pow_add, Nat.sub_add_cancel h1], map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  push Not at h1
  have hnum : ((v - σ : ℕ) : ℝ) ≤ (((ℓ - 1) * r : ℕ) : ℝ) + 1 - (b : ℝ) / (ℓ : ℝ) := by
    rw [Nat.cast_sub h1.le, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
    set β := (b : ℝ) / (ℓ : ℝ) with hβdef
    have hβ : β * ℓ = b := by rw [hβdef]; field_simp
    have h1R : (σ : ℝ) < v := by exact_mod_cast h1
    have hv2 : (v : ℝ) * ((ℓ : ℝ) - 1) ^ 2 ≤ r * ℓ * ((ℓ : ℝ) - 1) := by
      have := mul_le_mul_of_nonneg_right hvR hd.le
      nlinarith
    by_cases hc : ((ℓ : ℝ) - 1) * r * ℓ < b
    · exfalso
      have hlt : (v : ℝ) * ((ℓ : ℝ) - 1) ^ 2 < σ * ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
      have := lt_of_mul_lt_mul_right hlt (by positivity)
      linarith
    · push Not at hc
      have hβr : β ≤ ((ℓ : ℝ) - 1) * r := by
        by_contra hh; push Not at hh
        have := mul_lt_mul_of_pos_right hh hL
        linarith
      have hA : ((ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2) * (((ℓ : ℝ) - 1) * r - β) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (by linarith)
      have hlt : (v : ℝ) * ((ℓ : ℝ) - 1) ^ 2 <
          (σ + ((ℓ : ℝ) - 1) * r - β) * ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
      have := lt_of_mul_lt_mul_right hlt (by positivity)
      linarith
  have hC2 := Formalism.WindowSums.arc_C2Lower O ℓ ε u' ((ℓ - 1) * r) b (v - σ) hnum
  unfold Formalism.WindowSums.IdLQ at hC2
  obtain ⟨s, t, hst⟩ := Ideal.mem_span_pair.mp hC2
  rw [hx, ← hst]
  have e1 : PowerSeries.C ((ℓ : O) ^ σ) * PowerSeries.C ((ℓ : O) ^ (v - σ)) =
      PowerSeries.C ((ℓ : O) ^ v) := by
    rw [← map_mul, ← pow_add, Nat.add_sub_cancel' h1.le]
  set W := (w * (PowerSeries.X - PowerSeries.C (ℓ : O)) * PowerSeries.X ^ (ℓ - 1)) ^ r
  have e : PowerSeries.C ((ℓ : O) ^ σ) * (W * (s * PowerSeries.C ((ℓ : O) ^ (v - σ)) +
      t * PowerSeries.X ^ b)) = (W * s) * PowerSeries.C ((ℓ : O) ^ v) +
      (PowerSeries.C ((ℓ : O) ^ σ) * W * t) * PowerSeries.X ^ b := by
    linear_combination (W * s) * e1
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

end Formalism.NOK
