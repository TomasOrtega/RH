import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hl`. Establish `hρ0 : (0 : ℝ) < ρ` using `h0`. Establish `hρ1 : (ρ : ℝ) ≤ 1` using `h1.le`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨a, b, c, hw, rfl⟩` from `hx`. Establish `e : algebraMap A (PreDisc l u ρ) ((l : A) ^ c) * (algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b) * IsLocalization.Away.invSelf (l : A) ^ c) = algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b)`. Rewrite using `[map_pow, mul_left_comm, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]`. Break down `le_or_gt m b with hb | hb` into its components or cases. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hb`.

Use `⟨c, (l : A) ^ a * u ^ k, 0, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hp : (ρ : ℝ) ^ m ≤ (ρ : ℝ) ^ b` using `pow_le_pow_of_le_one hρ0.le hρ1 hb.le`.

Establish `h2 : (l : ℝ) ^ (c + n) ≤ (l : ℝ) ^ a`. Rewrite `hw` using `[div_mul_eq_mul_div, le_div_iff₀ (by positivity)]`. Establish `h3 : (l : ℝ) ^ (c + n) * (ρ : ℝ) ^ b ≤ (l : ℝ) ^ a * (ρ : ℝ) ^ b`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_right h3 (by positivity)`.

Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le ((pow_le_pow_iff_right₀ hl1).1 h2)`. Use `⟨c, 0, (l : A) ^ k * u ^ b, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `zero => exact ⟨0, 0, 0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨c, z₁, z₂, h⟩` from `hx`. Take `⟨c', z₁', z₂', h'⟩` from `hy`. Use `⟨c + c', (l : A) ^ c' * z₁ + (l : A) ^ c * z₁', z₂ + z₂', ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, map_mul, map_pow, pow_add] at h h' ⊢`. Take the linear combination `(algebraMap A (PreDisc l u ρ) (l : A)) ^ c' * h + (algebraMap A (PreDisc l u ρ) (l : A)) ^ c * h'`. Consider the case `smul a x _ hx`. Take `⟨c, z₁, z₂, h⟩` from `hx`. Use `⟨c, a * z₁, a * z₂, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, map_mul, map_pow, pow_add, Algebra.smul_def] at h ⊢`. Take the linear combination `(algebraMap A (PreDisc l u ρ) a) * h`.
-/
theorem exists_of_mem_ball_small {l : ℕ} (hl : 1 < l) {A : Type} [CommRing A] (u : A) {ρ : ℝ≥0} (h0 : 0 < ρ)
    (h1 : ρ < 1) (m n : ℕ) {y : PreDisc l u ρ} (hy : y ∈ ball l u ρ ((ρ : ℝ) ^ m / (l : ℝ) ^ n)) :
    ∃ (c : ℕ) (z₁ z₂ : A), algebraMap A (PreDisc l u ρ) ((l : A) ^ c) * y =
      algebraMap A (PreDisc l u ρ) (u ^ m * z₁ + (l : A) ^ (c + n) * z₂) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl
  have hρ0 : (0 : ℝ) < ρ := h0
  have hρ1 : (ρ : ℝ) ≤ 1 := h1.le
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, c, hw, rfl⟩ := hx
    have e : algebraMap A (PreDisc l u ρ) ((l : A) ^ c) * (algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b) *
        IsLocalization.Away.invSelf (l : A) ^ c) = algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b) := by
      rw [map_pow, mul_left_comm, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
    rcases le_or_gt m b with hb | hb
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb
      refine ⟨c, (l : A) ^ a * u ^ k, 0, ?_⟩
      rw [e]; congr 1; ring
    · have hp : (ρ : ℝ) ^ m ≤ (ρ : ℝ) ^ b := pow_le_pow_of_le_one hρ0.le hρ1 hb.le
      have h2 : (l : ℝ) ^ (c + n) ≤ (l : ℝ) ^ a := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hw
        have h3 : (l : ℝ) ^ (c + n) * (ρ : ℝ) ^ b ≤ (l : ℝ) ^ a * (ρ : ℝ) ^ b :=
          calc (l : ℝ) ^ (c + n) * (ρ : ℝ) ^ b = (l : ℝ) ^ c * (ρ : ℝ) ^ b * (l : ℝ) ^ n := by ring
            _ ≤ _ := hw
            _ ≤ (ρ : ℝ) ^ b * (l : ℝ) ^ a := mul_le_mul_of_nonneg_right hp (by positivity)
            _ = _ := mul_comm _ _
        exact le_of_mul_le_mul_right h3 (by positivity)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ((pow_le_pow_iff_right₀ hl1).1 h2)
      refine ⟨c, 0, (l : A) ^ k * u ^ b, ?_⟩
      rw [e]; congr 1; ring
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, z₁, z₂, h⟩ := hx
    obtain ⟨c', z₁', z₂', h'⟩ := hy
    refine ⟨c + c', (l : A) ^ c' * z₁ + (l : A) ^ c * z₁', z₂ + z₂', ?_⟩
    simp only [map_add, map_mul, map_pow, pow_add] at h h' ⊢
    linear_combination (algebraMap A (PreDisc l u ρ) (l : A)) ^ c' * h +
      (algebraMap A (PreDisc l u ρ) (l : A)) ^ c * h'
  | smul a x _ hx =>
    obtain ⟨c, z₁, z₂, h⟩ := hx
    refine ⟨c, a * z₁, a * z₂, ?_⟩
    simp only [map_add, map_mul, map_pow, pow_add, Algebra.smul_def] at h ⊢
    linear_combination (algebraMap A (PreDisc l u ρ) a) * h

/- English proof (translation)
Establish `hb : algebraMap A (PreDisc l u ρ) x ∈ ball l u ρ ((ρ : ℝ) ^ m / (l : ℝ) ^ n)` using `mem_ball_of_gauge_lt l u ρ ((norm_ofPre l u ρ _).symm.trans_lt hx)`. Take `⟨c, z₁, z₂, h⟩` from `exists_of_mem_ball_small hl u h0 h1 m n hb`. Establish `hn : (l : A) ∈ nonZeroDivisors A` using `mem_nonZeroDivisors_iff_left.2 ht`. Establish `hi : Function.Injective (algebraMap A (PreDisc l u ρ))` using `IsLocalization.injective (M := Submonoid.powers (l : A)) _ (Submonoid.powers_le.2 hn)`. Rewrite `h` using `[← map_mul]`.

Establish `h2` using `hi h`. Establish `key : ∀ (c : ℕ) (w : A), u ^ m ∣ (l : A) ^ c * w → u ^ m ∣ w` using `fun c => by`. Proceed by induction on `c with`. Consider the case `zero => intro w hw`. Simplify using `using hw`.

Consider the case `succ c ih`. Introduce and unpack `w ⟨y, hy⟩`. Conclude with `ih w (hd _ y (by rw [← hy]; ring))`. Take `⟨z, hz⟩` from `key c (x - (l : A) ^ n * z₂) ⟨z₁, by rw [pow_add] at h2; linear_combination h2⟩`. Conclude with `⟨z, z₂, by linear_combination hz⟩`.
-/
theorem exists_of_norm_toDisc_lt {l : ℕ} (hl : 1 < l) {A : Type} [CommRing A] (u : A)
    (ht : ∀ x : A, (l : A) * x = 0 → x = 0) (m : ℕ) (hd : ∀ x y : A, (l : A) * x = u ^ m * y → u ^ m ∣ x)
    {ρ : ℝ≥0} (h0 : 0 < ρ) (h1 : ρ < 1) (n : ℕ) (x : A) (hx : ‖toDisc l u ρ x‖ < (ρ : ℝ) ^ m / (l : ℝ) ^ n) :
    ∃ z₁ z₂ : A, x = u ^ m * z₁ + (l : A) ^ n * z₂ := by
  have hb : algebraMap A (PreDisc l u ρ) x ∈ ball l u ρ ((ρ : ℝ) ^ m / (l : ℝ) ^ n) :=
    mem_ball_of_gauge_lt l u ρ ((norm_ofPre l u ρ _).symm.trans_lt hx)
  obtain ⟨c, z₁, z₂, h⟩ := exists_of_mem_ball_small hl u h0 h1 m n hb
  have hn : (l : A) ∈ nonZeroDivisors A := mem_nonZeroDivisors_iff_left.2 ht
  have hi : Function.Injective (algebraMap A (PreDisc l u ρ)) :=
    IsLocalization.injective (M := Submonoid.powers (l : A)) _ (Submonoid.powers_le.2 hn)
  rw [← map_mul] at h
  have h2 := hi h
  have key : ∀ (c : ℕ) (w : A), u ^ m ∣ (l : A) ^ c * w → u ^ m ∣ w := fun c => by
    induction c with
    | zero => intro w hw; simpa using hw
    | succ c ih =>
      rintro w ⟨y, hy⟩
      exact ih w (hd _ y (by rw [← hy]; ring))
  obtain ⟨z, hz⟩ := key c (x - (l : A) ^ n * z₂) ⟨z₁, by rw [pow_add] at h2; linear_combination h2⟩
  exact ⟨z, z₂, by linear_combination hz⟩

/- English proof (translation)
Establish `h` using `congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) bk.monic.as_sum`. Simplify using `only [map_add, map_pow, map_sum, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_C] at h`. Establish `e : (X : bk.S) ^ bk.Ep.natDegree = bk.E - ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * (X : bk.S) ^ i`. Rewrite using `[eq_sub_iff_add_eq]`. Conclude with `h.symm`.

Rewrite using `[e]`. Use `sub_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left (sum_mem fun i hi => ?_))` and prove the remaining obligations. Take `⟨w, hw⟩` from `bk.dvd_coeff i (Finset.mem_range.1 hi)`. Rewrite using `[hw, map_mul, map_natCast, mul_assoc]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`.
-/
theorem BK.X_pow_natDegree_mem_J {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    (X : bk.S) ^ bk.Ep.natDegree ∈ bk.J := by
  have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) bk.monic.as_sum
  simp only [map_add, map_pow, map_sum, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X,
    Polynomial.coe_C] at h
  have e : (X : bk.S) ^ bk.Ep.natDegree =
      bk.E - ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * (X : bk.S) ^ i := by
    rw [eq_sub_iff_add_eq]; exact h.symm
  rw [e]
  refine sub_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left (sum_mem fun i hi => ?_))
  obtain ⟨w, hw⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
  rw [hw, map_mul, map_natCast, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Introduce `l hl K bk A _ s ht hd ρ h0 h1 n`. Establish `hl0 : (0 : ℝ) < l` using `Nat.cast_pos.2 hl.out.pos`. Establish `hρ0 : (0 : ℝ) < ρ` using `h0`. Establish `hr : 0 < (ρ : ℝ) ^ (bk.Ep.natDegree * n) / (l : ℝ) ^ n` using `by positivity`. Use `⟨_, half_pos hr, fun x hx => ?_⟩` and prove the remaining obligations.

Take `⟨z₁, z₂, rfl⟩` from `exists_of_norm_toDisc_lt hl.out.one_lt (s X) ht _ (hd _) h0 h1 n x (hx.trans_lt (half_lt_self hr))`. Use `add_mem (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_right _ _ ?_)` and prove the remaining obligations. Rewrite using `[← map_pow, pow_mul]`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow bk.X_pow_natDegree_mem_J n)`. Rewrite using `[← map_natCast s, ← map_pow]`.

Conclude with `Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) n)`.
-/
theorem mem_J_pow_of_norm_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A), (∀ x : A, (l : A) * x = 0 → x = 0) → (∀ (m : ℕ) (x y : A), (l : A) * x = s X ^ m * y → s X ^ m ∣ x) → ∀ (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ x : A, ‖toDisc l (s X) ρ x‖ ≤ r → x ∈ (bk.J ^ n).map s := by
  intro l hl K bk A _ s ht hd ρ h0 h1 n
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hρ0 : (0 : ℝ) < ρ := h0
  have hr : 0 < (ρ : ℝ) ^ (bk.Ep.natDegree * n) / (l : ℝ) ^ n := by positivity
  refine ⟨_, half_pos hr, fun x hx => ?_⟩
  obtain ⟨z₁, z₂, rfl⟩ := exists_of_norm_toDisc_lt hl.out.one_lt (s X) ht _ (hd _) h0 h1 n x
    (hx.trans_lt (half_lt_self hr))
  refine add_mem (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_right _ _ ?_)
  · rw [← map_pow, pow_mul]
    exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow bk.X_pow_natDegree_mem_J n)
  · rw [← map_natCast s, ← map_pow]
    exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) n)

end GlobalTheory.BSP
