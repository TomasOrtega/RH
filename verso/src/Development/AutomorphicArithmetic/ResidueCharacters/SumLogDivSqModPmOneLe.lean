import Mathlib

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces.Sums

open Real Finset

/- English proof (translation)
Introduce `l hl`. Simplify using `only [Finset.mem_filter] at hl`. Rewrite using `[Finset.mem_Icc]`. Conclude with `⟨hl.2.1, Nat.le_floor hl.2.2⟩`.
-/
lemma filter_sub_Icc (T : Finset ℕ) (Y : ℝ) :
    T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y) ⊆ Finset.Icc 1 ⌊Y⌋₊ := by
  intro l hl
  simp only [Finset.mem_filter] at hl
  rw [Finset.mem_Icc]
  exact ⟨hl.2.1, Nat.le_floor hl.2.2⟩

/- English proof (translation)
Establish `hlogY : 0 ≤ Real.log Y` using `Real.log_nonneg hY`. Establish `h1 : ∑ l ∈ T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l ≤ (T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y)).card • Real.log Y`. Apply `Finset.sum_le_card_nsmul` to reduce the goal to its premises. Introduce `l hl`. Simplify using `only [Finset.mem_filter] at hl`.

Establish `: (1 : ℝ) ≤ l` using `by exact_mod_cast hl.2.1`. Conclude with `Real.log_le_log (by linarith) hl.2.2`. Establish `h2 : ((T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y)).card : ℝ) ≤ Y`. Use `Finset.card_le_card (filter_sub_Icc T Y)` as an intermediate fact. Rewrite `this` using `[Nat.card_Icc]`.

Establish `h3 : ((T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y)).card : ℝ) ≤ (⌊Y⌋₊ : ℝ)`. Conclude with `(by omega : (T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y)).card ≤ ⌊Y⌋₊)` after adjusting the coercions. Conclude with `h3.trans (Nat.floor_le (by linarith))`. Rewrite `h1` using `[nsmul_eq_mul]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sum_log_le (T : Finset ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    ∑ l ∈ T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l ≤ Y * Real.log Y := by
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have h1 : ∑ l ∈ T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l ≤
      (T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y)).card • Real.log Y := by
    apply Finset.sum_le_card_nsmul
    intro l hl
    simp only [Finset.mem_filter] at hl
    have : (1 : ℝ) ≤ l := by exact_mod_cast hl.2.1
    exact Real.log_le_log (by linarith) hl.2.2
  have h2 : ((T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y)).card : ℝ) ≤ Y := by
    have := Finset.card_le_card (filter_sub_Icc T Y)
    rw [Nat.card_Icc] at this
    have h3 : ((T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y)).card : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by
      exact_mod_cast (by omega : (T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y)).card ≤ ⌊Y⌋₊)
    exact h3.trans (Nat.floor_le (by linarith))
  rw [nsmul_eq_mul] at h1
  nlinarith

/- English proof (translation)
Establish `hlogY : 0 ≤ Real.log Y` using `Real.log_nonneg hY`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `l hl`. Simplify using `only [Finset.mem_filter] at hl`.

Establish `: (1 : ℝ) ≤ l` using `by exact_mod_cast hl.2.1`. Rewrite using `[div_eq_mul_inv]`. Conclude with `mul_le_mul_of_nonneg_right (Real.log_le_log (by linarith) hl.2.2) (by positivity)`. Use `_ ≤ ∑ l ∈ Finset.Icc 1 ⌊Y⌋₊, Real.log Y * ((l : ℝ))⁻¹ := by`. Apply `Finset.sum_le_sum_of_subset_of_nonneg (filter_sub_Icc T Y)` to reduce the goal to its premises.

Introduce `l _ _`. Check the signs of the components of the expression. Use `_ = Real.log Y * (harmonic ⌊Y⌋₊ : ℝ) := by`. Rewrite using `[← Finset.mul_sum, harmonic_eq_sum_Icc]`. Use `push_cast`.

Both sides reduce to the same expression. Use `_ ≤ Real.log Y * (1 + Real.log ⌊Y⌋₊) := by`. Conclude with `mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) hlogY`. Use `_ ≤ Real.log Y * (1 + Real.log Y) := by`. Establish `hf : (1 : ℝ) ≤ ⌊Y⌋₊` using `by exact_mod_cast Nat.le_floor (by exact_mod_cast hY)`.

Establish `: Real.log ⌊Y⌋₊ ≤ Real.log Y` using `Real.log_le_log (by linarith) (Nat.floor_le (by linarith))`. Use the polynomial consequences of the given equalities and inequalities. Use `_ ≤ (1 + Real.log Y) ^ 2 := by nlinarith`.
-/
theorem sum_log_div_le (T : Finset ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    ∑ l ∈ T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l / l ≤ (1 + Real.log Y) ^ 2 := by
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  calc ∑ l ∈ T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l / l
      ≤ ∑ l ∈ T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y), Real.log Y * ((l : ℝ))⁻¹ := by
        apply Finset.sum_le_sum
        intro l hl
        simp only [Finset.mem_filter] at hl
        have : (1 : ℝ) ≤ l := by exact_mod_cast hl.2.1
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (Real.log_le_log (by linarith) hl.2.2) (by positivity)
    _ ≤ ∑ l ∈ Finset.Icc 1 ⌊Y⌋₊, Real.log Y * ((l : ℝ))⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (filter_sub_Icc T Y)
        intro l _ _
        positivity
    _ = Real.log Y * (harmonic ⌊Y⌋₊ : ℝ) := by
        rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
        push_cast
        rfl
    _ ≤ Real.log Y * (1 + Real.log ⌊Y⌋₊) := by
        exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) hlogY
    _ ≤ Real.log Y * (1 + Real.log Y) := by
        have hf : (1 : ℝ) ≤ ⌊Y⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hY)
        have : Real.log ⌊Y⌋₊ ≤ Real.log Y := Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
        nlinarith
    _ ≤ (1 + Real.log Y) ^ 2 := by nlinarith

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `l hl`. Simplify using `only [Finset.mem_filter] at hl`. Establish `h2 : (2 : ℝ) ≤ l` using `by exact_mod_cast hl.2.1`.

Establish `hlog : 0 ≤ Real.log l` using `Real.log_nonneg (by linarith)`. Rewrite using `[div_le_iff₀ (by linarith)]`. Rewrite using `[show 2 * (Real.log l / l) * ((l : ℝ) - 1) = Real.log l * (2 * ((l : ℝ) - 1) / l) by field_simp]`. Establish `: 1 ≤ 2 * ((l : ℝ) - 1) / l`. Rewrite using `[le_div_iff₀ (by linarith)]; linarith`.

Use the polynomial consequences of the given equalities and inequalities. Use `_ = 2 * ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l / l := by`. Rewrite using `[Finset.mul_sum]`. Use `_ ≤ 2 * ∑ l ∈ T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l / l := by`. Apply `mul_le_mul_of_nonneg_left _ (by norm_num)` to reduce the goal to its premises.

Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `l hl`. Simplify using `only [Finset.mem_filter] at hl ⊢`. Conclude with `⟨hl.1, by omega, hl.2.2⟩`. Introduce `l _ _`.

Establish `: (0:ℝ) ≤ l` using `by positivity`. Break down `Nat.eq_zero_or_pos l with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `: (1:ℝ) ≤ l` using `by exact_mod_cast h`.

Conclude with `div_nonneg (Real.log_nonneg this) (by linarith)`. Use `_ ≤ 2 * (1 + Real.log Y) ^ 2 := by`. Use `sum_log_div_le T Y hY` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_log_div_pred_le (T : Finset ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l / ((l : ℝ) - 1) ≤ 2 * (1 + Real.log Y) ^ 2 := by
  calc ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l / ((l : ℝ) - 1)
      ≤ ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ (l : ℝ) ≤ Y), 2 * (Real.log l / l) := by
        apply Finset.sum_le_sum
        intro l hl
        simp only [Finset.mem_filter] at hl
        have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.2.1
        have hlog : 0 ≤ Real.log l := Real.log_nonneg (by linarith)
        rw [div_le_iff₀ (by linarith)]
        rw [show 2 * (Real.log l / l) * ((l : ℝ) - 1) = Real.log l * (2 * ((l : ℝ) - 1) / l) by
          field_simp]
        have : 1 ≤ 2 * ((l : ℝ) - 1) / l := by
          rw [le_div_iff₀ (by linarith)]; linarith
        nlinarith
    _ = 2 * ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l / l := by
        rw [Finset.mul_sum]
    _ ≤ 2 * ∑ l ∈ T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l / l := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro l hl
          simp only [Finset.mem_filter] at hl ⊢
          exact ⟨hl.1, by omega, hl.2.2⟩
        · intro l _ _
          have : (0:ℝ) ≤ l := by positivity
          rcases Nat.eq_zero_or_pos l with h | h
          · subst h; simp
          · have : (1:ℝ) ≤ l := by exact_mod_cast h
            exact div_nonneg (Real.log_nonneg this) (by linarith)
    _ ≤ 2 * (1 + Real.log Y) ^ 2 := by
        have := sum_log_div_le T Y hY
        linarith

def frobeniusStickelbergerDetMulSigmaCube (u : ℝ) : ℝ := (Real.log u + 2) / u

/- English proof (translation)
Unfold `frobeniusStickelbergerDetMulSigmaCube`. Use `Real.log_nonneg hu` as an intermediate fact. Check the signs of the components of the expression.
-/
lemma logAddTwoDivSelf_nonneg {u : ℝ} (hu : 1 ≤ u) : 0 ≤ frobeniusStickelbergerDetMulSigmaCube u := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  have := Real.log_nonneg hu
  positivity

/- English proof (translation)
Establish `h` using `Real.log_le_sub_one_of_pos (div_pos hv hu)`. Rewrite `h` using `[Real.log_div hv.ne' hu.ne']`. Establish `: v / u - 1 = (v - u) / u` using `by field_simp`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma log_sub_le {u v : ℝ} (hu : 0 < u) (hv : 0 < v) : Real.log v - Real.log u ≤ (v - u) / u := by
  have h := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div hv.ne' hu.ne'] at h
  have : v / u - 1 = (v - u) / u := by field_simp
  linarith

/- English proof (translation)
Unfold `frobeniusStickelbergerDetMulSigmaCube`. Establish `hu0 : 0 < u` using `by linarith`. Establish `huM : 0 < u + M` using `by linarith`. Establish `ha : 0 ≤ Real.log u` using `Real.log_nonneg hu`. Establish `hb` using `log_sub_le hu0 huM`.

Establish `hX : 0 ≤ Real.log u * u + M - Real.log (u + M) * u`. Establish `: (u + M - u) / u * u = M` using `by field_simp; ring`. Establish `h2 : (Real.log (u + M) - Real.log u) * u ≤ (u + M - u) / u * u` using `mul_le_mul_of_nonneg_right hb hu0.le`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[div_le_div_iff₀ (by positivity) (by linarith)]`.

Rewrite using `[div_sub_div _ _ hu0.ne' huM.ne']`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ (by positivity)]`. Use polynomial arithmetic with `[mul_nonneg (by linarith : (0:ℝ) ≤ u + 2 * M) hX, mul_nonneg ha (mul_nonneg (by linarith : (0:ℝ) ≤ M) (by linarith : (0:ℝ) ≤ M)), mul_nonneg (by linarith : (0:ℝ) ≤ M) hu0.le, mul_pos huM huM, mul_pos hu0 huM]`.
-/
lemma step_le (u M : ℝ) (hu : 1 ≤ u) (hM : 1 ≤ M) :
    Real.log (u + M) / (u + M) ^ 2 ≤ (frobeniusStickelbergerDetMulSigmaCube u - frobeniusStickelbergerDetMulSigmaCube (u + M)) / M := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  have hu0 : 0 < u := by linarith
  have huM : 0 < u + M := by linarith
  have ha : 0 ≤ Real.log u := Real.log_nonneg hu
  have hb := log_sub_le hu0 huM
  have hX : 0 ≤ Real.log u * u + M - Real.log (u + M) * u := by
    have : (u + M - u) / u * u = M := by field_simp; ring
    have h2 : (Real.log (u + M) - Real.log u) * u ≤ (u + M - u) / u * u :=
      mul_le_mul_of_nonneg_right hb hu0.le
    nlinarith
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  rw [div_sub_div _ _ hu0.ne' huM.ne']
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ u + 2 * M) hX, mul_nonneg ha (mul_nonneg (by linarith : (0:ℝ) ≤ M) (by linarith : (0:ℝ) ≤ M)),
    mul_nonneg (by linarith : (0:ℝ) ≤ M) hu0.le, mul_pos huM huM, mul_pos hu0 huM]

/- English proof (translation)
Proceed by induction on `J with`. Consider the case `zero => simp`. Consider the case `succ J ih`. Rewrite using `[Finset.sum_range_succ]`. Establish `hJ : 1 ≤ u + (J : ℝ) * M`.

Establish `: (0:ℝ) ≤ (J : ℝ) * M` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs` using `step_le (u + (J : ℝ) * M) M hJ hM`. Establish `e1 : u + ((J : ℝ) + 1) * M = u + (J : ℝ) * M + M` using `by ring`. Establish `e2 : u + ((J + 1 : ℕ) : ℝ) * M = u + (J : ℝ) * M + M` using `by push_cast; ring`.

Rewrite using `[e1, e2]`. Establish `: (frobeniusStickelbergerDetMulSigmaCube u - frobeniusStickelbergerDetMulSigmaCube (u + ↑J * M)) / M + (frobeniusStickelbergerDetMulSigmaCube (u + ↑J * M) - frobeniusStickelbergerDetMulSigmaCube (u + ↑J * M + M)) / M = (frobeniusStickelbergerDetMulSigmaCube u - frobeniusStickelbe …` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma tele_le (u M : ℝ) (hu : 1 ≤ u) (hM : 1 ≤ M) (J : ℕ) :
    ∑ j ∈ Finset.range J, Real.log (u + ((j : ℝ) + 1) * M) / (u + ((j : ℝ) + 1) * M) ^ 2 ≤
      (frobeniusStickelbergerDetMulSigmaCube u - frobeniusStickelbergerDetMulSigmaCube (u + (J : ℝ) * M)) / M := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have hJ : 1 ≤ u + (J : ℝ) * M := by
      have : (0:ℝ) ≤ (J : ℝ) * M := by positivity
      linarith
    have hs := step_le (u + (J : ℝ) * M) M hJ hM
    have e1 : u + ((J : ℝ) + 1) * M = u + (J : ℝ) * M + M := by ring
    have e2 : u + ((J + 1 : ℕ) : ℝ) * M = u + (J : ℝ) * M + M := by push_cast; ring
    rw [e1, e2]
    have : (frobeniusStickelbergerDetMulSigmaCube u - frobeniusStickelbergerDetMulSigmaCube (u + ↑J * M)) / M + (frobeniusStickelbergerDetMulSigmaCube (u + ↑J * M) - frobeniusStickelbergerDetMulSigmaCube (u + ↑J * M + M)) / M =
        (frobeniusStickelbergerDetMulSigmaCube u - frobeniusStickelbergerDetMulSigmaCube (u + ↑J * M + M)) / M := by ring
    linarith

/- English proof (translation)
Use `set N := S.sup id with hN`. Establish `hsub : S ⊆ (Finset.range (N + 1)).image (fun j => u0 + j * M)`. Introduce `l hl`. Take `⟨j, rfl⟩` from `hS _ hl`. Rewrite using `[Finset.mem_image]`.

Use `⟨j, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_range]`. Establish `h1 : u0 + j * M ≤ N` using `Finset.le_sup (f := id) hl`. Establish `h2 : j ≤ j * M` using `Nat.le_mul_of_pos_right j hM`. Use linear arithmetic over natural numbers and integers.

Establish `hinj : Set.InjOn (fun j => u0 + j * M) ↑(Finset.range (N + 1))`. Introduce `a _ b _ h`. Simplify using `only at h`. Conclude with `Nat.eq_of_mul_eq_mul_right hM (by omega)`. Establish `hu' : (1 : ℝ) ≤ u0` using `by exact_mod_cast hu`.

Establish `hM' : (1 : ℝ) ≤ M` using `by exact_mod_cast hM`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum_of_subset_of_nonneg hsub` to reduce the goal to its premises. Introduce `l _ _`. Use `Real.log_natCast_nonneg l` as an intermediate fact.

Check the signs of the components of the expression. Use `_ = ∑ j ∈ Finset.range (N + 1), Real.log ((u0 + j * M : ℕ) : ℝ) / ((u0 + j * M : ℕ) : ℝ) ^ 2 := by`. Rewrite using `[Finset.sum_image hinj]`. Use `_ = ∑ j ∈ Finset.range N, Real.log ((u0 : ℝ) + ((j : ℝ) + 1) * M) / ((u0 : ℝ) + ((j : ℝ) + 1) * M) ^ 2 + Real.log u0 / (u0 : ℝ) ^ 2 := by`. Rewrite using `[Finset.sum_range_succ']`.

Use `push_cast`. Simplify using the standard rewrite rules. Use `_ ≤ (frobeniusStickelbergerDetMulSigmaCube u0 - frobeniusStickelbergerDetMulSigmaCube (u0 + (N : ℝ) * M)) / M + Real.log u0 / (u0 : ℝ) ^ 2 := by`. Use `tele_le (u0 : ℝ) (M : ℝ) hu' hM' N` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `_ ≤ Real.log u0 / (u0 : ℝ) ^ 2 + frobeniusStickelbergerDetMulSigmaCube u0 / M := by`. Establish `h0 : 0 ≤ frobeniusStickelbergerDetMulSigmaCube (u0 + (N : ℝ) * M)` using `logAddTwoDivSelf_nonneg (by`. Establish `: (0:ℝ) ≤ (N : ℝ) * M` using `by positivity`. Use the proof step `linarith)`. Establish `: (frobeniusStickelbergerDetMulSigmaCube u0 - frobeniusStickelbergerDetMulSigmaCube (u0 + (N : ℝ) * M)) / M ≤ frobeniusStickelbergerDetMulSigmaCube u0 / M` using `div_le_div_of_nonneg_right (by linarith) (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma ap_sum (S : Finset ℕ) (u0 M : ℕ) (hu : 1 ≤ u0) (hM : 1 ≤ M)
    (hS : ∀ l ∈ S, ∃ j : ℕ, l = u0 + j * M) :
    ∑ l ∈ S, Real.log l / (l : ℝ) ^ 2 ≤ Real.log u0 / (u0 : ℝ) ^ 2 + frobeniusStickelbergerDetMulSigmaCube u0 / M := by
  classical
  set N := S.sup id with hN
  have hsub : S ⊆ (Finset.range (N + 1)).image (fun j => u0 + j * M) := by
    intro l hl
    obtain ⟨j, rfl⟩ := hS _ hl
    rw [Finset.mem_image]
    refine ⟨j, ?_, rfl⟩
    rw [Finset.mem_range]
    have h1 : u0 + j * M ≤ N := Finset.le_sup (f := id) hl
    have h2 : j ≤ j * M := Nat.le_mul_of_pos_right j hM
    omega
  have hinj : Set.InjOn (fun j => u0 + j * M) ↑(Finset.range (N + 1)) := by
    intro a _ b _ h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_right hM (by omega)
  have hu' : (1 : ℝ) ≤ u0 := by exact_mod_cast hu
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  calc ∑ l ∈ S, Real.log l / (l : ℝ) ^ 2
      ≤ ∑ l ∈ (Finset.range (N + 1)).image (fun j => u0 + j * M), Real.log l / (l : ℝ) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro l _ _
        have := Real.log_natCast_nonneg l
        positivity
    _ = ∑ j ∈ Finset.range (N + 1), Real.log ((u0 + j * M : ℕ) : ℝ) / ((u0 + j * M : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_image hinj]
    _ = ∑ j ∈ Finset.range N, Real.log ((u0 : ℝ) + ((j : ℝ) + 1) * M) / ((u0 : ℝ) + ((j : ℝ) + 1) * M) ^ 2
          + Real.log u0 / (u0 : ℝ) ^ 2 := by
        rw [Finset.sum_range_succ']
        push_cast
        simp
    _ ≤ (frobeniusStickelbergerDetMulSigmaCube u0 - frobeniusStickelbergerDetMulSigmaCube (u0 + (N : ℝ) * M)) / M + Real.log u0 / (u0 : ℝ) ^ 2 := by
        have := tele_le (u0 : ℝ) (M : ℝ) hu' hM' N
        linarith
    _ ≤ Real.log u0 / (u0 : ℝ) ^ 2 + frobeniusStickelbergerDetMulSigmaCube u0 / M := by
        have h0 : 0 ≤ frobeniusStickelbergerDetMulSigmaCube (u0 + (N : ℝ) * M) := logAddTwoDivSelf_nonneg (by
          have : (0:ℝ) ≤ (N : ℝ) * M := by positivity
          linarith)
        have : (frobeniusStickelbergerDetMulSigmaCube u0 - frobeniusStickelbergerDetMulSigmaCube (u0 + (N : ℝ) * M)) / M ≤ frobeniusStickelbergerDetMulSigmaCube u0 / M :=
          div_le_div_of_nonneg_right (by linarith) (by linarith)
        linarith

/- English proof (translation)
Establish `h` using `ap_sum (T.filter (fun l : ℕ => 2 ≤ l)) 1 1 le_rfl le_rfl (by`. Introduce `l hl`. Simplify using `only [Finset.mem_filter] at hl`. Conclude with `⟨l - 1, by omega⟩)`. Establish `: frobeniusStickelbergerDetMulSigmaCube ((1 : ℕ) : ℝ) = 2` using `by unfold frobeniusStickelbergerDetMulSigmaCube; simp`.

Rewrite `h` using `[this]`. Simplify using `using h`.
-/
theorem sum_log_div_sq_le (T : Finset ℕ) :
    ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l), Real.log l / (l : ℝ) ^ 2 ≤ 2 := by
  have h := ap_sum (T.filter (fun l : ℕ => 2 ≤ l)) 1 1 le_rfl le_rfl (by
    intro l hl
    simp only [Finset.mem_filter] at hl
    exact ⟨l - 1, by omega⟩)
  have : frobeniusStickelbergerDetMulSigmaCube ((1 : ℕ) : ℝ) = 2 := by unfold frobeniusStickelbergerDetMulSigmaCube; simp
  rw [this] at h
  simpa using h

/- English proof (translation)
Use `set c := ⌈A⌉₊ with hc`. Establish `hcA : A ≤ (c : ℝ)` using `Nat.le_ceil A`. Establish `hcA' : (c : ℝ) < A + 1` using `Nat.ceil_lt_add_one (by linarith)`. Establish `hc2 : 2 ≤ c`. Establish `: (1 : ℝ) < c` using `by linarith`.

Conclude with `this` after adjusting the coercions. Establish `hu : 1 ≤ c - 1` using `by omega`. Establish `hcast : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1`. Rewrite using `[Nat.cast_sub (by omega)]; simp`. Establish `h` using `ap_sum (T.filter (fun l : ℕ => A ≤ (l : ℝ))) (c - 1) 1 hu le_rfl (by`.

Introduce `l hl`. Simplify using `only [Finset.mem_filter] at hl`. Establish `: c ≤ l` using `Nat.ceil_le.mpr hl.2`. Conclude with `⟨l - (c - 1), by omega⟩)`. Rewrite `h` using `[hcast]`.

Unfold `frobeniusStickelbergerDetMulSigmaCube at h`. Use `set u := (c : ℝ) - 1 with hu_def`. Establish `hu1 : 1 ≤ u`. Establish `: (2:ℝ) ≤ c` using `by exact_mod_cast hc2`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `huA : u < A` using `by linarith`. Establish `huA2 : A / 2 ≤ u` using `by linarith`. Establish `hlogu : Real.log u ≤ Real.log A` using `Real.log_le_log (by linarith) huA.le`. Establish `hlogu0 : 0 ≤ Real.log u` using `Real.log_nonneg hu1`. Establish `hA0 : 0 < A` using `by linarith`.

Simplify using `only [Nat.cast_one, div_one] at h`. Establish `h1 : Real.log u / u ^ 2 ≤ Real.log u / u`. Apply `div_le_div_of_nonneg_left hlogu0 (by linarith)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : (Real.log u + 2) / u ≤ (Real.log A + 2) / (A / 2)`.

Apply `div_le_div₀ (by linarith) (by linarith) (by linarith) huA2` to reduce the goal to its premises. Establish `h3 : Real.log u / u ≤ (Real.log A + 2) / (A / 2)`. Apply `div_le_div₀ (by linarith) (by linarith) (by linarith) huA2` to reduce the goal to its premises. Establish `h4 : (Real.log A + 2) / (A / 2) = 2 * (Real.log A + 2) / A`. Clear the denominators using the available nonvanishing facts.

Establish `h5 : 4 * (Real.log A + 2) / A = 2 * (Real.log A + 2) / A + 2 * (Real.log A + 2) / A` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_log_div_sq_tail (T : Finset ℕ) (A : ℝ) (hA : 2 ≤ A) :
    ∑ l ∈ T.filter (fun l : ℕ => A ≤ (l : ℝ)), Real.log l / (l : ℝ) ^ 2 ≤ 4 * (Real.log A + 2) / A := by
  set c := ⌈A⌉₊ with hc
  have hcA : A ≤ (c : ℝ) := Nat.le_ceil A
  have hcA' : (c : ℝ) < A + 1 := Nat.ceil_lt_add_one (by linarith)
  have hc2 : 2 ≤ c := by
    have : (1 : ℝ) < c := by linarith
    exact_mod_cast this
  have hu : 1 ≤ c - 1 := by omega
  have hcast : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h := ap_sum (T.filter (fun l : ℕ => A ≤ (l : ℝ))) (c - 1) 1 hu le_rfl (by
    intro l hl
    simp only [Finset.mem_filter] at hl
    have : c ≤ l := Nat.ceil_le.mpr hl.2
    exact ⟨l - (c - 1), by omega⟩)
  rw [hcast] at h
  unfold frobeniusStickelbergerDetMulSigmaCube at h
  set u := (c : ℝ) - 1 with hu_def
  have hu1 : 1 ≤ u := by
    have : (2:ℝ) ≤ c := by exact_mod_cast hc2
    linarith
  have huA : u < A := by linarith
  have huA2 : A / 2 ≤ u := by linarith
  have hlogu : Real.log u ≤ Real.log A := Real.log_le_log (by linarith) huA.le
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hA0 : 0 < A := by linarith
  simp only [Nat.cast_one, div_one] at h
  have h1 : Real.log u / u ^ 2 ≤ Real.log u / u := by
    apply div_le_div_of_nonneg_left hlogu0 (by linarith)
    nlinarith
  have h2 : (Real.log u + 2) / u ≤ (Real.log A + 2) / (A / 2) := by
    apply div_le_div₀ (by linarith) (by linarith) (by linarith) huA2
  have h3 : Real.log u / u ≤ (Real.log A + 2) / (A / 2) := by
    apply div_le_div₀ (by linarith) (by linarith) (by linarith) huA2
  have h4 : (Real.log A + 2) / (A / 2) = 2 * (Real.log A + 2) / A := by
    field_simp
  have h5 : 4 * (Real.log A + 2) / A = 2 * (Real.log A + 2) / A + 2 * (Real.log A + 2) / A := by ring
  linarith

/- English proof (translation)
Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma log_ge_one_of_three {Y : ℝ} (hY : 3 ≤ Y) : 1 ≤ Real.log Y := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  norm_num at this
  linarith

/- English proof (translation)
Establish `hY0 : 0 < Y` using `by linarith`. Establish `hu0 : 0 < u` using `by linarith`. Establish `hl` using `log_ge_one_of_three hY`. Establish `hb` using `log_sub_le hY0 hu0`. Establish `hd : (Real.log u - Real.log Y) * Y ≤ u - Y`.

Use `mul_le_mul_of_nonneg_right hb hY0.le` as an intermediate fact. Establish `e : (u - Y) / Y * Y = u - Y` using `by field_simp`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity)]`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hl), mul_nonneg (sub_nonneg.mpr hu) hY0.le, mul_nonneg (mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hl)) (by linarith : (0:ℝ) ≤ u + Y), mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hu)]`.
-/
lemma logsq_anti {u Y : ℝ} (hY : 3 ≤ Y) (hu : Y ≤ u) :
    Real.log u / u ^ 2 ≤ Real.log Y / Y ^ 2 := by
  have hY0 : 0 < Y := by linarith
  have hu0 : 0 < u := by linarith
  have hl := log_ge_one_of_three hY
  have hb := log_sub_le hY0 hu0
  have hd : (Real.log u - Real.log Y) * Y ≤ u - Y := by
    have := mul_le_mul_of_nonneg_right hb hY0.le
    have e : (u - Y) / Y * Y = u - Y := by field_simp
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hl), mul_nonneg (sub_nonneg.mpr hu) hY0.le,
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hl)) (by linarith : (0:ℝ) ≤ u + Y),
    mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hu)]

/- English proof (translation)
Unfold `frobeniusStickelbergerDetMulSigmaCube`. Establish `hY0 : 0 < Y` using `by linarith`. Establish `hu0 : 0 < u` using `by linarith`. Establish `hl` using `Real.log_nonneg hY`. Establish `hb` using `log_sub_le hY0 hu0`.

Establish `hd : (Real.log u - Real.log Y) * Y ≤ u - Y`. Use `mul_le_mul_of_nonneg_right hb hY0.le` as an intermediate fact. Establish `e : (u - Y) / Y * Y = u - Y` using `by field_simp`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[div_le_div_iff₀ hu0 hY0]`.

Use polynomial arithmetic with `[mul_nonneg hl (sub_nonneg.mpr hu)]`.
-/
lemma logAddTwoDivSelf_le_of_le {u Y : ℝ} (hY : 1 ≤ Y) (hu : Y ≤ u) : frobeniusStickelbergerDetMulSigmaCube u ≤ frobeniusStickelbergerDetMulSigmaCube Y := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  have hY0 : 0 < Y := by linarith
  have hu0 : 0 < u := by linarith
  have hl := Real.log_nonneg hY
  have hb := log_sub_le hY0 hu0
  have hd : (Real.log u - Real.log Y) * Y ≤ u - Y := by
    have := mul_le_mul_of_nonneg_right hb hY0.le
    have e : (u - Y) / Y * Y = u - Y := by field_simp
    linarith
  rw [div_le_div_iff₀ hu0 hY0]
  nlinarith [mul_nonneg hl (sub_nonneg.mpr hu)]

/- English proof (translation)
Establish `hM4 : (4 : ℝ) ≤ M` using `by linarith`. Establish `hM4n : 4 ≤ M` using `by exact_mod_cast hM4`. Establish `hMpos : (0 : ℝ) < M` using `by linarith`. Use `set f : ℕ → ℝ := fun l => Real.log l / (l : ℝ) ^ 2 with hf`. Establish `fnn : ∀ l, 0 ≤ f l`.

Introduce `l`. Use `Real.log_natCast_nonneg l` as an intermediate fact. Simplify using `only [hf]`. Check the signs of the components of the expression. Establish `hsplit : ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ (l % M = 1 ∨ l % M = M - 1)), f l ≤ ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ l % M = 1), f l + ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ l % M = M - 1), f l`.

Rewrite using `[Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `l _`. Use `fnn l` as an intermediate fact. Apply the tactic sequence `split_ifs <;> first | linarith | (exfalso; tauto)`.

Establish `h1` using `ap_sum (T.filter (fun l : ℕ => 2 ≤ l ∧ l % M = 1)) (M + 1) M (by omega) (by omega) (by`. Introduce `l hl`. Simplify using `only [Finset.mem_filter] at hl`. Establish `h` using `Nat.div_add_mod l M`. Rewrite `h` using `[hl.2.2]`.

Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : ∃ q, l / M = q + 1 := by`. Break down `Nat.eq_zero_or_pos (l / M) with h0 | h0` into its components or cases. Rewrite `h` using `[h0]`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨l / M - 1, by omega⟩`.

Rewrite `h` using `[hq]`. Conclude with `⟨q, by linarith⟩)`. Establish `h2` using `ap_sum (T.filter (fun l : ℕ => 2 ≤ l ∧ l % M = M - 1)) (M - 1) M (by omega) (by omega) (by`. Introduce `l hl`. Simplify using `only [Finset.mem_filter] at hl`.

Establish `h` using `Nat.div_add_mod l M`. Rewrite `h` using `[hl.2.2]`. Conclude with `⟨l / M, by linarith⟩)`. Establish `c1 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1` using `by push_cast; ring`. Establish `c2 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1` using `by rw [Nat.cast_sub (by omega)]; simp`.

Rewrite `h1` using `[c1]`. Rewrite `h2` using `[c2]`. Establish `a1 : Real.log ((M : ℝ) + 1) / ((M : ℝ) + 1) ^ 2 ≤ Real.log Y / Y ^ 2` using `logsq_anti hY (by linarith)`. Establish `a2 : Real.log ((M : ℝ) - 1) / ((M : ℝ) - 1) ^ 2 ≤ Real.log Y / Y ^ 2` using `logsq_anti hY hYM`. Establish `b1 : frobeniusStickelbergerDetMulSigmaCube ((M : ℝ) + 1) / M ≤ frobeniusStickelbergerDetMulSigmaCube Y / M` using `div_le_div_of_nonneg_right (logAddTwoDivSelf_le_of_le (by linarith) (by linarith)) hMpos.le`.

Establish `b2 : frobeniusStickelbergerDetMulSigmaCube ((M : ℝ) - 1) / M ≤ frobeniusStickelbergerDetMulSigmaCube Y / M` using `div_le_div_of_nonneg_right (logAddTwoDivSelf_le_of_le (by linarith) hYM) hMpos.le`. Establish `e : frobeniusStickelbergerDetMulSigmaCube Y / M = (Real.log Y + 2) / (Y * M)` using `by unfold frobeniusStickelbergerDetMulSigmaCube; rw [div_div]`. Establish `e2 : 2 * Real.log Y / Y ^ 2 + 2 * (Real.log Y + 2) / (Y * M) = 2 * (Real.log Y / Y ^ 2) + 2 * ((Real.log Y + 2) / (Y * M))` using `by ring`. Simplify using `only [hf] at hsplit`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_log_div_sq_mod_pm_one_le (T : Finset ℕ) (M : ℕ) (Y : ℝ) (hY : 3 ≤ Y) (hYM : Y ≤ (M : ℝ) - 1) :
    ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ (l % M = 1 ∨ l % M = M - 1)), Real.log l / (l : ℝ) ^ 2 ≤
      2 * Real.log Y / Y ^ 2 + 2 * (Real.log Y + 2) / (Y * M) := by
  classical
  have hM4 : (4 : ℝ) ≤ M := by linarith
  have hM4n : 4 ≤ M := by exact_mod_cast hM4
  have hMpos : (0 : ℝ) < M := by linarith
  set f : ℕ → ℝ := fun l => Real.log l / (l : ℝ) ^ 2 with hf
  have fnn : ∀ l, 0 ≤ f l := by
    intro l
    have := Real.log_natCast_nonneg l
    simp only [hf]
    positivity
  have hsplit : ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ (l % M = 1 ∨ l % M = M - 1)), f l ≤
      ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ l % M = 1), f l +
      ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ l % M = M - 1), f l := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro l _
    have := fnn l
    split_ifs <;> first | linarith | (exfalso; tauto)
  have h1 := ap_sum (T.filter (fun l : ℕ => 2 ≤ l ∧ l % M = 1)) (M + 1) M (by omega) (by omega) (by
    intro l hl
    simp only [Finset.mem_filter] at hl
    have h := Nat.div_add_mod l M
    rw [hl.2.2] at h
    obtain ⟨q, hq⟩ : ∃ q, l / M = q + 1 := by
      rcases Nat.eq_zero_or_pos (l / M) with h0 | h0
      · rw [h0] at h; omega
      · exact ⟨l / M - 1, by omega⟩
    rw [hq] at h
    exact ⟨q, by linarith⟩)
  have h2 := ap_sum (T.filter (fun l : ℕ => 2 ≤ l ∧ l % M = M - 1)) (M - 1) M (by omega) (by omega) (by
    intro l hl
    simp only [Finset.mem_filter] at hl
    have h := Nat.div_add_mod l M
    rw [hl.2.2] at h
    exact ⟨l / M, by linarith⟩)
  have c1 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
  have c2 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [c1] at h1
  rw [c2] at h2
  have a1 : Real.log ((M : ℝ) + 1) / ((M : ℝ) + 1) ^ 2 ≤ Real.log Y / Y ^ 2 := logsq_anti hY (by linarith)
  have a2 : Real.log ((M : ℝ) - 1) / ((M : ℝ) - 1) ^ 2 ≤ Real.log Y / Y ^ 2 := logsq_anti hY hYM
  have b1 : frobeniusStickelbergerDetMulSigmaCube ((M : ℝ) + 1) / M ≤ frobeniusStickelbergerDetMulSigmaCube Y / M :=
    div_le_div_of_nonneg_right (logAddTwoDivSelf_le_of_le (by linarith) (by linarith)) hMpos.le
  have b2 : frobeniusStickelbergerDetMulSigmaCube ((M : ℝ) - 1) / M ≤ frobeniusStickelbergerDetMulSigmaCube Y / M :=
    div_le_div_of_nonneg_right (logAddTwoDivSelf_le_of_le (by linarith) hYM) hMpos.le
  have e : frobeniusStickelbergerDetMulSigmaCube Y / M = (Real.log Y + 2) / (Y * M) := by unfold frobeniusStickelbergerDetMulSigmaCube; rw [div_div]
  have e2 : 2 * Real.log Y / Y ^ 2 + 2 * (Real.log Y + 2) / (Y * M) =
      2 * (Real.log Y / Y ^ 2) + 2 * ((Real.log Y + 2) / (Y * M)) := by ring
  simp only [hf] at hsplit
  linarith

/- English proof (translation)
Establish `hlog : Real.log n = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p`. Rewrite using `[Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]`. Establish `hT' : ∑ p ∈ T, (padicValNat p n : ℝ) * Real.log p = ∑ p ∈ T, (n.factorization p : ℝ) * Real.log p`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `p hp`.

Rewrite using `[Nat.factorization_def n (hT p hp)]`. Rewrite using `[hT', hlog]`. Combine the equalities or inequalities in the displayed calculation. Use `symm`. Apply `Finset.sum_subset Finset.inter_subset_left` to reduce the goal to its premises.

Introduce `p hp hnot`. Establish `: p ∉ n.primeFactors` using `fun h => hnot (Finset.mem_inter.mpr ⟨hp, h⟩)`. Rewrite `this` using `[← Nat.support_factorization, Finsupp.notMem_support_iff]`. Simplify using `[this]`. Use `_ ≤ ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by`.

Apply `Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right` to reduce the goal to its premises. Introduce `p _ _`. Use `Real.log_natCast_nonneg p` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem sum_padicVal_log_le (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (n : ℕ) (hn : n ≠ 0) :
    ∑ p ∈ T, (padicValNat p n : ℝ) * Real.log p ≤ Real.log n := by
  classical
  have hlog : Real.log n = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  have hT' : ∑ p ∈ T, (padicValNat p n : ℝ) * Real.log p =
      ∑ p ∈ T, (n.factorization p : ℝ) * Real.log p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.factorization_def n (hT p hp)]
  rw [hT', hlog]
  calc ∑ p ∈ T, (n.factorization p : ℝ) * Real.log p
      = ∑ p ∈ T ∩ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro p hp hnot
        have : p ∉ n.primeFactors := fun h => hnot (Finset.mem_inter.mpr ⟨hp, h⟩)
        rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at this
        simp [this]
    _ ≤ ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro p _ _
        have := Real.log_natCast_nonneg p
        positivity

end Formalism.MainNotions.TwistedPlaces.Sums

end

namespace Formalism.MainNotions.TwistedPlaces.Cong

/- English proof (translation)
Apply `IsCoprime.pow_left` to reduce the goal to its premises. Rewrite using `[Prime.coprime_iff_not_dvd Int.prime_two, ← even_iff_two_dvd, Int.not_even_iff_odd]`. Conclude with `hg`.
-/
lemma coprime_two_pow_of_odd (K : ℕ) (g : ℤ) (hg : Odd g) : IsCoprime ((2:ℤ) ^ K) g := by
  apply IsCoprime.pow_left
  rw [Prime.coprime_iff_not_dvd Int.prime_two, ← even_iff_two_dvd, Int.not_even_iff_odd]
  exact hg

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_range_succ, Int.even_add, ih, Nat.even_add_one]`. Establish `: ¬ Even (x ^ n)`.

Rewrite using `[Int.not_even_iff_odd]`. Conclude with `hx.pow`. The claim follows by propositional logic.
-/
lemma geom_sum_even_iff (x : ℤ) (hx : Odd x) (n : ℕ) :
    Even (∑ i ∈ Finset.range n, x ^ i) ↔ Even n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Int.even_add, ih, Nat.even_add_one]
    have : ¬ Even (x ^ n) := by
      rw [Int.not_even_iff_odd]; exact hx.pow
    tauto

/- English proof (translation)
Establish `hg : Odd (∑ i ∈ Finset.range m, x ^ i)`. Rewrite using `[← Int.not_even_iff_odd, geom_sum_even_iff x hx m, Nat.not_even_iff_odd]`. Conclude with `hm`. Rewrite `h` using `[← mul_geom_sum]`. Conclude with `(coprime_two_pow_of_odd K _ hg).dvd_of_dvd_mul_right h`.
-/
lemma dvd_sub_one_of_pow_odd (K : ℕ) (x : ℤ) (hx : Odd x) (m : ℕ) (hm : Odd m)
    (h : (2:ℤ) ^ K ∣ x ^ m - 1) : (2:ℤ) ^ K ∣ x - 1 := by
  have hg : Odd (∑ i ∈ Finset.range m, x ^ i) := by
    rw [← Int.not_even_iff_odd, geom_sum_even_iff x hx m, Nat.not_even_iff_odd]; exact hm
  rw [← mul_geom_sum] at h
  exact (coprime_two_pow_of_odd K _ hg).dvd_of_dvd_mul_right h

/- English proof (translation)
Break down `h with h | h` into its components or cases. Conclude with `Or.inl (dvd_sub_one_of_pow_odd K x hx m hm h)`. Use `right`. Establish `h' : (2:ℤ) ^ K ∣ (-x) ^ m - 1`. Rewrite using `[hm.neg_pow]`.

Establish `e : -x ^ m - 1 = -(x ^ m + 1)` using `by ring`. Rewrite using `[e, dvd_neg]`. Conclude with `h`. Use `dvd_sub_one_of_pow_odd K (-x) hx.neg m hm h'` as an intermediate fact. Establish `e : -x - 1 = -(x + 1)` using `by ring`.

Rewrite `this` using `[e, dvd_neg]`. Then use the resulting hypothesis.
-/
lemma pm_of_pow_odd (K : ℕ) (x : ℤ) (hx : Odd x) (m : ℕ) (hm : Odd m)
    (h : (2:ℤ) ^ K ∣ x ^ m - 1 ∨ (2:ℤ) ^ K ∣ x ^ m + 1) :
    (2:ℤ) ^ K ∣ x - 1 ∨ (2:ℤ) ^ K ∣ x + 1 := by
  rcases h with h | h
  · exact Or.inl (dvd_sub_one_of_pow_odd K x hx m hm h)
  · right
    have h' : (2:ℤ) ^ K ∣ (-x) ^ m - 1 := by
      rw [hm.neg_pow]
      have e : -x ^ m - 1 = -(x ^ m + 1) := by ring
      rw [e, dvd_neg]; exact h
    have := dvd_sub_one_of_pow_odd K (-x) hx.neg m hm h'
    have e : -x - 1 = -(x + 1) := by ring
    rwa [e, dvd_neg] at this

/- English proof (translation)
Take `⟨b, rfl⟩` from `hy`. Break down `K with _ | _ | k` into its components or cases. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using `only [Nat.add_sub_cancel]`.

Establish `e4 : (2:ℤ) ^ (k + 1 + 1) = 4 * 2 ^ k` using `by ring`. Rewrite `h` using `[e4]`. Break down `h with h | h` into its components or cases. Establish `e : (2 * b + 1) ^ 2 - 1 = 4 * (b * (b + 1))` using `by ring`. Rewrite `h` using `[e]`.

Establish `h'` using `(mul_dvd_mul_iff_left (by norm_num : (4:ℤ) ≠ 0)).mp h`. Break down `Int.even_or_odd b with hb | hb` into its components or cases. Use `left`. Establish `hb1 : Odd (b + 1)` using `hb.add_one`. Establish `: (2:ℤ) ^ k ∣ b` using `(coprime_two_pow_of_odd k _ hb1).dvd_of_dvd_mul_right h'`.

Establish `e2 : 2 * b + 1 - 1 = 2 * b` using `by ring`. Rewrite using `[e2, pow_succ, mul_comm _ (2:ℤ)]`. Conclude with `mul_dvd_mul_left 2 this`. Use `right`. Establish `: (2:ℤ) ^ k ∣ b + 1` using `(coprime_two_pow_of_odd k _ hb).dvd_of_dvd_mul_left h'`.

Establish `e2 : 2 * b + 1 + 1 = 2 * (b + 1)` using `by ring`. Rewrite using `[e2, pow_succ, mul_comm _ (2:ℤ)]`. Conclude with `mul_dvd_mul_left 2 this`. It suffices to derive a contradiction. Establish `e : (2 * b + 1) ^ 2 + 1 = 4 * (b * (b + 1)) + 2` using `by ring`.

Rewrite `h` using `[e]`. Establish `h4 : (4:ℤ) ∣ 4 * (b * (b + 1)) + 2` using `dvd_trans ⟨2 ^ k, rfl⟩ h`. Generalize the expression as in `b * (b + 1) = t at h4`. Use linear arithmetic over natural numbers and integers.
-/
lemma pm_of_sq (K : ℕ) (y : ℤ) (hy : Odd y)
    (h : (2:ℤ) ^ K ∣ y ^ 2 - 1 ∨ (2:ℤ) ^ K ∣ y ^ 2 + 1) :
    (2:ℤ) ^ (K - 1) ∣ y - 1 ∨ (2:ℤ) ^ (K - 1) ∣ y + 1 := by
  obtain ⟨b, rfl⟩ := hy
  rcases K with _ | _ | k
  · simp
  · simp
  simp only [Nat.add_sub_cancel]
  have e4 : (2:ℤ) ^ (k + 1 + 1) = 4 * 2 ^ k := by ring
  rw [e4] at h
  rcases h with h | h
  · have e : (2 * b + 1) ^ 2 - 1 = 4 * (b * (b + 1)) := by ring
    rw [e] at h
    have h' := (mul_dvd_mul_iff_left (by norm_num : (4:ℤ) ≠ 0)).mp h
    rcases Int.even_or_odd b with hb | hb
    · left
      have hb1 : Odd (b + 1) := hb.add_one
      have : (2:ℤ) ^ k ∣ b := (coprime_two_pow_of_odd k _ hb1).dvd_of_dvd_mul_right h'
      have e2 : 2 * b + 1 - 1 = 2 * b := by ring
      rw [e2, pow_succ, mul_comm _ (2:ℤ)]
      exact mul_dvd_mul_left 2 this
    · right
      have : (2:ℤ) ^ k ∣ b + 1 := (coprime_two_pow_of_odd k _ hb).dvd_of_dvd_mul_left h'
      have e2 : 2 * b + 1 + 1 = 2 * (b + 1) := by ring
      rw [e2, pow_succ, mul_comm _ (2:ℤ)]
      exact mul_dvd_mul_left 2 this
  · exfalso
    have e : (2 * b + 1) ^ 2 + 1 = 4 * (b * (b + 1)) + 2 := by ring
    rw [e] at h
    have h4 : (4:ℤ) ∣ 4 * (b * (b + 1)) + 2 := dvd_trans ⟨2 ^ k, rfl⟩ h
    generalize b * (b + 1) = t at h4
    omega

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => intro K x _ h`. Simplify using `using h`. Consider the case `succ a ih`. Introduce `K x hx h`.

Establish `h2 : (2:ℤ) ^ K ∣ (x ^ (2 ^ a)) ^ 2 - 1 ∨ (2:ℤ) ^ K ∣ (x ^ (2 ^ a)) ^ 2 + 1`. Rewrite using `[← pow_mul, ← pow_succ]` and apply the resulting hypothesis. Use `ih (K - 1) x hx (pm_of_sq K _ hx.pow h2)` as an intermediate fact. Rewrite `this` using `[Nat.sub_sub, Nat.add_comm 1 a]`. Then use the resulting hypothesis.
-/
lemma pm_of_two_pow (a : ℕ) : ∀ (K : ℕ) (x : ℤ), Odd x →
    ((2:ℤ) ^ K ∣ x ^ (2 ^ a) - 1 ∨ (2:ℤ) ^ K ∣ x ^ (2 ^ a) + 1) →
    ((2:ℤ) ^ (K - a) ∣ x - 1 ∨ (2:ℤ) ^ (K - a) ∣ x + 1) := by
  induction a with
  | zero => intro K x _ h; simpa using h
  | succ a ih =>
    intro K x hx h
    have h2 : (2:ℤ) ^ K ∣ (x ^ (2 ^ a)) ^ 2 - 1 ∨ (2:ℤ) ^ K ∣ (x ^ (2 ^ a)) ^ 2 + 1 := by
      rwa [← pow_mul, ← pow_succ]
    have := ih (K - 1) x hx (pm_of_sq K _ hx.pow h2)
    rwa [Nat.sub_sub, Nat.add_comm 1 a] at this

/- English proof (translation)
Take `⟨a, m, hm, rfl⟩` from `Nat.exists_eq_two_pow_mul_odd ho.ne'`. Establish `hv : padicValNat 2 (2 ^ a * m) = a`. Rewrite using `[padicValNat.mul (by positivity) hm.pos.ne', padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]), add_zero]`. Rewrite using `[hv]`. Apply `pm_of_two_pow a K x hx` to reduce the goal to its premises.

Rewrite `h` using `[pow_mul]`. Conclude with `pm_of_pow_odd K _ hx.pow m hm h`.
-/
lemma pm_int (K : ℕ) (x : ℤ) (hx : Odd x) (o : ℕ) (ho : 0 < o)
    (h : (2:ℤ) ^ K ∣ x ^ o - 1 ∨ (2:ℤ) ^ K ∣ x ^ o + 1) :
    (2:ℤ) ^ (K - padicValNat 2 o) ∣ x - 1 ∨ (2:ℤ) ^ (K - padicValNat 2 o) ∣ x + 1 := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd ho.ne'
  have hv : padicValNat 2 (2 ^ a * m) = a := by
    rw [padicValNat.mul (by positivity) hm.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]), add_zero]
  rw [hv]
  apply pm_of_two_pow a K x hx
  rw [pow_mul] at h
  exact pm_of_pow_odd K _ hx.pow m hm h

/- English proof (translation)
Establish `hc : Nat.Coprime l (2 ^ K)`. Apply `Nat.Coprime.pow_right` to reduce the goal to its premises. Conclude with `Nat.coprime_two_right.mpr hl`. Use `⟨Nat.totient (2 ^ K), Nat.totient_pos.mpr (by positivity), Or.inl ?_⟩` and prove the remaining obligations. Establish `h1` using `Nat.ModEq.pow_totient hc`.

Establish `h2` using `(ZMod.natCast_eq_natCast_iff _ _ _).mpr h1`. Move the coercions through the operations in `at h2`. Conclude with `h2`.
-/
theorem ordPM_nonempty (K l : ℕ) (hl : Odd l) :
    {o : ℕ | 0 < o ∧ ((l : ZMod (2 ^ K)) ^ o = 1 ∨ (l : ZMod (2 ^ K)) ^ o = -1)}.Nonempty := by
  have hc : Nat.Coprime l (2 ^ K) := by
    apply Nat.Coprime.pow_right
    exact Nat.coprime_two_right.mpr hl
  refine ⟨Nat.totient (2 ^ K), Nat.totient_pos.mpr (by positivity), Or.inl ?_⟩
  have h1 := Nat.ModEq.pow_totient hc
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
  push_cast at h2
  exact h2

/- English proof (translation)
Establish `hlz : Odd (l : ℤ)` using `by exact_mod_cast hl`. Establish `hint : (2:ℤ) ^ K ∣ (l:ℤ) ^ o - 1 ∨ (2:ℤ) ^ K ∣ (l:ℤ) ^ o + 1`. Break down `h with h | h` into its components or cases. Use `left`. Establish `h0 : (((l:ℤ) ^ o - 1 : ℤ) : ZMod (2 ^ K)) = 0` using `by push_cast; rw [h]; ring`.

Use `(ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ K)).mp h0` as an intermediate fact. Conclude with `this` after adjusting the coercions. Use `right`. Establish `h0 : (((l:ℤ) ^ o + 1 : ℤ) : ZMod (2 ^ K)) = 0` using `by push_cast; rw [h]; ring`. Use `(ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ K)).mp h0` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Establish `key` using `pm_int K (l:ℤ) hlz o ho hint`. Generalize the expression as in `K - padicValNat 2 o = s at key ⊢`. Break down `Nat.eq_zero_or_pos s with hs | hs` into its components or cases. Substitute `hs` using the available equality.

Use `right`. Simplify using `[Nat.mod_one]`. Establish `hN : 2 ≤ 2 ^ s`. Combine the equalities or inequalities in the displayed calculation. Use `_ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs`.

Establish `hl1 : 1 ≤ l` using `hl.pos`. Break down `key with h1 | h1` into its components or cases. Use `left`. Establish `h2 : 2 ^ s ∣ l - 1`. Establish `: ((2 ^ s : ℕ) : ℤ) ∣ ((l - 1 : ℕ) : ℤ)`.

Rewrite using `[Nat.cast_sub hl1]`. Use `push_cast`. Conclude with `h1`. Conclude with `Int.natCast_dvd_natCast.mp this`. Establish `h3` using `(Nat.modEq_iff_dvd' hl1).mpr h2`.

Rewrite `h3` using `[Nat.ModEq, Nat.mod_eq_of_lt (by omega)]`. Conclude with `h3.symm`. Use `right`. Establish `h2 : 2 ^ s ∣ l + 1` using `by exact_mod_cast h1`. Establish `hr` using `Nat.mod_lt l (by omega : 0 < 2 ^ s)`.

Establish `h3 : (l % 2 ^ s + 1) % 2 ^ s = 0`. Rewrite using `[Nat.mod_add_mod]`. Conclude with `Nat.mod_eq_zero_of_dvd h2`. Generalize the expression as in `l % 2 ^ s = r at hr h3 ⊢`. Generalize the expression as in `2 ^ s = N at hr h3 hN ⊢`.

Assume the negation of the conclusion as `hne`. Establish `hlt : r + 1 < N` using `by omega`. Rewrite `h3` using `[Nat.mod_eq_of_lt hlt]`. Use linear arithmetic over natural numbers and integers.
-/
theorem pm_one_of_pow (K l o : ℕ) (hl : Odd l) (ho : 0 < o)
    (h : (l : ZMod (2 ^ K)) ^ o = 1 ∨ (l : ZMod (2 ^ K)) ^ o = -1) :
    l % 2 ^ (K - padicValNat 2 o) = 1 ∨ l % 2 ^ (K - padicValNat 2 o) = 2 ^ (K - padicValNat 2 o) - 1 := by
  have hlz : Odd (l : ℤ) := by exact_mod_cast hl
  have hint : (2:ℤ) ^ K ∣ (l:ℤ) ^ o - 1 ∨ (2:ℤ) ^ K ∣ (l:ℤ) ^ o + 1 := by
    rcases h with h | h
    · left
      have h0 : (((l:ℤ) ^ o - 1 : ℤ) : ZMod (2 ^ K)) = 0 := by push_cast; rw [h]; ring
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ K)).mp h0
      exact_mod_cast this
    · right
      have h0 : (((l:ℤ) ^ o + 1 : ℤ) : ZMod (2 ^ K)) = 0 := by push_cast; rw [h]; ring
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ K)).mp h0
      exact_mod_cast this
  have key := pm_int K (l:ℤ) hlz o ho hint
  generalize K - padicValNat 2 o = s at key ⊢
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; right; simp [Nat.mod_one]
  have hN : 2 ≤ 2 ^ s := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have hl1 : 1 ≤ l := hl.pos
  rcases key with h1 | h1
  · left
    have h2 : 2 ^ s ∣ l - 1 := by
      have : ((2 ^ s : ℕ) : ℤ) ∣ ((l - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hl1]; push_cast; exact h1
      exact Int.natCast_dvd_natCast.mp this
    have h3 := (Nat.modEq_iff_dvd' hl1).mpr h2
    rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega)] at h3
    exact h3.symm
  · right
    have h2 : 2 ^ s ∣ l + 1 := by exact_mod_cast h1
    have hr := Nat.mod_lt l (by omega : 0 < 2 ^ s)
    have h3 : (l % 2 ^ s + 1) % 2 ^ s = 0 := by
      rw [Nat.mod_add_mod]; exact Nat.mod_eq_zero_of_dvd h2
    generalize l % 2 ^ s = r at hr h3 ⊢
    generalize 2 ^ s = N at hr h3 hN ⊢
    by_contra hne
    have hlt : r + 1 < N := by omega
    rw [Nat.mod_eq_of_lt hlt] at h3
    omega

/- English proof (translation)
Conclude with `Nat.le_of_dvd ho pow_padicValNat_dvd`.
-/
theorem two_pow_padicVal_le (o : ℕ) (ho : 0 < o) : 2 ^ padicValNat 2 o ≤ o := by
  exact Nat.le_of_dvd ho pow_padicValNat_dvd

end Formalism.MainNotions.TwistedPlaces.Cong

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces.Asym

open Real

open Asymptotics Filter

end Formalism.MainNotions.TwistedPlaces.Asym

end
