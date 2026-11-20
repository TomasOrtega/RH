import Mathlib

namespace GlobalTheory.CompanionTheory.DiagDom

/- English proof (translation)
The claim follows from `|∑ i, W σ i * c i - c σ| ≤ (Fintype.card κ : ℝ) * ε * C := by have hrw : ∑ i, W σ i * c i - c σ = ∑ i, (W σ i - if σ = i then 1 else 0) * c i := by simp [sub_mul, Finset.sum_sub_distrib, ite_mul] rw [hrw] calc |∑ i, (W σ i - if σ = i then 1 else 0) * c i| ≤ ∑ i, |(W σ i - if σ = …`.
-/
theorem perturb_bound {κ : Type} [Fintype κ] [DecidableEq κ] (W : κ → κ → ℝ) (ε C : ℝ)
    (hW : ∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) (c : κ → ℝ)
    (hC : ∀ i, |c i| ≤ C) (σ : κ) :
    |∑ i, W σ i * c i - c σ| ≤ (Fintype.card κ : ℝ) * ε * C := by
  have hrw : ∑ i, W σ i * c i - c σ = ∑ i, (W σ i - if σ = i then 1 else 0) * c i := by
    simp [sub_mul, Finset.sum_sub_distrib, ite_mul]
  rw [hrw]
  calc |∑ i, (W σ i - if σ = i then 1 else 0) * c i|
      ≤ ∑ i, |(W σ i - if σ = i then 1 else 0) * c i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : κ, ε * C := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (hW σ i).le (hC i) (abs_nonneg _) ((abs_nonneg _).trans (hW σ i).le)
    _ = (Fintype.card κ : ℝ) * ε * C := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/- English proof (translation)
Introduce `κ _ _ M`. Establish `hn0 : (0 : ℝ) ≤ (Fintype.card κ : ℝ)` using `Nat.cast_nonneg _`. Establish `hM1 : 0 < |M| + 1` using `by positivity`. Use `⟨1 / (2 * ((Fintype.card κ : ℝ) + 1) * (|M| + 1)), by positivity, fun W hW => ?_⟩` and prove the remaining obligations. Use `set n : ℝ := (Fintype.card κ : ℝ) with hn`.

Use `set ε := 1 / (2 * (n + 1) * (|M| + 1)) with hε`. Establish `hδ : n * ε * (2 * (|M| + 1)) ≤ 1`. Establish `e : n * ε * (2 * (|M| + 1)) = n / (n + 1)`. Rewrite using `[hε]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e, div_le_one (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hε0 : 0 < ε` using `by positivity`. Establish `hδ0 : 0 ≤ n * ε` using `by positivity`. Establish `hδh : n * ε ≤ 1 / 2` using `by nlinarith [abs_nonneg M]`.

Break down `isEmpty_or_nonempty κ with hκ | hκ` into its components or cases. Conclude with `⟨fun c _ => funext fun i => (IsEmpty.false i).elim, fun c _ _ i => (IsEmpty.false i).elim⟩`. Establish `bound : ∀ c : κ → ℝ, ∃ j, ∀ σ, |∑ i, W σ i * c i - c σ| ≤ n * ε * |c j| ∧ |c σ| ≤ |c j|`. Introduce `c`. Take `⟨j, -, hj⟩` from `Finset.exists_max_image Finset.univ (fun i => |c i|) Finset.univ_nonempty`.

Conclude with `⟨j, fun σ => ⟨perturb_bound W ε |c j| hW c (fun i => hj i (Finset.mem_univ i)) σ, hj σ (Finset.mem_univ σ)⟩⟩`. Prove the components needed by the constructor for the conclusion. Introduce `c hc`. Take `⟨j, hj⟩` from `bound c`. Establish `h1` using `(hj j).1`.

Rewrite `h1` using `[hc j, zero_sub, abs_neg]`. Establish `hC : |c j| = 0` using `by nlinarith [abs_nonneg (c j)]`. Use function extensionality and compare the values at `i`. Establish `h2` using `(hj i).2`. Rewrite `h2` using `[hC]`.

Conclude with `abs_nonpos_iff.mp h2`. Introduce `c hpos hratio i`. Take `⟨j, hj⟩` from `bound c`. Establish `hC0 : 0 ≤ |c j|` using `abs_nonneg _`. Establish `h1 : |c j| ≤ ∑ k, W j k * c k + n * ε * |c j|`.

Establish `e` using `abs_sub_abs_le_abs_sub (c j) (∑ k, W j k * c k)`. Rewrite `e` using `[abs_sub_comm (c j), abs_of_pos (hpos j)]`. Combine the linear relations using `[(hj j).1]`. Establish `h2 : ∑ k, W i k * c k - n * ε * |c j| ≤ c i`. Combine the linear relations using `[(abs_le.mp (hj i).1).2]`.

Establish `h3` using `hratio j i`. Establish `hyi` using `hpos i`. Establish `hMy : M * ∑ k, W i k * c k ≤ |M| * ∑ k, W i k * c k` using `mul_le_mul_of_nonneg_right (le_abs_self M) hyi.le`. Establish `s1 : n * ε * |c j| * (2 * (|M| + 1)) ≤ |c j|`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hδ hC0]`.

Establish `s2 : |c j| * (1 - n * ε) ≤ |M| * ∑ k, W i k * c k` using `by nlinarith`. Establish `s3 : n * ε * |c j| * (|M| + 1) < (∑ k, W i k * c k) * (|M| + 1)`. Use polynomial arithmetic with `[mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ 1 - 2 * (n * ε))]`. Establish `s4 : n * ε * |c j| < ∑ k, W i k * c k` using `lt_of_mul_lt_mul_right s3 hM1.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem small_perturbation_injective_pos :
    ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (M : ℝ), ∃ ε : ℝ, 0 < ε ∧ ∀ W : κ → κ → ℝ,
      (∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) →
      (∀ c : κ → ℝ, (∀ σ, ∑ i, W σ i * c i = 0) → c = 0) ∧
      ∀ c : κ → ℝ, (∀ σ, 0 < ∑ i, W σ i * c i) →
        (∀ σ τ, ∑ i, W σ i * c i ≤ M * ∑ i, W τ i * c i) → ∀ i, 0 < c i := by
  intro κ _ _ M
  have hn0 : (0 : ℝ) ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hM1 : 0 < |M| + 1 := by positivity
  refine ⟨1 / (2 * ((Fintype.card κ : ℝ) + 1) * (|M| + 1)), by positivity, fun W hW => ?_⟩
  set n : ℝ := (Fintype.card κ : ℝ) with hn
  set ε := 1 / (2 * (n + 1) * (|M| + 1)) with hε
  have hδ : n * ε * (2 * (|M| + 1)) ≤ 1 := by
    have e : n * ε * (2 * (|M| + 1)) = n / (n + 1) := by
      rw [hε]
      field_simp
    rw [e, div_le_one (by linarith)]
    linarith
  have hε0 : 0 < ε := by positivity
  have hδ0 : 0 ≤ n * ε := by positivity
  have hδh : n * ε ≤ 1 / 2 := by nlinarith [abs_nonneg M]
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · exact ⟨fun c _ => funext fun i => (IsEmpty.false i).elim, fun c _ _ i => (IsEmpty.false i).elim⟩
  have bound : ∀ c : κ → ℝ, ∃ j, ∀ σ,
      |∑ i, W σ i * c i - c σ| ≤ n * ε * |c j| ∧ |c σ| ≤ |c j| := by
    intro c
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |c i|) Finset.univ_nonempty
    exact ⟨j, fun σ => ⟨perturb_bound W ε |c j| hW c (fun i => hj i (Finset.mem_univ i)) σ,
      hj σ (Finset.mem_univ σ)⟩⟩
  constructor
  · intro c hc
    obtain ⟨j, hj⟩ := bound c
    have h1 := (hj j).1
    rw [hc j, zero_sub, abs_neg] at h1
    have hC : |c j| = 0 := by nlinarith [abs_nonneg (c j)]
    funext i
    have h2 := (hj i).2
    rw [hC] at h2
    exact abs_nonpos_iff.mp h2
  · intro c hpos hratio i
    obtain ⟨j, hj⟩ := bound c
    have hC0 : 0 ≤ |c j| := abs_nonneg _
    have h1 : |c j| ≤ ∑ k, W j k * c k + n * ε * |c j| := by
      have e := abs_sub_abs_le_abs_sub (c j) (∑ k, W j k * c k)
      rw [abs_sub_comm (c j), abs_of_pos (hpos j)] at e
      linarith [(hj j).1]
    have h2 : ∑ k, W i k * c k - n * ε * |c j| ≤ c i := by
      linarith [(abs_le.mp (hj i).1).2]
    have h3 := hratio j i
    have hyi := hpos i
    have hMy : M * ∑ k, W i k * c k ≤ |M| * ∑ k, W i k * c k :=
      mul_le_mul_of_nonneg_right (le_abs_self M) hyi.le
    have s1 : n * ε * |c j| * (2 * (|M| + 1)) ≤ |c j| := by
      nlinarith [mul_le_mul_of_nonneg_right hδ hC0]
    have s2 : |c j| * (1 - n * ε) ≤ |M| * ∑ k, W i k * c k := by nlinarith
    have s3 : n * ε * |c j| * (|M| + 1) < (∑ k, W i k * c k) * (|M| + 1) := by
      nlinarith [mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ 1 - 2 * (n * ε))]
    have s4 : n * ε * |c j| < ∑ k, W i k * c k := lt_of_mul_lt_mul_right s3 hM1.le
    linarith

end GlobalTheory.CompanionTheory.DiagDom
