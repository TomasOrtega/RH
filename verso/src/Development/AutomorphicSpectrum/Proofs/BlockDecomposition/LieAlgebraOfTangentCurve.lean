import Mathlib
import Formalism.UnipotentAdelicQuotients.SmComplete
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

namespace GlobalTheory.CompanionTheory.SmTangent

section Abstract

variable {A : Type*} [NormedRing A]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using h1`. Consider the case `succ k ih`. Rewrite using `[pow_succ, pow_succ]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_pow_le_pow_of_le (h1 : ‖(1 : A)‖ ≤ 1) {b : A} {C : ℝ} (hC : 1 ≤ C) (hb : ‖b‖ ≤ C) (k : ℕ) :
    ‖b ^ k‖ ≤ C ^ k := by
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    rw [pow_succ, pow_succ]
    calc ‖b ^ k * b‖ ≤ ‖b ^ k‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ C ^ k * C := by
        gcongr

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e : a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + (a - b) * b ^ k`. Rewrite using `[pow_succ', pow_succ']`.

Use `noncomm_ring`. Establish `hC0 : 0 ≤ C` using `by linarith`. Establish `hCk : 1 ≤ C ^ k` using `one_le_pow₀ hC`. Establish `hd : 0 ≤ ‖a - b‖` using `norm_nonneg _`. Establish `t1 : ‖a * (a ^ k - b ^ k)‖ ≤ C * (k * C ^ k * ‖a - b‖)` using `(norm_mul_le _ _).trans (by gcongr)`.

Establish `t2 : ‖(a - b) * b ^ k‖ ≤ ‖a - b‖ * C ^ k` using `(norm_mul_le _ _).trans (by gcongr; exact norm_pow_le_pow_of_le h1 hC hb k)`. Establish `t3 : ‖a - b‖ * C ^ k ≤ ‖a - b‖ * C ^ (k + 1)` using `mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC (Nat.le_succ k)) hd`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_pow_sub_pow_le (h1 : ‖(1 : A)‖ ≤ 1) {a b : A} {C : ℝ} (hC : 1 ≤ C) (ha : ‖a‖ ≤ C)
    (hb : ‖b‖ ≤ C) (k : ℕ) : ‖a ^ k - b ^ k‖ ≤ k * C ^ k * ‖a - b‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + (a - b) * b ^ k := by
      rw [pow_succ', pow_succ']
      noncomm_ring
    have hC0 : 0 ≤ C := by linarith
    have hCk : 1 ≤ C ^ k := one_le_pow₀ hC
    have hd : 0 ≤ ‖a - b‖ := norm_nonneg _
    have t1 : ‖a * (a ^ k - b ^ k)‖ ≤ C * (k * C ^ k * ‖a - b‖) :=
      (norm_mul_le _ _).trans (by gcongr)
    have t2 : ‖(a - b) * b ^ k‖ ≤ ‖a - b‖ * C ^ k :=
      (norm_mul_le _ _).trans (by gcongr; exact norm_pow_le_pow_of_le h1 hC hb k)
    have t3 : ‖a - b‖ * C ^ k ≤ ‖a - b‖ * C ^ (k + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC (Nat.le_succ k)) hd
    rw [e]
    calc ‖a * (a ^ k - b ^ k) + (a - b) * b ^ k‖
        ≤ ‖a * (a ^ k - b ^ k)‖ + ‖(a - b) * b ^ k‖ := norm_add_le _ _
      _ ≤ C * (k * C ^ k * ‖a - b‖) + ‖a - b‖ * C ^ (k + 1) := by linarith
      _ = ((k + 1 : ℕ) : ℝ) * C ^ (k + 1) * ‖a - b‖ := by
        push_cast; ring

variable [NormedAlgebra ℝ A] [CompleteSpace A]

/- English proof (translation)
Use `set E : ℝ → A := fun s => NormedSpace.exp (s • Y) with hE`. Establish `hE0 : E 0 = 1` using `by simp [hE]`. Establish `hEd : HasDerivAt E Y 0`. Use `hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)` as an intermediate fact. Simplify using `using this`.

Establish `hs : Tendsto (fun k : ℕ => t / (k : ℝ)) atTop (𝓝 0)` using `tendsto_const_div_atTop_nhds_zero_nat t`. Take `⟨M1, hM1⟩` from `hd.isBigO_sub.bound`. Take `⟨M2, hM2⟩` from `hEd.isBigO_sub.bound`. Use `set M : ℝ := max (max M1 M2) 0 with hM`. Establish `hM0 : 0 ≤ M` using `le_max_right _ _`.

Use `set c : ℝ := M * |t| with hc`. Establish `hc0 : 0 ≤ c` using `by positivity`. Establish `hbound : ∀ (f : ℝ → A) (M' : ℝ), M' ≤ M → f 0 = 1 → (∀ᶠ s in 𝓝 (0 : ℝ), ‖f s - f 0‖ ≤ M' * ‖s - 0‖) → ∀ᶠ k : ℕ in atTop, ‖f (t / k)‖ ≤ 1 + c / k`. Introduce `f M' hM' hf hb`. Use `filter_upwards [hs.eventually hb, eventually_gt_atTop 0] with k hk hk0`.

Establish `hk' : (0 : ℝ) < k` using `by exact_mod_cast hk0`. Rewrite `hk` using `[hf]`. Establish `e : f (t / k) = 1 + (f (t / k) - 1)` using `by abel`. Rewrite using `[e]`. Use `(norm_add_le _ _).trans (add_le_add h1 (hk.trans ?_))` and prove the remaining obligations.

Establish `: ‖t / (k : ℝ) - 0‖ = |t| / k`. Simplify using `[abs_div]`. Rewrite using `[this, hc, mul_div_assoc]`. Use `gcongr`. Establish `ha` using `hbound γ M1 ((le_max_left _ _).trans (le_max_left _ _)) h0 hM1`.

Establish `hb` using `hbound E M2 ((le_max_right _ _).trans (le_max_left _ _)) hE0 hM2`. Establish `hpow : ∀ k : ℕ, 0 < k → (1 + c / k) ^ k ≤ Real.exp c`. Introduce `k hk`. Establish `hk' : (k : ℝ) ≠ 0` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[add_comm]`. Conclude with `Real.add_one_le_exp _`. Use `_ = Real.exp c := by`. Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Establish `hD : HasDerivAt (fun s => γ s - E s) 0 0`. Use `hd.sub hEd` as an intermediate fact. Rewrite `this` using `[sub_self]`. Conclude with `this`.

Establish `hlo : (fun s => γ s - E s) =o[𝓝 0] (fun s : ℝ => s)`. Use `hasDerivAt_iff_isLittleO_nhds_zero.1 hD` as an intermediate fact. Simplify `this` using `[h0, hE0]`. Establish `hK : Tendsto (fun k : ℕ => Real.exp c * ((k : ℝ) * ‖γ (t / k) - E (t / k)‖)) atTop (𝓝 0)`. Establish `: Tendsto (fun k : ℕ => (k : ℝ) * ‖γ (t / k) - E (t / k)‖) atTop (𝓝 0)`.

Rewrite using `[Metric.tendsto_nhds]`. Introduce `ε hε`. Establish `hp : 0 < |t| + 1` using `by positivity`. Establish `hcε : 0 < ε / (|t| + 1)` using `by positivity`. Use `filter_upwards [(hlo.comp_tendsto hs).def hcε, eventually_gt_atTop 0] with k hk hk0`.

Establish `hk' : (0 : ℝ) < k` using `by exact_mod_cast hk0`. Simplify using `only [Function.comp] at hk`. Establish `e : ‖t / (k : ℝ)‖ = |t| / k` using `by simp [abs_div]`. Rewrite `hk` using `[e]`. Rewrite using `[Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_lt_one hp]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = ε := mul_one _`. Simplify using `using this.const_mul (Real.exp c)`.

Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Use `squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hK` and prove the remaining obligations. Use `filter_upwards [ha, hb, eventually_gt_atTop 0] with k hak hbk hk0`. Establish `hk' : (k : ℝ) ≠ 0` using `by positivity`. Establish `hC : 1 ≤ 1 + c / k`.

Establish `: 0 ≤ c / k` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hEk : NormedSpace.exp (t • Y) = E (t / k) ^ k`. Simplify using `only [hE]`. Use `letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A`.

Rewrite using `[← NormedSpace.exp_nsmul]`. Use `congr 1`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℝ, smul_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hEk]`. Use `(norm_pow_sub_pow_le h1 hC hak hbk k).trans ?_` and prove the remaining obligations. Use `hpow k hk0` as an intermediate fact. Establish `hn : 0 ≤ ‖γ (t / k) - E (t / k)‖` using `norm_nonneg _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tendsto_pow_of_hasDerivAt (h1 : ‖(1 : A)‖ ≤ 1) (γ : ℝ → A) (Y : A) (h0 : γ 0 = 1)
    (hd : HasDerivAt γ Y 0) (t : ℝ) :
    Tendsto (fun k : ℕ => γ (t / k) ^ k) atTop (𝓝 (NormedSpace.exp (t • Y))) := by
  set E : ℝ → A := fun s => NormedSpace.exp (s • Y) with hE
  have hE0 : E 0 = 1 := by simp [hE]
  have hEd : HasDerivAt E Y 0 := by
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
    simpa using this
  have hs : Tendsto (fun k : ℕ => t / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat t
  obtain ⟨M1, hM1⟩ := hd.isBigO_sub.bound
  obtain ⟨M2, hM2⟩ := hEd.isBigO_sub.bound
  set M : ℝ := max (max M1 M2) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  set c : ℝ := M * |t| with hc
  have hc0 : 0 ≤ c := by positivity
  have hbound : ∀ (f : ℝ → A) (M' : ℝ), M' ≤ M → f 0 = 1 →
      (∀ᶠ s in 𝓝 (0 : ℝ), ‖f s - f 0‖ ≤ M' * ‖s - 0‖) →
      ∀ᶠ k : ℕ in atTop, ‖f (t / k)‖ ≤ 1 + c / k := by
    intro f M' hM' hf hb
    filter_upwards [hs.eventually hb, eventually_gt_atTop 0] with k hk hk0
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
    rw [hf] at hk
    have e : f (t / k) = 1 + (f (t / k) - 1) := by abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add h1 (hk.trans ?_))
    have : ‖t / (k : ℝ) - 0‖ = |t| / k := by
      simp [abs_div]
    rw [this, hc, mul_div_assoc]
    gcongr
  have ha := hbound γ M1 ((le_max_left _ _).trans (le_max_left _ _)) h0 hM1
  have hb := hbound E M2 ((le_max_right _ _).trans (le_max_left _ _)) hE0 hM2
  have hpow : ∀ k : ℕ, 0 < k → (1 + c / k) ^ k ≤ Real.exp c := by
    intro k hk
    have hk' : (k : ℝ) ≠ 0 := by positivity
    calc (1 + c / k) ^ k ≤ (Real.exp (c / k)) ^ k := by
          gcongr
          rw [add_comm]
          exact Real.add_one_le_exp _
      _ = Real.exp c := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  have hD : HasDerivAt (fun s => γ s - E s) 0 0 := by
    have := hd.sub hEd
    rw [sub_self] at this
    exact this
  have hlo : (fun s => γ s - E s) =o[𝓝 0] (fun s : ℝ => s) := by
    have := hasDerivAt_iff_isLittleO_nhds_zero.1 hD
    simpa [h0, hE0] using this
  have hK : Tendsto (fun k : ℕ => Real.exp c * ((k : ℝ) * ‖γ (t / k) - E (t / k)‖)) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => (k : ℝ) * ‖γ (t / k) - E (t / k)‖) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hp : 0 < |t| + 1 := by positivity
      have hcε : 0 < ε / (|t| + 1) := by positivity
      filter_upwards [(hlo.comp_tendsto hs).def hcε, eventually_gt_atTop 0] with k hk hk0
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
      simp only [Function.comp] at hk
      have e : ‖t / (k : ℝ)‖ = |t| / k := by simp [abs_div]
      rw [e] at hk
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
      calc (k : ℝ) * ‖γ (t / k) - E (t / k)‖ ≤ k * (ε / (|t| + 1) * (|t| / k)) := by gcongr
        _ = ε * (|t| / (|t| + 1)) := by field_simp
        _ < ε * 1 := by
          gcongr
          rw [div_lt_one hp]
          linarith
        _ = ε := mul_one _
    simpa using this.const_mul (Real.exp c)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hK
  filter_upwards [ha, hb, eventually_gt_atTop 0] with k hak hbk hk0
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have hC : 1 ≤ 1 + c / k := by
    have : 0 ≤ c / k := by positivity
    linarith
  have hEk : NormedSpace.exp (t • Y) = E (t / k) ^ k := by
    simp only [hE]
    letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
    rw [← NormedSpace.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
  rw [hEk]
  refine (norm_pow_sub_pow_le h1 hC hak hbk k).trans ?_
  have := hpow k hk0
  have hn : 0 ≤ ‖γ (t / k) - E (t / k)‖ := norm_nonneg _
  calc (k : ℝ) * (1 + c / k) ^ k * ‖γ (t / k) - E (t / k)‖
      ≤ k * Real.exp c * ‖γ (t / k) - E (t / k)‖ := by gcongr
    _ = Real.exp c * ((k : ℝ) * ‖γ (t / k) - E (t / k)‖) := by ring

end Abstract

/- English proof (translation)
Establish `hs` using `hasDerivAt_iff_tendsto_slope.1 hd`. Use `letI R : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing`. Use `letI Al : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra`. Use `haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _`. Establish `h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1`.

Rewrite using `[← Matrix.diagonal_one, Matrix.linfty_opNorm_diagonal]`. Conclude with `(pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp`. Establish `hd' : HasDerivAt γ Y 0` using `hasDerivAt_iff_tendsto_slope.2 hs`. Establish `key` using `@tendsto_pow_of_hasDerivAt _ R Al this h1 γ Y h0 hd' t`. Establish `e : (t : ℂ) • Y = t • Y`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `key`.
-/
theorem matrix_tendsto (n : ℕ) (γ : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (h0 : γ 0 = 1) (hd : HasDerivAt γ Y 0) (t : ℝ) :
    Tendsto (fun k : ℕ => γ (t / k) ^ k) atTop (𝓝 (NormedSpace.exp ((t : ℂ) • Y))) := by
  have hs := hasDerivAt_iff_tendsto_slope.1 hd
  letI R : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI Al : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.linfty_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  have hd' : HasDerivAt γ Y 0 := hasDerivAt_iff_tendsto_slope.2 hs
  have key := @tendsto_pow_of_hasDerivAt _ R Al this h1 γ Y h0 hd' t
  have e : (t : ℂ) • Y = t • Y := by
    ext i j
    simp
  rw [e]
  exact key

/- English proof (translation)
Introduce `n G hG γ Y h0 hev hd t`. Take `⟨hcl, h1G, hmul, -⟩` from `hG`. Establish `hpowG : ∀ g ∈ G, ∀ k : ℕ, g ^ k ∈ G`. Introduce `g hg k`. Proceed by induction on `k with`.

Consider the case `zero => simpa using h1G`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `hmul _ ih _ hg`. Establish `hs : Tendsto (fun k : ℕ => t / (k : ℝ)) atTop (𝓝 0)` using `tendsto_const_div_atTop_nhds_zero_nat t`. Use `hcl.mem_of_tendsto (matrix_tendsto n γ Y h0 hd t) ?_` and prove the remaining obligations.

Use `filter_upwards [hs.eventually hev] with k hk`. Conclude with `hpowG _ hk k`.
-/
theorem tangent_mem_lieAlg : ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsClosedMatrixGroup G →
    ∀ (γ : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ), γ 0 = 1 →
      (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ G) → HasDerivAt γ Y 0 → Y ∈ lieAlg G := by
  intro n G hG γ Y h0 hev hd t
  obtain ⟨hcl, h1G, hmul, -⟩ := hG
  have hpowG : ∀ g ∈ G, ∀ k : ℕ, g ^ k ∈ G := by
    intro g hg k
    induction k with
    | zero => simpa using h1G
    | succ k ih => rw [pow_succ]; exact hmul _ ih _ hg
  have hs : Tendsto (fun k : ℕ => t / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat t
  refine hcl.mem_of_tendsto (matrix_tendsto n γ Y h0 hd t) ?_
  filter_upwards [hs.eventually hev] with k hk
  exact hpowG _ hk k

end GlobalTheory.CompanionTheory.SmTangent
