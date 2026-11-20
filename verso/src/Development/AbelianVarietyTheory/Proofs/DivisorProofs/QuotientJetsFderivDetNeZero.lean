import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
namespace GlobalTheory

/- English proof (translation)
Introduce `n`. Use `⟨1 / (4 * ((n : ℝ) + 1)), by positivity, ?_⟩` and prove the remaining obligations. Introduce `p w0 w hw0 hw h0 hL0 hwp hLj`. Use `set ε : ℝ := 1 / (4 * ((n : ℝ) + 1)) with hε`. Establish `hεpos : 0 < ε` using `by positivity`.

Establish `hε4 : ε ≤ 1 / 4`. Rewrite using `[hε]; apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)`. Establish `: (0:ℝ) ≤ n` using `Nat.cast_nonneg n`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set a := w0 p with ha_def`.

Establish `ha_norm : 3 / 4 ≤ ‖a‖`. Establish `h1 : ‖(1:ℂ)‖ ≤ ‖a‖ + ‖a - 1‖`. Use `norm_sub_le a (a - 1)` as an intermediate fact. Simplify using `using this`. Simplify using `at h1`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha : a ≠ 0`. Introduce `h`. Rewrite `ha_norm` using `[h]`. Simplify using `at ha_norm`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨ha, ?_⟩` and prove the remaining obligations. Use `set L0 := fderiv ℂ w0 p with hL0_def`. Establish `hL0' : ‖L0‖ ≤ ε`. Use `hL0` as an intermediate fact.

Rewrite `this` using `[fderiv_sub_const]`. Then use the resulting hypothesis. Establish `hproj : ∀ j : Fin n, HasFDerivAt (fun v : V n => v j - p j) (EuclideanSpace.proj (𝕜` using `ℂ) j) p := by`. Introduce `j`. Use `(EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) j).hasFDerivAt (x := p)` as an intermediate fact. Conclude with `this.sub_const (p j)`.

Establish `hLj' : ∀ j : Fin n, ∀ ξ : V n, ‖fderiv ℂ (w j) p ξ - ξ j‖ ≤ ε * ‖ξ‖`. Introduce `j ξ`. Establish `hd : fderiv ℂ (fun v : V n => w j v - (v j - p j)) p = fderiv ℂ (w j) p - EuclideanSpace.proj (𝕜` using `ℂ) j := ((hw j).hasFDerivAt.sub (hproj j)).fderiv`. Use `(fderiv ℂ (fun v : V n => w j v - (v j - p j)) p).le_opNorm ξ` as an intermediate fact. Rewrite `this` using `[hd]`.

Establish `h2` using `hLj j`. Rewrite `h2` using `[hd]`. Combine the equalities or inequalities in the displayed calculation. Use `set F : V n → V n := fun v => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n) with hF`. Establish `hq : ∀ j : Fin n, HasFDerivAt (fun v => w j v / w0 v) (w j p • ((-(a ^ 2)⁻¹) • L0) + a⁻¹ • fderiv ℂ (w j) p) p`.

Introduce `j`. Establish `hinv : HasFDerivAt (fun v => (w0 v)⁻¹) ((-(a ^ 2)⁻¹) • L0) p` using `(hasDerivAt_inv ha).comp_hasFDerivAt p hw0.hasFDerivAt`. Use `HasFDerivAt.mul (hw j).hasFDerivAt hinv` as an intermediate fact. Establish `e : (fun v => w j v / w0 v) = (w j * fun v => (w0 v)⁻¹)`. Use function extensionality and compare the values at `v`.

Simplify using `[div_eq_mul_inv]`. Rewrite using `[e]`. Conclude with `this`. Establish `hFd : DifferentiableAt ℂ F p`. Rewrite using `[differentiableAt_piLp]`.

Introduce `j`. Simplify `(hq j).differentiableAt` using `[hF]`. Use `set D := fderiv ℂ F p with hD`. Establish `hDj : ∀ j : Fin n, ∀ ξ : V n, (D ξ) j = w j p * ((-(a ^ 2)⁻¹) * L0 ξ) + a⁻¹ * fderiv ℂ (w j) p ξ`. Introduce `j ξ`.

Establish `h1 : HasFDerivAt (fun v => EuclideanSpace.proj (𝕜` using `ℂ) j (F v)) ((EuclideanSpace.proj (𝕜 := ℂ) j).comp D) p := (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) j).hasFDerivAt.comp p hFd.hasFDerivAt`. Establish `h2 : (fun v => EuclideanSpace.proj (𝕜` using `ℂ) j (F v)) = fun v => w j v / w0 v := by`. Use function extensionality and compare the values at `v`. Simplify using `[hF]`. Rewrite `h1` using `[h2]`.

Use `congrArg (fun T : V n →L[ℂ] ℂ => T ξ) (h1.unique (hq j))` as an intermediate fact. Simplify using `using this`. Establish `hinj : ∀ ξ : V n, D ξ = 0 → ξ = 0`. Introduce `ξ hξ`. Establish `hcoord : ∀ j : Fin n, ‖ξ j‖ ≤ 2 * ε * ‖ξ‖`.

Introduce `j`. Establish `e` using `hDj j ξ`. Rewrite `e` using `[hξ]`. Simplify using `only [PiLp.zero_apply] at e`. Establish `e2 : a * fderiv ℂ (w j) p ξ = w j p * L0 ξ`.

Establish `: a ^ 2 * (w j p * ((-(a ^ 2)⁻¹) * L0 ξ) + a⁻¹ * fderiv ℂ (w j) p ξ) = 0`. Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree. Clear denominators, using `at this` for the nonvanishing conditions. Take the linear combination `this`.

Establish `hL0ξ : ‖L0 ξ‖ ≤ ε * ‖ξ‖` using `(L0.le_opNorm ξ).trans (mul_le_mul_of_nonneg_right hL0' (norm_nonneg _))`. Establish `e3 : ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ ≤ ε * (ε * ‖ξ‖)`. Rewrite using `[← norm_mul, e2, norm_mul]`. Conclude with `mul_le_mul (hwp j) hL0ξ (norm_nonneg _) hεpos.le`. Establish `e4 : ‖fderiv ℂ (w j) p ξ‖ ≤ ε * ‖ξ‖`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `: (3/4) * (ε * ‖ξ‖) < ‖a‖ * ‖fderiv ℂ (w j) p ξ‖`. Combine the equalities or inequalities in the displayed calculation. Establish `: ε * (ε * ‖ξ‖) ≤ (3/4) * (ε * ‖ξ‖)` using `mul_le_mul_of_nonneg_right (by linarith) (by positivity)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e5` using `hLj' j ξ`. Establish `: ‖ξ j‖ ≤ ‖fderiv ℂ (w j) p ξ‖ + ‖fderiv ℂ (w j) p ξ - ξ j‖`. Use `norm_sub_le (fderiv ℂ (w j) p ξ) (fderiv ℂ (w j) p ξ - ξ j)` as an intermediate fact. Simplify using `using this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsq : ‖ξ‖ ^ 2 ≤ (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2`. Rewrite using `[EuclideanSpace.norm_sq_eq]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `i _`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2`. Use `_ = (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := by simp`. Establish `hc : (n : ℝ) * (2 * ε) ^ 2 ≤ 1 / 4`. Rewrite using `[hε]`.

Establish `hn : (0:ℝ) ≤ n` using `Nat.cast_nonneg n`. Rewrite using `[show (2 * (1 / (4 * ((n:ℝ) + 1)))) ^ 2 = 1 / (4 * ((n:ℝ)+1)^2) by field_simp; ring]`. Rewrite using `[mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `: ‖ξ‖ ^ 2 ≤ (1/4) * ‖ξ‖ ^ 2`.

Combine the equalities or inequalities in the displayed calculation. Establish `: ‖ξ‖ ^ 2 = 0` using `by nlinarith [sq_nonneg ‖ξ‖]`. Simplify using `using this`. Introduce `hdet`. Establish `h` using `(LinearMap.det_eq_zero_iff_ker_ne_bot (f := (D : V n →ₗ[ℂ] V n))).1 hdet`.

Apply `h` to reduce the goal to its premises. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `m hm`. Conclude with `hinj m hm`.
-/
theorem quot_jets_det_ne_zero : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ (p : V n) (w0 : V n → ℂ) (w : Fin n → V n → ℂ), DifferentiableAt ℂ w0 p → (∀ j, DifferentiableAt ℂ (w j) p) → ‖w0 p - 1‖ ≤ ε → ‖fderiv ℂ (fun v => w0 v - 1) p‖ ≤ ε → (∀ j, ‖w j p‖ ≤ ε) → (∀ j, ‖fderiv ℂ (fun v : V n => w j v - (v j - p j)) p‖ ≤ ε) → w0 p ≠ 0 ∧ (fderiv ℂ (fun v : V n => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n)) p).det ≠ 0 := by
  intro n
  refine ⟨1 / (4 * ((n : ℝ) + 1)), by positivity, ?_⟩
  intro p w0 w hw0 hw h0 hL0 hwp hLj
  set ε : ℝ := 1 / (4 * ((n : ℝ) + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hε4 : ε ≤ 1 / 4 := by
    rw [hε]; apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  set a := w0 p with ha_def
  have ha_norm : 3 / 4 ≤ ‖a‖ := by
    have h1 : ‖(1:ℂ)‖ ≤ ‖a‖ + ‖a - 1‖ := by
      have := norm_sub_le a (a - 1)
      simpa using this
    simp at h1
    linarith
  have ha : a ≠ 0 := by
    intro h; rw [h] at ha_norm; simp at ha_norm; linarith
  refine ⟨ha, ?_⟩
  set L0 := fderiv ℂ w0 p with hL0_def
  have hL0' : ‖L0‖ ≤ ε := by
    have := hL0; rwa [fderiv_sub_const] at this
  have hproj : ∀ j : Fin n, HasFDerivAt (fun v : V n => v j - p j) (EuclideanSpace.proj (𝕜 := ℂ) j) p := by
    intro j
    have := (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) j).hasFDerivAt (x := p)
    exact this.sub_const (p j)
  have hLj' : ∀ j : Fin n, ∀ ξ : V n, ‖fderiv ℂ (w j) p ξ - ξ j‖ ≤ ε * ‖ξ‖ := by
    intro j ξ
    have hd : fderiv ℂ (fun v : V n => w j v - (v j - p j)) p
        = fderiv ℂ (w j) p - EuclideanSpace.proj (𝕜 := ℂ) j :=
      ((hw j).hasFDerivAt.sub (hproj j)).fderiv
    have := (fderiv ℂ (fun v : V n => w j v - (v j - p j)) p).le_opNorm ξ
    rw [hd] at this
    have h2 := hLj j
    rw [hd] at h2
    calc ‖fderiv ℂ (w j) p ξ - ξ j‖ = ‖(fderiv ℂ (w j) p - EuclideanSpace.proj (𝕜 := ℂ) j) ξ‖ := by simp
      _ ≤ _ := this
      _ ≤ ε * ‖ξ‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  set F : V n → V n := fun v => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n) with hF
  have hq : ∀ j : Fin n, HasFDerivAt (fun v => w j v / w0 v)
      (w j p • ((-(a ^ 2)⁻¹) • L0) + a⁻¹ • fderiv ℂ (w j) p) p := by
    intro j
    have hinv : HasFDerivAt (fun v => (w0 v)⁻¹) ((-(a ^ 2)⁻¹) • L0) p :=
      (hasDerivAt_inv ha).comp_hasFDerivAt p hw0.hasFDerivAt
    have := HasFDerivAt.mul (hw j).hasFDerivAt hinv
    have e : (fun v => w j v / w0 v) = (w j * fun v => (w0 v)⁻¹) := by
      funext v; simp [div_eq_mul_inv]
    rw [e]; exact this
  have hFd : DifferentiableAt ℂ F p := by
    rw [differentiableAt_piLp]
    intro j
    simpa [hF] using (hq j).differentiableAt
  set D := fderiv ℂ F p with hD
  have hDj : ∀ j : Fin n, ∀ ξ : V n, (D ξ) j = w j p * ((-(a ^ 2)⁻¹) * L0 ξ) + a⁻¹ * fderiv ℂ (w j) p ξ := by
    intro j ξ
    have h1 : HasFDerivAt (fun v => EuclideanSpace.proj (𝕜 := ℂ) j (F v)) ((EuclideanSpace.proj (𝕜 := ℂ) j).comp D) p :=
      (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) j).hasFDerivAt.comp p hFd.hasFDerivAt
    have h2 : (fun v => EuclideanSpace.proj (𝕜 := ℂ) j (F v)) = fun v => w j v / w0 v := by
      funext v; simp [hF]
    rw [h2] at h1
    have := congrArg (fun T : V n →L[ℂ] ℂ => T ξ) (h1.unique (hq j))
    simpa using this
  have hinj : ∀ ξ : V n, D ξ = 0 → ξ = 0 := by
    intro ξ hξ
    have hcoord : ∀ j : Fin n, ‖ξ j‖ ≤ 2 * ε * ‖ξ‖ := by
      intro j
      have e := hDj j ξ
      rw [hξ] at e
      simp only [PiLp.zero_apply] at e
      have e2 : a * fderiv ℂ (w j) p ξ = w j p * L0 ξ := by
        have : a ^ 2 * (w j p * ((-(a ^ 2)⁻¹) * L0 ξ) + a⁻¹ * fderiv ℂ (w j) p ξ) = 0 := by
          rw [← e]; ring
        field_simp at this
        linear_combination this
      have hL0ξ : ‖L0 ξ‖ ≤ ε * ‖ξ‖ := (L0.le_opNorm ξ).trans (mul_le_mul_of_nonneg_right hL0' (norm_nonneg _))
      have e3 : ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ ≤ ε * (ε * ‖ξ‖) := by
        rw [← norm_mul, e2, norm_mul]
        exact mul_le_mul (hwp j) hL0ξ (norm_nonneg _) hεpos.le
      have e4 : ‖fderiv ℂ (w j) p ξ‖ ≤ ε * ‖ξ‖ := by
        by_contra hc
        push_neg at hc
        have : (3/4) * (ε * ‖ξ‖) < ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ := by
          calc (3/4) * (ε * ‖ξ‖) ≤ ‖a‖ * (ε * ‖ξ‖) := mul_le_mul_of_nonneg_right ha_norm (by positivity)
            _ < ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ := mul_lt_mul_of_pos_left hc (by linarith)
        have : ε * (ε * ‖ξ‖) ≤ (3/4) * (ε * ‖ξ‖) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        linarith
      have e5 := hLj' j ξ
      have : ‖ξ j‖ ≤ ‖fderiv ℂ (w j) p ξ‖ + ‖fderiv ℂ (w j) p ξ - ξ j‖ := by
        have := norm_sub_le (fderiv ℂ (w j) p ξ) (fderiv ℂ (w j) p ξ - ξ j)
        simpa using this
      linarith
    have hsq : ‖ξ‖ ^ 2 ≤ (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖ξ.ofLp i‖ ^ 2 ≤ ∑ _i : Fin n, (2 * ε * ‖ξ‖) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            exact pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
        _ = (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := by simp
    have hc : (n : ℝ) * (2 * ε) ^ 2 ≤ 1 / 4 := by
      rw [hε]
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      rw [show (2 * (1 / (4 * ((n:ℝ) + 1)))) ^ 2 = 1 / (4 * ((n:ℝ)+1)^2) by field_simp; ring]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have : ‖ξ‖ ^ 2 ≤ (1/4) * ‖ξ‖ ^ 2 := by
      calc ‖ξ‖ ^ 2 ≤ (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := hsq
        _ = ((n : ℝ) * (2 * ε) ^ 2) * ‖ξ‖ ^ 2 := by ring
        _ ≤ (1/4) * ‖ξ‖ ^ 2 := mul_le_mul_of_nonneg_right hc (by positivity)
    have : ‖ξ‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖ξ‖]
    simpa using this
  intro hdet
  have h := (LinearMap.det_eq_zero_iff_ker_ne_bot (f := (D : V n →ₗ[ℂ] V n))).1 hdet
  apply h
  rw [LinearMap.ker_eq_bot']
  intro m hm
  exact hinj m hm

end GlobalTheory
