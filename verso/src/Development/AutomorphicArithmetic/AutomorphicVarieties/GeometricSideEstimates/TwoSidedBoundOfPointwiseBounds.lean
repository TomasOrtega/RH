import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.MomentBoundOfPointwiseMoments

open UpperTheory.V.Lit.Geo

/- English proof (translation)
Break down `le_or_gt |x| 1 with h | h` into its components or cases. Establish `h1` using `Real.abs_exp_sub_one_sub_id_le h`. Establish `h2 : x ^ 2 ≤ x ^ 2 * Real.exp |x|` using `le_mul_of_one_le_right (sq_nonneg x) (Real.one_le_exp (abs_nonneg x))`. Establish `h3` using `(abs_le.mp h1).2`. Combine the linear equalities and inequalities to obtain the conclusion.

Break down `le_or_gt 0 x with hx | hx` into its components or cases. Rewrite `h`, the goal using `[abs_of_nonneg hx]`. Establish `: Real.exp x ≤ x ^ 2 * Real.exp x` using `le_mul_of_one_le_left (Real.exp_pos x).le (by nlinarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h`, the goal using `[abs_of_neg hx]`.

Establish `h1 : Real.exp x ≤ 1` using `Real.exp_le_one_iff.mpr hx.le`. Establish `h2 : x ^ 2 ≤ x ^ 2 * Real.exp (-x)` using `le_mul_of_one_le_right (sq_nonneg x) (Real.one_le_exp (by linarith))`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem exp_quad (x : ℝ) : Real.exp x ≤ 1 + x + x ^ 2 * Real.exp |x| := by
  rcases le_or_gt |x| 1 with h | h
  · have h1 := Real.abs_exp_sub_one_sub_id_le h
    have h2 : x ^ 2 ≤ x ^ 2 * Real.exp |x| :=
      le_mul_of_one_le_right (sq_nonneg x) (Real.one_le_exp (abs_nonneg x))
    have h3 := (abs_le.mp h1).2
    linarith
  · rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx] at h ⊢
      have : Real.exp x ≤ x ^ 2 * Real.exp x :=
        le_mul_of_one_le_left (Real.exp_pos x).le (by nlinarith)
      linarith
    · rw [abs_of_neg hx] at h ⊢
      have h1 : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx.le
      have h2 : x ^ 2 ≤ x ^ 2 * Real.exp (-x) :=
        le_mul_of_one_le_right (sq_nonneg x) (Real.one_le_exp (by linarith))
      nlinarith

/- English proof (translation)
Establish `hpi` using `Real.pi_pos`. Establish `hE : Real.exp (-Real.pi * (q + u)) = Real.exp (-Real.pi * q) * Real.exp (-Real.pi * u)`. Rewrite using `[← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hx` using `exp_quad (-Real.pi * u)`. Establish `habs : |-Real.pi * u| = Real.pi * |u|`. Rewrite using `[abs_mul, abs_neg, abs_of_pos hpi]`. Rewrite `hx` using `[habs]`. Establish `hu4 : |u| ≤ q / 4` using `by nlinarith [abs_nonneg u, mul_nonneg (sub_nonneg.mpr h4) hq]`.

Establish `hu2 : u ^ 2 ≤ ε ^ 2 * q ^ 2`. Use `mul_self_le_mul_self (abs_nonneg u) hu` as an intermediate fact. Use polynomial arithmetic with `[sq_abs u]`. Establish `hpu : Real.pi * |u| ≤ Real.pi * (q / 4)` using `mul_le_mul_of_nonneg_left hu4 hpi.le`. Establish `hy0 : 0 ≤ Real.pi * q / 4` using `by positivity`.

Establish `hexp1 : Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q) ≤ Real.exp (-Real.pi * (1 / 2 * q)) * Real.exp (-(Real.pi * q / 4))`. Rewrite using `[← Real.exp_add, ← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hquad : (Real.pi * q / 4) ^ 2 ≤ 2 * Real.exp (Real.pi * q / 4)`.

Use `Real.quadratic_le_exp_of_nonneg hy0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hey : (Real.pi * q / 4) ^ 2 * Real.exp (-(Real.pi * q / 4)) ≤ 2`. Establish `h1 : Real.exp (Real.pi * q / 4) * Real.exp (-(Real.pi * q / 4)) = 1`. Rewrite using `[← Real.exp_add]`.

Simplify using the standard rewrite rules. Establish `h2` using `Real.exp_pos (-(Real.pi * q / 4))`. Use the polynomial consequences of the given equalities and inequalities. Establish `A : (-Real.pi * u) ^ 2 ≤ ε ^ 2 * (Real.pi ^ 2 * q ^ 2)`. Establish `: (-Real.pi * u) ^ 2 = Real.pi ^ 2 * u ^ 2` using `by ring`.

Rewrite using `[this]`. Use polynomial arithmetic with `[sq_nonneg Real.pi]`. Establish `hterm : (-Real.pi * u) ^ 2 * Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q) ≤ 32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hE]`.

Establish `hE0` using `Real.exp_pos (-Real.pi * q)`. Establish `hm` using `mul_le_mul_of_nonneg_left hx hE0.le`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem up_pt (q u ε : ℝ) (hq : 0 ≤ q) (h0 : 0 ≤ ε) (h4 : ε ≤ 1 / 4) (hu : |u| ≤ ε * q) :
    Real.exp (-Real.pi * (q + u)) ≤ Real.exp (-Real.pi * q) + -Real.pi * (u * Real.exp (-Real.pi * q)) +
      32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) := by
  have hpi := Real.pi_pos
  have hE : Real.exp (-Real.pi * (q + u)) = Real.exp (-Real.pi * q) * Real.exp (-Real.pi * u) := by
    rw [← Real.exp_add]; congr 1; ring
  have hx := exp_quad (-Real.pi * u)
  have habs : |-Real.pi * u| = Real.pi * |u| := by
    rw [abs_mul, abs_neg, abs_of_pos hpi]
  rw [habs] at hx
  have hu4 : |u| ≤ q / 4 := by nlinarith [abs_nonneg u, mul_nonneg (sub_nonneg.mpr h4) hq]
  have hu2 : u ^ 2 ≤ ε ^ 2 * q ^ 2 := by
    have := mul_self_le_mul_self (abs_nonneg u) hu
    nlinarith [sq_abs u]
  have hpu : Real.pi * |u| ≤ Real.pi * (q / 4) := mul_le_mul_of_nonneg_left hu4 hpi.le
  have hy0 : 0 ≤ Real.pi * q / 4 := by positivity
  have hexp1 : Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q) ≤
      Real.exp (-Real.pi * (1 / 2 * q)) * Real.exp (-(Real.pi * q / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hquad : (Real.pi * q / 4) ^ 2 ≤ 2 * Real.exp (Real.pi * q / 4) := by
    have := Real.quadratic_le_exp_of_nonneg hy0
    nlinarith
  have hey : (Real.pi * q / 4) ^ 2 * Real.exp (-(Real.pi * q / 4)) ≤ 2 := by
    have h1 : Real.exp (Real.pi * q / 4) * Real.exp (-(Real.pi * q / 4)) = 1 := by
      rw [← Real.exp_add]; simp
    have h2 := Real.exp_pos (-(Real.pi * q / 4))
    nlinarith
  have A : (-Real.pi * u) ^ 2 ≤ ε ^ 2 * (Real.pi ^ 2 * q ^ 2) := by
    have : (-Real.pi * u) ^ 2 = Real.pi ^ 2 * u ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg Real.pi]
  have hterm : (-Real.pi * u) ^ 2 * Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q) ≤
      32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) := by
    calc (-Real.pi * u) ^ 2 * Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q)
        = (-Real.pi * u) ^ 2 * (Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q)) := by ring
      _ ≤ (ε ^ 2 * (Real.pi ^ 2 * q ^ 2)) *
            (Real.exp (-Real.pi * (1 / 2 * q)) * Real.exp (-(Real.pi * q / 4))) :=
          mul_le_mul A hexp1 (by positivity) (by positivity)
      _ = 16 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) *
            ((Real.pi * q / 4) ^ 2 * Real.exp (-(Real.pi * q / 4))) := by ring
      _ ≤ 16 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) * 2 := by gcongr
      _ = 32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) := by ring
  rw [hE]
  have hE0 := Real.exp_pos (-Real.pi * q)
  have hm := mul_le_mul_of_nonneg_left hx hE0.le
  nlinarith

/- English proof (translation)
Establish `h` using `Real.add_one_le_exp (-Real.pi * u - m)`. Establish `hE : Real.exp (-Real.pi * (q + u)) = Real.exp m * Real.exp (-Real.pi * q) * Real.exp (-Real.pi * u - m)`. Rewrite using `[← Real.exp_add, ← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hE]`. Establish `hp : 0 ≤ Real.exp m * Real.exp (-Real.pi * q)` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h hp]`.
-/
private theorem low_pt (q u m : ℝ) :
    Real.exp m * ((1 - m) * Real.exp (-Real.pi * q) + -Real.pi * (u * Real.exp (-Real.pi * q))) ≤
      Real.exp (-Real.pi * (q + u)) := by
  have h := Real.add_one_le_exp (-Real.pi * u - m)
  have hE : Real.exp (-Real.pi * (q + u)) =
      Real.exp m * Real.exp (-Real.pi * q) * Real.exp (-Real.pi * u - m) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hE]
  have hp : 0 ≤ Real.exp m * Real.exp (-Real.pi * q) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hp]

/- English proof (translation)
Rewrite using `[Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]`. Establish `hu4 : |u| ≤ q / 4` using `by nlinarith [mul_nonneg (sub_nonneg.mpr h4) hq]`. Establish `hpi` using `Real.pi_pos`. Establish `h1` using `Real.add_one_le_exp (Real.pi * q / 2)`. Establish `hsplit : Real.exp (-Real.pi * (1 / 2 * q)) = Real.exp (-Real.pi * q) * Real.exp (Real.pi * q / 2)`.

Rewrite using `[← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`. Establish `hE` using `Real.exp_pos (-Real.pi * q)`.

Establish `h2 : q / 4 ≤ Real.exp (Real.pi * q / 2)` using `by nlinarith [Real.pi_gt_three]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem sum_pt (q u ε : ℝ) (hq : 0 ≤ q) (h4 : ε ≤ 1 / 4) (hu : |u| ≤ ε * q) :
    ‖u * Real.exp (-Real.pi * q)‖ ≤ Real.exp (-Real.pi * (1 / 2 * q)) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hu4 : |u| ≤ q / 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr h4) hq]
  have hpi := Real.pi_pos
  have h1 := Real.add_one_le_exp (Real.pi * q / 2)
  have hsplit : Real.exp (-Real.pi * (1 / 2 * q)) =
      Real.exp (-Real.pi * q) * Real.exp (Real.pi * q / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit]
  have hE := Real.exp_pos (-Real.pi * q)
  have h2 : q / 4 ≤ Real.exp (Real.pi * q / 2) := by nlinarith [Real.pi_gt_three]
  calc |u| * Real.exp (-Real.pi * q) ≤ q / 4 * Real.exp (-Real.pi * q) :=
        mul_le_mul_of_nonneg_right hu4 hE.le
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2 hE.le

/- English proof (translation)
Introduce `N`. Use `⟨32 * 2 ^ N, by positivity, ?_⟩` and prove the remaining obligations. Introduce `ι _ q u ε hS h0 h4 hu`. Take `⟨hq, hsc⟩` from `hS`. Establish `hsum1` using `(hsc 1 1 one_pos le_rfl).1`.

Simplify using `only [one_mul] at hsum1`. Establish `hhalf` using `hsc (1 / 2) 1 (by norm_num) (by norm_num)`. Establish `hsumh : Summable fun i => Real.exp (-Real.pi * (1 / 2 * q i))` using `hhalf.1`. Establish `hSle : ∑' i, Real.exp (-Real.pi * (1 / 2 * q i)) ≤ 2 ^ N * ∑' i, Real.exp (-Real.pi * q i)`. Establish `h` using `hhalf.2`.

Establish `h2 : (1 : ℝ) / (1 / 2) = 2` using `by norm_num`. Rewrite `h` using `[h2]`. Simplify using `only [one_mul] at h`. Conclude with `h`. Use `set Z := ∑' i, Real.exp (-Real.pi * q i) with hZ`.

Use `set Z' := ∑' i, Real.exp (-Real.pi * (q i + u i)) with hZ'`. Use `set M := ∑' i, u i * Real.exp (-Real.pi * q i) with hM`. Use `set S := ∑' i, Real.exp (-Real.pi * (1 / 2 * q i)) with hS'`. Take `⟨i0⟩` from `‹Nonempty ι›`. Establish `hZpos : 0 < Z` using `hsum1.tsum_pos (fun i => (Real.exp_pos _).le) i0 (Real.exp_pos _)`.

Establish `hsumM : Summable fun i => u i * Real.exp (-Real.pi * q i)` using `Summable.of_norm_bounded hsumh (fun i => sum_pt (q i) (u i) ε (hq i) h4 (hu i))`. Establish `hR : HasSum (fun i => Real.exp (-Real.pi * q i) + -Real.pi * (u i * Real.exp (-Real.pi * q i)) + 32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q i))) (Z + -Real.pi * M + 32 * ε ^ 2 * S)` using `(hsum1.hasSum.add (hsumM.hasSum.mul_left _)).add (hsumh.hasSum.mul_left _)`. Establish `hsum' : Summable fun i => Real.exp (-Real.pi * (q i + u i))` using `Summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le) (fun i => up_pt (q i) (u i) ε (hq i) h0 h4 (hu i)) hR.summable`. Establish `hup : Z' ≤ Z + -Real.pi * M + 32 * ε ^ 2 * S`. Rewrite using `[← hR.tsum_eq]`.

Conclude with `Summable.tsum_le_tsum (fun i => up_pt (q i) (u i) ε (hq i) h0 h4 (hu i)) hsum' hR.summable`. Use `set m := -Real.pi * M / Z with hm`. Establish `hmZ : m * Z = -Real.pi * M` using `by rw [hm]; exact div_mul_cancel₀ _ hZpos.ne'`. Establish `hlow : Real.exp m * Z ≤ Z'`. Establish `hL : HasSum (fun i => Real.exp m * ((1 - m) * Real.exp (-Real.pi * q i) + -Real.pi * (u i * Real.exp (-Real.pi * q i)))) (Real.exp m * ((1 - m) * Z + -Real.pi * M))` using `((hsum1.hasSum.mul_left (1 - m)).add (hsumM.hasSum.mul_left (-Real.pi))).mul_left (Real.exp m)`.

Establish `e : (1 - m) * Z + -Real.pi * M = Z` using `by linear_combination (-1 : ℝ) * hmZ`. Rewrite using `[← e, ← hL.tsum_eq]`. Conclude with `Summable.tsum_le_tsum (fun i => low_pt (q i) (u i) m) hL.summable hsum'`. Establish `hZ'pos : 0 < Z'` using `lt_of_lt_of_le (by positivity) hlow`. Establish `hLo : m ≤ Real.log Z' - Real.log Z`.

Use `Real.log_le_log (by positivity) hlow` as an intermediate fact. Rewrite `this` using `[Real.log_mul (Real.exp_pos m).ne' hZpos.ne', Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hUp : Real.log Z' - Real.log Z ≤ m + 32 * 2 ^ N * ε ^ 2`. Establish `h1` using `Real.log_le_sub_one_of_pos (div_pos hZ'pos hZpos)`.

Rewrite `h1` using `[Real.log_div hZ'pos.ne' hZpos.ne']`. Establish `h2 : Z' / Z - 1 ≤ m + 32 * 2 ^ N * ε ^ 2`. Rewrite using `[div_sub_one hZpos.ne', div_le_iff₀ hZpos]`. Establish `h3` using `mul_le_mul_of_nonneg_left hSle (by positivity : (0 : ℝ) ≤ 32 * ε ^ 2)`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hexpr : Real.pi * (M / Z) = -m` using `by rw [hm]; ring`. Rewrite using `[hexpr, abs_le]`. Establish `hK : (0 : ℝ) ≤ 32 * 2 ^ N * ε ^ 2` using `by positivity`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem UpperTheory.two_sided_bound_of_pointwise_bounds :
    LogTaylor := by
  intro N
  refine ⟨32 * 2 ^ N, by positivity, ?_⟩
  intro ι _ q u ε hS h0 h4 hu
  obtain ⟨hq, hsc⟩ := hS
  have hsum1 := (hsc 1 1 one_pos le_rfl).1
  simp only [one_mul] at hsum1
  have hhalf := hsc (1 / 2) 1 (by norm_num) (by norm_num)
  have hsumh : Summable fun i => Real.exp (-Real.pi * (1 / 2 * q i)) := hhalf.1
  have hSle : ∑' i, Real.exp (-Real.pi * (1 / 2 * q i)) ≤
      2 ^ N * ∑' i, Real.exp (-Real.pi * q i) := by
    have h := hhalf.2
    have h2 : (1 : ℝ) / (1 / 2) = 2 := by norm_num
    rw [h2] at h
    simp only [one_mul] at h
    exact h
  set Z := ∑' i, Real.exp (-Real.pi * q i) with hZ
  set Z' := ∑' i, Real.exp (-Real.pi * (q i + u i)) with hZ'
  set M := ∑' i, u i * Real.exp (-Real.pi * q i) with hM
  set S := ∑' i, Real.exp (-Real.pi * (1 / 2 * q i)) with hS'
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hZpos : 0 < Z := hsum1.tsum_pos (fun i => (Real.exp_pos _).le) i0 (Real.exp_pos _)
  have hsumM : Summable fun i => u i * Real.exp (-Real.pi * q i) :=
    Summable.of_norm_bounded hsumh (fun i => sum_pt (q i) (u i) ε (hq i) h4 (hu i))
  have hR : HasSum (fun i => Real.exp (-Real.pi * q i) + -Real.pi * (u i * Real.exp (-Real.pi * q i)) +
      32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q i))) (Z + -Real.pi * M + 32 * ε ^ 2 * S) :=
    (hsum1.hasSum.add (hsumM.hasSum.mul_left _)).add (hsumh.hasSum.mul_left _)
  have hsum' : Summable fun i => Real.exp (-Real.pi * (q i + u i)) :=
    Summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le)
      (fun i => up_pt (q i) (u i) ε (hq i) h0 h4 (hu i)) hR.summable
  have hup : Z' ≤ Z + -Real.pi * M + 32 * ε ^ 2 * S := by
    rw [← hR.tsum_eq]
    exact Summable.tsum_le_tsum (fun i => up_pt (q i) (u i) ε (hq i) h0 h4 (hu i)) hsum' hR.summable
  set m := -Real.pi * M / Z with hm
  have hmZ : m * Z = -Real.pi * M := by rw [hm]; exact div_mul_cancel₀ _ hZpos.ne'
  have hlow : Real.exp m * Z ≤ Z' := by
    have hL : HasSum (fun i => Real.exp m * ((1 - m) * Real.exp (-Real.pi * q i) +
        -Real.pi * (u i * Real.exp (-Real.pi * q i)))) (Real.exp m * ((1 - m) * Z + -Real.pi * M)) :=
      ((hsum1.hasSum.mul_left (1 - m)).add (hsumM.hasSum.mul_left (-Real.pi))).mul_left (Real.exp m)
    have e : (1 - m) * Z + -Real.pi * M = Z := by linear_combination (-1 : ℝ) * hmZ
    rw [← e, ← hL.tsum_eq]
    exact Summable.tsum_le_tsum (fun i => low_pt (q i) (u i) m) hL.summable hsum'
  have hZ'pos : 0 < Z' := lt_of_lt_of_le (by positivity) hlow
  have hLo : m ≤ Real.log Z' - Real.log Z := by
    have := Real.log_le_log (by positivity) hlow
    rw [Real.log_mul (Real.exp_pos m).ne' hZpos.ne', Real.log_exp] at this
    linarith
  have hUp : Real.log Z' - Real.log Z ≤ m + 32 * 2 ^ N * ε ^ 2 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hZ'pos hZpos)
    rw [Real.log_div hZ'pos.ne' hZpos.ne'] at h1
    have h2 : Z' / Z - 1 ≤ m + 32 * 2 ^ N * ε ^ 2 := by
      rw [div_sub_one hZpos.ne', div_le_iff₀ hZpos]
      have h3 := mul_le_mul_of_nonneg_left hSle (by positivity : (0 : ℝ) ≤ 32 * ε ^ 2)
      nlinarith
    linarith
  have hexpr : Real.pi * (M / Z) = -m := by rw [hm]; ring
  rw [hexpr, abs_le]
  have hK : (0 : ℝ) ≤ 32 * 2 ^ N * ε ^ 2 := by positivity
  constructor <;> linarith
