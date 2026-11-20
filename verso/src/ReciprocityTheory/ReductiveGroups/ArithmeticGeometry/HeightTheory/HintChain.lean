import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HintISBounds

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

/- English proof (translation)
Use `haveI := hd.graded c`. Take `⟨Bw, hBw⟩` from `d.hint_bdd sg c (f := d.w (d.jc c)) (hd.bdd sg d.wL _ (Or.inl ⟨by rw [hd.WW_span]; exact Submodule.subset_span ⟨_, rfl⟩, rfl⟩))`. Take `⟨Be, hBe⟩` from `d.hint_bdd sg c (hd.bdd sg (d.n1 • d.wde) d.et (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))`. Take `⟨Bt, hBt⟩` from `d.hint_bdd sg c (hd.bdd sg ((2 : ℕ) • d.G1) d.ta1 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))`. Take `⟨B2, hB2⟩` from `d.hint_bdd sg c (hd.bdd sg d.G2 d.ta2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))`.

Take `⟨k, hk⟩` from `d.hint_thp_ne hd c`. Take `⟨Bh, hBh⟩` from `d.hint_bdd sg c (f := d.thp k) (hd.bdd sg d.wF _ (Or.inr (Or.inl ⟨by rw [hd.Thp_span]; exact Submodule.subset_span ⟨k, rfl⟩, rfl⟩)))`. Establish `hwm` using `hd.w_mem (d.jc c) c`. Establish `hw0` using `hd.w_base c`. Establish `hem` using `hd.et_mem c`.

Establish `he0` using `hd.et_ne c`. Establish `htm` using `hd.firstSectionMem c`. Establish `ht0` using `hd.firstSectionNeZero c`. Establish `h2m` using `hd.secondSectionMem c`. Establish `h20` using `hd.secondSectionNeZero c`.

Establish `hhm` using `hd.thp_mem k c`. Establish `hn1 : 0 < d.n1` using `Nat.mul_pos hd.i_ge hd.g_zero_ge_ask_sum`. Establish `hi : (1 : ℝ) ≤ d.i` using `by exact_mod_cast hd.i_ge`. Establish `hn1r : (d.n1 : ℝ) = d.i * d.g0` using `by simp [Data.n1]`. Establish `hn1r1 : (1 : ℝ) ≤ d.n1` using `by exact_mod_cast hn1`.

Establish `hκ : (d.n1 : ℝ) * (d.cc / d.i) = d.g0 * d.cc`. Rewrite using `[hn1r]`. Clear the denominators using the available nonvanishing facts. Establish `hq : 1 ≤ 2 - 2 * d.cc * d.g0` using `by linarith [hd.ccg0]`. Establish `IU : d.HintIS c sg (fun P => Real.log ‖d.hintU c P‖)` using `d.hint_intU hd h c sg`.

Take `⟨ht1m, ht10, ht1l⟩` from `d.hint_pow hd htm ht0 d.n1 hn1`. Take `⟨he2m, he20, he2l⟩` from `d.hint_pow hd hem he0 2 two_pos`. Take `⟨hwpm, hwp0, hwpl⟩` from `d.hint_pow hd hwm hw0 (2 * d.n1) (by omega)`. Establish `hW1 : d.n1 • ((2 : ℕ) • d.G1) + (2 : ℕ) • (d.n1 • d.wde) = (2 * d.n1) • d.wL`. Simplify using `only [Data.G1, smul_sub, smul_smul, mul_comm d.n1 2]`.

Normalize the expressions using the abelian group laws. Establish `hf1m : d.ta1 c ^ d.n1 * d.et c ^ 2 ∈ 𝒜 c ((2 * d.n1) • d.wL)`. Rewrite using `[← hW1]`. Conclude with `SetLike.mul_mem_graded ht1m he2m`. Establish `hf10` using `hd.mul_ne_zero c ht1m he2m ht10 he20`.

Establish `Ir1 : d.HintIS c sg (fun P => Real.log ‖P (ratio (Ω` using `Ω c) (d.ta1 c ^ d.n1 * d.et c ^ 2) (d.w (d.jc c) c ^ (2 * d.n1)))‖) := d.hint_intNorm hd h c sg _ (hint_ratio_ne hd hwpm hwp0 hf1m hf10)`. Establish `E1 : ∀ P, (d.n1 : ℝ) * Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P) + 2 * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) = Real.log ‖P (ratio (Ω` using `Ω c) (d.ta1 c ^ d.n1 * d.et c ^ 2) (d.w (d.jc c) c ^ (2 * d.n1)))‖ + 2 * d.n1 * Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) := by`. Introduce `P`. Establish `h1` using `d.hint_log_mul hd ht1m he2m ht10 he20 P`. Rewrite `h1` using `[hW1, ht1l, he2l]`.

Establish `h2` using `d.hint_log_line hd hwpm hwp0 hf1m hf10 P`. Rewrite `h2` using `[hwpl]`. Move the coercions through the operations in `at h1 h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `I2 : ∀ P, -(Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) + Real.log ‖d.hintU c P‖) ≤ d.tableLineDegreeFive * d.DF + d.cc / d.i * (-Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) + d.cc * d.tableLineDegreeTwo`.

Introduce `P`. Rewrite using `[← d.hint_log_be hd c P]`. Conclude with `hI2be c P`. Establish `Iet : d.HintIS c sg (fun P => Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P))`. Use `d.hintIS_bounds hd h (d.hint_meas hd c sg hem he0) (d.hintIS_lin hd h Ir1 IU (1 / (2 - 2 * d.cc * d.g0)) (-(2 * d.n1) / (2 - 2 * d.cc * d.g0)) (-(d.n1 * Real.log Bt + 2 * d.n1 * (d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo)) / (2 - 2 * d.cc * d.g0))) (fun P hP => ? …` and prove the remaining obligations.

Establish `e1` using `E1 P`. Establish `lt` using `d.hint_log_le hd htm ht0 hBt P hP`. Establish `lt2` using `mul_le_mul_of_nonneg_left lt (by positivity : (0 : ℝ) ≤ d.n1)`. Establish `ib2` using `mul_le_mul_of_nonneg_left (I2 P) (by positivity : (0 : ℝ) ≤ 2 * d.n1)`. Establish `hκ' : (d.n1 : ℝ) * (d.cc / d.i) * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) = d.g0 * d.cc * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)` using `by rw [hκ]`.

Establish `hqp : (0 : ℝ) < 2 - 2 * d.cc * d.g0` using `by linarith`. Rewrite using `[← sub_nonneg]`. Establish `: ∀ x y z : ℝ, 1 / (2 - 2 * d.cc * d.g0) * x + -(2 * d.n1) / (2 - 2 * d.cc * d.g0) * y + -z / (2 - 2 * d.cc * d.g0) = (x - 2 * d.n1 * y - z) / (2 - 2 * d.cc * d.g0)`. Introduce `x y z`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, sub_nonneg, div_le_iff₀ hqp]`. Use the polynomial consequences of the given equalities and inequalities. Establish `Iw : d.HintIS c sg (fun P => Real.log (d.nrm c d.wL (d.w (d.jc c) c) P))`. Use `d.hintIS_bounds hd h (d.hint_meas hd c sg hwm hw0) (d.hintIS_lin hd h Iet IU (d.cc / d.i) (-1) (-(d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo))) (fun P _ => ?_) _ (d.hint_log_le hd hwm hw0 hBw)` and prove the remaining obligations. Use `I2 P` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `It1 : d.HintIS c sg (fun P => Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P))`. Use `d.hintIS_bounds hd h (d.hint_meas hd c sg htm ht0) (d.hintIS_lin hd h Ir1 Iw (1 / d.n1) 2 (-(2 * Real.log Be) / d.n1)) (fun P hP => ?_) _ (d.hint_log_le hd htm ht0 hBt)` and prove the remaining obligations. Establish `e1` using `E1 P`. Establish `le` using `d.hint_log_le hd hem he0 hBe P hP`.

Establish `hnp : (0 : ℝ) < d.n1` using `by linarith`. Establish `: ∀ x y : ℝ, 1 / (d.n1 : ℝ) * x + 2 * y + -(2 * Real.log Be) / d.n1 = (x + 2 * d.n1 * y - 2 * Real.log Be) / d.n1`. Introduce `x y`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, div_le_iff₀ hnp]`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨hwqm, hwq0, hwql⟩` from `d.hint_pow hd hwm hw0 (d.D + 4) (by omega)`. Establish `hW2 : d.wF + d.G2 = (d.D + 4) • d.wL` using `by rw [Data.G2]; abel`. Establish `hf2m : d.thp k c * d.ta2 c ∈ 𝒜 c ((d.D + 4) • d.wL)`.

Rewrite using `[← hW2]`. Conclude with `SetLike.mul_mem_graded hhm h2m`. Establish `hf20` using `hd.mul_ne_zero c hhm h2m hk h20`. Establish `Ir2 : d.HintIS c sg (fun P => Real.log ‖P (ratio (Ω` using `Ω c) (d.thp k c * d.ta2 c) (d.w (d.jc c) c ^ (d.D + 4)))‖) := d.hint_intNorm hd h c sg _ (hint_ratio_ne hd hwqm hwq0 hf2m hf20)`. Establish `E2 : ∀ P, Real.log (d.nrm c d.wF (d.thp k c) P) + Real.log (d.nrm c d.G2 (d.ta2 c) P) = Real.log ‖P (ratio (Ω` using `Ω c) (d.thp k c * d.ta2 c) (d.w (d.jc c) c ^ (d.D + 4)))‖ + ((d.D + 4 : ℕ) : ℝ) * Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) := by`.

Introduce `P`. Establish `h1` using `d.hint_log_mul hd hhm h2m hk h20 P`. Rewrite `h1` using `[hW2]`. Establish `h2` using `d.hint_log_line hd hwqm hwq0 hf2m hf20 P`. Rewrite `h2` using `[hwql]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨Iet, Iw, It1, ⟨d.thp k c, hhm, hk, ?_⟩, ?_⟩` and prove the remaining obligations. Use `d.hintIS_bounds hd h (d.hint_meas hd c sg hhm hk) (d.hintIS_lin hd h Ir2 Iw 1 ((d.D + 4 : ℕ) : ℝ) (-Real.log B2)) (fun P hP => ?_) _ (d.hint_log_le hd hhm hk hBh)` and prove the remaining obligations. Establish `e2` using `E2 P`. Establish `l2` using `d.hint_log_le hd h2m h20 hB2 P hP`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `d.hintIS_bounds hd h (d.hint_meas hd c sg h2m h20) (d.hintIS_lin hd h Ir2 Iw 1 ((d.D + 4 : ℕ) : ℝ) (-Real.log Bh)) (fun P hP => ?_) _ (d.hint_log_le hd h2m h20 hB2)` and prove the remaining obligations. Establish `e2` using `E2 P`. Establish `l2` using `d.hint_log_le hd hhm hk hBh P hP`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hint_chain (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (c : ι) (sg : K →+* ℂ) :
    d.HintIS c sg (fun P => Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) ∧
    d.HintIS c sg (fun P => Real.log (d.nrm c d.wL (d.w (d.jc c) c) P)) ∧
    d.HintIS c sg (fun P => Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P)) ∧
    (∃ e, e ∈ 𝒜 c d.wF ∧ e ≠ 0 ∧ d.HintIS c sg (fun P => Real.log (d.nrm c d.wF e P))) ∧
    d.HintIS c sg (fun P => Real.log (d.nrm c d.G2 (d.ta2 c) P)) := by
  haveI := hd.graded c
  obtain ⟨Bw, hBw⟩ := d.hint_bdd sg c (f := d.w (d.jc c)) (hd.bdd sg d.wL _ (Or.inl
    ⟨by rw [hd.WW_span]; exact Submodule.subset_span ⟨_, rfl⟩, rfl⟩))
  obtain ⟨Be, hBe⟩ := d.hint_bdd sg c
    (hd.bdd sg (d.n1 • d.wde) d.et (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  obtain ⟨Bt, hBt⟩ := d.hint_bdd sg c
    (hd.bdd sg ((2 : ℕ) • d.G1) d.ta1 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  obtain ⟨B2, hB2⟩ := d.hint_bdd sg c
    (hd.bdd sg d.G2 d.ta2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
  obtain ⟨k, hk⟩ := d.hint_thp_ne hd c
  obtain ⟨Bh, hBh⟩ := d.hint_bdd sg c (f := d.thp k) (hd.bdd sg d.wF _ (Or.inr (Or.inl
    ⟨by rw [hd.Thp_span]; exact Submodule.subset_span ⟨k, rfl⟩, rfl⟩)))
  have hwm := hd.w_mem (d.jc c) c
  have hw0 := hd.w_base c
  have hem := hd.et_mem c
  have he0 := hd.et_ne c
  have htm := hd.firstSectionMem c
  have ht0 := hd.firstSectionNeZero c
  have h2m := hd.secondSectionMem c
  have h20 := hd.secondSectionNeZero c
  have hhm := hd.thp_mem k c
  have hn1 : 0 < d.n1 := Nat.mul_pos hd.i_ge hd.g_zero_ge_ask_sum
  have hi : (1 : ℝ) ≤ d.i := by exact_mod_cast hd.i_ge
  have hn1r : (d.n1 : ℝ) = d.i * d.g0 := by simp [Data.n1]
  have hn1r1 : (1 : ℝ) ≤ d.n1 := by exact_mod_cast hn1
  have hκ : (d.n1 : ℝ) * (d.cc / d.i) = d.g0 * d.cc := by
    rw [hn1r]; field_simp
  have hq : 1 ≤ 2 - 2 * d.cc * d.g0 := by linarith [hd.ccg0]
  have IU : d.HintIS c sg (fun P => Real.log ‖d.hintU c P‖) := d.hint_intU hd h c sg

  obtain ⟨ht1m, ht10, ht1l⟩ := d.hint_pow hd htm ht0 d.n1 hn1
  obtain ⟨he2m, he20, he2l⟩ := d.hint_pow hd hem he0 2 two_pos
  obtain ⟨hwpm, hwp0, hwpl⟩ := d.hint_pow hd hwm hw0 (2 * d.n1) (by omega)
  have hW1 : d.n1 • ((2 : ℕ) • d.G1) + (2 : ℕ) • (d.n1 • d.wde) = (2 * d.n1) • d.wL := by
    simp only [Data.G1, smul_sub, smul_smul, mul_comm d.n1 2]; abel
  have hf1m : d.ta1 c ^ d.n1 * d.et c ^ 2 ∈ 𝒜 c ((2 * d.n1) • d.wL) := by
    rw [← hW1]; exact SetLike.mul_mem_graded ht1m he2m
  have hf10 := hd.mul_ne_zero c ht1m he2m ht10 he20
  have Ir1 : d.HintIS c sg (fun P => Real.log ‖P (ratio (Ω := Ω c) (d.ta1 c ^ d.n1 * d.et c ^ 2)
      (d.w (d.jc c) c ^ (2 * d.n1)))‖) :=
    d.hint_intNorm hd h c sg _ (hint_ratio_ne hd hwpm hwp0 hf1m hf10)
  have E1 : ∀ P, (d.n1 : ℝ) * Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P) +
      2 * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) =
      Real.log ‖P (ratio (Ω := Ω c) (d.ta1 c ^ d.n1 * d.et c ^ 2)
        (d.w (d.jc c) c ^ (2 * d.n1)))‖ + 2 * d.n1 * Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) := by
    intro P
    have h1 := d.hint_log_mul hd ht1m he2m ht10 he20 P
    rw [hW1, ht1l, he2l] at h1
    have h2 := d.hint_log_line hd hwpm hwp0 hf1m hf10 P
    rw [hwpl] at h2
    push_cast at h1 h2
    linarith
  have I2 : ∀ P, -(Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) + Real.log ‖d.hintU c P‖) ≤
      d.tableLineDegreeFive * d.DF + d.cc / d.i * (-Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) +
        d.cc * d.tableLineDegreeTwo := by
    intro P; rw [← d.hint_log_be hd c P]; exact hI2be c P

  have Iet : d.HintIS c sg (fun P => Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) := by
    refine d.hintIS_bounds hd h (d.hint_meas hd c sg hem he0)
      (d.hintIS_lin hd h Ir1 IU (1 / (2 - 2 * d.cc * d.g0)) (-(2 * d.n1) / (2 - 2 * d.cc * d.g0))
        (-(d.n1 * Real.log Bt + 2 * d.n1 * (d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo)) /
          (2 - 2 * d.cc * d.g0))) (fun P hP => ?_) _ (d.hint_log_le hd hem he0 hBe)
    have e1 := E1 P
    have lt := d.hint_log_le hd htm ht0 hBt P hP
    have lt2 := mul_le_mul_of_nonneg_left lt (by positivity : (0 : ℝ) ≤ d.n1)
    have ib2 := mul_le_mul_of_nonneg_left (I2 P) (by positivity : (0 : ℝ) ≤ 2 * d.n1)
    have hκ' : (d.n1 : ℝ) * (d.cc / d.i) * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) =
        d.g0 * d.cc * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) := by rw [hκ]
    have hqp : (0 : ℝ) < 2 - 2 * d.cc * d.g0 := by linarith
    rw [← sub_nonneg]
    have : ∀ x y z : ℝ, 1 / (2 - 2 * d.cc * d.g0) * x + -(2 * d.n1) / (2 - 2 * d.cc * d.g0) * y +
        -z / (2 - 2 * d.cc * d.g0) = (x - 2 * d.n1 * y - z) / (2 - 2 * d.cc * d.g0) := by
      intro x y z; ring
    rw [this, sub_nonneg, div_le_iff₀ hqp]
    nlinarith

  have Iw : d.HintIS c sg (fun P => Real.log (d.nrm c d.wL (d.w (d.jc c) c) P)) := by
    refine d.hintIS_bounds hd h (d.hint_meas hd c sg hwm hw0)
      (d.hintIS_lin hd h Iet IU (d.cc / d.i) (-1) (-(d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo)))
      (fun P _ => ?_) _ (d.hint_log_le hd hwm hw0 hBw)
    have := I2 P
    linarith

  have It1 : d.HintIS c sg (fun P => Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P)) := by
    refine d.hintIS_bounds hd h (d.hint_meas hd c sg htm ht0)
      (d.hintIS_lin hd h Ir1 Iw (1 / d.n1) 2 (-(2 * Real.log Be) / d.n1)) (fun P hP => ?_) _
      (d.hint_log_le hd htm ht0 hBt)
    have e1 := E1 P
    have le := d.hint_log_le hd hem he0 hBe P hP
    have hnp : (0 : ℝ) < d.n1 := by linarith
    have : ∀ x y : ℝ, 1 / (d.n1 : ℝ) * x + 2 * y + -(2 * Real.log Be) / d.n1 =
        (x + 2 * d.n1 * y - 2 * Real.log Be) / d.n1 := by
      intro x y; field_simp; ring
    rw [this, div_le_iff₀ hnp]
    nlinarith

  obtain ⟨hwqm, hwq0, hwql⟩ := d.hint_pow hd hwm hw0 (d.D + 4) (by omega)
  have hW2 : d.wF + d.G2 = (d.D + 4) • d.wL := by rw [Data.G2]; abel
  have hf2m : d.thp k c * d.ta2 c ∈ 𝒜 c ((d.D + 4) • d.wL) := by
    rw [← hW2]; exact SetLike.mul_mem_graded hhm h2m
  have hf20 := hd.mul_ne_zero c hhm h2m hk h20
  have Ir2 : d.HintIS c sg (fun P => Real.log ‖P (ratio (Ω := Ω c) (d.thp k c * d.ta2 c)
      (d.w (d.jc c) c ^ (d.D + 4)))‖) :=
    d.hint_intNorm hd h c sg _ (hint_ratio_ne hd hwqm hwq0 hf2m hf20)
  have E2 : ∀ P, Real.log (d.nrm c d.wF (d.thp k c) P) + Real.log (d.nrm c d.G2 (d.ta2 c) P) =
      Real.log ‖P (ratio (Ω := Ω c) (d.thp k c * d.ta2 c) (d.w (d.jc c) c ^ (d.D + 4)))‖ +
        ((d.D + 4 : ℕ) : ℝ) * Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) := by
    intro P
    have h1 := d.hint_log_mul hd hhm h2m hk h20 P
    rw [hW2] at h1
    have h2 := d.hint_log_line hd hwqm hwq0 hf2m hf20 P
    rw [hwql] at h2
    linarith
  refine ⟨Iet, Iw, It1, ⟨d.thp k c, hhm, hk, ?_⟩, ?_⟩
  · refine d.hintIS_bounds hd h (d.hint_meas hd c sg hhm hk)
      (d.hintIS_lin hd h Ir2 Iw 1 ((d.D + 4 : ℕ) : ℝ) (-Real.log B2)) (fun P hP => ?_) _
      (d.hint_log_le hd hhm hk hBh)
    have e2 := E2 P
    have l2 := d.hint_log_le hd h2m h20 hB2 P hP
    linarith
  · refine d.hintIS_bounds hd h (d.hint_meas hd c sg h2m h20)
      (d.hintIS_lin hd h Ir2 Iw 1 ((d.D + 4 : ℕ) : ℝ) (-Real.log Bh)) (fun P hP => ?_) _
      (d.hint_log_le hd h2m h20 hB2)
    have e2 := E2 P
    have l2 := d.hint_log_le hd hhm hk hBh P hP
    linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
