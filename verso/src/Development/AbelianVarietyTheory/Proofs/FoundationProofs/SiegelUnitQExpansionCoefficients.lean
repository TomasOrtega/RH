import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplexStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitQExpansionCoeffsIntegralStatement

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KExp

/- English proof (translation)
Rewrite using `[Complex.norm_exp]`. Use `congr 1`. Simplify using `[Complex.mul_re, Complex.mul_im]`.
-/
theorem norm_cexp_real (t : ℝ) (z : ℂ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * z)‖ = Real.exp (-2 * Real.pi * t * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hnon : (Function.support d).Nonempty`. Take `⟨r, hr⟩` from `Function.ne_iff.mp hne`. Conclude with `⟨r, hr⟩`. Use `set r0 := hwf.min hnon with hr0def`.

Establish `hr0 : d r0 ≠ 0` using `hwf.min_mem hnon`. Establish `hle : ∀ r, d r ≠ 0 → r0 ≤ r` using `fun r hr => hwf.min_le hnon hr`. Use `choose zs hzS hzim using fun j : ℕ => hS (max z1.im 0 + j)`. Use `set y1 := z1.im with hy1`. Establish `hnorm : ∀ (r : ℚ) (z : ℂ), ‖d r * Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) - r0) * z)‖ = ‖d r‖ * Real.exp (-2 * Real.pi * ((r : ℝ) - r0) * z.im)`.

Introduce `r z`. Rewrite using `[norm_mul]`. Use `norm_cexp_real ((r : ℝ) - r0) z` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[this]`.

Set `f : ℕ → ℚ → ℂ` to `fun j r => d r * Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) - r0) * zs j)`. Set `g : ℚ → ℂ` to `fun r => if r = r0 then d r0 else 0`. Set `bound : ℚ → ℝ` to `fun r => ‖d r‖ * Real.exp (-2 * Real.pi * ((r : ℝ) - r0) * y1)`. Establish `hb : Summable bound`. Establish `h2` using `((summable_norm_iff (E := ℂ)).mpr h1).mul_right (Real.exp (2 * Real.pi * r0 * y1))`.

Use `h2.congr fun r => ?_` and prove the remaining obligations. Simplify using `only [bound]`. Establish `hn` using `norm_cexp_real (r : ℝ) z1`. Rewrite `hn` using `[Complex.ofReal_ratCast]`. Rewrite using `[norm_mul, hn, mul_assoc, ← Real.exp_add]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hlim` using `tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop) (f := f) (g := g) hb ?_ ?_`. Establish `hf0 : ∀ j, ∑' r, f j r = 0`. Introduce `j`.

Establish `h` using `(hz (zs j) (hzS j)).mul_left (Complex.exp (-(2 * Real.pi * Complex.I * (r0 : ℂ) * zs j)))`. Rewrite `h` using `[mul_zero]`. Use `Eq.trans (tsum_congr fun r => ?_) h.tsum_eq` and prove the remaining obligations. Simplify using `only [f]`. Rewrite using `[mul_left_comm, ← Complex.exp_add]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hg : ∑' r, g r = d r0`. Rewrite using `[tsum_eq_single r0 (fun r hr => by simp [g, hr])]`. Simplify using `[g]`.

Simplify using `only [hf0, hg] at hlim`. Conclude with `hr0 (tendsto_nhds_unique hlim tendsto_const_nhds)`. Introduce `r`. Distinguish the cases in `hr : r = r0`. Substitute `hr` using the available equality.

Simplify using `only [f, g, if_pos rfl, sub_self, mul_zero, zero_mul, Complex.exp_zero, mul_one]`. Conclude with `tendsto_const_nhds`. Distinguish the cases in `hd : d r = 0`. Simplify using `only [f, g, hd, zero_mul, if_neg hr]`. Conclude with `tendsto_const_nhds`.

Establish `hlt : (r0 : ℝ) < r` using `by exact_mod_cast lt_of_le_of_ne (hle r hd) (Ne.symm hr)`. Simplify using `only [g, if_neg hr]`. Rewrite using `[tendsto_zero_iff_norm_tendsto_zero]`. Establish `hpos : 0 < 2 * Real.pi * ((r : ℝ) - r0)` using `by have := Real.pi_pos; nlinarith`. Establish `hT : Filter.Tendsto (fun j : ℕ => ‖d r‖ * Real.exp (-(2 * Real.pi * ((r : ℝ) - r0) * j))) Filter.atTop (nhds 0)`.

Use `(Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hpos)).const_mul ‖d r‖` as an intermediate fact. Simplify using `using this`. Use `squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hT` and prove the remaining obligations. Simplify using `only [f]`. Rewrite using `[hnorm]`.

Use `mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)` and prove the remaining obligations. Establish `: (j : ℝ) ≤ (zs j).im`. Use `hzim j` as an intermediate fact. Establish `: (0 : ℝ) ≤ max y1 0` using `le_max_right _ _`. Combine the linear equalities and inequalities to obtain the conclusion.

Use the polynomial consequences of the given equalities and inequalities. Use `Filter.Eventually.of_forall fun j r => ?_` and prove the remaining obligations. Simplify using `only [f, bound]`. Rewrite using `[hnorm]`. Distinguish the cases in `hd : d r = 0`.

Simplify using `[hd]`. Use `mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)` and prove the remaining obligations. Establish `h1 : (r0 : ℝ) ≤ r` using `by exact_mod_cast hle r hd`. Establish `: y1 ≤ (zs j).im`. Use `hzim j` as an intermediate fact.

Establish `: y1 ≤ max y1 0` using `le_max_left _ _`. Establish `: (0:ℝ) ≤ j` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp : 0 ≤ 2 * Real.pi * ((r : ℝ) - r0)` using `mul_nonneg (by positivity) (by linarith)`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left this hp]`.
-/
theorem uniq (d : ℚ → ℂ) (hwf : (Function.support d).IsWF) (S : Set ℂ)
    (hz : ∀ z ∈ S, HasSum (fun r : ℚ => d r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) 0)
    (z1 : ℂ) (h1 : Summable (fun r : ℚ => d r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z1)))
    (hS : ∀ y : ℝ, ∃ z ∈ S, y < z.im) : d = 0 := by
  by_contra hne
  have hnon : (Function.support d).Nonempty := by
    obtain ⟨r, hr⟩ := Function.ne_iff.mp hne
    exact ⟨r, hr⟩
  set r0 := hwf.min hnon with hr0def
  have hr0 : d r0 ≠ 0 := hwf.min_mem hnon
  have hle : ∀ r, d r ≠ 0 → r0 ≤ r := fun r hr => hwf.min_le hnon hr
  choose zs hzS hzim using fun j : ℕ => hS (max z1.im 0 + j)
  set y1 := z1.im with hy1
  have hnorm : ∀ (r : ℚ) (z : ℂ), ‖d r * Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) - r0) * z)‖
      = ‖d r‖ * Real.exp (-2 * Real.pi * ((r : ℝ) - r0) * z.im) := by
    intro r z
    rw [norm_mul]
    have := norm_cexp_real ((r : ℝ) - r0) z
    push_cast at this
    rw [this]
  let f : ℕ → ℚ → ℂ := fun j r => d r * Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) - r0) * zs j)
  let g : ℚ → ℂ := fun r => if r = r0 then d r0 else 0
  let bound : ℚ → ℝ := fun r => ‖d r‖ * Real.exp (-2 * Real.pi * ((r : ℝ) - r0) * y1)
  have hb : Summable bound := by
    have h2 := ((summable_norm_iff (E := ℂ)).mpr h1).mul_right (Real.exp (2 * Real.pi * r0 * y1))
    refine h2.congr fun r => ?_
    simp only [bound]
    have hn := norm_cexp_real (r : ℝ) z1
    rw [Complex.ofReal_ratCast] at hn
    rw [norm_mul, hn, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop) (f := f) (g := g) hb ?_ ?_
  · have hf0 : ∀ j, ∑' r, f j r = 0 := by
      intro j
      have h := (hz (zs j) (hzS j)).mul_left (Complex.exp (-(2 * Real.pi * Complex.I * (r0 : ℂ) * zs j)))
      rw [mul_zero] at h
      refine Eq.trans (tsum_congr fun r => ?_) h.tsum_eq
      simp only [f]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      ring
    have hg : ∑' r, g r = d r0 := by
      rw [tsum_eq_single r0 (fun r hr => by simp [g, hr])]
      simp [g]
    simp only [hf0, hg] at hlim
    exact hr0 (tendsto_nhds_unique hlim tendsto_const_nhds)
  · intro r
    by_cases hr : r = r0
    · subst hr
      simp only [f, g, if_pos rfl, sub_self, mul_zero, zero_mul, Complex.exp_zero, mul_one]
      exact tendsto_const_nhds
    by_cases hd : d r = 0
    · simp only [f, g, hd, zero_mul, if_neg hr]
      exact tendsto_const_nhds
    have hlt : (r0 : ℝ) < r := by exact_mod_cast lt_of_le_of_ne (hle r hd) (Ne.symm hr)
    simp only [g, if_neg hr]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hpos : 0 < 2 * Real.pi * ((r : ℝ) - r0) := by have := Real.pi_pos; nlinarith
    have hT : Filter.Tendsto (fun j : ℕ => ‖d r‖ * Real.exp (-(2 * Real.pi * ((r : ℝ) - r0) * j))) Filter.atTop (nhds 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hpos)).const_mul ‖d r‖
      simpa using this
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hT
    simp only [f]
    rw [hnorm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have : (j : ℝ) ≤ (zs j).im := by
      have := hzim j
      have : (0 : ℝ) ≤ max y1 0 := le_max_right _ _
      linarith
    nlinarith
  · refine Filter.Eventually.of_forall fun j r => ?_
    simp only [f, bound]
    rw [hnorm]
    by_cases hd : d r = 0
    · simp [hd]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have h1 : (r0 : ℝ) ≤ r := by exact_mod_cast hle r hd
    have : y1 ≤ (zs j).im := by
      have := hzim j
      have : y1 ≤ max y1 0 := le_max_left _ _
      have : (0:ℝ) ≤ j := by positivity
      linarith
    have hp : 0 ≤ 2 * Real.pi * ((r : ℝ) - r0) := mul_nonneg (by positivity) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left this hp]

end GlobalTheory.KExp

namespace GlobalTheory.KExp

/- English proof (translation)
Introduce `Ω _ _ _ ε T c M a b hM haM hadm`. Use `set x : Fin 2 → ℚ := ![(a : ℚ) / M, (b : ℚ) / M] with hx`. Take `⟨k, hk⟩` from `GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral c M a hM haM`. Take `⟨A', hA', -⟩` from `hk b hadm`. Establish `hmem` using `GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hadm`.

Use `set f := siegel T c x with hf`. Take `⟨φ, C, hφ, hsum⟩` from `T.an_exp f`. Establish `hMq : (M : ℚ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `hMc : (M : ℂ) ≠ 0` using `by exact_mod_cast hM.ne'`. Set `ι : ℕ → ℚ` to `fun n => ((k : ℚ) + n) / M`.

Establish `hι : Function.Injective ι`. Introduce `n m h`. Simplify using `only [ι] at h`. Rewrite `h` using `[div_left_inj' hMq, add_right_inj]`. Conclude with `h` after adjusting the coercions.

Set `B : ℚ → ℂ` to `fun r => if h : ∃ n, ι n = r then A' h.choose else 0`. Establish `hBι : ∀ n, B (ι n) = A' n`. Introduce `n`. Establish `h : ∃ m, ι m = ι n` using `⟨n, rfl⟩`. Simplify using `only [B, dif_pos h]`.

Rewrite using `[hι h.choose_spec]`. Establish `hB0 : ∀ r, r ∉ Set.range ι → B r = 0`. Introduce `r hr`. Simplify using `only [B]`. Rewrite using `[dif_neg]`.

Conclude with `hr`. Establish `hBsum : ∀ z : ℂ, 0 < z.im → HasSum (fun r : ℚ => B r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (sgC c x z)`. Introduce `z hz`. Establish `h2` using `(hA' ⟨z, hz⟩).mul_left (ee ((k : ℂ) / M * z))`. Rewrite using `[← hι.hasSum_iff (fun r hr => by simp [hB0 r hr])]`.

Establish `e1 : ((fun r : ℚ => B r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) ∘ ι) = fun n : ℕ => ee ((k : ℂ) / M * z) * (A' n * Complex.exp (2 * Real.pi * Complex.I * n * z / M))`. Use function extensionality and compare the values at `n`. Simplify using `only [Function.comp_apply, hBι, ι, ee]`. Rewrite using `[mul_left_comm, ← Complex.exp_add]`. Use `congr 2`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `e2 : sgC c x z = ee ((k : ℂ) / M * z) * (sg c x ⟨z, hz⟩ * ee (-((k : ℂ) / M) * z))`. Simplify using `only [sgC, UpperHalfPlane.ofComplex_apply_of_im_pos hz]`. Rewrite using `[mul_left_comm, ee, ee, ← Complex.exp_add]`.

Establish `: 2 * Real.pi * Complex.I * ((k : ℂ) / M * z) + 2 * Real.pi * Complex.I * (-((k : ℂ) / M) * (z : ℂ)) = 0`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Complex.exp_zero, mul_one]`. Rewrite using `[e1, e2]`. Simplify using `using h2`.

Establish `hgerm : φ =ᶠ[Filter.codiscreteWithin Hs] sgC c x`. Use `hφ.symm.trans hmem` as an intermediate fact. Conclude with `Filter.Germ.coe_eq.mp this`. Set `S : Set ℂ` to `{z | C < z.im ∧ 0 < z.im ∧ φ z = sgC c x z}`. Establish `hS : ∀ y : ℝ, ∃ z ∈ S, y < z.im`.

Introduce `y`. Use `set Y := max (max y C) 0 + 1 with hY`. Use `set w : ℂ := Complex.I * Y`. Establish `hwim : w.im = Y` using `by simp [w]`. Establish `hw : w ∈ Hs` using `by show 0 < w.im`.

Rewrite using `[hwim]`. Use `le_max_right (max y C) 0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hgerm w hw`. Establish `h2 : Metric.ball w (1 / 2) ∈ nhdsWithin w {w}ᶜ` using `nhdsWithin_le_nhds (Metric.ball_mem_nhds w (by norm_num))`.

Take `⟨z, hz1, hz2⟩` from `Filter.nonempty_of_mem (Filter.inter_mem h1 h2)`. Establish `hdist : |z.im - Y| < 1 / 2`. Use `Complex.abs_im_le_norm (z - w)` as an intermediate fact. Rewrite `hz2` using `[Metric.mem_ball, dist_eq_norm]`. Rewrite `this` using `[Complex.sub_im, hwim]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hyY : y ≤ max (max y C) 0` using `le_trans (le_max_left _ _) (le_max_left _ _)`. Establish `hCY : C ≤ max (max y C) 0` using `le_trans (le_max_right _ _) (le_max_left _ _)`. Establish `h0Y : 0 ≤ max (max y C) 0` using `le_max_right _ _`. Establish `hzim : max (max y C) 0 + 1 / 2 < z.im`.

Use `(abs_lt.mp hdist).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hzH : z ∈ Hs` using `show 0 < z.im by linarith`. Use `⟨z, ⟨by linarith, by linarith, ?_⟩, by linarith⟩` and prove the remaining obligations. Break down `hz1 with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd hzH h`. Set `d : ℚ → ℂ` to `fun r => ε ((T.exp f).coeff r) - B r`. Establish `hd : d = 0`. Use `GlobalTheory.KExp.uniq d ?_ S ?_ (Complex.I * (|C| + 1)) ?_ hS` and prove the remaining obligations.

Establish `hR : (Set.range ι).IsWF`. Establish `: Set.range ι = ι '' Set.univ` using `Set.image_univ.symm`. Rewrite using `[this]`. Use `(Set.IsPWO.image_of_monotone (Set.isPWO_of_wellQuasiOrderedLE _) ?_).isWF` and prove the remaining obligations. Introduce `n m h`.

Simplify using `only [ι]`. Use `gcongr`. Use `((T.exp f).isWF_support.union hR).mono ?_` and prove the remaining obligations. Introduce `r hr`. Assume the negation of the conclusion as `hn`.

Simplify using `only [Set.mem_union, not_or] at hn`. Apply `hr` to reduce the goal to its premises. Simplify using `only [d, hB0 r hn.2]`. Establish `: (T.exp f).coeff r = 0` using `by simpa [HahnSeries.support] using hn.1`. Simplify using `[this]`.

Introduce `z hz`. Use `(hsum z hz.1).sub (hBsum z hz.2.1)` as an intermediate fact. Rewrite `this` using `[hz.2.2, sub_self]`. Simplify `this` using `[d, sub_mul]`. Establish `hzi : C < (Complex.I * (|C| + 1)).im` using `by simp; have := le_abs_self C; linarith`.

Establish `hzp : 0 < (Complex.I * (|C| + 1)).im` using `by simp; positivity`. Use `((hsum _ hzi).summable.sub (hBsum _ hzp).summable)` as an intermediate fact. Simplify `this` using `[d, sub_mul]`. Establish `hdr : ∀ r, ε ((T.exp f).coeff r) = B r` using `fun r => sub_eq_zero.mp (congrFun hd r)`. Use `⟨k, fun n => (T.exp f).coeff (ι n), ?_, fun n => rfl, ?_⟩` and prove the remaining obligations.

Establish `: (fun n => ε ((T.exp f).coeff (ι n))) = A'` using `funext fun n => by rw [hdr, hBι]`. Rewrite using `[this]`. Conclude with `hA'`. Introduce `r hr`. Establish `hr' : r ∉ Set.range ι`.

Introduce and unpack `⟨n, rfl⟩`. Conclude with `hr n rfl`. Use `hdr r` as an intermediate fact. Rewrite `this` using `[hB0 r hr']`. Conclude with `(map_eq_zero_iff ε ε.injective).mp this`.
-/
theorem siegel_exp : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b : ℕ), 0 < M → a < M → admitted c ![(a : ℚ) / M, (b : ℚ) / M] → ∃ (k : ℤ) (A : ℕ → Ω), GlobalTheory.QFam.HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => ε (A n)) ∧ (∀ n : ℕ, (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff (((k : ℚ) + n) / M) = A n) ∧ ∀ r : ℚ, (∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) → (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff r = 0 := by
  intro Ω _ _ _ ε T c M a b hM haM hadm
  classical
  set x : Fin 2 → ℚ := ![(a : ℚ) / M, (b : ℚ) / M] with hx
  obtain ⟨k, hk⟩ := GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral c M a hM haM
  obtain ⟨A', hA', -⟩ := hk b hadm
  have hmem := GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hadm
  set f := siegel T c x with hf
  obtain ⟨φ, C, hφ, hsum⟩ := T.an_exp f
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  let ι : ℕ → ℚ := fun n => ((k : ℚ) + n) / M
  have hι : Function.Injective ι := by
    intro n m h
    simp only [ι] at h
    rw [div_left_inj' hMq, add_right_inj] at h
    exact_mod_cast h
  let B : ℚ → ℂ := fun r => if h : ∃ n, ι n = r then A' h.choose else 0
  have hBι : ∀ n, B (ι n) = A' n := by
    intro n
    have h : ∃ m, ι m = ι n := ⟨n, rfl⟩
    simp only [B, dif_pos h]
    rw [hι h.choose_spec]
  have hB0 : ∀ r, r ∉ Set.range ι → B r = 0 := by
    intro r hr
    simp only [B]
    rw [dif_neg]
    exact hr
  have hBsum : ∀ z : ℂ, 0 < z.im →
      HasSum (fun r : ℚ => B r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (sgC c x z) := by
    intro z hz
    have h2 := (hA' ⟨z, hz⟩).mul_left (ee ((k : ℂ) / M * z))
    rw [← hι.hasSum_iff (fun r hr => by simp [hB0 r hr])]
    have e1 : ((fun r : ℚ => B r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) ∘ ι) = fun n : ℕ =>
        ee ((k : ℂ) / M * z) * (A' n * Complex.exp (2 * Real.pi * Complex.I * n * z / M)) := by
      funext n
      simp only [Function.comp_apply, hBι, ι, ee]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      field_simp
    have e2 : sgC c x z = ee ((k : ℂ) / M * z) * (sg c x ⟨z, hz⟩ * ee (-((k : ℂ) / M) * z)) := by
      simp only [sgC, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      rw [mul_left_comm, ee, ee, ← Complex.exp_add]
      have : 2 * Real.pi * Complex.I * ((k : ℂ) / M * z) + 2 * Real.pi * Complex.I * (-((k : ℂ) / M) * (z : ℂ)) = 0 := by
        ring
      rw [this, Complex.exp_zero, mul_one]
    rw [e1, e2]
    simpa using h2
  have hgerm : φ =ᶠ[Filter.codiscreteWithin Hs] sgC c x := by
    have := hφ.symm.trans hmem
    exact Filter.Germ.coe_eq.mp this
  let S : Set ℂ := {z | C < z.im ∧ 0 < z.im ∧ φ z = sgC c x z}
  have hS : ∀ y : ℝ, ∃ z ∈ S, y < z.im := by
    intro y
    set Y := max (max y C) 0 + 1 with hY
    set w : ℂ := Complex.I * Y
    have hwim : w.im = Y := by simp [w]
    have hw : w ∈ Hs := by
      show 0 < w.im
      rw [hwim]; have := le_max_right (max y C) 0; linarith
    have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hgerm w hw
    have h2 : Metric.ball w (1 / 2) ∈ nhdsWithin w {w}ᶜ :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds w (by norm_num))
    obtain ⟨z, hz1, hz2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
    have hdist : |z.im - Y| < 1 / 2 := by
      have := Complex.abs_im_le_norm (z - w)
      rw [Metric.mem_ball, dist_eq_norm] at hz2
      rw [Complex.sub_im, hwim] at this
      linarith
    have hyY : y ≤ max (max y C) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
    have hCY : C ≤ max (max y C) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
    have h0Y : 0 ≤ max (max y C) 0 := le_max_right _ _
    have hzim : max (max y C) 0 + 1 / 2 < z.im := by
      have := (abs_lt.mp hdist).1; linarith
    have hzH : z ∈ Hs := show 0 < z.im by linarith
    refine ⟨z, ⟨by linarith, by linarith, ?_⟩, by linarith⟩
    rcases hz1 with h | h
    · exact h
    · exact absurd hzH h
  let d : ℚ → ℂ := fun r => ε ((T.exp f).coeff r) - B r
  have hd : d = 0 := by
    refine GlobalTheory.KExp.uniq d ?_ S ?_ (Complex.I * (|C| + 1)) ?_ hS
    · have hR : (Set.range ι).IsWF := by
        have : Set.range ι = ι '' Set.univ := Set.image_univ.symm
        rw [this]
        refine (Set.IsPWO.image_of_monotone (Set.isPWO_of_wellQuasiOrderedLE _) ?_).isWF
        intro n m h
        simp only [ι]
        gcongr
      refine ((T.exp f).isWF_support.union hR).mono ?_
      · intro r hr
        by_contra hn
        simp only [Set.mem_union, not_or] at hn
        apply hr
        simp only [d, hB0 r hn.2]
        have : (T.exp f).coeff r = 0 := by simpa [HahnSeries.support] using hn.1
        simp [this]
    · intro z hz
      have := (hsum z hz.1).sub (hBsum z hz.2.1)
      rw [hz.2.2, sub_self] at this
      simpa [d, sub_mul] using this
    · have hzi : C < (Complex.I * (|C| + 1)).im := by
        simp; have := le_abs_self C; linarith
      have hzp : 0 < (Complex.I * (|C| + 1)).im := by simp; positivity
      have := ((hsum _ hzi).summable.sub (hBsum _ hzp).summable)
      simpa [d, sub_mul] using this
  have hdr : ∀ r, ε ((T.exp f).coeff r) = B r := fun r => sub_eq_zero.mp (congrFun hd r)
  refine ⟨k, fun n => (T.exp f).coeff (ι n), ?_, fun n => rfl, ?_⟩
  · have : (fun n => ε ((T.exp f).coeff (ι n))) = A' := funext fun n => by rw [hdr, hBι]
    rw [this]
    exact hA'
  · intro r hr
    have hr' : r ∉ Set.range ι := by
      rintro ⟨n, rfl⟩
      exact hr n rfl
    have := hdr r
    rw [hB0 r hr'] at this
    exact (map_eq_zero_iff ε ε.injective).mp this

end GlobalTheory.KExp
