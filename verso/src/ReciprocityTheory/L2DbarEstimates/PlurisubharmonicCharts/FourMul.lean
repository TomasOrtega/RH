import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSum

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

def FOURMulStatement (f : ℕ) : Prop :=
  ∀ (Ω : Set (Fin f → ℝ)) (h1 h2 : (Fin f → ℂ) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ h1 (tube f Ω) → DifferentiableOn ℂ h2 (tube f Ω) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h1 (s + fun k => (m k : ℂ)) = h1 s) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h2 (s + fun k => (m k : ℂ)) = h2 s) →
    ∀ b ∈ Ω,
    Summable (fun ν : Fin f → ℤ => ‖fourCoeff h1 b ν‖) →
    Summable (fun ν : Fin f → ℤ => ‖fourCoeff h2 b ν‖) →
    ∀ ν : Fin f → ℤ,
      fourCoeff (h1 * h2) b ν = ∑' ν' : Fin f → ℤ, fourCoeff h1 b ν' * fourCoeff h2 b (ν - ν')

def FOURMulStatement' (f : ℕ) : Prop :=
  ∀ (Ω : Set (Fin f → ℝ)) (h1 h2 : (Fin f → ℂ) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ h1 (tube f Ω) → DifferentiableOn ℂ h2 (tube f Ω) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h1 (s + fun k => (m k : ℂ)) = h1 s) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h2 (s + fun k => (m k : ℂ)) = h2 s) →
    ∀ b ∈ Ω, ∀ ν : Fin f → ℤ,
      HasSum (fun ν' : Fin f → ℤ => fourCoeff h1 b ν' * fourCoeff h2 b (ν - ν'))
        (fourCoeff (h1 * h2) b ν)

def FOURMulSuppStatement (f : ℕ) : Prop :=
  ∀ (Ω : Set (Fin f → ℝ)) (h1 h2 : (Fin f → ℂ) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ h1 (tube f Ω) → DifferentiableOn ℂ h2 (tube f Ω) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h1 (s + fun k => (m k : ℂ)) = h1 s) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h2 (s + fun k => (m k : ℂ)) = h2 s) →
    ∀ b ∈ Ω, ∀ ν : Fin f → ℤ, fourCoeff (h1 * h2) b ν ≠ 0 →
      ∃ ν1 ν2, ν1 + ν2 = ν ∧ fourCoeff h1 b ν1 ≠ 0 ∧ fourCoeff h2 b ν2 ≠ 0

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def fmLine {f : ℕ} (h : (Fin f → ℂ) → ℂ) (b : Fin f → ℝ) : (Fin f → ℝ) → ℂ :=
  fun x => h (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I)

/- English proof (translation)
Simplify using `only [UnitAddTorus.mFourierCoeff, ContinuousMap.star_apply, smul_eq_mul, neg_neg]`. Rewrite using `[← integral_conj]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Simplify using `[UnitAddTorus.mFourier_neg]`.
-/
theorem fm_coeff_star {f : ℕ} (F : C(UnitAddTorus (Fin f), ℂ)) (i : Fin f → ℤ) :
    conj (UnitAddTorus.mFourierCoeff (⇑(star F)) i) = UnitAddTorus.mFourierCoeff (⇑F) (-i) := by
  simp only [UnitAddTorus.mFourierCoeff, ContinuousMap.star_apply, smul_eq_mul, neg_neg]
  rw [← integral_conj]
  congr 1
  funext t
  simp [UnitAddTorus.mFourier_neg]

/- English proof (translation)
Simplify using `only [UnitAddTorus.mFourierCoeff, ContinuousMap.mul_apply, smul_eq_mul]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Rewrite using `[neg_add, UnitAddTorus.mFourier_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fm_coeff_shift {f : ℕ} (F : C(UnitAddTorus (Fin f), ℂ)) (ν i : Fin f → ℤ) :
    UnitAddTorus.mFourierCoeff (⇑(UnitAddTorus.mFourier (-ν) * F)) i =
      UnitAddTorus.mFourierCoeff (⇑F) (i + ν) := by
  simp only [UnitAddTorus.mFourierCoeff, ContinuousMap.mul_apply, smul_eq_mul]
  congr 1
  funext t
  rw [neg_add, UnitAddTorus.mFourier_add]
  ring

/- English proof (translation)
Establish `H` using `UnitAddTorus.hasSum_prod_mFourierCoeff ((star F1).toLp 2 volume ℂ) ((UnitAddTorus.mFourier (-ν) * F2).toLp 2 volume ℂ)`. Establish `H2 : HasSum (fun i => UnitAddTorus.mFourierCoeff (⇑F1) (-i) * UnitAddTorus.mFourierCoeff (⇑F2) (i + ν)) (UnitAddTorus.mFourierCoeff (⇑F1 * ⇑F2) ν)`. Use `H using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Rewrite using `[UnitAddTorus.mFourierCoeff_toLp, UnitAddTorus.mFourierCoeff_toLp, fm_coeff_star, fm_coeff_shift]`.

Rewrite using `[UnitAddTorus.mFourierCoeff]`. Apply `integral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) (star F1), ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) (UnitAddTorus.mFourier (-ν) * F2)] with t h1 h2`. Rewrite using `[h1, h2]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← (Equiv.neg (Fin f → ℤ)).hasSum_iff]`. Use `H2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[sub_neg_eq_add, add_comm]`.
-/
theorem fm_conv {f : ℕ} (F1 F2 : C(UnitAddTorus (Fin f), ℂ)) (ν : Fin f → ℤ) :
    HasSum (fun ν' => UnitAddTorus.mFourierCoeff (⇑F1) ν' * UnitAddTorus.mFourierCoeff (⇑F2) (ν - ν'))
      (UnitAddTorus.mFourierCoeff (⇑F1 * ⇑F2) ν) := by
  have H := UnitAddTorus.hasSum_prod_mFourierCoeff ((star F1).toLp 2 volume ℂ)
    ((UnitAddTorus.mFourier (-ν) * F2).toLp 2 volume ℂ)
  have H2 : HasSum (fun i => UnitAddTorus.mFourierCoeff (⇑F1) (-i) *
      UnitAddTorus.mFourierCoeff (⇑F2) (i + ν)) (UnitAddTorus.mFourierCoeff (⇑F1 * ⇑F2) ν) := by
    convert H using 1
    · funext i
      rw [UnitAddTorus.mFourierCoeff_toLp, UnitAddTorus.mFourierCoeff_toLp, fm_coeff_star,
        fm_coeff_shift]
    · rw [UnitAddTorus.mFourierCoeff]
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) (star F1),
        ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
          (UnitAddTorus.mFourier (-ν) * F2)] with t h1 h2
      rw [h1, h2]
      simp
      ring
  rw [← (Equiv.neg (Fin f → ℤ)).hasSum_iff]
  convert H2 using 1
  funext i
  simp [sub_neg_eq_add, add_comm]

/- English proof (translation)
Rewrite using `[UnitAddTorus.mFourierCoeff_eq_integral _ ν 0, fourCoeff]`. Establish `hset : ({x : Fin f → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin f → ℝ) i) ((0 : Fin f → ℝ) i + 1)} : Set (Fin f → ℝ)) = Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1)`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[hset, ← integral_const_mul]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Establish `h1 : (fun i => ((t i : ℝ) : UnitAddCircle)) = fsProj f t` using `rfl`. Use `beta_reduce`. Rewrite using `[h1, fsFun_proj _ hper, smul_eq_mul, fs_mFourier_proj]`. Simplify using `only [fmLine]`.

Rewrite using `[mul_comm, ← mul_assoc, ← Complex.exp_add]`. Use `congr 2`. Simplify using `only [Pi.neg_apply, Int.cast_neg, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Take the linear combination `(-2 * (Real.pi : ℂ) * (ν k : ℂ) * (b k : ℂ)) * Complex.I_sq`.
-/
theorem fm_fourCoeff {f : ℕ} (h : (Fin f → ℂ) → ℂ) (b : Fin f → ℝ)
    (hper : ∀ x (n : Fin f → ℤ), fmLine h b (x + fun i => (n i : ℝ)) = fmLine h b x)
    (ν : Fin f → ℤ) :
    fourCoeff h b ν = Complex.exp (2 * Real.pi * ∑ k, (ν k : ℂ) * (b k : ℂ)) *
      UnitAddTorus.mFourierCoeff (fsFun (fmLine h b)) ν := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ ν 0, fourCoeff]
  have hset : ({x : Fin f → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin f → ℝ) i) ((0 : Fin f → ℝ) i + 1)}
      : Set (Fin f → ℝ)) = Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1) := by
    ext x; simp
  rw [hset, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have h1 : (fun i => ((t i : ℝ) : UnitAddCircle)) = fsProj f t := rfl
  beta_reduce
  rw [h1, fsFun_proj _ hper, smul_eq_mul, fs_mFourier_proj]
  simp only [fmLine]
  rw [mul_comm, ← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [Pi.neg_apply, Int.cast_neg, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  linear_combination (-2 * (Real.pi : ℂ) * (ν k : ℂ) * (b k : ℂ)) * Complex.I_sq

/- English proof (translation)
Introduce `Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb ν`. Establish `hopen : IsOpen (tube f Ω)` using `hΩ.preimage (by fun_prop)`. Establish `hmem : ∀ x : Fin f → ℝ, (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I) ∈ tube f Ω`. Introduce `x`. Use `show (fun k => ((x k : ℂ) + (b k : ℂ) * Complex.I).im) ∈ Ω`.

Use `hb using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Establish `hc : ∀ hh : (Fin f → ℂ) → ℂ, DifferentiableOn ℂ hh (tube f Ω) → Continuous (fmLine hh b)`. Introduce `hh hd`.

Establish `hcc : Continuous (fun y : Fin f → ℝ => (fun k => (y k : ℂ) + (b k : ℂ) * Complex.I))` using `by fun_prop`. Use `continuous_iff_continuousAt.2 fun y => ?_` and prove the remaining obligations. Conclude with `((hd _ (hmem y)).differentiableAt (hopen.mem_nhds (hmem y))).continuousAt.comp hcc.continuousAt`. Establish `hper : ∀ hh : (Fin f → ℂ) → ℂ, (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, hh (s + fun k => (m k : ℂ)) = hh s) → ∀ x (n : Fin f → ℤ), fmLine hh b (x + fun i => (n i : ℝ)) = fmLine hh b x`. Introduce `hh hp x n`.

Use `hp _ (hmem x) n` as an intermediate fact. Simplify using `only [fmLine]`. Use `this using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hper12 : ∀ x (n : Fin f → ℤ), fmLine (h1 * h2) b (x + fun i => (n i : ℝ)) = fmLine (h1 * h2) b x`. Introduce `x n`. Use `show fmLine h1 b _ * fmLine h2 b _ = fmLine h1 b x * fmLine h2 b x`.

Rewrite using `[hper h1 hp1, hper h2 hp2]`. Set `F1 : C(UnitAddTorus (Fin f), ℂ)` to `⟨fsFun (fmLine h1 b), fsFun_continuous _ (hc h1 hd1) (hper h1 hp1)⟩`. Set `F2 : C(UnitAddTorus (Fin f), ℂ)` to `⟨fsFun (fmLine h2 b), fsFun_continuous _ (hc h2 hd2) (hper h2 hp2)⟩`. Establish `e12 : fsFun (fmLine (h1 * h2) b) = ⇑F1 * ⇑F2` using `rfl`. Rewrite using `[fm_fourCoeff (h1 * h2) b hper12, e12]`.

Establish `H` using `(fm_conv F1 F2 ν).mul_left (Complex.exp (2 * Real.pi * ∑ k, (ν k : ℂ) * (b k : ℂ)))`. Use `H.congr_fun fun ν' => ?_` and prove the remaining obligations. Rewrite using `[fm_fourCoeff h1 b (hper h1 hp1), fm_fourCoeff h2 b (hper h2 hp2)]`. Establish `hE : Complex.exp (2 * Real.pi * ∑ k, (ν k : ℂ) * (b k : ℂ)) = Complex.exp (2 * Real.pi * ∑ k, (ν' k : ℂ) * (b k : ℂ)) * Complex.exp (2 * Real.pi * ∑ k, ((ν - ν') k : ℂ) * (b k : ℂ))`. Rewrite using `[← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]`.

Use `congr 3`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.sub_apply, Int.cast_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hE]`.

Simplify using `only [F1, F2, ContinuousMap.coe_mk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem four_mul' (f : ℕ) : FOURMulStatement' f := by
  intro Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb ν
  have hopen : IsOpen (tube f Ω) := hΩ.preimage (by fun_prop)
  have hmem : ∀ x : Fin f → ℝ, (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I) ∈ tube f Ω := by
    intro x
    show (fun k => ((x k : ℂ) + (b k : ℂ) * Complex.I).im) ∈ Ω
    convert hb using 1
    funext k
    simp
  have hc : ∀ hh : (Fin f → ℂ) → ℂ, DifferentiableOn ℂ hh (tube f Ω) →
      Continuous (fmLine hh b) := by
    intro hh hd
    have hcc : Continuous (fun y : Fin f → ℝ => (fun k => (y k : ℂ) + (b k : ℂ) * Complex.I)) := by
      fun_prop
    refine continuous_iff_continuousAt.2 fun y => ?_
    exact ((hd _ (hmem y)).differentiableAt (hopen.mem_nhds (hmem y))).continuousAt.comp
      hcc.continuousAt
  have hper : ∀ hh : (Fin f → ℂ) → ℂ,
      (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, hh (s + fun k => (m k : ℂ)) = hh s) →
      ∀ x (n : Fin f → ℤ), fmLine hh b (x + fun i => (n i : ℝ)) = fmLine hh b x := by
    intro hh hp x n
    have := hp _ (hmem x) n
    simp only [fmLine]
    convert this using 2
    funext k
    simp only [Pi.add_apply]
    push_cast
    ring
  have hper12 : ∀ x (n : Fin f → ℤ),
      fmLine (h1 * h2) b (x + fun i => (n i : ℝ)) = fmLine (h1 * h2) b x := by
    intro x n
    show fmLine h1 b _ * fmLine h2 b _ = fmLine h1 b x * fmLine h2 b x
    rw [hper h1 hp1, hper h2 hp2]
  let F1 : C(UnitAddTorus (Fin f), ℂ) :=
    ⟨fsFun (fmLine h1 b), fsFun_continuous _ (hc h1 hd1) (hper h1 hp1)⟩
  let F2 : C(UnitAddTorus (Fin f), ℂ) :=
    ⟨fsFun (fmLine h2 b), fsFun_continuous _ (hc h2 hd2) (hper h2 hp2)⟩
  have e12 : fsFun (fmLine (h1 * h2) b) = ⇑F1 * ⇑F2 := rfl
  rw [fm_fourCoeff (h1 * h2) b hper12, e12]
  have H := (fm_conv F1 F2 ν).mul_left (Complex.exp (2 * Real.pi * ∑ k, (ν k : ℂ) * (b k : ℂ)))
  refine H.congr_fun fun ν' => ?_
  rw [fm_fourCoeff h1 b (hper h1 hp1), fm_fourCoeff h2 b (hper h2 hp2)]
  have hE : Complex.exp (2 * Real.pi * ∑ k, (ν k : ℂ) * (b k : ℂ)) =
      Complex.exp (2 * Real.pi * ∑ k, (ν' k : ℂ) * (b k : ℂ)) *
        Complex.exp (2 * Real.pi * ∑ k, ((ν - ν') k : ℂ) * (b k : ℂ)) := by
    rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
    congr 3
    funext k
    simp only [Pi.sub_apply, Int.cast_sub]
    ring
  rw [hE]
  simp only [F1, F2, ContinuousMap.coe_mk]
  ring

/- English proof (translation)
Introduce `Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb _ _ ν`. Conclude with `(four_mul' f Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb ν).tsum_eq.symm`.
-/
theorem four_mul (f : ℕ) : FOURMulStatement f := by
  intro Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb _ _ ν
  exact (four_mul' f Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb ν).tsum_eq.symm

/- English proof (translation)
Introduce `Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb ν hne`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Establish `H` using `four_mul' f Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb ν`. Establish `hz : ∀ ν' : Fin f → ℤ, fourCoeff h1 b ν' * fourCoeff h2 b (ν - ν') = 0`.

Introduce `ν'`. Distinguish the cases in `h0 : fourCoeff h1 b ν' = 0`. Rewrite using `[h0, zero_mul]`. Rewrite using `[hno ν' (ν - ν') (by abel) h0, mul_zero]`. Establish `H0 : HasSum (fun ν' : Fin f → ℤ => fourCoeff h1 b ν' * fourCoeff h2 b (ν - ν')) 0`.

Simplify using `[hz]`. Conclude with `hne (H.unique H0)`.
-/
theorem four_mul_supp (f : ℕ) : FOURMulSuppStatement f := by
  intro Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb ν hne
  by_contra hno
  push Not at hno
  have H := four_mul' f Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb ν
  have hz : ∀ ν' : Fin f → ℤ, fourCoeff h1 b ν' * fourCoeff h2 b (ν - ν') = 0 := by
    intro ν'
    by_cases h0 : fourCoeff h1 b ν' = 0
    · rw [h0, zero_mul]
    · rw [hno ν' (ν - ν') (by abel) h0, mul_zero]
  have H0 : HasSum (fun ν' : Fin f → ℤ => fourCoeff h1 b ν' * fourCoeff h2 b (ν - ν')) 0 := by
    simp [hz]
  exact hne (H.unique H0)

end

end ReciprocityTheory.L2DbarEstimates.Y
