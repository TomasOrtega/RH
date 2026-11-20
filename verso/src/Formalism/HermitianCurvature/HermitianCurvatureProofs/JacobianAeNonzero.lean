import Formalism.HermitianCurvature.HermitianCurvatureProofs.LinearChangeOfVariablesBis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FourthWeightDensityOfParts

open Matrix Formalism.FourierDecayAlt MeasureTheory
open scoped ENNReal

namespace Formalism.FourierDecayAlt.P

namespace RootChangeOfVariables

/- English proof (translation)
Establish `e : ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ : ℂ →L[ℝ] ℂ).toLinearMap = (LinearMap.mulLeft ℂ c).restrictScalars ℝ`. Use extensionality with `x`. Simplify using `[mul_comm]`. Rewrite using `[ContinuousLinearMap.det, e, LinearMap.det_restrictScalars, LinearMap.det_mulLeft, Algebra.norm_complex_apply]`.
-/
lemma jac (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ : ℂ →L[ℝ] ℂ).det = Complex.normSq c := by
  have e : ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ : ℂ →L[ℝ] ℂ).toLinearMap =
      (LinearMap.mulLeft ℂ c).restrictScalars ℝ := by
    ext x; simp [mul_comm]
  rw [ContinuousLinearMap.det, e, LinearMap.det_restrictScalars, LinearMap.det_mulLeft,
    Algebra.norm_complex_apply]

/- English proof (translation)
Rewrite using `[ae_iff]`. Establish `: {a : ℂ | ¬ a ∈ {D : ℂ | D ≠ 0}} = {0}` using `by ext a; simp`. Rewrite using `[this, measure_singleton]`.
-/
lemma ae_ne_zero : ∀ᵐ D : ℂ, D ∈ {D : ℂ | D ≠ 0} := by
  rw [ae_iff]
  have : {a : ℂ | ¬ a ∈ {D : ℂ | D ≠ 0}} = {0} := by ext a; simp
  rw [this, measure_singleton]

end RootChangeOfVariables

open RootChangeOfVariables

/- English proof (translation)
Introduce `s φ hs hφ`. Establish `hs0 : s ≠ 0` using `by omega`. Use `haveI : NeZero s := ⟨hs0⟩`. Take `⟨ρ, hρ⟩ : ∃ ρ : ℂ → ℂ, ρ = fun D => D ^ ((s : ℂ)⁻¹)` from `⟨_, rfl⟩`. Establish `hρn : ∀ D, ρ D ^ s = D` using `fun D => by rw [hρ]; exact Complex.cpow_nat_inv_pow D hs0`.

Establish `hρm : Measurable ρ` using `by rw [hρ]; exact measurable_id.pow_const _`. Use `set S : Set ℂ := {z | z ^ s ≠ 0 ∧ ρ (z ^ s) = z} with hS`. Establish `hSm : MeasurableSet S`. Apply `MeasurableSet.inter` to reduce the goal to its premises. Conclude with `(measurableSet_singleton (0 : ℂ)).compl.preimage (measurable_id.pow_const s)`.

Conclude with `measurableSet_eq_fun (hρm.comp (measurable_id.pow_const s)) measurable_id`. Establish `hS0 : ∀ z ∈ S, z ≠ 0` using `fun z hz e => hz.1 (by rw [e]; exact zero_pow hs0)`. Take `⟨wt, hwt⟩ : ∃ wt : ℂ → ℝ≥0∞, wt = fun z => ENNReal.ofReal (((s : ℕ) : ℝ) ^ 2 * ‖z‖ ^ (2 * (s - 1)))` from `⟨_, rfl⟩`. Establish `hwtm : Measurable wt`. Rewrite using `[hwt]`.

Conclude with `Measurable.ennreal_ofReal (measurable_const.mul ((continuous_norm.pow _).measurable))`. Establish `hL : ∀ ψ : ℂ → ℝ≥0∞, ∫⁻ D, ψ (ρ D) = ∫⁻ z in S, wt z * ψ z`. Introduce `ψ`. Establish `himg : (fun z : ℂ => z ^ s) '' S = {D : ℂ | D ≠ 0}`. Use extensionality with `D`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `hz.1`. Introduce `hD`. Use `⟨ρ D, ⟨?_, ?_⟩, hρn D⟩` and prove the remaining obligations.

Rewrite using `[hρn]`. Conclude with `hD`. Rewrite using `[hρn]`. Establish `hinj : Set.InjOn (fun z : ℂ => z ^ s) S`. Introduce `z1 h1 z2 h2 e`.

Rewrite using `[← h1.2, ← h2.2]`. Simplify using `only at e`. Rewrite using `[e]`. Establish `hder : ∀ z ∈ S, HasFDerivWithinAt (fun z : ℂ => z ^ s) ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ((s : ℂ) * z ^ (s - 1))).restrictScalars ℝ) S z` using `fun z _ => ((hasDerivAt_pow s z).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt`. Establish `step1 : ∫⁻ D, ψ (ρ D) = ∫⁻ D in {D : ℂ | D ≠ 0}, ψ (ρ D)`.

Rewrite using `[Measure.restrict_eq_self_of_ae_mem ae_ne_zero]`. Rewrite using `[step1, ← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm hder hinj]`. Apply `setLIntegral_congr_fun hSm` to reduce the goal to its premises. Introduce `z hz`. Simplify using `only`.

Rewrite using `[jac, hz.2, hwt]`. Use `congr 2`. Rewrite using `[abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_mul, map_pow, Complex.normSq_natCast, Complex.normSq_eq_norm_sq, ← pow_mul, sq]`. Use `set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / s) with hζ`. Establish `hprim : IsPrimitiveRoot ζ s` using `Complex.isPrimitiveRoot_exp s hs0`.

Establish `hζn : ∀ j, ‖ζ ^ j‖ = 1` using `fun j => by rw [norm_pow, hprim.norm'_eq_one hs0, one_pow]`. Establish `hζ0 : ∀ j, ζ ^ j ≠ 0` using `fun j h => by have := hζn j; rw [h, norm_zero] at this; exact zero_ne_one this`. Establish `hrot : ∀ (j : ℕ) (G : ℂ → ℝ≥0∞), ∫⁻ z in S, G (ζ ^ j * z) = ∫⁻ y in (fun z => ζ ^ j * z) '' S, G y`. Introduce `j G`. Establish `hder : ∀ z ∈ S, HasFDerivWithinAt (fun z : ℂ => ζ ^ j * z) ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (ζ ^ j * 1)).restrictScalars ℝ) S z` using `fun z _ => (((hasDerivAt_id z).const_mul (ζ ^ j)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt`.

Establish `hinj : Set.InjOn (fun z : ℂ => ζ ^ j * z) S` using `fun z1 _ z2 _ e => mul_left_cancel₀ (hζ0 j) e`. Rewrite using `[lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm hder hinj]`. Apply `setLIntegral_congr_fun hSm` to reduce the goal to its premises. Introduce `z _`. Simplify using `only`.

Rewrite using `[jac, mul_one, Complex.normSq_eq_norm_sq, hζn, one_pow, abs_one, ENNReal.ofReal_one, one_mul]`. Establish `hroots : ∀ D, ((Polynomial.nthRoots s D).map φ).sum = ∑ j ∈ Finset.range s, φ (ζ ^ j * ρ D)`. Introduce `D`. Rewrite using `[hprim.nthRoots_eq (hρn D), Multiset.map_map]`. Both sides reduce to the same expression.

Simplify using `only [hroots]`. Establish `hmeas : ∀ j ∈ Finset.range s, Measurable (fun D => φ (ζ ^ j * ρ D))` using `fun j _ => hφ.comp (measurable_const.mul hρm)`. Rewrite using `[lintegral_finset_sum _ hmeas]`. Establish `hterm : ∀ j ∈ Finset.range s, ∫⁻ D, φ (ζ ^ j * ρ D) = ∫⁻ y in (fun z => ζ ^ j * z) '' S, wt y * φ y`. Introduce `j _`.

Rewrite using `[hL (fun z => φ (ζ ^ j * z)), ← hrot j (fun y => wt y * φ y)]`. Apply `setLIntegral_congr_fun hSm` to reduce the goal to its premises. Introduce `z _`. Simplify using `only [hwt, norm_mul, hζn, one_mul]`. Rewrite using `[Finset.sum_congr rfl hterm]`.

Establish `hTm : ∀ j, MeasurableSet ((fun z => ζ ^ j * z) '' S)` using `fun j => (MeasurableEquiv.mulLeft₀ (ζ ^ j) (hζ0 j)).measurableSet_image.mpr hSm`. Establish `hdisj : Set.PairwiseDisjoint (↑(Finset.range s)) (fun j => (fun z => ζ ^ j * z) '' S)`. Introduce `j hj j' hj' hne`. Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce and unpack `y ⟨z, hz, rfl⟩ ⟨z', hz', e⟩`.

Establish `h1 : ∀ i : ℕ, (ζ ^ i) ^ s = 1` using `fun i => by`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]`. Establish `hpow : z' ^ s = z ^ s`. Use `congrArg (fun t => t ^ s) e` as an intermediate fact. Simplify using `only [mul_pow, h1, one_mul] at this`.

Conclude with `this`. Establish `hzz : z' = z` using `by rw [← hz'.2, ← hz.2, hpow]`. Rewrite `e` using `[hzz]`. Use `mul_right_cancel₀ (hS0 z hz) e` as an intermediate fact. Conclude with `hne (hprim.pow_inj (Finset.mem_range.mp hj') (Finset.mem_range.mp hj) this).symm`.

Rewrite using `[← lintegral_biUnion_finset hdisj (fun j _ => hTm j)]`. Establish `hunion : (⋃ j ∈ Finset.range s, (fun z => ζ ^ j * z) '' S) = {y : ℂ | y ≠ 0}`. Use extensionality with `y`. Simplify using `only [Set.mem_iUnion, Set.mem_image, Finset.mem_range, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨j, _, z, hz, rfl⟩`. Conclude with `mul_ne_zero (hζ0 j) (hS0 z hz)`. Introduce `hy set z0 := ρ (y ^ s) with hz0`. Establish `hz0n : z0 ^ s = y ^ s` using `hρn _`. Establish `hz0S : z0 ∈ S` using `⟨by rw [hz0n]; exact pow_ne_zero s hy, by rw [hz0n]⟩`.

Establish `hz00` using `hS0 z0 hz0S`. Establish `h1 : (y / z0) ^ s = 1` using `by rw [div_pow, hz0n, div_self (pow_ne_zero s hy)]`. Take `⟨j, hj, hjeq⟩` from `hprim.eq_pow_of_pow_eq_one h1`. Conclude with `⟨j, hj, z0, hz0S, by rw [hjeq]; field_simp⟩`. Rewrite using `[hunion, Measure.restrict_eq_self_of_ae_mem ae_ne_zero, hwt]`.
-/
theorem rootCOV_statement : C2.RootCOV := by
  intro s φ hs hφ
  have hs0 : s ≠ 0 := by omega
  haveI : NeZero s := ⟨hs0⟩

  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℂ → ℂ, ρ = fun D => D ^ ((s : ℂ)⁻¹) := ⟨_, rfl⟩
  have hρn : ∀ D, ρ D ^ s = D := fun D => by rw [hρ]; exact Complex.cpow_nat_inv_pow D hs0
  have hρm : Measurable ρ := by rw [hρ]; exact measurable_id.pow_const _
  set S : Set ℂ := {z | z ^ s ≠ 0 ∧ ρ (z ^ s) = z} with hS
  have hSm : MeasurableSet S := by
    apply MeasurableSet.inter
    · exact (measurableSet_singleton (0 : ℂ)).compl.preimage (measurable_id.pow_const s)
    · exact measurableSet_eq_fun (hρm.comp (measurable_id.pow_const s)) measurable_id
  have hS0 : ∀ z ∈ S, z ≠ 0 := fun z hz e => hz.1 (by rw [e]; exact zero_pow hs0)

  obtain ⟨wt, hwt⟩ : ∃ wt : ℂ → ℝ≥0∞, wt = fun z => ENNReal.ofReal (((s : ℕ) : ℝ) ^ 2 * ‖z‖ ^ (2 * (s - 1))) :=
    ⟨_, rfl⟩
  have hwtm : Measurable wt := by
    rw [hwt]; exact Measurable.ennreal_ofReal (measurable_const.mul ((continuous_norm.pow _).measurable))

  have hL : ∀ ψ : ℂ → ℝ≥0∞, ∫⁻ D, ψ (ρ D) = ∫⁻ z in S, wt z * ψ z := by
    intro ψ
    have himg : (fun z : ℂ => z ^ s) '' S = {D : ℂ | D ≠ 0} := by
      ext D; constructor
      · rintro ⟨z, hz, rfl⟩; exact hz.1
      · intro hD
        refine ⟨ρ D, ⟨?_, ?_⟩, hρn D⟩
        · rw [hρn]; exact hD
        · rw [hρn]
    have hinj : Set.InjOn (fun z : ℂ => z ^ s) S := by
      intro z1 h1 z2 h2 e
      rw [← h1.2, ← h2.2]; simp only at e; rw [e]
    have hder : ∀ z ∈ S, HasFDerivWithinAt (fun z : ℂ => z ^ s)
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ((s : ℂ) * z ^ (s - 1))).restrictScalars ℝ) S z :=
      fun z _ => ((hasDerivAt_pow s z).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    have step1 : ∫⁻ D, ψ (ρ D) = ∫⁻ D in {D : ℂ | D ≠ 0}, ψ (ρ D) := by
      rw [Measure.restrict_eq_self_of_ae_mem ae_ne_zero]
    rw [step1, ← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm hder hinj]
    apply setLIntegral_congr_fun hSm
    intro z hz
    dsimp only
    rw [jac, hz.2, hwt]
    congr 2
    rw [abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_mul, map_pow, Complex.normSq_natCast,
      Complex.normSq_eq_norm_sq, ← pow_mul, sq]

  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / s) with hζ
  have hprim : IsPrimitiveRoot ζ s := Complex.isPrimitiveRoot_exp s hs0
  have hζn : ∀ j, ‖ζ ^ j‖ = 1 := fun j => by rw [norm_pow, hprim.norm'_eq_one hs0, one_pow]
  have hζ0 : ∀ j, ζ ^ j ≠ 0 := fun j h => by have := hζn j; rw [h, norm_zero] at this; exact zero_ne_one this
  have hrot : ∀ (j : ℕ) (G : ℂ → ℝ≥0∞), ∫⁻ z in S, G (ζ ^ j * z) = ∫⁻ y in (fun z => ζ ^ j * z) '' S, G y := by
    intro j G
    have hder : ∀ z ∈ S, HasFDerivWithinAt (fun z : ℂ => ζ ^ j * z)
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (ζ ^ j * 1)).restrictScalars ℝ) S z :=
      fun z _ => (((hasDerivAt_id z).const_mul (ζ ^ j)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    have hinj : Set.InjOn (fun z : ℂ => ζ ^ j * z) S := fun z1 _ z2 _ e => mul_left_cancel₀ (hζ0 j) e
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm hder hinj]
    apply setLIntegral_congr_fun hSm
    intro z _
    dsimp only
    rw [jac, mul_one, Complex.normSq_eq_norm_sq, hζn, one_pow, abs_one, ENNReal.ofReal_one, one_mul]

  have hroots : ∀ D, ((Polynomial.nthRoots s D).map φ).sum = ∑ j ∈ Finset.range s, φ (ζ ^ j * ρ D) := by
    intro D
    rw [hprim.nthRoots_eq (hρn D), Multiset.map_map]
    rfl
  simp only [hroots]
  have hmeas : ∀ j ∈ Finset.range s, Measurable (fun D => φ (ζ ^ j * ρ D)) :=
    fun j _ => hφ.comp (measurable_const.mul hρm)
  rw [lintegral_finset_sum _ hmeas]
  have hterm : ∀ j ∈ Finset.range s, ∫⁻ D, φ (ζ ^ j * ρ D) =
      ∫⁻ y in (fun z => ζ ^ j * z) '' S, wt y * φ y := by
    intro j _
    rw [hL (fun z => φ (ζ ^ j * z)), ← hrot j (fun y => wt y * φ y)]
    apply setLIntegral_congr_fun hSm
    intro z _
    simp only [hwt, norm_mul, hζn, one_mul]
  rw [Finset.sum_congr rfl hterm]
  have hTm : ∀ j, MeasurableSet ((fun z => ζ ^ j * z) '' S) := fun j =>
    (MeasurableEquiv.mulLeft₀ (ζ ^ j) (hζ0 j)).measurableSet_image.mpr hSm
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range s)) (fun j => (fun z => ζ ^ j * z) '' S) := by
    intro j hj j' hj' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨z, hz, rfl⟩ ⟨z', hz', e⟩
    have h1 : ∀ i : ℕ, (ζ ^ i) ^ s = 1 := fun i => by
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    have hpow : z' ^ s = z ^ s := by
      have := congrArg (fun t => t ^ s) e
      simp only [mul_pow, h1, one_mul] at this
      exact this
    have hzz : z' = z := by rw [← hz'.2, ← hz.2, hpow]
    rw [hzz] at e
    have := mul_right_cancel₀ (hS0 z hz) e
    exact hne (hprim.pow_inj (Finset.mem_range.mp hj') (Finset.mem_range.mp hj) this).symm
  rw [← lintegral_biUnion_finset hdisj (fun j _ => hTm j)]
  have hunion : (⋃ j ∈ Finset.range s, (fun z => ζ ^ j * z) '' S) = {y : ℂ | y ≠ 0} := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨j, _, z, hz, rfl⟩
      exact mul_ne_zero (hζ0 j) (hS0 z hz)
    · intro hy
      set z0 := ρ (y ^ s) with hz0
      have hz0n : z0 ^ s = y ^ s := hρn _
      have hz0S : z0 ∈ S := ⟨by rw [hz0n]; exact pow_ne_zero s hy, by rw [hz0n]⟩
      have hz00 := hS0 z0 hz0S
      have h1 : (y / z0) ^ s = 1 := by rw [div_pow, hz0n, div_self (pow_ne_zero s hy)]
      obtain ⟨j, hj, hjeq⟩ := hprim.eq_pow_of_pow_eq_one h1
      exact ⟨j, hj, z0, hz0S, by rw [hjeq]; field_simp⟩
  rw [hunion, Measure.restrict_eq_self_of_ae_mem ae_ne_zero, hwt]

/- English proof (translation)
The claim follows from `fourth_weight_density_of_parts rootCOV_statement linear_change_of_variables_bis`.
-/
theorem slice_density_independent : C2.SliceDensityIndependent := fourth_weight_density_of_parts rootCOV_statement linear_change_of_variables_bis

end Formalism.FourierDecayAlt.P
