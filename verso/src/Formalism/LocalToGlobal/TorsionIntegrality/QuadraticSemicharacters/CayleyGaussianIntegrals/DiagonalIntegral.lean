import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.KerPNonzero
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ExtensionActionPermutesPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GaloisDescentSubspaces
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ExtensionFiltrationStable

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Formalism.L2.Th1.H

/- English proof (translation)
Establish `hlin : Continuous fun z => H z v`. Set `f : V →ₗ[ℂ] ℂ` to `{ toFun := fun z => H z v map_add' := fun a b => by simp map_smul' := fun c a => by simp }`. Conclude with `f.continuous_of_finiteDimensional`. Establish `hfun : (fun z => altE H v z) = fun z => -(H z v).im`. Use function extensionality and compare the values at `z`.

Unfold `altE`. Rewrite using `[hH z v, Complex.conj_im]`. Rewrite using `[hfun]`. Conclude with `(Complex.continuous_im.comp hlin).neg`.
-/
theorem continuous_altE {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V)
    (hH : IsHerm H) (v : V) : Continuous fun z => altE H v z := by
  have hlin : Continuous fun z => H z v := by
    let f : V →ₗ[ℂ] ℂ :=
      { toFun := fun z => H z v
        map_add' := fun a b => by simp
        map_smul' := fun c a => by simp }
    exact f.continuous_of_finiteDimensional
  have hfun : (fun z => altE H v z) = fun z => -(H z v).im := by
    funext z
    unfold altE
    rw [hH z v, Complex.conj_im]
  rw [hfun]
  exact (Complex.continuous_im.comp hlin).neg

def diagCoef {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (y x : V) : ℂ :=
  α y * α x * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H y x : ℂ)) *
    Complex.exp (-(Real.pi : ℂ) * H (y + x) (y + x) / 2)

/- English proof (translation)
Rewrite using `[wt_eq_cexp H hH z]`. Simplify using `only [opU, kerP, kerK]`. Rewrite using `[← tsum_mul_right, ← tsum_mul_left, ← tsum_mul_right]`. Use `tsum_congr (fun x => ?_)` and prove the remaining obligations. Unfold `diagCoef`.

Establish `hP : (Real.pi : ℂ) * H (z + y + (x : V)) z + (-(Real.pi : ℂ) * H (z + y) (x : V) - Real.pi * H (x : V) (x : V) / 2) + (-(Real.pi : ℂ) * H z y - Real.pi * H y y / 2) + (-(Real.pi : ℂ) * H z z) = -(Real.pi : ℂ) * Complex.I * (altE H y (x : V) : ℂ) + (-(Real.pi : ℂ) * H (y + (x : V) …`. Simplify using `only [map_add, LinearMap.add_apply, altE]`. Rewrite using `[hH y z, hH (x : V) z, hH y (x : V)]`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`. Establish `e1` using `congrArg Complex.exp hP`.

Simplify using `only [Complex.exp_add] at e1`. Take the linear combination `(α y * α (x : V)) * e1`.
-/
theorem diag_expansion {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (hH : IsHerm H) (α : V → ℂ)
    (Λ : AddSubgroup V) (y z : V) :
    α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ)
      = ∑' x : Λ, diagCoef H α y (x : V) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ)) := by
  rw [wt_eq_cexp H hH z]
  simp only [opU, kerP, kerK]
  rw [← tsum_mul_right, ← tsum_mul_left, ← tsum_mul_right]
  refine tsum_congr (fun x => ?_)
  unfold diagCoef
  have hP : (Real.pi : ℂ) * H (z + y + (x : V)) z
      + (-(Real.pi : ℂ) * H (z + y) (x : V) - Real.pi * H (x : V) (x : V) / 2)
      + (-(Real.pi : ℂ) * H z y - Real.pi * H y y / 2)
      + (-(Real.pi : ℂ) * H z z)
      = -(Real.pi : ℂ) * Complex.I * (altE H y (x : V) : ℂ)
        + (-(Real.pi : ℂ) * H (y + (x : V)) (y + (x : V)) / 2)
        + 2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ) := by
    simp only [map_add, LinearMap.add_apply, altE]
    rw [hH y z, hH (x : V) z, hH y (x : V)]
    apply Complex.ext <;> simp <;> ring
  have e1 := congrArg Complex.exp hP
  simp only [Complex.exp_add] at e1
  linear_combination (α y * α (x : V)) * e1

/- English proof (translation)
Establish `: 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[this, Complex.norm_exp_ofReal_mul_I]`.
-/
theorem norm_char (t : ℝ) : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))‖ = 1 := by
  have : 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Establish `hn : ∀ a : ℂ, (a = 1 ∨ a = -1) → ‖a‖ = 1`. Apply the tactic sequence `rintro a (rfl | rfl) <;> simp`. Unfold `diagCoef`. Rewrite using `[norm_mul, norm_mul, norm_mul, hn _ hy, hn _ hx, Complex.norm_exp, Complex.norm_exp]`. Establish `h1 : (-(Real.pi : ℂ) * Complex.I * (altE H y x : ℂ)).re = 0`.

Simplify using the standard rewrite rules. Establish `h2 : (-(Real.pi : ℂ) * H (y + x) (y + x) / 2).re = -(Real.pi / 2) * (H (y + x) (y + x)).re`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h2]`.

Simplify using the standard rewrite rules.
-/
theorem norm_diagCoef {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (y x : V)
    (hy : α y = 1 ∨ α y = -1) (hx : α x = 1 ∨ α x = -1) :
    ‖diagCoef H α y x‖ = Real.exp (-(Real.pi / 2) * (H (y + x) (y + x)).re) := by
  have hn : ∀ a : ℂ, (a = 1 ∨ a = -1) → ‖a‖ = 1 := by
    rintro a (rfl | rfl) <;> simp
  unfold diagCoef
  rw [norm_mul, norm_mul, norm_mul, hn _ hy, hn _ hx, Complex.norm_exp, Complex.norm_exp]
  have h1 : (-(Real.pi : ℂ) * Complex.I * (altE H y x : ℂ)).re = 0 := by
    simp
  have h2 : (-(Real.pi : ℂ) * H (y + x) (y + x) / 2).re = -(Real.pi / 2) * (H (y + x) (y + x)).re := by
    simp
    ring
  rw [h1, h2]
  simp

/- English proof (translation)
Introduce `V _ _ _ _ _ μ _ H Λ Λ₂ α hH hPos hL hS hS₂ hC hC₂ D' hD' hB y hy`. Use `haveI : DiscreteTopology Λ := hL.1`. Use `haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance`. Use `set F : Λ → V → ℂ := fun x z => diagCoef H α y (x : V) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ)) with hF`. Establish `hexp : ∀ z, α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ) = ∑' x : Λ, F x z` using `fun z => diag_expansion H hH α Λ y z`.

Simplify using `only [hexp]`. Establish `hαy : α y = 1 ∨ α y = -1` using `hC₂.1 y hy`. Take `⟨c, C, hc, hC', hcC⟩` from `formNormEquiv V H hH hPos`. Establish `hnorm : ∀ (x : Λ) (z : V), ‖F x z‖ = Real.exp (-(Real.pi / 2) * (H (y + (x : V)) (y + (x : V))).re)`. Introduce `x z`.

Simplify using `only [hF]`. Rewrite using `[norm_mul, norm_char, mul_one, norm_diagCoef H α y x hαy (hC.1 x x.2)]`. Use `set g : Λ → ℝ := fun x => Real.exp (-(Real.pi / 2) * (H (y + (x : V)) (y + (x : V))).re) with hg_def`. Establish `hg : Summable g`. Take `⟨u, hu, hub⟩` from `latticeGaussSummable V Λ hL (Real.pi / 2 * c) ‖y‖ (by positivity)`.

Use `Summable.of_nonneg_of_le (fun x => (Real.exp_pos _).le) (fun x => ?_) hu` and prove the remaining obligations. Establish `h1` using `hub x (-y) (by simp)`. Use `le_trans ?_ h1` and prove the remaining obligations. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `h2` using `(hcC (y + (x : V))).1`.

Establish `h3 : ‖(x : V) - -y‖ = ‖y + (x : V)‖`. Rewrite using `[sub_neg_eq_add, add_comm]`. Rewrite using `[h3]`. Use polynomial arithmetic with `[Real.pi_pos]`. Establish `hfin : μ D' < ⊤` using `hB.measure_lt_top`.

Use `haveI : IsFiniteMeasure (μ.restrict D') := MeasureTheory.isFiniteMeasure_restrict.mpr hfin.ne`. Establish `hcont : ∀ x : Λ, Continuous (F x)`. Introduce `x`. Simplify using `only [hF]`. Conclude with `continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_altE H hH _))))`.

Establish `hint : ∀ x : Λ, Integrable (F x) (μ.restrict D')`. Introduce `x`. Conclude with `(integrable_const (g x)).mono' (hcont x).aestronglyMeasurable (Filter.Eventually.of_forall fun z => (hnorm x z).le)`. Establish `hsum : Summable fun x => ∫ z, ‖F x z‖ ∂(μ.restrict D')`. Establish `he : (fun x => ∫ z, ‖F x z‖ ∂(μ.restrict D')) = fun x => (μ D').toReal * g x`.

Use function extensionality and compare the values at `x`. Simplify using `only [hnorm x]`. Simplify using `[hg_def, Measure.real]`. Rewrite using `[he]`. Conclude with `hg.mul_left _`.

Rewrite using `[← integral_tsum_of_summable_integral_norm hint hsum]`. Establish `hd : diagCoef H α y (-y) = 1`. Establish `hneg : α (-y) = α y` using `(semicharacterBasic V H hH Λ₂ α hC₂).2.1 y hy`. Establish `him : altE H y (-y) = 0`. Unfold `altE`.

Rewrite using `[map_neg, Complex.neg_im, neg_eq_zero]`. Establish `h` using `congrArg Complex.im (hH y y)`. Rewrite `h` using `[Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `diagCoef`.

Rewrite using `[hneg, him, add_neg_cancel]`. Apply the tactic sequence `rcases hαy with h | h <;> simp [h]`. Establish `hterm : ∀ x : Λ, ∫ z in D', F x z ∂μ = if (x : V) = -y then ((μ D').toReal : ℂ) else 0`. Introduce `x`. Simplify using `only [hF]`.

Rewrite using `[integral_const_mul]`. Use `split_ifs with hx`. Rewrite using `[hx, add_neg_cancel, hd, one_mul]`. Simplify using `[altE, Measure.real]`. Establish `hne : y + (x : V) ≠ 0` using `fun h => hx (eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h))`.

Establish `hy' : y ∈ dualLat H Λ₂`. Rewrite using `[hS₂]`. Conclude with `hy`. Establish `hx' : (x : V) ∈ dualLat H Λ`. Rewrite using `[hS]`.

Conclude with `x.2`. Establish `hmem : y + (x : V) ∈ dualLat H (Λ ⊓ Λ₂)`. Use `add_mem ?_ ?_` and prove the remaining obligations. Conclude with `fun w hw => hy' w (AddSubgroup.mem_inf.mp hw).2`. Conclude with `fun w hw => hx' w (AddSubgroup.mem_inf.mp hw).1`.

Rewrite using `[characterIntegral V μ H hH hPos (Λ ⊓ Λ₂) D' hD' _ hmem hne, mul_zero]`. Simplify using `only [hterm]`. Use `split_ifs with hyΛ`. Establish `hiff : ∀ x : Λ, ((x : V) = -y) ↔ x = ⟨-y, neg_mem hyΛ⟩` using `fun x => by`. Simplify using `[Subtype.ext_iff]`.

Simplify using `[hiff]`. Establish `hno : ∀ x : Λ, (x : V) ≠ -y` using `fun x h => hyΛ (by`. Establish `hx2` using `x.2`. Rewrite `hx2` using `[h]`. Simplify using `using hx2)`.

Simplify using `[hno]`.
-/
theorem diagonalIntegral : DiagIntegral := by
  classical
  intro V _ _ _ _ _ μ _ H Λ Λ₂ α hH hPos hL hS hS₂ hC hC₂ D' hD' hB y hy
  haveI : DiscreteTopology Λ := hL.1
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  set F : Λ → V → ℂ := fun x z => diagCoef H α y (x : V) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ)) with hF
  have hexp : ∀ z, α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ) = ∑' x : Λ, F x z :=
    fun z => diag_expansion H hH α Λ y z
  simp only [hexp]
  have hαy : α y = 1 ∨ α y = -1 := hC₂.1 y hy
  obtain ⟨c, C, hc, hC', hcC⟩ := formNormEquiv V H hH hPos
  have hnorm : ∀ (x : Λ) (z : V), ‖F x z‖ = Real.exp (-(Real.pi / 2) * (H (y + (x : V)) (y + (x : V))).re) := by
    intro x z
    simp only [hF]
    rw [norm_mul, norm_char, mul_one, norm_diagCoef H α y x hαy (hC.1 x x.2)]
  set g : Λ → ℝ := fun x => Real.exp (-(Real.pi / 2) * (H (y + (x : V)) (y + (x : V))).re) with hg_def
  have hg : Summable g := by
    obtain ⟨u, hu, hub⟩ := latticeGaussSummable V Λ hL (Real.pi / 2 * c) ‖y‖ (by positivity)
    refine Summable.of_nonneg_of_le (fun x => (Real.exp_pos _).le) (fun x => ?_) hu
    have h1 := hub x (-y) (by simp)
    refine le_trans ?_ h1
    apply Real.exp_le_exp.mpr
    have h2 := (hcC (y + (x : V))).1
    have h3 : ‖(x : V) - -y‖ = ‖y + (x : V)‖ := by
      rw [sub_neg_eq_add, add_comm]
    rw [h3]
    nlinarith [Real.pi_pos]
  have hfin : μ D' < ⊤ := hB.measure_lt_top
  haveI : IsFiniteMeasure (μ.restrict D') := MeasureTheory.isFiniteMeasure_restrict.mpr hfin.ne
  have hcont : ∀ x : Λ, Continuous (F x) := by
    intro x
    simp only [hF]
    exact continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_altE H hH _))))
  have hint : ∀ x : Λ, Integrable (F x) (μ.restrict D') := by
    intro x
    exact (integrable_const (g x)).mono' (hcont x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => (hnorm x z).le)
  have hsum : Summable fun x => ∫ z, ‖F x z‖ ∂(μ.restrict D') := by
    have he : (fun x => ∫ z, ‖F x z‖ ∂(μ.restrict D')) = fun x => (μ D').toReal * g x := by
      funext x
      simp only [hnorm x]
      simp [hg_def, Measure.real]
    rw [he]
    exact hg.mul_left _
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  have hd : diagCoef H α y (-y) = 1 := by
    have hneg : α (-y) = α y := (semicharacterBasic V H hH Λ₂ α hC₂).2.1 y hy
    have him : altE H y (-y) = 0 := by
      unfold altE
      rw [map_neg, Complex.neg_im, neg_eq_zero]
      have h := congrArg Complex.im (hH y y)
      rw [Complex.conj_im] at h
      linarith
    unfold diagCoef
    rw [hneg, him, add_neg_cancel]
    rcases hαy with h | h <;> simp [h]
  have hterm : ∀ x : Λ, ∫ z in D', F x z ∂μ = if (x : V) = -y then ((μ D').toReal : ℂ) else 0 := by
    intro x
    simp only [hF]
    rw [integral_const_mul]
    split_ifs with hx
    · rw [hx, add_neg_cancel, hd, one_mul]
      simp [altE, Measure.real]
    · have hne : y + (x : V) ≠ 0 := fun h => hx (eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h))
      have hy' : y ∈ dualLat H Λ₂ := by
        rw [hS₂]
        exact hy
      have hx' : (x : V) ∈ dualLat H Λ := by
        rw [hS]
        exact x.2
      have hmem : y + (x : V) ∈ dualLat H (Λ ⊓ Λ₂) := by
        refine add_mem ?_ ?_
        · exact fun w hw => hy' w (AddSubgroup.mem_inf.mp hw).2
        · exact fun w hw => hx' w (AddSubgroup.mem_inf.mp hw).1
      rw [characterIntegral V μ H hH hPos (Λ ⊓ Λ₂) D' hD' _ hmem hne, mul_zero]
  simp only [hterm]
  split_ifs with hyΛ
  · have hiff : ∀ x : Λ, ((x : V) = -y) ↔ x = ⟨-y, neg_mem hyΛ⟩ := fun x => by
      simp [Subtype.ext_iff]
    simp [hiff]
  · have hno : ∀ x : Λ, (x : V) ≠ -y := fun x h => hyΛ (by
      have hx2 := x.2
      rw [h] at hx2
      simpa using hx2)
    simp [hno]

/- English proof (translation)
Introduce `V _ _ _ H Λ α hH hPos hL hS hC`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Use `letI : MeasurableSpace V := borel V`. Use `haveI : BorelSpace V := ⟨rfl⟩`.

Take `⟨D, hD1, hD2, hD3, -⟩` from `fundamentalDomainExists V MeasureTheory.Measure.addHaar (Λ ⊓ Λ) (by rw [inf_idem]; exact hL)`. Establish `hint` using `hD V MeasureTheory.Measure.addHaar H Λ Λ α hH hPos hL hS hS hC hC D hD1 hD2 0 (zero_mem _)`. Simplify using `[opU, hne] at hint`. Establish `h0 : (MeasureTheory.Measure.addHaar D).toReal = 0`. Conclude with `hint.symm` after adjusting the coercions.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem KerPNonzero_of (hD : DiagIntegral) : KerPNonzero := by
  intro V _ _ _ H Λ α hH hPos hL hS hC
  by_contra hne
  push_neg at hne
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  obtain ⟨D, hD1, hD2, hD3, -⟩ :=
    fundamentalDomainExists V MeasureTheory.Measure.addHaar (Λ ⊓ Λ) (by rw [inf_idem]; exact hL)
  have hint := hD V MeasureTheory.Measure.addHaar H Λ Λ α hH hPos hL hS hS hC hC D hD1 hD2 0 (zero_mem _)
  simp [opU, hne] at hint
  have h0 : (MeasureTheory.Measure.addHaar D).toReal = 0 := by
    exact_mod_cast hint.symm
  linarith

end Formalism.L2.Th1.H
