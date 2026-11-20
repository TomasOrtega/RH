import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenOfPoincareLelongHyperplane
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HessCRestrictThm
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul

namespace ReciprocityTheory.AnForm.A

open MeasureTheory Filter Topology

open scoped ContDiff

noncomputable section

/- English proof (translation)
Establish `h1` using `iteratedFDeriv_two_apply (𝕜 := ℝ) (g ∘ P) z ![a, b]`. Establish `h2` using `iteratedFDeriv_two_apply (𝕜 := ℝ) g (P z) ![P a, P b]`. Rewrite `h1` using `[P.iteratedFDeriv_comp_right hg z le_rfl]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2`. Rewrite using `[← h1, ← h2]`.

Simplify using `only [ContinuousMultilinearMap.compContinuousLinearMap_apply]`. Use `congr 1`. Apply the tactic sequence `funext i; fin_cases i <;> rfl`.
-/
theorem fderiv2_comp_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → ℝ) (P : F →L[ℝ] E) (hg : ContDiff ℝ 2 g)
    (z a b : F) :
    fderiv ℝ (fderiv ℝ (g ∘ P)) z a b = fderiv ℝ (fderiv ℝ g) (P z) (P a) (P b) := by
  have h1 := iteratedFDeriv_two_apply (𝕜 := ℝ) (g ∘ P) z ![a, b]
  have h2 := iteratedFDeriv_two_apply (𝕜 := ℝ) g (P z) ![P a, P b]
  rw [P.iteratedFDeriv_comp_right hg z le_rfl] at h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  rw [← h1, ← h2]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i; fin_cases i <;> rfl

def gReg (ε : ℝ) (ζ : ℂ) : ℝ := (1 / 2) * Real.log (‖ζ‖ ^ 2 + ε)

/- English proof (translation)
Establish `hs : ‖ζ‖ ^ 2 + ε ≠ 0` using `by positivity`. Establish `h1` using `((hasStrictFDerivAt_norm_sq ζ).hasFDerivAt.add_const ε).log hs`. Establish `h2 : HasFDerivAt (gReg ε) ((1 / 2 : ℝ) • ((‖ζ‖ ^ 2 + ε)⁻¹ • (2 • innerSL ℝ ζ))) ζ` using `h1.const_mul (1 / 2 : ℝ)`. Use `h2.congr_fderiv ?_` and prove the remaining obligations. Use `module`.
-/
theorem gReg_hasFDerivAt {ε : ℝ} (hε : 0 < ε) (ζ : ℂ) :
    HasFDerivAt (gReg ε) ((‖ζ‖ ^ 2 + ε)⁻¹ • innerSL ℝ ζ) ζ := by
  have hs : ‖ζ‖ ^ 2 + ε ≠ 0 := by positivity
  have h1 := ((hasStrictFDerivAt_norm_sq ζ).hasFDerivAt.add_const ε).log hs
  have h2 : HasFDerivAt (gReg ε) ((1 / 2 : ℝ) • ((‖ζ‖ ^ 2 + ε)⁻¹ • (2 • innerSL ℝ ζ))) ζ :=
    h1.const_mul (1 / 2 : ℝ)
  refine h2.congr_fderiv ?_
  module

/- English proof (translation)
Use function extensionality and compare the values at `ζ`. Conclude with `(gReg_hasFDerivAt hε ζ).fderiv`.
-/
theorem fderiv_gReg {ε : ℝ} (hε : 0 < ε) :
    fderiv ℝ (gReg ε) = fun ζ => (‖ζ‖ ^ 2 + ε)⁻¹ • innerSL ℝ ζ := by
  funext ζ; exact (gReg_hasFDerivAt hε ζ).fderiv

/- English proof (translation)
Establish `hs : ‖ζ‖ ^ 2 + ε ≠ 0` using `by positivity`. Establish `hq : HasFDerivAt (fun y : ℂ => ‖y‖ ^ 2 + ε) (2 • innerSL ℝ ζ) ζ` using `(hasStrictFDerivAt_norm_sq ζ).hasFDerivAt.add_const ε`. Establish `hc` using `(hasFDerivAt_inv (𝕜 := ℝ) hs).comp ζ hq`. Establish `hL : HasFDerivAt (fun y : ℂ => innerSL ℝ y) (innerSL ℝ) ζ` using `(innerSL ℝ).hasFDerivAt`. Establish `h` using `hc.smul hL`.

Establish `h' : HasFDerivAt (fun y : ℂ => (‖y‖ ^ 2 + ε)⁻¹ • innerSL ℝ y) _ ζ` using `h`. Rewrite using `[fderiv_gReg hε, h'.fderiv]`. Establish `hi : ∀ x y : ℂ, (innerSL ℝ x) y = x.re * y.re + x.im * y.im` using `fun x y => by`. Rewrite using `[innerSL_apply_apply]`. Simplify using `[Complex.inner]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[hi]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem second_fderiv_regularized_log {ε : ℝ} (hε : 0 < ε) (ζ a b : ℂ) :
    fderiv ℝ (fderiv ℝ (gReg ε)) ζ a b =
      (‖ζ‖ ^ 2 + ε)⁻¹ * inner ℝ a b - 2 * inner ℝ ζ a * inner ℝ ζ b / (‖ζ‖ ^ 2 + ε) ^ 2 := by
  have hs : ‖ζ‖ ^ 2 + ε ≠ 0 := by positivity
  have hq : HasFDerivAt (fun y : ℂ => ‖y‖ ^ 2 + ε) (2 • innerSL ℝ ζ) ζ :=
    (hasStrictFDerivAt_norm_sq ζ).hasFDerivAt.add_const ε
  have hc := (hasFDerivAt_inv (𝕜 := ℝ) hs).comp ζ hq
  have hL : HasFDerivAt (fun y : ℂ => innerSL ℝ y) (innerSL ℝ) ζ :=
    (innerSL ℝ).hasFDerivAt
  have h := hc.smul hL
  have h' : HasFDerivAt (fun y : ℂ => (‖y‖ ^ 2 + ε)⁻¹ • innerSL ℝ y) _ ζ := h
  rw [fderiv_gReg hε, h'.fderiv]
  have hi : ∀ x y : ℂ, (innerSL ℝ x) y = x.re * y.re + x.im * y.im := fun x y => by
    rw [innerSL_apply_apply]; simp [Complex.inner]; ring
  simp [hi]
  field_simp
  ring

/- English proof (translation)
Unfold `gReg`. Use `contDiff_const.mul ((contDiff_norm_sq ℝ).add contDiff_const |>.log fun ζ => ?_)` and prove the remaining obligations. Check the signs of the components of the expression.
-/
theorem gReg_contDiff {ε : ℝ} (hε : 0 < ε) {m : WithTop ℕ∞} : ContDiff ℝ m (gReg ε) := by
  unfold gReg
  refine contDiff_const.mul ((contDiff_norm_sq ℝ).add contDiff_const |>.log fun ζ => ?_)
  positivity

def cReg (ε : ℝ) (ζ : ℂ) : ℝ := ε / (2 * (‖ζ‖ ^ 2 + ε) ^ 2)

/- English proof (translation)
Set `P : (Fin (n + 1) → ℂ) →L[ℝ] ℂ` to `ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℂ) i`. Establish `hf : (fun y : Fin (n + 1) → ℂ => gReg ε (y i)) = gReg ε ∘ P` using `rfl`. Establish `hP : ∀ y, P y = y i` using `fun y => rfl`. Use extensionality with `a b`. Simplify using `only [hessC, hf, fderiv2_comp_clm _ P (gReg_contDiff hε), hP]`.

Distinguish the cases in `ha : a = i`. Distinguish the cases in `hb : b = i`. Rewrite using `[ha, hb]`. Establish `hs : ‖z i‖ ^ 2 + ε ≠ 0` using `by positivity`. Establish `hn : ‖z i‖ ^ 2 = (z i).re ^ 2 + (z i).im ^ 2`.

Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : fderiv ℝ (fderiv ℝ (gReg ε)) (z i) 1 1 + fderiv ℝ (fderiv ℝ (gReg ε)) (z i) Complex.I Complex.I = 4 * cReg ε (z i)`. Rewrite using `[second_fderiv_regularized_log hε, second_fderiv_regularized_log hε]`. Simplify using `only [Complex.inner, cReg, hn]`.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : fderiv ℝ (fderiv ℝ (gReg ε)) (z i) 1 Complex.I - fderiv ℝ (fderiv ℝ (gReg ε)) (z i) Complex.I 1 = 0`. Rewrite using `[second_fderiv_regularized_log hε, second_fderiv_regularized_log hε]`.

Simplify using `only [Complex.inner]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]`. Rewrite using `[h1, h2]`.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, Ne.symm hb]`. Simplify using `[Pi.single_apply, Ne.symm ha]`.
-/
theorem hessC_gReg {n : ℕ} {ε : ℝ} (hε : 0 < ε) (i : Fin (n + 1)) (z : Fin (n + 1) → ℂ) :
    hessC (fun y : Fin (n + 1) → ℂ => gReg ε (y i)) z =
      ((cReg ε (z i) : ℝ) : ℂ) • Matrix.single i i 1 := by
  let P : (Fin (n + 1) → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℂ) i
  have hf : (fun y : Fin (n + 1) → ℂ => gReg ε (y i)) = gReg ε ∘ P := rfl
  have hP : ∀ y, P y = y i := fun y => rfl
  ext a b
  simp only [hessC, hf, fderiv2_comp_clm _ P (gReg_contDiff hε), hP]
  by_cases ha : a = i
  · by_cases hb : b = i
    · rw [ha, hb]
      have hs : ‖z i‖ ^ 2 + ε ≠ 0 := by positivity
      have hn : ‖z i‖ ^ 2 = (z i).re ^ 2 + (z i).im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have h1 : fderiv ℝ (fderiv ℝ (gReg ε)) (z i) 1 1 +
          fderiv ℝ (fderiv ℝ (gReg ε)) (z i) Complex.I Complex.I = 4 * cReg ε (z i) := by
        rw [second_fderiv_regularized_log hε, second_fderiv_regularized_log hε]
        simp only [Complex.inner, cReg, hn]
        simp
        field_simp
        ring
      have h2 : fderiv ℝ (fderiv ℝ (gReg ε)) (z i) 1 Complex.I -
          fderiv ℝ (fderiv ℝ (gReg ε)) (z i) Complex.I 1 = 0 := by
        rw [second_fderiv_regularized_log hε, second_fderiv_regularized_log hε]
        simp only [Complex.inner]
        simp
        ring
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      rw [h1, h2]
      simp
    · simp [Pi.single_apply, Ne.symm hb]
  · simp [Pi.single_apply, Ne.symm ha]

/- English proof (translation)
Use `contDiff_iff_contDiffAt.2 fun z => ?_` and prove the remaining obligations. Distinguish the cases in `hz : z ∈ U`. Conclude with `hf.contDiffAt (hU.mem_nhds hz)`. Establish `hzK : z ∈ Kᶜ` using `fun h => hz (hKU h)`. Use `(contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_` and prove the remaining obligations.

Use `filter_upwards [hK.isOpen_compl.mem_nhds hzK] with y hy using h0 y hy`.
-/
theorem contDiff_of_contDiffOn_zero_off {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U K : Set E} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → F} {m : WithTop ℕ∞} (hf : ContDiffOn ℝ m f U)
    (h0 : ∀ z ∉ K, f z = 0) : ContDiff ℝ m f := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : z ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hz)
  · have hzK : z ∈ Kᶜ := fun h => hz (hKU h)
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isOpen_compl.mem_nhds hzK] with y hy using h0 y hy

/- English proof (translation)
Establish `h1 : v =ᶠ[𝓝 z] fun _ => 0` using `(notMem_tsupport_iff_eventuallyEq).1 hz`. Establish `h2 : fderiv ℝ (fderiv ℝ v) z = 0`. Rewrite using `[h1.fderiv.fderiv_eq]`. Simplify using the standard rewrite rules. Use extensionality with `i j`.

Simplify using `[hessC, h2]`.
-/
theorem hessC_eq_zero_of_notMem {D : ℕ} {v : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (hz : z ∉ tsupport v) : hessC v z = 0 := by
  have h1 : v =ᶠ[𝓝 z] fun _ => 0 := (notMem_tsupport_iff_eventuallyEq).1 hz
  have h2 : fderiv ℝ (fderiv ℝ v) z = 0 := by
    rw [h1.fderiv.fderiv_eq]
    simp
  ext i j
  simp [hessC, h2]

/- English proof (translation)
Establish `h1 : ContDiffOn ℝ (m + 1) (fderiv ℝ φ) U` using `hφ.fderiv_of_isOpen hU (by norm_cast)`. Establish `h2 : ContDiffOn ℝ m (fderiv ℝ (fderiv ℝ φ)) U` using `h1.fderiv_of_isOpen hU le_rfl`. Establish `hH : ∀ a b : Fin D → ℂ, ContDiffOn ℝ m (fun z => fderiv ℝ (fderiv ℝ φ) z a b) U` using `fun a b => (h2.clm_apply contDiffOn_const).clm_apply contDiffOn_const`. Establish `hC : ∀ g : (Fin D → ℂ) → ℝ, ContDiffOn ℝ m g U → ContDiffOn ℝ m (fun z => (g z : ℂ)) U` using `fun g hg => Complex.ofRealCLM.contDiff.comp_contDiffOn hg`. Simplify using `only [hessC]`.

Use `ContDiffOn.div_const (ContDiffOn.add (hC _ ((hH _ _).add (hH _ _))) (contDiffOn_const.mul (hC _ ((hH _ _).sub (hH _ _))))) _` and prove the remaining obligations.
-/
theorem hessC_contDiffOn {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    {m : ℕ} (hφ : ContDiffOn ℝ (m + 2) φ U) (i j : Fin D) :
    ContDiffOn ℝ m (fun z => hessC φ z i j) U := by
  have h1 : ContDiffOn ℝ (m + 1) (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_cast)
  have h2 : ContDiffOn ℝ m (fderiv ℝ (fderiv ℝ φ)) U := h1.fderiv_of_isOpen hU le_rfl
  have hH : ∀ a b : Fin D → ℂ, ContDiffOn ℝ m (fun z => fderiv ℝ (fderiv ℝ φ) z a b) U :=
    fun a b => (h2.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hC : ∀ g : (Fin D → ℂ) → ℝ, ContDiffOn ℝ m g U → ContDiffOn ℝ m (fun z => (g z : ℂ)) U :=
    fun g hg => Complex.ofRealCLM.contDiff.comp_contDiffOn hg
  simp only [hessC]
  refine ContDiffOn.div_const (ContDiffOn.add (hC _ ((hH _ _).add (hH _ _)))
    (contDiffOn_const.mul (hC _ ((hH _ _).sub (hH _ _))))) _

/- English proof (translation)
Simplify using `only [mdisc, Matrix.det_apply', Matrix.sum_apply]`. Use `contDiffOn_const.mul (ContDiffOn.sum fun S _ => contDiffOn_const.mul (ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => ContDiffOn.sum fun k _ => hA k _ _)))` and prove the remaining obligations.
-/
theorem mdisc_contDiffOn {D : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin D → E → Matrix (Fin D) (Fin D) ℂ) {s : Set E} {m : WithTop ℕ∞}
    (hA : ∀ k i j, ContDiffOn ℝ m (fun z => A k z i j) s) :
    ContDiffOn ℝ m (fun z => mdisc (fun k => A k z)) s := by
  simp only [mdisc, Matrix.det_apply', Matrix.sum_apply]
  refine contDiffOn_const.mul (ContDiffOn.sum fun S _ => contDiffOn_const.mul
    (ContDiffOn.sum fun σ _ => contDiffOn_const.mul
      (contDiffOn_prod fun i _ => ContDiffOn.sum fun k _ => hA k _ _)))

/- English proof (translation)
Rewrite using `[ae_iff]`. Simplify using `only [ne_eq, not_not]`. Rewrite using `[volume_pi]`. Conclude with `Measure.pi_hyperplane _ i 0`.
-/
theorem ae_coord_ne_zero {n : ℕ} (i : Fin (n + 1)) : ∀ᵐ z : Fin (n + 1) → ℂ ∂volume, z i ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [volume_pi]
  exact Measure.pi_hyperplane _ i 0

/- English proof (translation)
The claim follows from `|gReg ε ζ| ≤ |Real.log ‖ζ‖| + (1 / 2) * Real.log (‖ζ‖ ^ 2 + 1) := by have hr : 0 < ‖ζ‖ := norm_pos_iff.2 hζ have hr2 : 0 < ‖ζ‖ ^ 2 := by positivity have hl1 : 0 ≤ Real.log (‖ζ‖ ^ 2 + 1) := Real.log_nonneg (by linarith) have hup : Real.log (‖ζ‖ ^ 2 + ε) ≤ Real.log (‖ζ‖ ^ 2 + 1) := …`.
-/
theorem gReg_abs_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {ζ : ℂ} (hζ : ζ ≠ 0) :
    |gReg ε ζ| ≤ |Real.log ‖ζ‖| + (1 / 2) * Real.log (‖ζ‖ ^ 2 + 1) := by
  have hr : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
  have hr2 : 0 < ‖ζ‖ ^ 2 := by positivity
  have hl1 : 0 ≤ Real.log (‖ζ‖ ^ 2 + 1) := Real.log_nonneg (by linarith)
  have hup : Real.log (‖ζ‖ ^ 2 + ε) ≤ Real.log (‖ζ‖ ^ 2 + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlo : Real.log (‖ζ‖ ^ 2) ≤ Real.log (‖ζ‖ ^ 2 + ε) := Real.log_le_log hr2 (by linarith)
  have h2 : Real.log (‖ζ‖ ^ 2) = 2 * Real.log ‖ζ‖ := by rw [Real.log_pow]; push_cast; ring
  unfold gReg
  rcases le_or_gt 0 (Real.log (‖ζ‖ ^ 2 + ε)) with h | h
  · rw [abs_of_nonneg (by linarith)]
    have := abs_nonneg (Real.log ‖ζ‖)
    linarith
  · rw [abs_of_neg (by linarith)]
    have := neg_abs_le (Real.log ‖ζ‖)
    linarith

/- English proof (translation)
Establish `hr2 : 0 < ‖ζ‖ ^ 2` using `by have := norm_pos_iff.2 hζ; positivity`. Establish `h1 : Tendsto (fun k : ℕ => ‖ζ‖ ^ 2 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (‖ζ‖ ^ 2 + 0))` using `tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat`. Rewrite `h1` using `[add_zero]`. Establish `h2` using `((Real.continuousAt_log hr2.ne').tendsto.comp h1).const_mul (1 / 2 : ℝ)`. Establish `h3 : (1 / 2 : ℝ) * Real.log (‖ζ‖ ^ 2) = Real.log ‖ζ‖`.

Rewrite using `[Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[h3]`. Conclude with `h2`.
-/
theorem tendsto_gReg {ζ : ℂ} (hζ : ζ ≠ 0) :
    Tendsto (fun k : ℕ => gReg (1 / ((k : ℝ) + 1)) ζ) atTop (𝓝 (Real.log ‖ζ‖)) := by
  have hr2 : 0 < ‖ζ‖ ^ 2 := by have := norm_pos_iff.2 hζ; positivity
  have h1 : Tendsto (fun k : ℕ => ‖ζ‖ ^ 2 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (‖ζ‖ ^ 2 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at h1
  have h2 := ((Real.continuousAt_log hr2.ne').tendsto.comp h1).const_mul (1 / 2 : ℝ)
  have h3 : (1 / 2 : ℝ) * Real.log (‖ζ‖ ^ 2) = Real.log ‖ζ‖ := by
    rw [Real.log_pow]; push_cast; ring
  rw [h3] at h2
  exact h2

/- English proof (translation)
Establish `hε0 : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1)` using `fun k => by positivity`. Establish `hε1 : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1` using `fun k => by`. Rewrite using `[div_le_one (by positivity)]; have := k.cast_nonneg (α := ℝ); linarith`. Use `tendsto_integral_of_dominated_convergence (fun z => |Real.log ‖z i‖| * |F z| + (1 / 2) * Real.log (‖z i‖ ^ 2 + 1) * |F z|) (fun k => (((gReg_contDiff (hε0 k) (m := 0)).continuous.comp (continuous_apply i)).mul hF).aestronglyMeasurable) ?_ ?_ ?_` and prove the remaining obligations. Use `Integrable.add ?_ ?_` and prove the remaining obligations.

Use `(hlog.integrable_smul_left_of_hasCompactSupport hF hFc).abs` as an intermediate fact. Use `this.congr (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only [smul_eq_mul, abs_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `Continuous.integrable_of_hasCompactSupport ?_ ?_` and prove the remaining obligations.

Establish `hc : Continuous (fun z : Fin (n + 1) → ℂ => Real.log (‖z i‖ ^ 2 + 1))` using `Continuous.log (by fun_prop) fun z => (add_pos_of_nonneg_of_pos (sq_nonneg _) one_pos).ne'`. Conclude with `(continuous_const.mul hc).mul hF.abs`. Conclude with `hFc.abs.mul_left`. Introduce `k filter_upwards [ae_coord_ne_zero i] with z hz`. Rewrite using `[norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, ← add_mul]`.

Conclude with `mul_le_mul_of_nonneg_right (gReg_abs_le (hε0 k) (hε1 k) hz) (abs_nonneg _)`. Use `filter_upwards [ae_coord_ne_zero i] with z hz`. Conclude with `(tendsto_gReg hz).mul_const _`.
-/
theorem tendsto_integral_gReg {n : ℕ} (i : Fin (n + 1)) (F : (Fin (n + 1) → ℂ) → ℝ) (hF : Continuous F)
    (hFc : HasCompactSupport F)
    (hlog : LocallyIntegrable (fun z : Fin (n + 1) → ℂ => Real.log ‖z i‖) volume) :
    Tendsto (fun k : ℕ => ∫ z, gReg (1 / ((k : ℝ) + 1)) (z i) * F z) atTop
      (𝓝 (∫ z, Real.log ‖z i‖ * F z)) := by
  have hε0 : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hε1 : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]; have := k.cast_nonneg (α := ℝ); linarith
  refine tendsto_integral_of_dominated_convergence
    (fun z => |Real.log ‖z i‖| * |F z| + (1 / 2) * Real.log (‖z i‖ ^ 2 + 1) * |F z|)
    (fun k => (((gReg_contDiff (hε0 k) (m := 0)).continuous.comp (continuous_apply i)).mul
      hF).aestronglyMeasurable) ?_ ?_ ?_
  · refine Integrable.add ?_ ?_
    · have := (hlog.integrable_smul_left_of_hasCompactSupport hF hFc).abs
      refine this.congr (Eventually.of_forall fun z => ?_)
      simp only [smul_eq_mul, abs_mul]; ring
    · refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · have hc : Continuous (fun z : Fin (n + 1) → ℂ => Real.log (‖z i‖ ^ 2 + 1)) :=
          Continuous.log (by fun_prop) fun z =>
            (add_pos_of_nonneg_of_pos (sq_nonneg _) one_pos).ne'
        exact (continuous_const.mul hc).mul hF.abs
      · exact hFc.abs.mul_left
  · intro k
    filter_upwards [ae_coord_ne_zero i] with z hz
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, ← add_mul]
    exact mul_le_mul_of_nonneg_right (gReg_abs_le (hε0 k) (hε1 k) hz) (abs_nonneg _)
  · filter_upwards [ae_coord_ne_zero i] with z hz
    exact (tendsto_gReg hz).mul_const _

variable {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `k`. Use `Fin.cases rfl (fun k => rfl) k` and prove the remaining obligations.
-/
theorem hessC_cons (f : (Fin (n + 1) → ℂ) → ℝ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ) :
    (fun k => hessC ((Fin.cons f φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z) =
      Fin.cons (hessC f z) (fun k => hessC (φ k) z) := by
  funext k; refine Fin.cases rfl (fun k => rfl) k

/- English proof (translation)
Establish `h` using `mdisc_update_smul (Fin.cons (Matrix.single i i 1) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 c (Matrix.single i i 1)`. Rewrite `h` using `[Fin.update_cons_zero, Fin.update_cons_zero]`. Rewrite using `[h]`. Establish `h2` using `mixedCof_diag B i`. Simplify using `only [mixedCof] at h2`.

Rewrite using `[h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mdisc_cons_smul_single (i : Fin (n + 1)) (c : ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (c • Matrix.single i i 1) B :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      c * ((1 / ((n : ℂ) + 1)) * mdisc (fun k => (B k).submatrix i.succAbove i.succAbove)) := by
  have h := mdisc_update_smul
    (Fin.cons (Matrix.single i i 1) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 c
    (Matrix.single i i 1)
  rw [Fin.update_cons_zero, Fin.update_cons_zero] at h
  rw [h]
  have h2 := mixedCof_diag B i
  simp only [mixedCof] at h2
  rw [h2]
  push_cast
  ring

/- English proof (translation)
Establish `h` using `mdisc_update_smul (Fin.cons 0 B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 0 0`. Simplify `h` using `[Fin.update_cons_zero]`.
-/
theorem mdisc_cons_zero (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons 0 B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 0 := by
  have h := mdisc_update_smul
    (Fin.cons 0 B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 0 0
  simpa [Fin.update_cons_zero] using h

def kDens (n : ℕ) : ℝ := ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1)

def minorDens (i : Fin (n + 1)) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) : ℝ :=
  (mdisc (fun k => (hessC (φ k) z).submatrix i.succAbove i.succAbove)).re

/- English proof (translation)
Unfold `maDens`. Rewrite using `[hessC_cons, hessC_gReg hε, mdisc_cons_smul_single]`. Establish `h1 : (1 / ((n : ℂ) + 1)) = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[h1, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]`. Simplify using `only [kDens, minorDens]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem maDens_cons_gReg {ε : ℝ} (hε : 0 < ε) (i : Fin (n + 1))
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) :
    maDens (Fin.cons (fun y => gReg ε (y i)) φ) z =
      kDens n * cReg ε (z i) * (1 / ((n : ℝ) + 1)) * minorDens i φ z := by
  unfold maDens
  rw [hessC_cons, hessC_gReg hε, mdisc_cons_smul_single]
  have h1 : (1 / ((n : ℂ) + 1)) = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  simp only [kDens, minorDens]
  ring
/- English proof (translation)
Unfold `maDens`. Rewrite using `[hessC_cons, hessC_eq_zero_of_notMem hz, mdisc_cons_zero]`. Simplify using the standard rewrite rules.
-/
theorem maDens_cons_eq_zero {v : (Fin (n + 1) → ℂ) → ℝ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    {z : Fin (n + 1) → ℂ} (hz : z ∉ tsupport v) : maDens (Fin.cons v φ) z = 0 := by
  unfold maDens
  rw [hessC_cons, hessC_eq_zero_of_notMem hz, mdisc_cons_zero]
  simp

def psiRef (n : ℕ) : Fin n → (Fin (n + 1) → ℂ) → ℝ := fun _ z => ∑ i, Complex.normSq (z i)

/- English proof (translation)
Unfold `psiRef`. Simplify using `only [Complex.normSq_eq_norm_sq]`. Conclude with `ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i)`.
-/
theorem psiRef_contDiff (k : Fin n) {m : WithTop ℕ∞} : ContDiff ℝ m (psiRef n k) := by
  unfold psiRef
  simp only [Complex.normSq_eq_norm_sq]
  exact ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i)

/- English proof (translation)
Establish `hp : ∀ k, hessC (psiRef n k) z = 1` using `fun k => hessC_sum_normSq z`. Simplify using `only [minorDens, hp]`. Rewrite using `[Matrix.submatrix_one _ (Fin.succAbove_right_injective), mdisc_const]`. Simplify using the standard rewrite rules.
-/
theorem minorDens_psiRef (i : Fin (n + 1)) (z : Fin (n + 1) → ℂ) : minorDens i (psiRef n) z = 1 := by
  have hp : ∀ k, hessC (psiRef n k) z = 1 := fun k => hessC_sum_normSq z
  simp only [minorDens, hp]
  rw [Matrix.submatrix_one _ (Fin.succAbove_right_injective), mdisc_const]
  simp

/- English proof (translation)
Conclude with `contDiffOn_infty.1 h (m + 2)` after adjusting the coercions.
-/
theorem cdo_of_infty {D : ℕ} {f : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)}
    (h : ContDiffOn ℝ ∞ f U) (m : ℕ) : ContDiffOn ℝ (m + 2) f U := by
  exact_mod_cast contDiffOn_infty.1 h (m + 2)

/- English proof (translation)
Establish `e : ((1 : ℕ) : WithTop ℕ∞) + 2 = 3` using `by norm_num`. Rewrite using `[e]`. Conclude with `h.contDiffOn`.
-/
theorem cdo_of_three {D : ℕ} {f : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)}
    (h : ContDiff ℝ 3 f) : ContDiffOn ℝ ((1 : ℕ) + 2) f U := by
  have e : ((1 : ℕ) : WithTop ℕ∞) + 2 = 3 := by norm_num
  rw [e]; exact h.contDiffOn

/- English proof (translation)
The claim follows from `Complex.reCLM.contDiff.comp_contDiffOn h`.
-/
theorem contDiffOn_re' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℂ}
    {s : Set E} {m : WithTop ℕ∞} (h : ContDiffOn ℝ m g s) :
    ContDiffOn ℝ m (fun z => (g z).re) s :=
  Complex.reCLM.contDiff.comp_contDiffOn h

/- English proof (translation)
Unfold `minorDens`. Use `contDiffOn_re' ?_` and prove the remaining obligations. Use `mdisc_contDiffOn (fun k z => (hessC (φ k) z).submatrix i.succAbove i.succAbove) fun k a b => ?_` and prove the remaining obligations. Conclude with `hessC_contDiffOn hU (cdo_of_infty (hφ k) m) (i.succAbove a) (i.succAbove b)`.
-/
theorem minorDens_contDiffOn (i : Fin (n + 1)) {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U)
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hφ : ∀ k, ContDiffOn ℝ ∞ (φ k) U) (m : ℕ) :
    ContDiffOn ℝ m (minorDens i φ) U := by
  unfold minorDens
  refine contDiffOn_re' ?_
  refine mdisc_contDiffOn (fun k z => (hessC (φ k) z).submatrix i.succAbove i.succAbove)
    fun k a b => ?_
  exact hessC_contDiffOn hU (cdo_of_infty (hφ k) m) (i.succAbove a) (i.succAbove b)

/- English proof (translation)
Establish `h : ContDiffOn ℝ (1 : ℕ) (maDens (Fin.cons f φ)) U`. Unfold `maDens`. Use `contDiffOn_const.mul (contDiffOn_re' ?_)` and prove the remaining obligations. Use `mdisc_contDiffOn (fun k z => hessC ((Fin.cons f φ : Fin (n + 1) → _) k) z) fun k i j => ?_` and prove the remaining obligations. Consider the cases of `k using Fin.cases with`.

Consider the case `zero => simpa using hessC_contDiffOn hU (cdo_of_three hf) i j`. Consider the case `succ k => simpa using hessC_contDiffOn hU (cdo_of_infty (hφ k) 1) i j`. Conclude with `(contDiff_of_contDiffOn_zero_off hU (isClosed_tsupport f) hfU h (fun z hz => maDens_cons_eq_zero φ hz)).continuous`.
-/
theorem maDens_cons_continuous {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U)
    {f : (Fin (n + 1) → ℂ) → ℝ} (hf : ContDiff ℝ 3 f) (hfU : tsupport f ⊆ U)
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hφ : ∀ k, ContDiffOn ℝ ∞ (φ k) U) :
    Continuous (maDens (Fin.cons f φ)) := by
  have h : ContDiffOn ℝ (1 : ℕ) (maDens (Fin.cons f φ)) U := by
    unfold maDens
    refine contDiffOn_const.mul (contDiffOn_re' ?_)
    refine mdisc_contDiffOn (fun k z => hessC ((Fin.cons f φ : Fin (n + 1) → _) k) z)
      fun k i j => ?_
    cases k using Fin.cases with
    | zero => simpa using hessC_contDiffOn hU (cdo_of_three hf) i j
    | succ k => simpa using hessC_contDiffOn hU (cdo_of_infty (hφ k) 1) i j
  exact (contDiff_of_contDiffOn_zero_off hU (isClosed_tsupport f) hfU h
    (fun z hz => maDens_cons_eq_zero φ hz)).continuous

/- English proof (translation)
Use `HasCompactSupport.intro hf.isCompact fun z hz => maDens_cons_eq_zero φ hz` and prove the remaining obligations.
-/
theorem maDens_cons_hasCompactSupport {f : (Fin (n + 1) → ℂ) → ℝ} (hf : HasCompactSupport f)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) : HasCompactSupport (maDens (Fin.cons f φ)) := by
  refine HasCompactSupport.intro hf.isCompact fun z hz => maDens_cons_eq_zero φ hz

def hDens (i : Fin (n + 1)) (v : (Fin (n + 1) → ℂ) → ℝ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ) : ℝ :=
  v z * minorDens i φ z

/- English proof (translation)
Take `⟨hU, hv, hvc, hvU, hφ⟩` from `hp`. Use `⟨contDiff_of_contDiffOn_zero_off hU (isClosed_tsupport v) hvU (hv.contDiffOn.mul (minorDens_contDiffOn i hU hφ 3)) fun z hz => ?_, hvc.mul_right⟩` and prove the remaining obligations. Simplify using `[hDens, image_eq_zero_of_notMem_tsupport hz]`.
-/
theorem hDens_props (i : Fin (n + 1)) {U : Set (Fin (n + 1) → ℂ)} {v : (Fin (n + 1) → ℂ) → ℝ}
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hp : PoincareLelongData U v φ) :
    ContDiff ℝ 3 (hDens i v φ) ∧ HasCompactSupport (hDens i v φ) := by
  obtain ⟨hU, hv, hvc, hvU, hφ⟩ := hp
  refine ⟨contDiff_of_contDiffOn_zero_off hU (isClosed_tsupport v) hvU
    (hv.contDiffOn.mul (minorDens_contDiffOn i hU hφ 3)) fun z hz => ?_, hvc.mul_right⟩
  simp [hDens, image_eq_zero_of_notMem_tsupport hz]

end

end ReciprocityTheory.AnForm.A
