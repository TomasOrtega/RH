import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnstatedLocalWeilLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitRepresentationHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilGaussSumExistenceHypothesisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilGaussConstantHypothesisStatement

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilRepW

open GlobalTheory.CompanionTheory.WeilSB (sb_comp sb_mul isLocallyConstant_char continuous_norm_of)
open GlobalTheory.CompanionTheory.SplitRep (chi_add modulus_neg_one modulus_neg')

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]
  [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

/- English proof (translation)
Apply `(algebraMap F E).injective` to reduce the goal to its premises. Simplify using `[algebraMap_norm_eq_mul_conj]`.
-/
theorem norm_neg' (x : E) : Algebra.norm F (-x) = Algebra.norm F x := by
  apply (algebraMap F E).injective
  simp [algebraMap_norm_eq_mul_conj]

/- English proof (translation)
Simplify using `only [FTs, localFourier]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Use `show Φ z * (χ _ : ℂ) = Φ z * (χ (Algebra.trace F E (z * conj F E u)) : ℂ)`. Rewrite using `[mul_comm (conj F E u)]`.
-/
theorem fts_apply (χ : AddChar F Circle) (μ : Measure E) (Φ : E → ℂ) (u : E) :
    FTs χ (conj F E) μ Φ u = localFourier μ (chE E χ) Φ (conj F E u) := by
  simp only [FTs, localFourier]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show Φ z * (χ _ : ℂ) = Φ z * (χ (Algebra.trace F E (z * conj F E u)) : ℂ)
  rw [mul_comm (conj F E u)]

/- English proof (translation)
Establish `h` using `(conjContinuousAddEquiv F E).toHomeomorph.measurableEmbedding.integral_map (μ := μ) f`. Establish `e : ((conjContinuousAddEquiv F E).toHomeomorph : E → E) = conj F E` using `rfl`. Rewrite `h` using `[e, map_conj_eq]`. Conclude with `h.symm`.
-/
theorem integral_conj (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → ℂ) :
    ∫ x, f (conj F E x) ∂μ = ∫ x, f x ∂μ := by
  have h := (conjContinuousAddEquiv F E).toHomeomorph.measurableEmbedding.integral_map (μ := μ) f
  have e : ((conjContinuousAddEquiv F E).toHomeomorph : E → E) = conj F E := rfl
  rw [e, map_conj_eq] at h
  exact h.symm

/- English proof (translation)
Establish `hχE : Continuous (chE E χ)` using `continuous_traceChar hχ hχ1`. Establish `hχE1 : chE E χ ≠ 1` using `traceChar_ne_one hχ hχ1`. Establish `e : FTs χ (conj F E) μ Φ = fun u => localFourier μ (chE E χ) Φ ((conjContinuousAddEquiv F E).toHomeomorph u)`. Use function extensionality and compare the values at `fun u => fts_apply χ μ Φ u`. Rewrite using `[e]`.

Conclude with `sb_comp _ (localFourier_mem_schwartzBruhat μ hχE hχE1 hΦ)`.
-/
theorem fts_sbe {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) (μ : Measure E)
    [μ.IsAddHaarMeasure] {Φ : E → ℂ} (hΦ : Φ ∈ SBE E) : FTs χ (conj F E) μ Φ ∈ SBE E := by
  have hχE : Continuous (chE E χ) := continuous_traceChar hχ hχ1
  have hχE1 : chE E χ ≠ 1 := traceChar_ne_one hχ hχ1
  have e : FTs χ (conj F E) μ Φ = fun u =>
      localFourier μ (chE E χ) Φ ((conjContinuousAddEquiv F E).toHomeomorph u) :=
    funext fun u => fts_apply χ μ Φ u
  rw [e]
  exact sb_comp _ (localFourier_mem_schwartzBruhat μ hχE hχE1 hΦ)

/- English proof (translation)
Establish `hχE : Continuous (chE E χ)` using `continuous_traceChar hχ hχ1`. Establish `hχE1 : chE E χ ≠ 1` using `traceChar_ne_one hχ hχ1`. Rewrite using `[fts_apply, ← localFourier_localFourier_selfDual hχE hχE1 hΦ z]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[localFourier]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Establish `e : conj F E u * z = conj F E (u * conj F E z)` using `by simp [map_mul]`. Use `show FTs χ (conj F E) (muE E χ) Φ u * (χ (Algebra.trace F E (u * conj F E z)) : ℂ) = localFourier (muE E χ) (chE E χ) Φ (conj F E u) * (χ (Algebra.trace F E (conj F E u * z)) : ℂ)`. Rewrite using `[fts_apply, e, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.trace_conj]`. Use `_ = ∫ v, localFourier (muE E χ) (chE E χ) Φ v * (chE E χ (v * z) : ℂ) ∂muE E χ := integral_conj (F := F) (muE E χ) (fun v => localFourier (muE E χ) (chE E χ) Φ v * (chE E χ (v * z) : ℂ))`.

Use `_ = _ := rfl`.
-/
theorem fts_fts {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) {Φ : E → ℂ}
    (hΦ : Φ ∈ SBE E) (z : E) :
    FTs χ (conj F E) (muE E χ) (FTs χ (conj F E) (muE E χ) Φ) z = Φ (-z) := by
  have hχE : Continuous (chE E χ) := continuous_traceChar hχ hχ1
  have hχE1 : chE E χ ≠ 1 := traceChar_ne_one hχ hχ1
  rw [fts_apply, ← localFourier_localFourier_selfDual hχE hχE1 hΦ z]
  calc localFourier (muE E χ) (chE E χ) (FTs χ (conj F E) (muE E χ) Φ) (conj F E z)
      = ∫ u, (fun v => localFourier (muE E χ) (chE E χ) Φ v * (chE E χ (v * z) : ℂ)) (conj F E u)
          ∂muE E χ := by
        rw [localFourier]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        have e : conj F E u * z = conj F E (u * conj F E z) := by simp [map_mul]
        show FTs χ (conj F E) (muE E χ) Φ u * (χ (Algebra.trace F E (u * conj F E z)) : ℂ) =
          localFourier (muE E χ) (chE E χ) Φ (conj F E u) * (χ (Algebra.trace F E (conj F E u * z)) : ℂ)
        rw [fts_apply, e, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.trace_conj]
    _ = ∫ v, localFourier (muE E χ) (chE E χ) Φ v * (chE E χ (v * z) : ℂ) ∂muE E χ :=
        integral_conj (F := F) (muE E χ) (fun v => localFourier (muE E χ) (chE E χ) Φ v * (chE E χ (v * z) : ℂ))
    _ = _ := rfl

omit [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
  [ValuativeRel E] [IsNonarchimedeanLocalField E] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [TopologicalSpace F] [TopologicalSpace E] in
/- English proof (translation)
Unfold `nsg`. Conclude with `if_pos ⟨1, by simp⟩`.
-/
theorem nsg_one : nsg E (1 : F) = 1 := by
  unfold nsg
  exact if_pos ⟨1, by simp⟩

omit [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
  [ValuativeRel E] [IsNonarchimedeanLocalField E] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [TopologicalSpace F] [TopologicalSpace E] in
/- English proof (translation)
Unfold `nsg`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem nsg_sq (x : F) : nsg E x * nsg E x = 1 := by
  unfold nsg
  split_ifs <;> norm_num

omit [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
  [ValuativeRel E] [IsNonarchimedeanLocalField E] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [TopologicalSpace F] [TopologicalSpace E] in
/- English proof (translation)
Establish `h` using `hη (Units.mk0 x hx * Units.mk0 y hy)`. Rewrite `h` using `[map_mul, Units.val_mul, hη, hη]`. Simplify using `using h.symm`.
-/
theorem nsg_mul {η : Fˣ →* ℂˣ} (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) {x y : F}
    (hx : x ≠ 0) (hy : y ≠ 0) : nsg E (x * y) = nsg E x * nsg E y := by
  have h := hη (Units.mk0 x hx * Units.mk0 y hy)
  rw [map_mul, Units.val_mul, hη, hη] at h
  simpa using h.symm

/- English proof (translation)
Simplify using `only [rWm, rW, if_pos h]`.
-/
theorem rWm_zero (χ : AddChar F Circle) (μ : Measure E) (lam : ℂ) {g : Matrix (Fin 2) (Fin 2) F}
    (h : g 1 0 = 0) (Φ : E → ℂ) (z : E) :
    rWm χ (conj F E) μ lam g Φ z = (χ (g 0 0 * g 0 1 * Algebra.norm F z) : ℂ) * nsg E (g 0 0) *
      ((modulus (g 0 0) : ℝ) : ℂ) * Φ (algebraMap F E (g 0 0) * z) := by
  simp only [rWm, rW, if_pos h]

/- English proof (translation)
Simplify using `only [rWm, rW, if_neg h]`.
-/
theorem rWm_ne (χ : AddChar F Circle) (μ : Measure E) (lam : ℂ) {g : Matrix (Fin 2) (Fin 2) F}
    (h : g 1 0 ≠ 0) (Φ : E → ℂ) (z : E) :
    rWm χ (conj F E) μ lam g Φ z = lam * nsg E (-(g 1 0)) * (((modulus (g 1 0) : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ u, (χ ((g 0 0 * Algebra.norm F z + g 1 1 * Algebra.norm F u -
        Algebra.trace F E (conj F E z * u)) / g 1 0) : ℂ) * Φ u ∂μ := by
  simp only [rWm, rW, if_neg h]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Rewrite using `[rWm_ne χ μ lam (by simp)]`. Simplify using `only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, modulus_neg_one, neg_neg, nsg_one]`. Simplify using `only [NNReal.coe_one, inv_one, Complex.ofReal_one, mul_one]`. Use `congr 1`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Establish `e : (0 * Algebra.norm F z + 0 * Algebra.norm F u - Algebra.trace F E (conj F E z * u)) / (-1 : F) = Algebra.trace F E (conj F E z * u)` using `by ring`. Use `show (χ _ : ℂ) * Φ u = Φ u * (χ _ : ℂ)`. Rewrite using `[e, mul_comm]`.
-/
theorem rW_w (χ : AddChar F Circle) (μ : Measure E) (lam : ℂ) (Φ : E → ℂ) :
    rWm χ (conj F E) μ lam !![0, 1; -1, 0] Φ = fun z => lam * FTs χ (conj F E) μ Φ z := by
  funext z
  rw [rWm_ne χ μ lam (by simp)]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, modulus_neg_one, neg_neg, nsg_one]
  simp only [NNReal.coe_one, inv_one, Complex.ofReal_one, mul_one]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have e : (0 * Algebra.norm F z + 0 * Algebra.norm F u - Algebra.trace F E (conj F E z * u)) / (-1 : F) =
      Algebra.trace F E (conj F E z * u) := by ring
  show (χ _ : ℂ) * Φ u = Φ u * (χ _ : ℂ)
  rw [e, mul_comm]

def GaussAt (χ : AddChar F Circle) (lam : ℂ) : Prop :=
  ∀ (a : Fˣ), ∀ Φ ∈ SBE E,
    ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTs χ (conj F E) (muE E χ) Φ u ∂muE E χ =
      lam * nsg E (a : F) * (((modulus (a : F) : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ

/- English proof (translation)
Establish `hN` using `continuous_norm_of (F := F) (E := E) hcont`. Establish `hlc` using `isLocallyConstant_char hχ hχ1`. Use `set f : E → ℂ := (valBall E 0 : Set E).indicator (fun _ => (1 : ℂ)) with hf`. Establish `hfS : f ∈ SBE E` using `indicator_valBall_zero_mem_schwartzBruhat (K := E)`. Use `set Φ : E → ℂ := fun z => (χ (-(Algebra.norm F z)) : ℂ) * f z with hΦd`.

Establish `hΦ : Φ ∈ SBE E` using `sb_mul (hlc.comp_continuous hN.neg) hfS`. Use `set I : ℂ := ∫ z, (χ (Algebra.norm F z) : ℂ) * Φ z ∂muE E χ with hI`. Establish `hI1 : I = (((muE E χ).real (valBall E 0 : Set E) : ℝ) : ℂ)`. Establish `e : ∀ z, (χ (Algebra.norm F z) : ℂ) * Φ z = f z` using `fun z => by`. Simplify using `only [hΦd]`.

Rewrite using `[← mul_assoc, ← chi_add, add_neg_cancel, AddChar.map_zero_eq_one]`. Simplify using the standard rewrite rules. Simplify using `only [hI, e, hf]`. Rewrite using `[integral_indicator_const (1 : ℂ) (measurableSet_valBall 0)]`. Simplify using the standard rewrite rules.

Establish `hI0 : I ≠ 0`. Rewrite using `[hI1]`. Establish `hpos : 0 < (muE E χ) (valBall E 0 : Set E)` using `(isOpen_valBall 0).measure_pos _ ⟨0, zero_mem _⟩`. Establish `hfin` using `(isCompact_valBall (K := E) 0).measure_lt_top (μ := muE E χ)`. Establish `: 0 < (muE E χ).real (valBall E 0 : Set E)` using `ENNReal.toReal_pos hpos.ne' hfin.ne`.

Conclude with `this.ne'` after adjusting the coercions. Establish `h1` using `hG 1 _ (fts_sbe hχ hχ1 (muE E χ) hΦ)`. Establish `h2` using `hG (-1) Φ hΦ`. Establish `hL : ∫ u, (χ (((1 : Fˣ) : F) * Algebra.norm F u) : ℂ) * FTs χ (conj F E) (muE E χ) (FTs χ (conj F E) (muE E χ) Φ) u ∂muE E χ = I`. Rewrite using `[hI, ← integral_neg_eq_self (fun z => (χ (Algebra.norm F z) : ℂ) * Φ z)]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Use `show _ * _ = _ * _`. Rewrite using `[fts_fts hχ hχ1 hΦ, norm_neg', Units.val_one, one_mul]`. Establish `hR1 : ∫ z, (χ (-(Algebra.norm F z) / ((1 : Fˣ) : F)) : ℂ) * FTs χ (conj F E) (muE E χ) Φ z ∂muE E χ = ∫ u, (χ (((-1 : Fˣ) : F) * Algebra.norm F u) : ℂ) * FTs χ (conj F E) (muE E χ) Φ u ∂muE E χ`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations.

Simplify using the standard rewrite rules. Establish `hR2 : ∫ z, (χ (-(Algebra.norm F z) / ((-1 : Fˣ) : F)) : ℂ) * Φ z ∂muE E χ = I`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite `h1` using `[hL, hR1, h2, hR2]`.

Simplify using `only [Units.val_one, Units.val_neg, modulus_neg_one, modulus_one, nsg_one] at h1`. Simplify using `only [NNReal.coe_one, inv_one, Complex.ofReal_one, mul_one] at h1`. Establish `: I * (lam * lam * nsg E (-1 : F) - 1) = 0` using `by linear_combination -h1`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `absurd h hI0`.

Take the linear combination `h`.
-/
theorem lam_sq {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    (hcont : Continuous (algebraMap F E)) {lam : ℂ} (hG : GaussAt (E := E) χ lam) :
    lam * lam * nsg E (-1 : F) = 1 := by
  have hN := continuous_norm_of (F := F) (E := E) hcont
  have hlc := isLocallyConstant_char hχ hχ1
  set f : E → ℂ := (valBall E 0 : Set E).indicator (fun _ => (1 : ℂ)) with hf
  have hfS : f ∈ SBE E := indicator_valBall_zero_mem_schwartzBruhat (K := E)
  set Φ : E → ℂ := fun z => (χ (-(Algebra.norm F z)) : ℂ) * f z with hΦd
  have hΦ : Φ ∈ SBE E := sb_mul (hlc.comp_continuous hN.neg) hfS
  set I : ℂ := ∫ z, (χ (Algebra.norm F z) : ℂ) * Φ z ∂muE E χ with hI
  have hI1 : I = (((muE E χ).real (valBall E 0 : Set E) : ℝ) : ℂ) := by
    have e : ∀ z, (χ (Algebra.norm F z) : ℂ) * Φ z = f z := fun z => by
      simp only [hΦd]
      rw [← mul_assoc, ← chi_add, add_neg_cancel, AddChar.map_zero_eq_one]
      simp
    simp only [hI, e, hf]
    rw [integral_indicator_const (1 : ℂ) (measurableSet_valBall 0)]
    simp
  have hI0 : I ≠ 0 := by
    rw [hI1]
    have hpos : 0 < (muE E χ) (valBall E 0 : Set E) :=
      (isOpen_valBall 0).measure_pos _ ⟨0, zero_mem _⟩
    have hfin := (isCompact_valBall (K := E) 0).measure_lt_top (μ := muE E χ)
    have : 0 < (muE E χ).real (valBall E 0 : Set E) := ENNReal.toReal_pos hpos.ne' hfin.ne
    exact_mod_cast this.ne'
  have h1 := hG 1 _ (fts_sbe hχ hχ1 (muE E χ) hΦ)
  have h2 := hG (-1) Φ hΦ
  have hL : ∫ u, (χ (((1 : Fˣ) : F) * Algebra.norm F u) : ℂ) *
      FTs χ (conj F E) (muE E χ) (FTs χ (conj F E) (muE E χ) Φ) u ∂muE E χ = I := by
    rw [hI, ← integral_neg_eq_self (fun z => (χ (Algebra.norm F z) : ℂ) * Φ z)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show _ * _ = _ * _
    rw [fts_fts hχ hχ1 hΦ, norm_neg', Units.val_one, one_mul]
  have hR1 : ∫ z, (χ (-(Algebra.norm F z) / ((1 : Fˣ) : F)) : ℂ) *
      FTs χ (conj F E) (muE E χ) Φ z ∂muE E χ =
      ∫ u, (χ (((-1 : Fˣ) : F) * Algebra.norm F u) : ℂ) * FTs χ (conj F E) (muE E χ) Φ u ∂muE E χ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp
  have hR2 : ∫ z, (χ (-(Algebra.norm F z) / ((-1 : Fˣ) : F)) : ℂ) * Φ z ∂muE E χ = I := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp
  rw [hL, hR1, h2, hR2] at h1
  simp only [Units.val_one, Units.val_neg, modulus_neg_one, modulus_one, nsg_one] at h1
  simp only [NNReal.coe_one, inv_one, Complex.ofReal_one, mul_one] at h1
  have : I * (lam * lam * nsg E (-1 : F) - 1) = 0 := by linear_combination -h1
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hI0
  · linear_combination h

/- English proof (translation)
Establish `h` using `lam_sq hχ hχ1 hcont hG`. Establish `hs` using `nsg_sq (E := E) (-1 : F)`. Take the linear combination `nsg E (-1 : F) * h - lam * lam * hs`.
-/
theorem lam_mul_self {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    (hcont : Continuous (algebraMap F E)) {lam : ℂ} (hG : GaussAt (E := E) χ lam) :
    lam * lam = nsg E (-1 : F) := by
  have h := lam_sq hχ hχ1 hcont hG
  have hs := nsg_sq (E := E) (-1 : F)
  linear_combination nsg E (-1 : F) * h - lam * lam * hs

/- English proof (translation)
Establish `hχE : Continuous (chE E χ)` using `continuous_traceChar hχ hχ1`. Establish `hχE1 : chE E χ ≠ 1` using `traceChar_ne_one hχ hχ1`. Establish `ha : a = (1 + b * c) / d`. Clear the denominators using the available nonvanishing facts. Take the linear combination `hdet`.

Use `set t : E := algebraMap F E d⁻¹ * z with ht`. Establish `hJt : conj F E t = algebraMap F E d⁻¹ * conj F E z`. Rewrite using `[ht, map_mul, conj_algebraMap]`. Use `set Ψ : E → ℂ := fun u => (χ (Algebra.trace F E (conj F E t * u)) : ℂ) * Φ u with hΨd`. Establish `hΨ : Ψ ∈ SBE E` using `sb_mul (f := fun u => (chE E χ (conj F E t * u) : ℂ)) ((isLocallyConstant_char hχE hχE1).comp_continuous (continuous_const.mul continuous_id)) hΦ`.

Establish `hA : d / c ≠ 0` using `div_ne_zero hd hc`. Establish `hG'` using `hG (Units.mk0 (d / c) hA) Ψ hΨ`. Simplify using `only [Units.val_mk0] at hG'`. Establish `hFT : ∀ v, FTs χ (conj F E) (muE E χ) Ψ v = FTs χ (conj F E) (muE E χ) Φ (v + t)`. Introduce `v`.

Simplify using `only [FTs]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Establish `e : conj F E (v + t) * u = conj F E t * u + conj F E v * u`. Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree.

Use `show (χ _ : ℂ) * Φ u * (χ _ : ℂ) = Φ u * (χ _ : ℂ)`. Rewrite using `[e, map_add, chi_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ∫ v, (χ ((a * Algebra.norm F z + d * Algebra.norm F v - Algebra.trace F E (conj F E z * v)) / c) : ℂ) * FTs χ (conj F E) (muE E χ) Φ v ∂muE E χ = (χ (b * Algebra.norm F z / d) : ℂ) * ∫ v, (χ (d / c * Algebra.norm F v) : ℂ) * FTs χ (conj F E) (muE E χ) Ψ v ∂muE E χ`. Rewrite using `[← integral_add_right_eq_self (fun v => (χ ((a * Algebra.norm F z + d * Algebra.norm F v - Algebra.trace F E (conj F E z * v)) / c) : ℂ) * FTs χ (conj F E) (muE E χ) Φ v) t, ← integral_const_mul]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Establish `hNt : Algebra.norm F t = d⁻¹ ^ 2 * Algebra.norm F z`. Rewrite using `[ht, map_mul, norm_algebraMap_eq_sq]`. Establish `hT1 : Algebra.trace F E (v * conj F E t) = d⁻¹ * Algebra.trace F E (conj F E z * v)`. Rewrite using `[hJt, show v * (algebraMap F E d⁻¹ * conj F E z) = algebraMap F E d⁻¹ * (conj F E z * v) by ring, trace_algebraMap_mul]`.

Establish `hT2 : Algebra.trace F E (conj F E z * (v + t)) = Algebra.trace F E (conj F E z * v) + d⁻¹ * (2 * Algebra.norm F z)`. Establish `e2 : conj F E z * t = algebraMap F E d⁻¹ * algebraMap F E (Algebra.norm F z)`. Rewrite using `[algebraMap_norm_eq_mul_conj (K := F), ht]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_add, map_add, e2, trace_algebraMap_mul, Algebra.trace_algebraMap, (Fact.out : Module.finrank F E = 2)]`.

Simplify using the standard rewrite rules. Establish `e : (a * Algebra.norm F z + d * Algebra.norm F (v + t) - Algebra.trace F E (conj F E z * (v + t))) / c = b * Algebra.norm F z / d + d / c * Algebra.norm F v`. Rewrite using `[norm_add, hNt, hT1, hT2, ha]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `show (χ _ : ℂ) * _ = _ * ((χ _ : ℂ) * _)`. Rewrite using `[e, chi_add, hFT]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∫ u, (χ ((-b * Algebra.norm F z + c * Algebra.norm F u - Algebra.trace F E (conj F E z * u)) / (-d)) : ℂ) * Φ u ∂muE E χ = (χ (b * Algebra.norm F z / d) : ℂ) * ∫ u, (χ (-(Algebra.norm F u) / (d / c)) : ℂ) * Ψ u ∂muE E χ`. Rewrite using `[← integral_const_mul]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Establish `hT : Algebra.trace F E (conj F E t * u) = d⁻¹ * Algebra.trace F E (conj F E z * u)`. Rewrite using `[hJt, mul_assoc, trace_algebraMap_mul]`. Establish `e : (-b * Algebra.norm F z + c * Algebra.norm F u - Algebra.trace F E (conj F E z * u)) / (-d) = b * Algebra.norm F z / d + (-(Algebra.norm F u) / (d / c) + Algebra.trace F E (conj F E t * u))`. Rewrite using `[hT]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hΨd, e, chi_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hMc : ((modulus c : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast modulus_ne_zero hc`.

Establish `hMd : ((modulus d : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast modulus_ne_zero hd`. Establish `hmod : modulus (d / c) = modulus d * (modulus c)⁻¹`. Rewrite using `[div_eq_mul_inv, modulus_mul, modulus_inv]`. Establish `hl` using `lam_mul_self hχ hχ1 hcont hG`. Establish `hs : nsg E (-c) * nsg E (d / c) = nsg E (-1 : F) * nsg E d`.

Rewrite using `[← nsg_mul hη (neg_ne_zero.2 hc) hA, ← nsg_mul hη (neg_ne_zero.2 one_ne_zero) hd]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hM` using `nsg_sq (E := E) (-1 : F)`. Establish `hfac : ∫ v, (χ ((a * Algebra.norm F z + d * Algebra.norm F v - Algebra.trace F E (conj F E z * v)) / c) : ℂ) * (lam * FTs χ (conj F E) (muE E χ) Φ v) ∂muE E χ = lam * ∫ v, (χ ((a * Algebra.norm F z + d * Algebra.norm F v - Algebra.trace F E (conj F E z * v)) / c) : ℂ) * FTs χ (co …`.

Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Use `show _ * (_ * _) = _ * (_ * _)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfac, h1, hG', h2, hmod]`.

Generalize the expression as in `(∫ u, (χ (-(Algebra.norm F u) / (d / c)) : ℂ) * Ψ u ∂muE E χ) = I`. Generalize the expression as in `(χ (b * Algebra.norm F z / d) : ℂ) = X`. Use `push_cast`. Establish `key : lam * lam * (nsg E (-c) * nsg E (d / c)) = nsg E d`. Rewrite using `[hs, hl, ← mul_assoc, hM, one_mul]`.

Establish `hMc' : (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) * (((modulus c : ℝ) : ℂ)) = 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Move the coercions through the operations in `at hMc'`. Simplify using `only [inv_inv, mul_inv]`.

Take the linear combination `(lam * X * I * ((modulus d : ℝ) : ℂ)⁻¹ * (((modulus c : ℝ) : ℂ)⁻¹ * ((modulus c : ℝ) : ℂ))) * key + (lam * X * I * ((modulus d : ℝ) : ℂ)⁻¹ * nsg E d) * hMc'`.
-/
theorem gauss_step {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    (hcont : Continuous (algebraMap F E)) {η : Fˣ →* ℂˣ}
    (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) {lam : ℂ} (hG : GaussAt (E := E) χ lam)
    {Φ : E → ℂ} (hΦ : Φ ∈ SBE E) {a b c d : F} (hc : c ≠ 0) (hd : d ≠ 0)
    (hdet : a * d - b * c = 1) (z : E) :
    lam * nsg E (-c) * (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ v, (χ ((a * Algebra.norm F z + d * Algebra.norm F v -
        Algebra.trace F E (conj F E z * v)) / c) : ℂ) *
          (lam * FTs χ (conj F E) (muE E χ) Φ v) ∂muE E χ =
    lam * nsg E d * (((modulus d : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ u, (χ ((-b * Algebra.norm F z + c * Algebra.norm F u -
        Algebra.trace F E (conj F E z * u)) / (-d)) : ℂ) * Φ u ∂muE E χ := by
  have hχE : Continuous (chE E χ) := continuous_traceChar hχ hχ1
  have hχE1 : chE E χ ≠ 1 := traceChar_ne_one hχ hχ1
  have ha : a = (1 + b * c) / d := by
    field_simp
    linear_combination hdet
  set t : E := algebraMap F E d⁻¹ * z with ht
  have hJt : conj F E t = algebraMap F E d⁻¹ * conj F E z := by
    rw [ht, map_mul, conj_algebraMap]
  set Ψ : E → ℂ := fun u => (χ (Algebra.trace F E (conj F E t * u)) : ℂ) * Φ u with hΨd
  have hΨ : Ψ ∈ SBE E :=
    sb_mul (f := fun u => (chE E χ (conj F E t * u) : ℂ))
      ((isLocallyConstant_char hχE hχE1).comp_continuous (continuous_const.mul continuous_id)) hΦ
  have hA : d / c ≠ 0 := div_ne_zero hd hc
  have hG' := hG (Units.mk0 (d / c) hA) Ψ hΨ
  simp only [Units.val_mk0] at hG'
  have hFT : ∀ v, FTs χ (conj F E) (muE E χ) Ψ v = FTs χ (conj F E) (muE E χ) Φ (v + t) := by
    intro v
    simp only [FTs]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have e : conj F E (v + t) * u = conj F E t * u + conj F E v * u := by
      rw [map_add]
      ring
    show (χ _ : ℂ) * Φ u * (χ _ : ℂ) = Φ u * (χ _ : ℂ)
    rw [e, map_add, chi_add]
    ring
  have h1 : ∫ v, (χ ((a * Algebra.norm F z + d * Algebra.norm F v -
        Algebra.trace F E (conj F E z * v)) / c) : ℂ) * FTs χ (conj F E) (muE E χ) Φ v ∂muE E χ =
      (χ (b * Algebra.norm F z / d) : ℂ) * ∫ v, (χ (d / c * Algebra.norm F v) : ℂ) *
        FTs χ (conj F E) (muE E χ) Ψ v ∂muE E χ := by
    rw [← integral_add_right_eq_self (fun v => (χ ((a * Algebra.norm F z + d * Algebra.norm F v -
        Algebra.trace F E (conj F E z * v)) / c) : ℂ) * FTs χ (conj F E) (muE E χ) Φ v) t,
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have hNt : Algebra.norm F t = d⁻¹ ^ 2 * Algebra.norm F z := by
      rw [ht, map_mul, norm_algebraMap_eq_sq]
    have hT1 : Algebra.trace F E (v * conj F E t) = d⁻¹ * Algebra.trace F E (conj F E z * v) := by
      rw [hJt, show v * (algebraMap F E d⁻¹ * conj F E z) =
        algebraMap F E d⁻¹ * (conj F E z * v) by ring, trace_algebraMap_mul]
    have hT2 : Algebra.trace F E (conj F E z * (v + t)) =
        Algebra.trace F E (conj F E z * v) + d⁻¹ * (2 * Algebra.norm F z) := by
      have e2 : conj F E z * t = algebraMap F E d⁻¹ * algebraMap F E (Algebra.norm F z) := by
        rw [algebraMap_norm_eq_mul_conj (K := F), ht]
        ring
      rw [mul_add, map_add, e2, trace_algebraMap_mul, Algebra.trace_algebraMap,
        (Fact.out : Module.finrank F E = 2)]
      simp
    have e : (a * Algebra.norm F z + d * Algebra.norm F (v + t) -
        Algebra.trace F E (conj F E z * (v + t))) / c =
        b * Algebra.norm F z / d + d / c * Algebra.norm F v := by
      rw [norm_add, hNt, hT1, hT2, ha]
      field_simp
      ring
    show (χ _ : ℂ) * _ = _ * ((χ _ : ℂ) * _)
    rw [e, chi_add, hFT]
    ring
  have h2 : ∫ u, (χ ((-b * Algebra.norm F z + c * Algebra.norm F u -
        Algebra.trace F E (conj F E z * u)) / (-d)) : ℂ) * Φ u ∂muE E χ =
      (χ (b * Algebra.norm F z / d) : ℂ) * ∫ u, (χ (-(Algebra.norm F u) / (d / c)) : ℂ) * Ψ u ∂muE E χ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hT : Algebra.trace F E (conj F E t * u) = d⁻¹ * Algebra.trace F E (conj F E z * u) := by
      rw [hJt, mul_assoc, trace_algebraMap_mul]
    have e : (-b * Algebra.norm F z + c * Algebra.norm F u -
        Algebra.trace F E (conj F E z * u)) / (-d) =
        b * Algebra.norm F z / d + (-(Algebra.norm F u) / (d / c) +
          Algebra.trace F E (conj F E t * u)) := by
      rw [hT]
      field_simp
      ring
    simp only [hΨd, e, chi_add]
    ring
  have hMc : ((modulus c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hc
  have hMd : ((modulus d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hd
  have hmod : modulus (d / c) = modulus d * (modulus c)⁻¹ := by
    rw [div_eq_mul_inv, modulus_mul, modulus_inv]
  have hl := lam_mul_self hχ hχ1 hcont hG
  have hs : nsg E (-c) * nsg E (d / c) = nsg E (-1 : F) * nsg E d := by
    rw [← nsg_mul hη (neg_ne_zero.2 hc) hA, ← nsg_mul hη (neg_ne_zero.2 one_ne_zero) hd]
    congr 1
    field_simp
  have hM := nsg_sq (E := E) (-1 : F)
  have hfac : ∫ v, (χ ((a * Algebra.norm F z + d * Algebra.norm F v -
        Algebra.trace F E (conj F E z * v)) / c) : ℂ) *
          (lam * FTs χ (conj F E) (muE E χ) Φ v) ∂muE E χ =
      lam * ∫ v, (χ ((a * Algebra.norm F z + d * Algebra.norm F v -
        Algebra.trace F E (conj F E z * v)) / c) : ℂ) * FTs χ (conj F E) (muE E χ) Φ v ∂muE E χ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show _ * (_ * _) = _ * (_ * _)
    ring
  rw [hfac, h1, hG', h2, hmod]
  generalize (∫ u, (χ (-(Algebra.norm F u) / (d / c)) : ℂ) * Ψ u ∂muE E χ) = I
  generalize (χ (b * Algebra.norm F z / d) : ℂ) = X
  push_cast
  have key : lam * lam * (nsg E (-c) * nsg E (d / c)) = nsg E d := by
    rw [hs, hl, ← mul_assoc, hM, one_mul]
  have hMc' : (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) * (((modulus c : ℝ) : ℂ)) = 1 := by
    push_cast
    field_simp
  push_cast at hMc'
  simp only [inv_inv, mul_inv]
  linear_combination (lam * X * I * ((modulus d : ℝ) : ℂ)⁻¹ * (((modulus c : ℝ) : ℂ)⁻¹ * ((modulus c : ℝ) : ℂ))) * key +
    (lam * X * I * ((modulus d : ℝ) : ℂ)⁻¹ * nsg E d) * hMc'

/- English proof (translation)
Establish `e00 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 0 0 = -g 0 1`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e01 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 0 1 = g 0 0`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e10 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 1 0 = -g 1 1`.

Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e11 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 1 1 = g 1 0`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`. Establish `hd2 : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1` using `by rw [← Matrix.det_fin_two]; exact hg`. Establish `hl` using `lam_mul_self hχ hχ1 hcont hG`.

Rewrite using `[rW_w]`. Use function extensionality and compare the values at `z`. Distinguish the cases in `hd : g 1 1 = 0`. Establish `hbc : g 0 1 * g 1 0 = -1` using `by rw [hd] at hd2; linear_combination -hd2`. Establish `hb : g 0 1 ≠ 0` using `fun h => by rw [h] at hbc; simp at hbc`.

Establish `hc : g 1 0 ≠ 0` using `fun h => by rw [h] at hbc; simp at hbc`. Establish `hcb : g 1 0 = -(g 0 1)⁻¹` using `by field_simp; linear_combination hbc`. Establish `hinv : ∫ u, FTs χ (conj F E) (muE E χ) Φ u * (χ (Algebra.trace F E (conj F E (algebraMap F E (g 0 1) * z) * u)) : ℂ) ∂muE E χ = Φ (-(algebraMap F E (g 0 1) * z))` using `fts_fts hχ hχ1 hΦ _`. Rewrite using `[rWm_zero χ _ lam (by rw [e10, hd, neg_zero]), rWm_ne χ _ lam hc, e00, e01, hd, modulus_neg']`. Establish `e1 : ∫ u, (χ ((g 0 0 * Algebra.norm F z + 0 * Algebra.norm F u - Algebra.trace F E (conj F E z * u)) / g 1 0) : ℂ) * (lam * FTs χ (conj F E) (muE E χ) Φ u) ∂muE E χ = lam * ((χ (-g 0 1 * g 0 0 * Algebra.norm F z) : ℂ) * ∫ u, FTs χ (conj F E) (muE E χ) Φ u * (χ (Algebra.trace F E …`.

Rewrite using `[← integral_const_mul, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Establish `hT : Algebra.trace F E (conj F E (algebraMap F E (g 0 1) * z) * u) = g 0 1 * Algebra.trace F E (conj F E z * u)`. Rewrite using `[map_mul (conj F E), conj_algebraMap, mul_assoc, trace_algebraMap_mul]`. Establish `e : (g 0 0 * Algebra.norm F z + 0 * Algebra.norm F u - Algebra.trace F E (conj F E z * u)) / g 1 0 = -g 0 1 * g 0 0 * Algebra.norm F z + Algebra.trace F E (conj F E (algebraMap F E (g 0 1) * z) * u)`.

Rewrite using `[hT, hcb]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `show (χ _ : ℂ) * (_ * _) = _ * (_ * (_ * _))`. Rewrite using `[e, chi_add]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hm : modulus (g 1 0) = (modulus (g 0 1))⁻¹`. Rewrite using `[hcb, modulus_neg', modulus_inv]`. Establish `hneg : -(algebraMap F E (g 0 1) * z) = algebraMap F E (-g 0 1) * z` using `by simp`. Establish `hs1 : nsg E (-(g 1 0)) * nsg E (g 0 1) = 1`.

Rewrite using `[← nsg_mul hη (neg_ne_zero.2 hc) hb, show -(g 1 0) * g 0 1 = 1 by linear_combination -hbc, nsg_one]`. Establish `hs2 : nsg E (-g 0 1) = nsg E (-1 : F) * nsg E (g 0 1)`. Rewrite using `[← nsg_mul hη (neg_ne_zero.2 one_ne_zero) hb]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hB` using `nsg_sq (E := E) (g 0 1)`. Establish `hs3 : nsg E (-(g 1 0)) = nsg E (g 0 1)` using `by linear_combination nsg E (g 0 1) * hs1 - nsg E (-(g 1 0)) * hB`. Rewrite using `[e1, hinv, hm, hneg, hs3, hs2, ← hl]`. Use `push_cast`. Simplify using `only [inv_inv]`.

Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hc : g 1 0 = 0`. Establish `had : g 0 0 * g 1 1 = 1` using `by rw [hc] at hd2; linear_combination hd2`. Establish `ha : g 0 0 ≠ 0` using `fun h => by rw [h] at had; simp at had`. Establish `hda : g 1 1 = (g 0 0)⁻¹` using `by field_simp; linear_combination had`.

Establish `hFT : FTs χ (conj F E) (muE E χ) Φ (algebraMap F E (g 0 0) * z) = ∫ u, Φ u * (χ (Algebra.trace F E (conj F E (algebraMap F E (g 0 0) * z) * u)) : ℂ) ∂muE E χ` using `rfl`. Rewrite using `[rWm_ne χ _ lam (by rw [e10]; exact neg_ne_zero.mpr hd), rWm_zero χ _ lam hc, e00, e10, e11, modulus_neg', hFT, hc]`. Establish `hs : nsg E (- -(g 1 1)) = nsg E (g 0 0)`. Establish `h1 : nsg E (g 1 1) * nsg E (g 0 0) = 1`. Rewrite using `[← nsg_mul hη hd ha, mul_comm, had, nsg_one]`.

Establish `hB` using `nsg_sq (E := E) (g 0 0)`. Rewrite using `[neg_neg]`. Take the linear combination `nsg E (g 0 0) * h1 - nsg E (g 1 1) * hB`. Establish `e1 : ∫ u, (χ ((-g 0 1 * Algebra.norm F z + 0 * Algebra.norm F u - Algebra.trace F E (conj F E z * u)) / -(g 1 1)) : ℂ) * Φ u ∂muE E χ = (χ (g 0 0 * g 0 1 * Algebra.norm F z) : ℂ) * ∫ u, Φ u * (χ (Algebra.trace F E (conj F E (algebraMap F E (g 0 0) * z) * u)) : ℂ) ∂muE E χ`. Rewrite using `[← integral_const_mul]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Establish `hT : Algebra.trace F E (conj F E (algebraMap F E (g 0 0) * z) * u) = g 0 0 * Algebra.trace F E (conj F E z * u)`. Rewrite using `[map_mul (conj F E), conj_algebraMap, mul_assoc, trace_algebraMap_mul]`. Establish `e : (-g 0 1 * Algebra.norm F z + 0 * Algebra.norm F u - Algebra.trace F E (conj F E z * u)) / -(g 1 1) = g 0 0 * g 0 1 * Algebra.norm F z + Algebra.trace F E (conj F E (algebraMap F E (g 0 0) * z) * u)`. Rewrite using `[hT, hda]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `show (χ _ : ℂ) * _ = _ * (_ * _)`. Rewrite using `[e, chi_add]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, hs, hda, modulus_inv]`. Use `push_cast`. Simplify using `only [inv_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[rWm_ne χ _ lam (by rw [e10]; exact neg_ne_zero.mpr hd), rWm_ne χ _ lam hc, e00, e10, e11, modulus_neg', neg_neg]`.

Conclude with `(gauss_step hχ hχ1 hcont hη hG hΦ hc hd hd2 z).symm`.
-/
theorem rep_w {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    (hcont : Continuous (algebraMap F E)) {η : Fˣ →* ℂˣ}
    (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) {lam : ℂ} (hG : GaussAt (E := E) χ lam)
    {g : Matrix (Fin 2) (Fin 2) F} (hg : g.det = 1) {Φ : E → ℂ} (hΦ : Φ ∈ SBE E) :
    rWm χ (conj F E) (muE E χ) lam (g * !![0, 1; -1, 0]) Φ =
      rWm χ (conj F E) (muE E χ) lam g (rWm χ (conj F E) (muE E χ) lam !![0, 1; -1, 0] Φ) := by
  have e00 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 0 0 = -g 0 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 0 1 = g 0 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 1 0 = -g 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 1 1 = g 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hd2 : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hg
  have hl := lam_mul_self hχ hχ1 hcont hG
  rw [rW_w]
  funext z
  by_cases hd : g 1 1 = 0
  · have hbc : g 0 1 * g 1 0 = -1 := by rw [hd] at hd2; linear_combination -hd2
    have hb : g 0 1 ≠ 0 := fun h => by rw [h] at hbc; simp at hbc
    have hc : g 1 0 ≠ 0 := fun h => by rw [h] at hbc; simp at hbc
    have hcb : g 1 0 = -(g 0 1)⁻¹ := by field_simp; linear_combination hbc
    have hinv : ∫ u, FTs χ (conj F E) (muE E χ) Φ u *
        (χ (Algebra.trace F E (conj F E (algebraMap F E (g 0 1) * z) * u)) : ℂ) ∂muE E χ =
        Φ (-(algebraMap F E (g 0 1) * z)) := fts_fts hχ hχ1 hΦ _
    rw [rWm_zero χ _ lam (by rw [e10, hd, neg_zero]), rWm_ne χ _ lam hc, e00, e01, hd, modulus_neg']
    have e1 : ∫ u, (χ ((g 0 0 * Algebra.norm F z + 0 * Algebra.norm F u -
        Algebra.trace F E (conj F E z * u)) / g 1 0) : ℂ) *
          (lam * FTs χ (conj F E) (muE E χ) Φ u) ∂muE E χ =
        lam * ((χ (-g 0 1 * g 0 0 * Algebra.norm F z) : ℂ) * ∫ u, FTs χ (conj F E) (muE E χ) Φ u *
          (χ (Algebra.trace F E (conj F E (algebraMap F E (g 0 1) * z) * u)) : ℂ) ∂muE E χ) := by
      rw [← integral_const_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      have hT : Algebra.trace F E (conj F E (algebraMap F E (g 0 1) * z) * u) =
          g 0 1 * Algebra.trace F E (conj F E z * u) := by
        rw [map_mul (conj F E), conj_algebraMap, mul_assoc, trace_algebraMap_mul]
      have e : (g 0 0 * Algebra.norm F z + 0 * Algebra.norm F u -
          Algebra.trace F E (conj F E z * u)) / g 1 0 =
          -g 0 1 * g 0 0 * Algebra.norm F z +
            Algebra.trace F E (conj F E (algebraMap F E (g 0 1) * z) * u) := by
        rw [hT, hcb]
        field_simp
        ring
      show (χ _ : ℂ) * (_ * _) = _ * (_ * (_ * _))
      rw [e, chi_add]
      ring
    have hm : modulus (g 1 0) = (modulus (g 0 1))⁻¹ := by
      rw [hcb, modulus_neg', modulus_inv]
    have hneg : -(algebraMap F E (g 0 1) * z) = algebraMap F E (-g 0 1) * z := by simp
    have hs1 : nsg E (-(g 1 0)) * nsg E (g 0 1) = 1 := by
      rw [← nsg_mul hη (neg_ne_zero.2 hc) hb, show -(g 1 0) * g 0 1 = 1 by linear_combination -hbc,
        nsg_one]
    have hs2 : nsg E (-g 0 1) = nsg E (-1 : F) * nsg E (g 0 1) := by
      rw [← nsg_mul hη (neg_ne_zero.2 one_ne_zero) hb]
      congr 1
      ring
    have hB := nsg_sq (E := E) (g 0 1)
    have hs3 : nsg E (-(g 1 0)) = nsg E (g 0 1) := by linear_combination nsg E (g 0 1) * hs1 - nsg E (-(g 1 0)) * hB
    rw [e1, hinv, hm, hneg, hs3, hs2, ← hl]
    push_cast
    simp only [inv_inv]
    ring
  · by_cases hc : g 1 0 = 0
    · have had : g 0 0 * g 1 1 = 1 := by rw [hc] at hd2; linear_combination hd2
      have ha : g 0 0 ≠ 0 := fun h => by rw [h] at had; simp at had
      have hda : g 1 1 = (g 0 0)⁻¹ := by field_simp; linear_combination had
      have hFT : FTs χ (conj F E) (muE E χ) Φ (algebraMap F E (g 0 0) * z) =
          ∫ u, Φ u * (χ (Algebra.trace F E (conj F E (algebraMap F E (g 0 0) * z) * u)) : ℂ) ∂muE E χ := rfl
      rw [rWm_ne χ _ lam (by rw [e10]; exact neg_ne_zero.mpr hd), rWm_zero χ _ lam hc, e00, e10, e11,
        modulus_neg', hFT, hc]
      have hs : nsg E (- -(g 1 1)) = nsg E (g 0 0) := by
        have h1 : nsg E (g 1 1) * nsg E (g 0 0) = 1 := by
          rw [← nsg_mul hη hd ha, mul_comm, had, nsg_one]
        have hB := nsg_sq (E := E) (g 0 0)
        rw [neg_neg]
        linear_combination nsg E (g 0 0) * h1 - nsg E (g 1 1) * hB
      have e1 : ∫ u, (χ ((-g 0 1 * Algebra.norm F z + 0 * Algebra.norm F u -
          Algebra.trace F E (conj F E z * u)) / -(g 1 1)) : ℂ) * Φ u ∂muE E χ =
          (χ (g 0 0 * g 0 1 * Algebra.norm F z) : ℂ) * ∫ u, Φ u *
            (χ (Algebra.trace F E (conj F E (algebraMap F E (g 0 0) * z) * u)) : ℂ) ∂muE E χ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        have hT : Algebra.trace F E (conj F E (algebraMap F E (g 0 0) * z) * u) =
            g 0 0 * Algebra.trace F E (conj F E z * u) := by
          rw [map_mul (conj F E), conj_algebraMap, mul_assoc, trace_algebraMap_mul]
        have e : (-g 0 1 * Algebra.norm F z + 0 * Algebra.norm F u -
            Algebra.trace F E (conj F E z * u)) / -(g 1 1) =
            g 0 0 * g 0 1 * Algebra.norm F z +
              Algebra.trace F E (conj F E (algebraMap F E (g 0 0) * z) * u) := by
          rw [hT, hda]
          field_simp
          ring
        show (χ _ : ℂ) * _ = _ * (_ * _)
        rw [e, chi_add]
        ring
      rw [e1, hs, hda, modulus_inv]
      push_cast
      simp only [inv_inv]
      ring
    · rw [rWm_ne χ _ lam (by rw [e10]; exact neg_ne_zero.mpr hd), rWm_ne χ _ lam hc, e00, e10, e11,
        modulus_neg', neg_neg]
      exact (gauss_step hχ hχ1 hcont hη hG hΦ hc hd hd2 z).symm

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη g hg Φ hΦ`. Use `haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)`. Use `haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.WeilSB.valuativeExtension_of_continuous hcont`. Use `haveI : Algebra.IsSeparable F E := inferInstance`.

Establish `hσc : σ = conj F E` using `(eq_one_or_eq_conj σ).resolve_left hσ`. Substitute `hσc` using the available equality. Take `⟨γ, hγ⟩` from `GlobalTheory.T.weil_gauss_sum_existence_hypothesis F χ hχ hχ1 E hfr hcont _ hσ η hη`. Establish `hl : γ = lamE E χ η` using `GlobalTheory.T.weil_gauss_constant_hypothesis F χ hχ hχ1 E hfr hcont _ hσ η hη γ hγ`. Substitute `hl` using the available equality.

Conclude with `rep_w hχ hχ1 hcont hη hγ hg hΦ`.
-/
theorem wRepW : Ad3.K.GL2LocalData.WRepW := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη g hg Φ hΦ
  haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.WeilSB.valuativeExtension_of_continuous hcont
  haveI : Algebra.IsSeparable F E := inferInstance
  have hσc : σ = conj F E := (eq_one_or_eq_conj σ).resolve_left hσ
  subst hσc
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.weil_gauss_sum_existence_hypothesis F χ hχ hχ1 E hfr hcont _ hσ η hη
  have hl : γ = lamE E χ η := GlobalTheory.T.weil_gauss_constant_hypothesis F χ hχ hχ1 E hfr hcont _ hσ η hη γ hγ
  subst hl
  exact rep_w hχ hχ1 hcont hη hγ hg hΦ

end GlobalTheory.CompanionTheory.WeilRepW
