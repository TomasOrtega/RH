import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open MeasureTheory Matrix Filter Topology
open GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GLnLocal (integralGL mem_integralGL_iff)
open GroundTheory.Automorphic.GodementSectionLocal (box mem_box isCompact_box isClopen_box modPow modPow_mul modPow_add schwartzBruhat2 slice localSection localZeta_mul_right vecMul_zero_cons)
open scoped ValuativeRel ENNReal ComplexConjugate
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RankinSelberg.Trilinear

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Simplify `modPow_mul (a : F) (b : F) s` using `[mp, modPow]`.
-/
theorem mp_mul (a b : Fˣ) (s : ℂ) : mp (a * b) s = mp a s * mp b s := by
  simpa [mp, modPow] using modPow_mul (a : F) (b : F) s

/- English proof (translation)
The claim follows from `modPow_add a.ne_zero s t`.
-/
theorem mp_add (a : Fˣ) (s t : ℂ) : mp a (s + t) = mp a s * mp a t :=
  modPow_add a.ne_zero s t

/- English proof (translation)
Establish `h : (0 : ℝ) < (modulus (a : F) : ℝ)` using `by exact_mod_cast modulus_pos a.ne_zero`. Simplify `Complex.norm_cpow_eq_rpow_re_of_pos h s` using `[mp]`.
-/
theorem norm_mp (a : Fˣ) (s : ℂ) : ‖mp a s‖ = (modulus (a : F) : ℝ) ^ s.re := by
  have h : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  simpa [mp] using Complex.norm_cpow_eq_rpow_re_of_pos h s

/- English proof (translation)
Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]`. Simplify using `only [dt, Matrix.vecMul, dotProduct, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dt_vecMul (r r' : Fin 2 → F) (κ : GL (Fin 2) F) :
    dt (r ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)) (r' ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)) =
      ((GeneralLinearGroup.det κ : Fˣ) : F) * dt r r' := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [dt, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

/- English proof (translation)
Simplify using `only [dt, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dt_smul_right (t : F) (r r' : Fin 2 → F) : dt r (t • r') = t * dt r r' := by
  simp only [dt, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[chF, hx]`. Establish `h : (u : F) * x ≠ 0` using `mul_ne_zero u.ne_zero hx`. Establish `e : Units.mk0 ((u : F) * x) h = u * Units.mk0 x hx` using `by ext; simp`. Simplify using `only [chF, dif_neg hx, dif_neg h, e, map_mul, Units.val_mul, mp_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem chF_unit_mul (c : Fˣ →* ℂˣ) (s : ℂ) (u : Fˣ) (x : F) :
    chF c s ((u : F) * x) = ((c u : ℂˣ) : ℂ) * mp u s * chF c s x := by
  by_cases hx : x = 0
  · simp [chF, hx]
  · have h : (u : F) * x ≠ 0 := mul_ne_zero u.ne_zero hx
    have e : Units.mk0 ((u : F) * x) h = u * Units.mk0 x hx := by ext; simp
    simp only [chF, dif_neg hx, dif_neg h, e, map_mul, Units.val_mul, mp_mul]
    ring

/- English proof (translation)
Establish `hν : ((ν t : ℂˣ) : ℂ) * (((ν t)⁻¹ : ℂˣ) : ℂ) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Simplify using `only [Kr, dt_smul_right, chF_unit_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]`. Take the linear combination `((c t : ℂˣ) : ℂ) * ((c t : ℂˣ) : ℂ) * mp t (s - 1) * mp t (s - 1) * chF (ν * c) (s - 1) (dt r₁ r₂) * chF (ν⁻¹ * c) (s - 1) (dt r₃ r₂) * chF c⁻¹ (-s) (dt r₁ r₃) * hν`.
-/
theorem Kr_smul (ν c : Fˣ →* ℂˣ) (s : ℂ) (t : Fˣ) (r₁ r₂ r₃ : Fin 2 → F) :
    Kr ν c s r₁ ((t : F) • r₂) r₃ =
      ((c t : ℂˣ) : ℂ) * ((c t : ℂˣ) : ℂ) * mp t (s - 1) * mp t (s - 1) * Kr ν c s r₁ r₂ r₃ := by
  have hν : ((ν t : ℂˣ) : ℂ) * (((ν t)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Kr, dt_smul_right, chF_unit_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
  linear_combination ((c t : ℂˣ) : ℂ) * ((c t : ℂˣ) : ℂ) * mp t (s - 1) * mp t (s - 1) *
    chF (ν * c) (s - 1) (dt r₁ r₂) * chF (ν⁻¹ * c) (s - 1) (dt r₃ r₂) * chF c⁻¹ (-s) (dt r₁ r₃) * hν

/- English proof (translation)
Use `set d : Fˣ := GeneralLinearGroup.det κ with hd`. Establish `hν : ((ν d : ℂˣ) : ℂ) * (((ν d)⁻¹ : ℂˣ) : ℂ) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hc : ((c d : ℂˣ) : ℂ) * (((c d)⁻¹ : ℂˣ) : ℂ) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Simplify using `only [Kr, dt_vecMul, ← hd, chF_unit_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]`. Use `set A := chF (ν * c) (s - 1) (dt r₁ r₂)`. Use `set B := chF (ν⁻¹ * c) (s - 1) (dt r₃ r₂)`. Use `set D := chF c⁻¹ (-s) (dt r₁ r₃)`. Take the linear combination `(((c d : ℂˣ) : ℂ) * ((c d : ℂˣ) : ℂ) * (((c d)⁻¹ : ℂˣ) : ℂ) * mp d (s - 1) * mp d (s - 1) * mp d (-s) * A * B * D) * hν + (((c d : ℂˣ) : ℂ) * mp d (s - 1) * mp d (s - 1) * mp d (-s) * A * B * D) * hc`.
-/
theorem Kr_vecMul (ν c : Fˣ →* ℂˣ) (s : ℂ) (κ : GL (Fin 2) F) (r₁ r₂ r₃ : Fin 2 → F) :
    Kr ν c s (r₁ ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)) (r₂ ᵥ* (κ : Matrix (Fin 2) (Fin 2) F))
        (r₃ ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)) =
      ((c (GeneralLinearGroup.det κ) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det κ) (s - 1) *
        mp (GeneralLinearGroup.det κ) (s - 1) * mp (GeneralLinearGroup.det κ) (-s) * Kr ν c s r₁ r₂ r₃ := by
  set d : Fˣ := GeneralLinearGroup.det κ with hd
  have hν : ((ν d : ℂˣ) : ℂ) * (((ν d)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hc : ((c d : ℂˣ) : ℂ) * (((c d)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Kr, dt_vecMul, ← hd, chF_unit_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
  set A := chF (ν * c) (s - 1) (dt r₁ r₂)
  set B := chF (ν⁻¹ * c) (s - 1) (dt r₃ r₂)
  set D := chF c⁻¹ (-s) (dt r₁ r₃)
  linear_combination (((c d : ℂˣ) : ℂ) * ((c d : ℂˣ) : ℂ) * (((c d)⁻¹ : ℂˣ) : ℂ) * mp d (s - 1) * mp d (s - 1) * mp d (-s) * A * B * D) * hν +
    (((c d : ℂˣ) : ℂ) * mp d (s - 1) * mp d (s - 1) * mp d (-s) * A * B * D) * hc

/- English proof (translation)
Use extensionality with `j`. Simplify using `[Matrix.vecMul, dotProduct, Fin.sum_univ_two]`.
-/
theorem zero_one_vecMul_eq_smul (z : F) (A : Matrix (Fin 2) (Fin 2) F) :
    ![0, z] ᵥ* A = z • (![0, 1] ᵥ* A) := by
  ext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/- English proof (translation)
Take `⟨h1, h2⟩` from `(GLnLocal.mem_integralGL_iff F 2).1 hκ`. Establish `key : ∀ g : GL (Fin 2) F, (∀ i j, g i j ∈ 𝒪[F]) → modulus ((GeneralLinearGroup.det g : Fˣ) : F) ≤ 1`. Introduce `g hg`. Rewrite using `[modulus_le_one_iff, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]`. Conclude with `sub_mem (mul_mem (hg 0 0) (hg 1 1)) (mul_mem (hg 0 1) (hg 1 0))`.

Establish `a` using `key κ h1`. Establish `b` using `key κ⁻¹ h2`. Rewrite `b` using `[map_inv, Units.val_inv_eq_inv_val, modulus_inv]`. Establish `hpos` using `modulus_pos (GeneralLinearGroup.det κ : Fˣ).ne_zero`. Conclude with `le_antisymm a ((inv_le_one₀ hpos).1 b)`.
-/
theorem modulus_det_of_mem {κ : GL (Fin 2) F} (hκ : κ ∈ integralGL F 2) :
    modulus ((GeneralLinearGroup.det κ : Fˣ) : F) = 1 := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hκ
  have key : ∀ g : GL (Fin 2) F, (∀ i j, g i j ∈ 𝒪[F]) → modulus ((GeneralLinearGroup.det g : Fˣ) : F) ≤ 1 := by
    intro g hg
    rw [modulus_le_one_iff, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    exact sub_mem (mul_mem (hg 0 0) (hg 1 1)) (mul_mem (hg 0 1) (hg 1 0))
  have a := key κ h1
  have b := key κ⁻¹ h2
  rw [map_inv, Units.val_inv_eq_inv_val, modulus_inv] at b
  have hpos := modulus_pos (GeneralLinearGroup.det κ : Fˣ).ne_zero
  exact le_antisymm a ((inv_le_one₀ hpos).1 b)

/- English proof (translation)
Rewrite using `[mp, modulus_det_of_mem hκ]`. Simplify using the standard rewrite rules.
-/
theorem mp_det_of_mem {κ : GL (Fin 2) F} (hκ : κ ∈ integralGL F 2) (s : ℂ) :
    mp (GeneralLinearGroup.det κ) s = 1 := by
  rw [mp, modulus_det_of_mem hκ]
  simp

def rowHomeo (κ : GL (Fin 2) F) : (Fin 2 → F) ≃ₜ (Fin 2 → F) where
  toFun r := r ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)
  invFun r := r ᵥ* ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  left_inv r := by
    simp only [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  right_inv r := by
    simp only [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  continuous_toFun := Continuous.matrix_vecMul continuous_id continuous_const
  continuous_invFun := Continuous.matrix_vecMul continuous_id continuous_const

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem rowHomeo_apply (κ : GL (Fin 2) F) (r : Fin 2 → F) :
    rowHomeo κ r = r ᵥ* (κ : Matrix (Fin 2) (Fin 2) F) := rfl

/- English proof (translation)
Establish `hH : (m2 ψ).IsAddHaarMeasure` using `by unfold m2; infer_instance`. Set `e : (Fin 2 → F) ≃+ (Fin 2 → F)` to `{ (rowHomeo κ).toEquiv with map_add' := fun x y => by simp [Matrix.add_vecMul] }`. Set `e' : (Fin 2 → F) ≃ₜ+ (Fin 2 → F)` to `{ e with continuous_toFun := (rowHomeo κ).continuous continuous_invFun := (rowHomeo κ).symm.continuous }`. Establish `hH' : (Measure.map (rowHomeo κ) (m2 ψ)).IsAddHaarMeasure` using `e'.isAddHaarMeasure_map (m2 ψ)`. Establish `hc` using `Measure.isAddLeftInvariant_eq_smul (Measure.map (rowHomeo κ) (m2 ψ)) (m2 ψ)`.

Use `set B : Set (Fin 2 → F) := (box F 0 : Set (Fin 2 → F))`. Establish `hBm : MeasurableSet B` using `(isClopen_box 0).isOpen.measurableSet`. Establish `hpre : (rowHomeo κ) ⁻¹' B = B`. Use extensionality with `x`. Conclude with `GodementSectionLocal.vecMul_mem_box_iff hκ 0 x`.

Establish `hval : Measure.map (rowHomeo κ) (m2 ψ) B = m2 ψ B`. Rewrite using `[Measure.map_apply (rowHomeo κ).continuous.measurable hBm, hpre]`. Establish `h0 : m2 ψ B ≠ 0` using `((isClopen_box 0).isOpen.measure_pos (m2 ψ) ⟨0, zero_mem _⟩).ne'`. Establish `hT : m2 ψ B ≠ ∞` using `(isCompact_box 0).measure_lt_top.ne`. Use `⟨(rowHomeo κ).continuous.measurable, ?_⟩` and prove the remaining obligations.

Rewrite `hval`, the goal using `[hc]`. Establish `hc1 : Measure.addHaarScalarFactor (Measure.map (rowHomeo κ) (m2 ψ)) (m2 ψ) = 1`. Rewrite `hval` using `[Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`. Use `(ENNReal.mul_eq_right h0 hT).1 hval` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Rewrite using `[hc1, one_smul]`.
-/
theorem measurePreserving_rowHomeo (ψ : AddChar F Circle) {κ : GL (Fin 2) F} (hκ : κ ∈ integralGL F 2) :
    MeasurePreserving (rowHomeo κ) (m2 ψ) (m2 ψ) := by
  have hH : (m2 ψ).IsAddHaarMeasure := by unfold m2; infer_instance
  let e : (Fin 2 → F) ≃+ (Fin 2 → F) :=
    { (rowHomeo κ).toEquiv with
      map_add' := fun x y => by simp [Matrix.add_vecMul] }
  let e' : (Fin 2 → F) ≃ₜ+ (Fin 2 → F) := { e with
    continuous_toFun := (rowHomeo κ).continuous
    continuous_invFun := (rowHomeo κ).symm.continuous }
  have hH' : (Measure.map (rowHomeo κ) (m2 ψ)).IsAddHaarMeasure :=
    e'.isAddHaarMeasure_map (m2 ψ)
  have hc := Measure.isAddLeftInvariant_eq_smul (Measure.map (rowHomeo κ) (m2 ψ)) (m2 ψ)
  set B : Set (Fin 2 → F) := (box F 0 : Set (Fin 2 → F))
  have hBm : MeasurableSet B := (isClopen_box 0).isOpen.measurableSet
  have hpre : (rowHomeo κ) ⁻¹' B = B := by
    ext x
    exact GodementSectionLocal.vecMul_mem_box_iff hκ 0 x
  have hval : Measure.map (rowHomeo κ) (m2 ψ) B = m2 ψ B := by
    rw [Measure.map_apply (rowHomeo κ).continuous.measurable hBm, hpre]
  have h0 : m2 ψ B ≠ 0 := ((isClopen_box 0).isOpen.measure_pos (m2 ψ) ⟨0, zero_mem _⟩).ne'
  have hT : m2 ψ B ≠ ∞ := (isCompact_box 0).measure_lt_top.ne
  refine ⟨(rowHomeo κ).continuous.measurable, ?_⟩
  rw [hc] at hval ⊢
  have hc1 : Measure.addHaarScalarFactor (Measure.map (rowHomeo κ) (m2 ψ)) (m2 ψ) = 1 := by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hval
    have := (ENNReal.mul_eq_right h0 hT).1 hval
    exact_mod_cast this
  rw [hc1, one_smul]

def polarMap (p : integralGL F 2 × Fˣ) : Fin 2 → F :=
  ![0, (p.2 : F)] ᵥ* (p.1.1 : Matrix (Fin 2) (Fin 2) F)

def polarMeas : Measure Fˣ :=
  (multHaar F).withDensity fun z => ENNReal.ofReal ((modulus (z : F) : ℝ) ^ 2)

/- English proof (translation)
Establish `hent : ∀ j, Measurable fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 1 j` using `fun j => Continuous.measurable (by fun_prop)`. Use `measurable_pi_iff.2 fun j => ?_` and prove the remaining obligations. Establish `: (fun p : integralGL F 2 × Fˣ => polarMap p j) = fun p => (p.2 : F) * (p.1.1 : Matrix (Fin 2) (Fin 2) F) 1 j`. Use function extensionality and compare the values at `p`. Simplify using `[polarMap, vecMul_zero_cons]`.

Rewrite using `[this]`. Conclude with `(measurableEmbedding_units_val.measurable.comp measurable_snd).mul ((hent j).comp (measurable_subtype_coe.comp measurable_fst))`.
-/
theorem measurable_polarMap [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)] :
    Measurable (polarMap (F := F)) := by
  have hent : ∀ j, Measurable fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 1 j := fun j =>
    Continuous.measurable (by fun_prop)
  refine measurable_pi_iff.2 fun j => ?_
  have : (fun p : integralGL F 2 × Fˣ => polarMap p j) =
      fun p => (p.2 : F) * (p.1.1 : Matrix (Fin 2) (Fin 2) F) 1 j := by
    funext p
    simp [polarMap, vecMul_zero_cons]
  rw [this]
  exact (measurableEmbedding_units_val.measurable.comp measurable_snd).mul
    ((hent j).comp (measurable_subtype_coe.comp measurable_fst))

/- English proof (translation)
The claim follows from `ENNReal.measurable_ofReal.comp ((measurable_coe_nnreal_real.comp (measurable_modulus.comp measurableEmbedding_units_val.measurable)).pow_const 2)`.
-/
theorem measurable_density : Measurable fun z : Fˣ => ENNReal.ofReal ((modulus (z : F) : ℝ) ^ 2) :=
  ENNReal.measurable_ofReal.comp
    ((measurable_coe_nnreal_real.comp (measurable_modulus.comp measurableEmbedding_units_val.measurable)).pow_const 2)

/- English proof (translation)
Set `f : F → ℂ` to `(valBall F n : Set F).indicator 1`. Establish `hf : f ∈ schwartzBruhat F` using `⟨GodementSectionLocal.isLocallyConstant_indicator ⟨isClosed_valBall n, isOpen_valBall n⟩ (IsLocallyConstant.const 1), HasCompactSupport.intro (isCompact_valBall n) fun x hx => Set.indicator_of_notMem hx _⟩`. Establish `hi` using `integrable_localZeta (χ := (1 : Fˣ →* ℂˣ)) (s := ((2 * σ : ℝ) : ℂ)) hf continuous_const (by simp [quasiCharExponent]; positivity)`. Use `lt_of_le_of_lt (le_of_eq ?_) hi.hasFiniteIntegral` and prove the remaining obligations. Use `lintegral_congr fun z => ?_` and prove the remaining obligations.

Establish `hz : (0 : ℝ) < (modulus (z : F) : ℝ)` using `by exact_mod_cast modulus_pos z.ne_zero`. Distinguish the cases in `h : (z : F) ∈ (valBall F n : Set F)`. Simplify using `only [f, Set.indicator_of_mem h, one_mul, Pi.one_apply, MonoidHom.one_apply, Units.val_one, mul_one]`. Rewrite using `[← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos hz]`. Simplify using the standard rewrite rules.

Simplify using `[f, Set.indicator_of_notMem h]`.
-/
theorem lintegral_ball_lt_top (n : ℤ) {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ z : Fˣ, (valBall F n : Set F).indicator (fun _ => (1 : ℝ≥0∞)) (z : F) *
      ENNReal.ofReal ((modulus (z : F) : ℝ) ^ (2 * σ)) ∂multHaar F < ∞ := by
  let f : F → ℂ := (valBall F n : Set F).indicator 1
  have hf : f ∈ schwartzBruhat F :=
    ⟨GodementSectionLocal.isLocallyConstant_indicator ⟨isClosed_valBall n, isOpen_valBall n⟩
      (IsLocallyConstant.const 1),
     HasCompactSupport.intro (isCompact_valBall n) fun x hx => Set.indicator_of_notMem hx _⟩
  have hi := integrable_localZeta (χ := (1 : Fˣ →* ℂˣ)) (s := ((2 * σ : ℝ) : ℂ)) hf continuous_const
    (by simp [quasiCharExponent]; positivity)
  refine lt_of_le_of_lt (le_of_eq ?_) hi.hasFiniteIntegral
  refine lintegral_congr fun z => ?_
  have hz : (0 : ℝ) < (modulus (z : F) : ℝ) := by exact_mod_cast modulus_pos z.ne_zero
  by_cases h : (z : F) ∈ (valBall F n : Set F)
  · simp only [f, Set.indicator_of_mem h, one_mul, Pi.one_apply, MonoidHom.one_apply, Units.val_one, mul_one]
    rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos hz]
    simp
  · simp [f, Set.indicator_of_notMem h]

def kfun (ψ : AddChar F Circle) (ν c : Fˣ →* ℂˣ) (s : ℂ) (B : Set (Fin 2 → F)) (r : Fin 2 → F) : ℝ≥0∞ :=
  ∫⁻ q in B ×ˢ B, ‖Kr ν c s q.1 r q.2‖ₑ ∂((m2 ψ).prod (m2 ψ))

/- English proof (translation)
Establish `h0 : (0 : ℝ) ≤ (modulus (t : F) : ℝ) ^ (s.re - 1) * (modulus (t : F) : ℝ) ^ (s.re - 1)`. Check the signs of the components of the expression. Rewrite using `[← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul h0, Kr_smul]`. Use `congr 1`. Simplify using `only [norm_mul, hc.2, norm_mp, one_mul, Complex.sub_re, Complex.one_re]`.
-/
theorem enorm_Kr_smul {ν c : Fˣ →* ℂˣ} (hc : IsUnit1 c) (s : ℂ) (t : Fˣ) (r₁ r₂ r₃ : Fin 2 → F) :
    ‖Kr ν c s r₁ ((t : F) • r₂) r₃‖ₑ =
      ENNReal.ofReal ((modulus (t : F) : ℝ) ^ (s.re - 1) * (modulus (t : F) : ℝ) ^ (s.re - 1)) *
        ‖Kr ν c s r₁ r₂ r₃‖ₑ := by
  have h0 : (0 : ℝ) ≤ (modulus (t : F) : ℝ) ^ (s.re - 1) * (modulus (t : F) : ℝ) ^ (s.re - 1) := by
    positivity
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul h0, Kr_smul]
  congr 1
  simp only [norm_mul, hc.2, norm_mp, one_mul, Complex.sub_re, Complex.one_re]

/- English proof (translation)
Simplify using `only [kfun, enorm_Kr_smul hc]`. Conclude with `lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`.
-/
theorem kfun_smul {ν c : Fˣ →* ℂˣ} (hc : IsUnit1 c) (ψ : AddChar F Circle) (s : ℂ) (B : Set (Fin 2 → F))
    (t : Fˣ) (r : Fin 2 → F) :
    kfun ψ ν c s B ((t : F) • r) =
      ENNReal.ofReal ((modulus (t : F) : ℝ) ^ (s.re - 1) * (modulus (t : F) : ℝ) ^ (s.re - 1)) *
        kfun ψ ν c s B r := by
  simp only [kfun, enorm_Kr_smul hc]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

def rowHomeo2 (κ : GL (Fin 2) F) : (Fin 2 → F) × (Fin 2 → F) ≃ₜ (Fin 2 → F) × (Fin 2 → F) :=
  (rowHomeo κ).prodCongr (rowHomeo κ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem rowHomeo2_apply (κ : GL (Fin 2) F) (q : (Fin 2 → F) × (Fin 2 → F)) :
    rowHomeo2 κ q = (q.1 ᵥ* (κ : Matrix (Fin 2) (Fin 2) F), q.2 ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)) := rfl

instance instSFinitePolarMeas : SFinite (polarMeas (F := F)) := by
  unfold polarMeas
  infer_instance

instance sigmaFinite_plane_measure (ψ : AddChar F Circle) : SigmaFinite (m2 ψ) := by
  unfold m2
  infer_instance

/- English proof (translation)
The claim follows from `(measurePreserving_rowHomeo ψ hκ).prod (measurePreserving_rowHomeo ψ hκ)`.
-/
theorem measurePreserving_rowHomeo2 (ψ : AddChar F Circle) {κ : GL (Fin 2) F} (hκ : κ ∈ integralGL F 2) :
    MeasurePreserving (rowHomeo2 κ) ((m2 ψ).prod (m2 ψ)) ((m2 ψ).prod (m2 ψ)) :=
  (measurePreserving_rowHomeo ψ hκ).prod (measurePreserving_rowHomeo ψ hκ)

/- English proof (translation)
Rewrite using `[Kr_vecMul]`. Simplify using `only [mp_det_of_mem hκ, mul_one]`.
-/
theorem Kr_row {ν c : Fˣ →* ℂˣ} (s : ℂ) {κ : GL (Fin 2) F} (hκ : κ ∈ integralGL F 2) (r₁ r₂ r₃ : Fin 2 → F) :
    Kr ν c s (r₁ ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)) (r₂ ᵥ* (κ : Matrix (Fin 2) (Fin 2) F))
        (r₃ ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)) =
      ((c (GeneralLinearGroup.det κ) : ℂˣ) : ℂ) * Kr ν c s r₁ r₂ r₃ := by
  rw [Kr_vecMul]
  simp only [mp_det_of_mem hκ, mul_one]

/- English proof (translation)
Establish `hpre : (rowHomeo2 κ) ⁻¹' ((box F n : Set (Fin 2 → F)) ×ˢ (box F n : Set (Fin 2 → F))) = (box F n : Set (Fin 2 → F)) ×ˢ (box F n : Set (Fin 2 → F))`. Use extensionality with `q`. Simplify using `[rowHomeo2, GodementSectionLocal.vecMul_mem_box_iff hκ]`. Establish `h` using `(measurePreserving_rowHomeo2 ψ hκ).setLIntegral_comp_preimage_emb (rowHomeo2 κ).measurableEmbedding (fun q => ‖Kr ν c s q.1 (![0, 1] ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)) q.2‖ₑ) ((box F n : Set (Fin 2 → F)) ×ˢ (box F n : Set (Fin 2 → F)))`. Rewrite `h` using `[hpre]`.

Simplify using `only [kfun]`. Rewrite using `[← h]`. Use `lintegral_congr fun q => ?_` and prove the remaining obligations. Simplify using `only [rowHomeo2_apply, Kr_row s hκ]`. Rewrite using `[← ofReal_norm, ← ofReal_norm, norm_mul, hc.2, one_mul]`.
-/
theorem kfun_row {ν c : Fˣ →* ℂˣ} (hc : IsUnit1 c) (ψ : AddChar F Circle) (s : ℂ) (n : ℤ)
    {κ : GL (Fin 2) F} (hκ : κ ∈ integralGL F 2) :
    kfun ψ ν c s (box F n) (![0, 1] ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)) =
      kfun ψ ν c s (box F n) ![0, 1] := by
  have hpre : (rowHomeo2 κ) ⁻¹' ((box F n : Set (Fin 2 → F)) ×ˢ (box F n : Set (Fin 2 → F))) =
      (box F n : Set (Fin 2 → F)) ×ˢ (box F n : Set (Fin 2 → F)) := by
    ext q
    simp [rowHomeo2, GodementSectionLocal.vecMul_mem_box_iff hκ]
  have h := (measurePreserving_rowHomeo2 ψ hκ).setLIntegral_comp_preimage_emb
    (rowHomeo2 κ).measurableEmbedding
    (fun q => ‖Kr ν c s q.1 (![0, 1] ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)) q.2‖ₑ)
    ((box F n : Set (Fin 2 → F)) ×ˢ (box F n : Set (Fin 2 → F)))
  rw [hpre] at h
  simp only [kfun]
  rw [← h]
  refine lintegral_congr fun q => ?_
  simp only [rowHomeo2_apply, Kr_row s hκ]
  rw [← ofReal_norm, ← ofReal_norm, norm_mul, hc.2, one_mul]

/- English proof (translation)
Use `(GodementSectionLocal.vecMul_mem_box_iff hκ n _).1 h` as an intermediate fact. Simplify using `using mem_box.1 this 1`.
-/
theorem mem_ball_of_polar {n : ℤ} {κ : GL (Fin 2) F} (hκ : κ ∈ integralGL F 2) {z : F}
    (h : ![0, z] ᵥ* (κ : Matrix (Fin 2) (Fin 2) F) ∈ box F n) : z ∈ valBall F n := by
  have := (GodementSectionLocal.vecMul_mem_box_iff hκ n _).1 h
  simpa using mem_box.1 this 1

/- English proof (translation)
Establish `hv : Measurable fun z : Fˣ => (z : F)` using `measurableEmbedding_units_val.measurable`. Establish `hmod : Measurable fun z : Fˣ => (modulus (z : F) : ℝ)` using `measurable_coe_nnreal_real.comp (measurable_modulus.comp hv)`. Establish `hgm : Measurable fun z : Fˣ => (valBall F n : Set F).indicator (fun _ => (1 : ℝ≥0∞)) (z : F) * ENNReal.ofReal ((modulus (z : F) : ℝ) ^ (σ - 1) * (modulus (z : F) : ℝ) ^ (σ - 1))`. Use `Measurable.mul ?_ ?_` and prove the remaining obligations. Conclude with `(measurable_const.indicator (measurableSet_valBall n)).comp hv`.

Conclude with `ENNReal.measurable_ofReal.comp ((hmod.pow_const _).mul (hmod.pow_const _))`. Rewrite using `[polarMeas, lintegral_withDensity_eq_lintegral_mul _ measurable_density hgm]`. Use `lt_of_le_of_lt (le_of_eq ?_) (lintegral_ball_lt_top (F := F) n hσ)` and prove the remaining obligations. Use `lintegral_congr fun z => ?_` and prove the remaining obligations. Establish `hz : (0 : ℝ) < (modulus (z : F) : ℝ)` using `by exact_mod_cast modulus_pos z.ne_zero`.

Establish `e : (modulus (z : F) : ℝ) ^ (2 * σ) = (modulus (z : F) : ℝ) ^ 2 * ((modulus (z : F) : ℝ) ^ (σ - 1) * (modulus (z : F) : ℝ) ^ (σ - 1))`. Rewrite using `[← Real.rpow_add hz, ← Real.rpow_natCast, ← Real.rpow_add hz]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Pi.mul_apply]`. Rewrite using `[e, ENNReal.ofReal_mul (p := (modulus (z : F) : ℝ) ^ 2) (by positivity)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lintegral_polar_lt_top (n : ℤ) {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ z : Fˣ, (valBall F n : Set F).indicator (fun _ => (1 : ℝ≥0∞)) (z : F) *
      ENNReal.ofReal ((modulus (z : F) : ℝ) ^ (σ - 1) * (modulus (z : F) : ℝ) ^ (σ - 1)) ∂polarMeas (F := F) < ∞ := by
  have hv : Measurable fun z : Fˣ => (z : F) := measurableEmbedding_units_val.measurable
  have hmod : Measurable fun z : Fˣ => (modulus (z : F) : ℝ) :=
    measurable_coe_nnreal_real.comp (measurable_modulus.comp hv)
  have hgm : Measurable fun z : Fˣ => (valBall F n : Set F).indicator (fun _ => (1 : ℝ≥0∞)) (z : F) *
      ENNReal.ofReal ((modulus (z : F) : ℝ) ^ (σ - 1) * (modulus (z : F) : ℝ) ^ (σ - 1)) := by
    refine Measurable.mul ?_ ?_
    · exact (measurable_const.indicator (measurableSet_valBall n)).comp hv
    · exact ENNReal.measurable_ofReal.comp ((hmod.pow_const _).mul (hmod.pow_const _))
  rw [polarMeas, lintegral_withDensity_eq_lintegral_mul _ measurable_density hgm]
  refine lt_of_le_of_lt (le_of_eq ?_) (lintegral_ball_lt_top (F := F) n hσ)
  refine lintegral_congr fun z => ?_
  have hz : (0 : ℝ) < (modulus (z : F) : ℝ) := by exact_mod_cast modulus_pos z.ne_zero
  have e : (modulus (z : F) : ℝ) ^ (2 * σ) = (modulus (z : F) : ℝ) ^ 2 *
      ((modulus (z : F) : ℝ) ^ (σ - 1) * (modulus (z : F) : ℝ) ^ (σ - 1)) := by
    rw [← Real.rpow_add hz, ← Real.rpow_natCast, ← Real.rpow_add hz]
    congr 1
    push_cast
    ring
  simp only [Pi.mul_apply]
  rw [e, ENNReal.ofReal_mul (p := (modulus (z : F) : ℝ) ^ 2) (by positivity)]
  ring

/- English proof (translation)
Take `⟨-, n₁, -, -, hn₁⟩` from `GodementSectionLocal.exists_invariant_of_mem_schwartzBruhat2 h₁`. Take `⟨-, n₂, -, -, hn₂⟩` from `GodementSectionLocal.exists_invariant_of_mem_schwartzBruhat2 hΨ`. Take `⟨-, n₃, -, -, hn₃⟩` from `GodementSectionLocal.exists_invariant_of_mem_schwartzBruhat2 h₃`. Use `set n : ℤ := min n₁ (min n₂ n₃) with hn`. Establish `hb₁ : ∀ x, φ₁ x ≠ 0 → x ∈ box F n` using `fun x hx => GodementSectionLocal.box_antitone (min_le_left _ _) (hn₁ x hx)`.

Establish `hb₂ : ∀ x, Ψ x ≠ 0 → x ∈ box F n` using `fun x hx => GodementSectionLocal.box_antitone ((min_le_right _ _).trans (min_le_left _ _)) (hn₂ x hx)`. Establish `hb₃ : ∀ x, φ₃ x ≠ 0 → x ∈ box F n` using `fun x hx => GodementSectionLocal.box_antitone ((min_le_right _ _).trans (min_le_right _ _)) (hn₃ x hx)`. Take `⟨M₁, hM₁⟩` from `h₁.1.continuous.bounded_above_of_compact_support h₁.2`. Take `⟨M₂, hM₂⟩` from `hΨ.1.continuous.bounded_above_of_compact_support hΨ.2`. Take `⟨M₃, hM₃⟩` from `h₃.1.continuous.bounded_above_of_compact_support h₃.2`.

Establish `hM₁0 : 0 ≤ M₁` using `(norm_nonneg _).trans (hM₁ 0)`. Establish `hM₂0 : 0 ≤ M₂` using `(norm_nonneg _).trans (hM₂ 0)`. Establish `hM₃0 : 0 ≤ M₃` using `(norm_nonneg _).trans (hM₃ 0)`. Use `set B : Set (Fin 2 → F) := (box F n : Set (Fin 2 → F)) with hB`. Establish `hBm : MeasurableSet B` using `(isClopen_box n).isOpen.measurableSet`.

Use `set A : ℝ≥0∞ := ENNReal.ofReal (M₂ * (M₁ * M₃)) with hA`. Establish `hmeas : Measurable (triI ν c s φ₁ Ψ φ₃)`. Establish `e₁ : Measurable φ₁` using `h₁.1.continuous.measurable`. Establish `e₂ : Measurable Ψ` using `hΨ.1.continuous.measurable`. Establish `e₃ : Measurable fun r => conj (φ₃ r)` using `(Complex.continuous_conj.comp h₃.1.continuous).measurable`.

Conclude with `(e₂.comp measurable_fst).mul (((e₁.comp (measurable_fst.comp measurable_snd)).mul (e₃.comp (measurable_snd.comp measurable_snd))).mul hm)`. Use `⟨hmeas.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Set `J : (Fin 2 → F) × (Fin 2 → F) × (Fin 2 → F) → ℝ≥0∞` to `(B ×ˢ (B ×ˢ B)).indicator fun p => ‖Kr ν c s p.2.1 p.1 p.2.2‖ₑ`. Establish `hJm : Measurable J` using `hm.enorm.indicator (hBm.prod (hBm.prod hBm))`. Establish `hle : ∀ p, ‖triI ν c s φ₁ Ψ φ₃ p‖ₑ ≤ A * J p`.

Introduce and unpack `⟨r₂, r₁, r₃⟩`. Distinguish the cases in `hp : (r₂, r₁, r₃) ∈ B ×ˢ (B ×ˢ B)`. Simplify using `only [J, Set.indicator_of_mem hp, triI, hA]`. Rewrite using `[← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations.

Simplify using `only [norm_mul, RCLike.norm_conj]`. Establish `hk` using `norm_nonneg (Kr ν c s r₁ r₂ r₃)`. Combine the equalities or inequalities in the displayed calculation. Establish `h0 : triI ν c s φ₁ Ψ φ₃ (r₂, r₁, r₃) = 0`. Simplify using `only [Set.mem_prod, not_and_or] at hp`.

Simplify using `only [triI]`. Assume the negation of the conclusion as `hne`. Establish `a₂ : Ψ r₂ ≠ 0` using `left_ne_zero_of_mul hne`. Establish `a₁ : φ₁ r₁ ≠ 0` using `left_ne_zero_of_mul (left_ne_zero_of_mul (right_ne_zero_of_mul hne))`. Establish `a₃ : conj (φ₃ r₃) ≠ 0` using `right_ne_zero_of_mul (left_ne_zero_of_mul (right_ne_zero_of_mul hne))`.

Establish `a₃' : φ₃ r₃ ≠ 0` using `fun h => a₃ (by simp [h])`. Break down `hp with h | h | h` into its components or cases. Conclude with `h (hb₂ _ a₂)`. Conclude with `h (hb₁ _ a₁)`. Conclude with `h (hb₃ _ a₃')`.

Simplify using `[h0]`. Establish `hJ : ∫⁻ p, J p ∂((m2 ψ).prod ((m2 ψ).prod (m2 ψ))) = ∫⁻ r, B.indicator (kfun ψ ν c s B) r ∂m2 ψ`. Rewrite using `[lintegral_prod _ hJm.aemeasurable]`. Use `lintegral_congr fun r => ?_` and prove the remaining obligations. Distinguish the cases in `hr : r ∈ B`.

Rewrite using `[Set.indicator_of_mem hr, kfun, ← lintegral_indicator (hBm.prod hBm)]`. Use `lintegral_congr fun q => ?_` and prove the remaining obligations. Distinguish the cases in `hq : q ∈ B ×ˢ B`. Establish `: (r, q) ∈ B ×ˢ (B ×ˢ B)` using `⟨hr, hq⟩`. Simplify using `only [J, Set.indicator_of_mem this, Set.indicator_of_mem hq]`.

Establish `: (r, q) ∉ B ×ˢ (B ×ˢ B)` using `fun h => hq h.2`. Simplify using `only [J, Set.indicator_of_notMem this, Set.indicator_of_notMem hq]`. Rewrite using `[Set.indicator_of_notMem hr]`. Establish `: ∀ q, J (r, q) = 0` using `fun q => Set.indicator_of_notMem (fun h => hr h.1) _`. Simplify using `[this]`.

Establish `hkm : Measurable (kfun ψ ν c s B)`. Establish `: Measurable fun x : (Fin 2 → F) × (Fin 2 → F) × (Fin 2 → F) => ‖Kr ν c s x.2.1 x.1 x.2.2‖ₑ` using `hm.enorm`. Conclude with `this.lintegral_prod_right'`. Establish `hGm : Measurable (B.indicator (kfun ψ ν c s B))` using `hkm.indicator hBm`. Establish `hH₀ : kfun ψ ν c s B ![0, 1] < ∞` using `(hi B (isCompact_box n)).hasFiniteIntegral`.

Set `g : Fˣ → ℝ≥0∞` to `fun z => (valBall F n : Set F).indicator (fun _ => (1 : ℝ≥0∞)) (z : F) * ENNReal.ofReal ((modulus (z : F) : ℝ) ^ (s.re - 1) * (modulus (z : F) : ℝ) ^ (s.re - 1))`. Establish `hgm : Measurable g`. Establish `hv : Measurable fun z : Fˣ => (z : F)` using `measurableEmbedding_units_val.measurable`. Establish `hmod : Measurable fun z : Fˣ => (modulus (z : F) : ℝ)` using `measurable_coe_nnreal_real.comp (measurable_modulus.comp hv)`. Use `Measurable.mul ?_ ?_` and prove the remaining obligations.

Conclude with `(measurable_const.indicator (measurableSet_valBall n)).comp hv`. Conclude with `ENNReal.measurable_ofReal.comp ((hmod.pow_const _).mul (hmod.pow_const _))`. Establish `hpt : ∀ p, B.indicator (kfun ψ ν c s B) (polarMap p) ≤ kfun ψ ν c s B ![0, 1] * g p.2`. Introduce and unpack `⟨κ, z⟩`. Distinguish the cases in `hr : polarMap (κ, z) ∈ B`.

Establish `hz : (z : F) ∈ (valBall F n : Set F)` using `mem_ball_of_polar κ.2 hr`. Rewrite using `[Set.indicator_of_mem hr]`. Simplify using `only [polarMap, g, Set.indicator_of_mem hz, one_mul]`. Rewrite using `[zero_one_vecMul_eq_smul, kfun_smul hc, kfun_row hc ψ s n κ.2, mul_comm]`. Rewrite using `[Set.indicator_of_notMem hr]`.

Conclude with `zero_le`. Establish `hint : ∫⁻ z, g z ∂polarMeas (F` using `F) < ∞ := lintegral_polar_lt_top n hs.1`. Establish `hfin : ∫⁻ r, B.indicator (kfun ψ ν c s B) r ∂m2 ψ < ∞`. Establish `e : ∫⁻ r, B.indicator (kfun ψ ν c s B) r ∂m2 ψ = C * ∫⁻ p, B.indicator (kfun ψ ν c s B) (polarMap p) ∂(m.prod (polarMeas (F` using `F))) := by conv_lhs => rw [h5]`. Rewrite using `[lintegral_smul_measure, lintegral_map hGm measurable_polarMap]`.

Both sides reduce to the same expression. Establish `e2 : ∫⁻ p : integralGL F 2 × Fˣ, kfun ψ ν c s B ![0, 1] * g p.2 ∂(m.prod (polarMeas (F` using `F))) = kfun ψ ν c s B ![0, 1] * ∫⁻ z, g z ∂polarMeas (F := F) := by`. Rewrite using `[lintegral_prod _ (by exact (measurable_const.mul (hgm.comp measurable_snd)).aemeasurable)]`. Simplify using `[lintegral_const_mul _ hgm]`. Rewrite using `[e]`.

Use `ENNReal.mul_lt_top ENNReal.coe_lt_top ?_` and prove the remaining obligations. Use `lt_of_le_of_lt (lintegral_mono hpt) ?_` and prove the remaining obligations. Rewrite using `[e2]`. Conclude with `ENNReal.mul_lt_top hH₀ hint`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[lintegral_const_mul _ hJm, hJ]`. Use `_ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin`.
-/
theorem integrable_triI [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]
    {ψ : AddChar F Circle} (m : Measure (integralGL F 2)) [IsProbabilityMeasure m] (C : NNReal)
    (h5 : m2 ψ = C • Measure.map (polarMap (F := F)) (m.prod (polarMeas (F := F))))
    {ν c : Fˣ →* ℂˣ} (hc : IsUnit1 c) {s : ℂ} (hs : Strip s)
    (hm : Measurable (fun p : (Fin 2 → F) × (Fin 2 → F) × (Fin 2 → F) => Kr ν c s p.2.1 p.1 p.2.2))
    (hi : ∀ B : Set (Fin 2 → F), IsCompact B → IntegrableOn
      (fun p : (Fin 2 → F) × (Fin 2 → F) => Kr ν c s p.1 ![0, 1] p.2) (B ×ˢ B) ((m2 ψ).prod (m2 ψ)))
    {φ₁ Ψ φ₃ : (Fin 2 → F) → ℂ} (h₁ : SB φ₁) (hΨ : SB Ψ) (h₃ : SB φ₃) :
    Integrable (triI ν c s φ₁ Ψ φ₃) ((m2 ψ).prod ((m2 ψ).prod (m2 ψ))) := by

  obtain ⟨-, n₁, -, -, hn₁⟩ := GodementSectionLocal.exists_invariant_of_mem_schwartzBruhat2 h₁
  obtain ⟨-, n₂, -, -, hn₂⟩ := GodementSectionLocal.exists_invariant_of_mem_schwartzBruhat2 hΨ
  obtain ⟨-, n₃, -, -, hn₃⟩ := GodementSectionLocal.exists_invariant_of_mem_schwartzBruhat2 h₃
  set n : ℤ := min n₁ (min n₂ n₃) with hn
  have hb₁ : ∀ x, φ₁ x ≠ 0 → x ∈ box F n := fun x hx =>
    GodementSectionLocal.box_antitone (min_le_left _ _) (hn₁ x hx)
  have hb₂ : ∀ x, Ψ x ≠ 0 → x ∈ box F n := fun x hx =>
    GodementSectionLocal.box_antitone ((min_le_right _ _).trans (min_le_left _ _)) (hn₂ x hx)
  have hb₃ : ∀ x, φ₃ x ≠ 0 → x ∈ box F n := fun x hx =>
    GodementSectionLocal.box_antitone ((min_le_right _ _).trans (min_le_right _ _)) (hn₃ x hx)
  obtain ⟨M₁, hM₁⟩ := h₁.1.continuous.bounded_above_of_compact_support h₁.2
  obtain ⟨M₂, hM₂⟩ := hΨ.1.continuous.bounded_above_of_compact_support hΨ.2
  obtain ⟨M₃, hM₃⟩ := h₃.1.continuous.bounded_above_of_compact_support h₃.2
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  have hM₃0 : 0 ≤ M₃ := (norm_nonneg _).trans (hM₃ 0)
  set B : Set (Fin 2 → F) := (box F n : Set (Fin 2 → F)) with hB
  have hBm : MeasurableSet B := (isClopen_box n).isOpen.measurableSet
  set A : ℝ≥0∞ := ENNReal.ofReal (M₂ * (M₁ * M₃)) with hA

  have hmeas : Measurable (triI ν c s φ₁ Ψ φ₃) := by
    have e₁ : Measurable φ₁ := h₁.1.continuous.measurable
    have e₂ : Measurable Ψ := hΨ.1.continuous.measurable
    have e₃ : Measurable fun r => conj (φ₃ r) :=
      (Complex.continuous_conj.comp h₃.1.continuous).measurable
    exact (e₂.comp measurable_fst).mul (((e₁.comp (measurable_fst.comp measurable_snd)).mul
      (e₃.comp (measurable_snd.comp measurable_snd))).mul hm)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩

  let J : (Fin 2 → F) × (Fin 2 → F) × (Fin 2 → F) → ℝ≥0∞ :=
    (B ×ˢ (B ×ˢ B)).indicator fun p => ‖Kr ν c s p.2.1 p.1 p.2.2‖ₑ
  have hJm : Measurable J := hm.enorm.indicator (hBm.prod (hBm.prod hBm))
  have hle : ∀ p, ‖triI ν c s φ₁ Ψ φ₃ p‖ₑ ≤ A * J p := by
    rintro ⟨r₂, r₁, r₃⟩
    by_cases hp : (r₂, r₁, r₃) ∈ B ×ˢ (B ×ˢ B)
    · simp only [J, Set.indicator_of_mem hp, triI, hA]
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [norm_mul, RCLike.norm_conj]
      have hk := norm_nonneg (Kr ν c s r₁ r₂ r₃)
      calc ‖Ψ r₂‖ * (‖φ₁ r₁‖ * ‖φ₃ r₃‖ * ‖Kr ν c s r₁ r₂ r₃‖)
          = ‖Ψ r₂‖ * (‖φ₁ r₁‖ * ‖φ₃ r₃‖) * ‖Kr ν c s r₁ r₂ r₃‖ := by ring
        _ ≤ M₂ * (M₁ * M₃) * ‖Kr ν c s r₁ r₂ r₃‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hM₂ _) (mul_le_mul (hM₁ _) (hM₃ _) (norm_nonneg _) hM₁0)
            (by positivity) hM₂0) hk
    · have h0 : triI ν c s φ₁ Ψ φ₃ (r₂, r₁, r₃) = 0 := by
        simp only [Set.mem_prod, not_and_or] at hp
        simp only [triI]
        by_contra hne
        have a₂ : Ψ r₂ ≠ 0 := left_ne_zero_of_mul hne
        have a₁ : φ₁ r₁ ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul (right_ne_zero_of_mul hne))
        have a₃ : conj (φ₃ r₃) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul (right_ne_zero_of_mul hne))
        have a₃' : φ₃ r₃ ≠ 0 := fun h => a₃ (by simp [h])
        rcases hp with h | h | h
        · exact h (hb₂ _ a₂)
        · exact h (hb₁ _ a₁)
        · exact h (hb₃ _ a₃')
      simp [h0]

  have hJ : ∫⁻ p, J p ∂((m2 ψ).prod ((m2 ψ).prod (m2 ψ))) = ∫⁻ r, B.indicator (kfun ψ ν c s B) r ∂m2 ψ := by
    rw [lintegral_prod _ hJm.aemeasurable]
    refine lintegral_congr fun r => ?_
    by_cases hr : r ∈ B
    · rw [Set.indicator_of_mem hr, kfun, ← lintegral_indicator (hBm.prod hBm)]
      refine lintegral_congr fun q => ?_
      by_cases hq : q ∈ B ×ˢ B
      · have : (r, q) ∈ B ×ˢ (B ×ˢ B) := ⟨hr, hq⟩
        simp only [J, Set.indicator_of_mem this, Set.indicator_of_mem hq]
      · have : (r, q) ∉ B ×ˢ (B ×ˢ B) := fun h => hq h.2
        simp only [J, Set.indicator_of_notMem this, Set.indicator_of_notMem hq]
    · rw [Set.indicator_of_notMem hr]
      have : ∀ q, J (r, q) = 0 := fun q =>
        Set.indicator_of_notMem (fun h => hr h.1) _
      simp [this]

  have hkm : Measurable (kfun ψ ν c s B) := by
    have : Measurable fun x : (Fin 2 → F) × (Fin 2 → F) × (Fin 2 → F) => ‖Kr ν c s x.2.1 x.1 x.2.2‖ₑ := hm.enorm
    exact this.lintegral_prod_right'
  have hGm : Measurable (B.indicator (kfun ψ ν c s B)) := hkm.indicator hBm
  have hH₀ : kfun ψ ν c s B ![0, 1] < ∞ := (hi B (isCompact_box n)).hasFiniteIntegral

  let g : Fˣ → ℝ≥0∞ := fun z => (valBall F n : Set F).indicator (fun _ => (1 : ℝ≥0∞)) (z : F) *
    ENNReal.ofReal ((modulus (z : F) : ℝ) ^ (s.re - 1) * (modulus (z : F) : ℝ) ^ (s.re - 1))
  have hgm : Measurable g := by
    have hv : Measurable fun z : Fˣ => (z : F) := measurableEmbedding_units_val.measurable
    have hmod : Measurable fun z : Fˣ => (modulus (z : F) : ℝ) :=
      measurable_coe_nnreal_real.comp (measurable_modulus.comp hv)
    refine Measurable.mul ?_ ?_
    · exact (measurable_const.indicator (measurableSet_valBall n)).comp hv
    · exact ENNReal.measurable_ofReal.comp ((hmod.pow_const _).mul (hmod.pow_const _))
  have hpt : ∀ p, B.indicator (kfun ψ ν c s B) (polarMap p) ≤ kfun ψ ν c s B ![0, 1] * g p.2 := by
    rintro ⟨κ, z⟩
    by_cases hr : polarMap (κ, z) ∈ B
    · have hz : (z : F) ∈ (valBall F n : Set F) := mem_ball_of_polar κ.2 hr
      rw [Set.indicator_of_mem hr]
      simp only [polarMap, g, Set.indicator_of_mem hz, one_mul]
      rw [zero_one_vecMul_eq_smul, kfun_smul hc, kfun_row hc ψ s n κ.2, mul_comm]
    · rw [Set.indicator_of_notMem hr]
      exact zero_le
  have hint : ∫⁻ z, g z ∂polarMeas (F := F) < ∞ := lintegral_polar_lt_top n hs.1
  have hfin : ∫⁻ r, B.indicator (kfun ψ ν c s B) r ∂m2 ψ < ∞ := by
    have e : ∫⁻ r, B.indicator (kfun ψ ν c s B) r ∂m2 ψ =
        C * ∫⁻ p, B.indicator (kfun ψ ν c s B) (polarMap p) ∂(m.prod (polarMeas (F := F))) := by
      conv_lhs => rw [h5]
      rw [lintegral_smul_measure, lintegral_map hGm measurable_polarMap]
      rfl
    have e2 : ∫⁻ p : integralGL F 2 × Fˣ, kfun ψ ν c s B ![0, 1] * g p.2 ∂(m.prod (polarMeas (F := F))) =
        kfun ψ ν c s B ![0, 1] * ∫⁻ z, g z ∂polarMeas (F := F) := by
      rw [lintegral_prod _ (by exact (measurable_const.mul (hgm.comp measurable_snd)).aemeasurable)]
      simp [lintegral_const_mul _ hgm]
    rw [e]
    refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
    refine lt_of_le_of_lt (lintegral_mono hpt) ?_
    rw [e2]
    exact ENNReal.mul_lt_top hH₀ hint
  calc ∫⁻ p, ‖triI ν c s φ₁ Ψ φ₃ p‖ₑ ∂((m2 ψ).prod ((m2 ψ).prod (m2 ψ)))
      ≤ ∫⁻ p, A * J p ∂((m2 ψ).prod ((m2 ψ).prod (m2 ψ))) := lintegral_mono hle
    _ = A * ∫⁻ r, B.indicator (kfun ψ ν c s B) r ∂m2 ψ := by
        rw [lintegral_const_mul _ hJm, hJ]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

def Iker (ψ : AddChar F Circle) (ν c : Fˣ →* ℂˣ) (s : ℂ) (φ₁ φ₃ : (Fin 2 → F) → ℂ) (r : Fin 2 → F) : ℂ :=
  ∫ q, φ₁ q.1 * conj (φ₃ q.2) * Kr ν c s q.1 r q.2 ∂((m2 ψ).prod (m2 ψ))

/- English proof (translation)
Simplify using `only [Iker, Kr_smul]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Iker_smul (ψ : AddChar F Circle) (ν c : Fˣ →* ℂˣ) (s : ℂ) (φ₁ φ₃ : (Fin 2 → F) → ℂ) (t : Fˣ)
    (r : Fin 2 → F) :
    Iker ψ ν c s φ₁ φ₃ ((t : F) • r) =
      ((c t : ℂˣ) : ℂ) * ((c t : ℂˣ) : ℂ) * mp t (s - 1) * mp t (s - 1) * Iker ψ ν c s φ₁ φ₃ r := by
  simp only [Iker, Kr_smul]
  rw [← integral_const_mul]
  congr 1
  funext q
  ring

/- English proof (translation)
Establish `h` using `(measurePreserving_rowHomeo2 ψ hκ).integral_comp (rowHomeo2 κ).measurableEmbedding (fun q => φ₁ q.1 * conj (φ₃ q.2) * Kr ν c s q.1 (![0, 1] ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)) q.2)`. Rewrite using `[Iker, ← h, ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [rowHomeo2_apply, Kr_row s hκ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem Iker_row (ψ : AddChar F Circle) (ν c : Fˣ →* ℂˣ) (s : ℂ) (φ₁ φ₃ : (Fin 2 → F) → ℂ)
    {κ : GL (Fin 2) F} (hκ : κ ∈ integralGL F 2) :
    Iker ψ ν c s φ₁ φ₃ (![0, 1] ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)) =
      ((c (GeneralLinearGroup.det κ) : ℂˣ) : ℂ) *
        ∫ q : (Fin 2 → F) × (Fin 2 → F), φ₁ (q.1 ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)) *
          conj (φ₃ (q.2 ᵥ* (κ : Matrix (Fin 2) (Fin 2) F))) * Kr ν c s q.1 ![0, 1] q.2
            ∂((m2 ψ).prod (m2 ψ)) := by
  have h := (measurePreserving_rowHomeo2 ψ hκ).integral_comp (rowHomeo2 κ).measurableEmbedding
    (fun q => φ₁ q.1 * conj (φ₃ q.2) * Kr ν c s q.1 (![0, 1] ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)) q.2)
  rw [Iker, ← h, ← integral_const_mul]
  congr 1
  funext q
  simp only [rowHomeo2_apply, Kr_row s hκ]
  ring

/- English proof (translation)
Establish `hu : ((μ₂ (GeneralLinearGroup.det κ) : ℂˣ) : ℂ) * conj ((μ₂ (GeneralLinearGroup.det κ) : ℂˣ) : ℂ) = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ₂.2]`. Simplify using the standard rewrite rules. Unfold `Av`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Establish `e₁` using `(h1 F ψ hψ μ₁ μ₂ φ₁ κ hφ₁).2.2.2 (dg2 a 1)`. Establish `e₃` using `(h1 F ψ hψ μ₁ μ₂ φ₃ κ hφ₃).2.2.2 (dg2 a 1)`. Rewrite using `[e₁, e₃, mp_det_of_mem hκ, mul_one (dg2 a 1)]`. Simplify using `only [mul_one, map_mul]`.

Take the linear combination `(W2 ψ μ₁ μ₂ (fun r => φ₁ (r ᵥ* (κ : Matrix (Fin 2) (Fin 2) F))) (dg2 a 1) * conj (W2 ψ μ₁ μ₂ (fun r => φ₃ (r ᵥ* (κ : Matrix (Fin 2) (Fin 2) F))) (dg2 a 1)) * ((c a : ℂˣ) : ℂ) * mp a (s - 1)) * hu`.
-/
theorem Av_row (h1 : Ad3.R.A1) {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ₁ μ₂ : Fˣ →* ℂˣ} (hμ₂ : IsUnit1 μ₂)
    {φ₁ φ₃ : (Fin 2 → F) → ℂ} (hφ₁ : SB φ₁) (hφ₃ : SB φ₃) (c : Fˣ →* ℂˣ) (s : ℂ)
    {κ : GL (Fin 2) F} (hκ : κ ∈ integralGL F 2) :
    Av (W2 ψ μ₁ μ₂ φ₁) (W2 ψ μ₁ μ₂ φ₃) c s κ =
      Av (W2 ψ μ₁ μ₂ fun r => φ₁ (r ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)))
        (W2 ψ μ₁ μ₂ fun r => φ₃ (r ᵥ* (κ : Matrix (Fin 2) (Fin 2) F))) c s 1 := by
  have hu : ((μ₂ (GeneralLinearGroup.det κ) : ℂˣ) : ℂ) * conj ((μ₂ (GeneralLinearGroup.det κ) : ℂˣ) : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ₂.2]
    simp
  unfold Av
  congr 1
  funext a
  have e₁ := (h1 F ψ hψ μ₁ μ₂ φ₁ κ hφ₁).2.2.2 (dg2 a 1)
  have e₃ := (h1 F ψ hψ μ₁ μ₂ φ₃ κ hφ₃).2.2.2 (dg2 a 1)
  rw [e₁, e₃, mp_det_of_mem hκ, mul_one (dg2 a 1)]
  simp only [mul_one, map_mul]
  linear_combination (W2 ψ μ₁ μ₂ (fun r => φ₁ (r ᵥ* (κ : Matrix (Fin 2) (Fin 2) F))) (dg2 a 1) *
    conj (W2 ψ μ₁ μ₂ (fun r => φ₃ (r ᵥ* (κ : Matrix (Fin 2) (Fin 2) F))) (dg2 a 1)) * ((c a : ℂˣ) : ℂ) * mp a (s - 1)) * hu

/- English proof (translation)
Rewrite using `[polarMeas, integral_withDensity_eq_integral_toReal_smul measurable_density (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), localZeta, ← integral_mul_const]`. Use `integral_congr_ae (ae_of_all _ fun z => ?_)` and prove the remaining obligations. Establish `hp : polarMap (κ, z) = (z : F) • (![0, 1] ᵥ* (κ.1 : Matrix (Fin 2) (Fin 2) F))` using `zero_one_vecMul_eq_smul _ _`. Establish `hsl : slice Ψ κ.1 (z : F) = Ψ (polarMap (κ, z))` using `rfl`. Establish `e : mp z (s - 1) * mp z (s - 1) * (((modulus (z : F) : ℝ) ^ 2 : ℝ) : ℂ) = ((modulus (z : F) : ℝ) : ℂ) ^ (2 * s)`.

Establish `h2 : (((modulus (z : F) : ℝ) ^ 2 : ℝ) : ℂ) = mp z 2`. Simplify using `[mp]`. Establish `h3 : ((modulus (z : F) : ℝ) : ℂ) ^ (2 * s) = mp z (2 * s)` using `rfl`. Rewrite using `[h2, h3, ← mp_add, ← mp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Complex.real_smul, hsl, ENNReal.toReal_ofReal (sq_nonneg (modulus (z : F) : ℝ))]`. Rewrite using `[← e, hp, Iker_smul]`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply, inv_inv, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_polar (ψ : AddChar F Circle) (ν c : Fˣ →* ℂˣ) (s : ℂ) (Ψ φ₁ φ₃ : (Fin 2 → F) → ℂ)
    (κ : integralGL F 2) :
    ∫ z, Ψ (polarMap (κ, z)) * Iker ψ ν c s φ₁ φ₃ (polarMap (κ, z)) ∂polarMeas (F := F) =
      localZeta (slice Ψ κ.1) (c * c⁻¹⁻¹) (2 * s) *
        Iker ψ ν c s φ₁ φ₃ (![0, 1] ᵥ* (κ.1 : Matrix (Fin 2) (Fin 2) F)) := by
  rw [polarMeas, integral_withDensity_eq_integral_toReal_smul measurable_density
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), localZeta, ← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  have hp : polarMap (κ, z) = (z : F) • (![0, 1] ᵥ* (κ.1 : Matrix (Fin 2) (Fin 2) F)) :=
    zero_one_vecMul_eq_smul _ _
  have hsl : slice Ψ κ.1 (z : F) = Ψ (polarMap (κ, z)) := rfl
  have e : mp z (s - 1) * mp z (s - 1) * (((modulus (z : F) : ℝ) ^ 2 : ℝ) : ℂ) =
      ((modulus (z : F) : ℝ) : ℂ) ^ (2 * s) := by
    have h2 : (((modulus (z : F) : ℝ) ^ 2 : ℝ) : ℂ) = mp z 2 := by
      simp [mp]
    have h3 : ((modulus (z : F) : ℝ) : ℂ) ^ (2 * s) = mp z (2 * s) := rfl
    rw [h2, h3, ← mp_add, ← mp_add]
    congr 1
    ring
  simp only [Complex.real_smul, hsl, ENNReal.toReal_ofReal (sq_nonneg (modulus (z : F) : ℝ))]
  rw [← e, hp, Iker_smul]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, inv_inv, Units.val_mul]
  ring

/- English proof (translation)
Introduce `h1 h3 h4 h5 F _ _ _ _ _ _ ψ hψ _ _ m _ _`. Take `⟨C3, hC3, h3'⟩` from `h3 F ψ hψ`. Take `⟨C5, hC5, h5'⟩` from `h5 F ψ hψ m`. Establish `hC5c : ((C5 : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hC5`. Use `⟨C3 / ((C5 : ℝ) : ℂ), div_ne_zero hC3 hC5c, ?_⟩` and prove the remaining obligations.

Introduce `μ₁ μ₂ c hμ₁ hμ₂ hc φ₁ φ₃ Ψ hφ₁ hφ₃ hΨ s hs`. Establish `hν : IsUnit1 (μ₂ * μ₁⁻¹)` using `⟨GodementSectionLocal.continuous_mul_inv hμ₂.1 hμ₁.1, fun x => by simp [hμ₁.2, hμ₂.2]⟩`. Take `⟨hKm, hKi⟩` from `h4 F ψ hψ (μ₂ * μ₁⁻¹) c hν hc s hs`. Establish `h5'' : m2 ψ = C5 • Measure.map (polarMap (F` using `F)) (m.prod (polarMeas (F := F))) := h5'`. Establish `hI : Integrable (triI (μ₂ * μ₁⁻¹) c s φ₁ Ψ φ₃) ((m2 ψ).prod ((m2 ψ).prod (m2 ψ)))` using `integrable_triI m C5 h5'' hc hs hKm hKi hφ₁ hΨ hφ₃`.

Use `⟨hI, ?_⟩` and prove the remaining obligations. Use `set I := Iker ψ (μ₂ * μ₁⁻¹) c s φ₁ φ₃ with hIdef`. Use `set G : (Fin 2 → F) → ℂ := fun r => Ψ r * I r with hG`. Establish `hfib : ∀ r, ∫ q, triI (μ₂ * μ₁⁻¹) c s φ₁ Ψ φ₃ (r, q) ∂((m2 ψ).prod (m2 ψ)) = G r` using `fun r => by`. Simplify using `only [hG, hIdef, Iker, triI]`.

Conclude with `integral_const_mul _ _`. Establish `hG1 : ∫ p, triI (μ₂ * μ₁⁻¹) c s φ₁ Ψ φ₃ p ∂((m2 ψ).prod ((m2 ψ).prod (m2 ψ))) = ∫ r, G r ∂m2 ψ`. Rewrite using `[integral_prod _ hI]`. Conclude with `integral_congr_ae (ae_of_all _ hfib)`. Establish `hGint : Integrable G (m2 ψ)`.

Use `hI.integral_prod_left` as an intermediate fact. Simplify `this` using `only [hfib]`. Establish `hmap : Measure.map (polarMap (F` using `F)) (m.prod (polarMeas (F := F))) = C5⁻¹ • m2 ψ := by conv_rhs => rw [h5'']`. Rewrite using `[smul_smul, inv_mul_cancel₀ hC5, one_smul]`. Establish `hGm : Integrable G (Measure.map (polarMap (F` using `F)) (m.prod (polarMeas (F := F)))) := by`.

Rewrite using `[hmap]`. Conclude with `hGint.smul_measure_nnreal`. Establish `hcomp : Integrable (fun p => G (polarMap p)) (m.prod (polarMeas (F` using `F))) := (integrable_map_measure hGm.aestronglyMeasurable measurable_polarMap.aemeasurable).1 hGm`. Establish `hG2 : ∫ r, G r ∂m2 ψ = ((C5 : ℝ) : ℂ) * ∫ p, G (polarMap p) ∂(m.prod (polarMeas (F` using `F))) := by conv_lhs => rw [h5'']`. Rewrite using `[integral_smul_nnreal_measure, integral_map measurable_polarMap.aemeasurable hGm.aestronglyMeasurable, NNReal.smul_def, Complex.real_smul]`.

Establish `hpt : ∀ κ : integralGL F 2, GodementSectionLocal.localSection c c⁻¹ s Ψ κ.1 * Av (W2 ψ μ₁ μ₂ φ₁) (W2 ψ μ₁ μ₂ φ₃) c s κ.1 = (C3 * gam ψ c⁻¹ (1 - s)) * ∫ z, G (polarMap (κ, z)) ∂polarMeas (F` using `F) := by`. Introduce `κ`. Establish `hm : GodementSectionLocal.modPow ((GeneralLinearGroup.det κ.1 : Fˣ) : F) s = 1` using `mp_det_of_mem κ.2 s`. Rewrite using `[Av_row h1 hψ hμ₂ hφ₁ hφ₃ c s κ.2, h3' μ₁ μ₂ c hμ₁ hμ₂ hc _ _ (h1 F ψ hψ μ₁ μ₂ φ₁ κ.1 hφ₁).1 (h1 F ψ hψ μ₁ μ₂ φ₃ κ.1 hφ₃).1 s hs]`. Simplify using `only [hG, hIdef]`.

Rewrite using `[integral_polar, Iker_row ψ _ c s φ₁ φ₃ κ.2, GodementSectionLocal.localSection, GodementSectionLocal.detU, hm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hZ : Zv m (W2 ψ μ₁ μ₂ φ₁) (W2 ψ μ₁ μ₂ φ₃) Ψ c s = (C3 * gam ψ c⁻¹ (1 - s)) * ∫ p, G (polarMap p) ∂(m.prod (polarMeas (F` using `F))) := by`. Rewrite using `[integral_prod _ hcomp, ← integral_const_mul]`. Conclude with `integral_congr_ae (ae_of_all _ hpt)`.

Rewrite using `[hG1, hG2, hZ]`. Clear the denominators using the available nonvanishing facts.
-/
theorem zv_eq_trilinear : Ad3.R.A1 → Ad3.R.A3 → Ad3.R.A4 → Ad3.R.A5 → Ad3.R.A6 := by
  intro h1 h3 h4 h5 F _ _ _ _ _ _ ψ hψ _ _ m _ _
  obtain ⟨C3, hC3, h3'⟩ := h3 F ψ hψ
  obtain ⟨C5, hC5, h5'⟩ := h5 F ψ hψ m
  have hC5c : ((C5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hC5
  refine ⟨C3 / ((C5 : ℝ) : ℂ), div_ne_zero hC3 hC5c, ?_⟩
  intro μ₁ μ₂ c hμ₁ hμ₂ hc φ₁ φ₃ Ψ hφ₁ hφ₃ hΨ s hs
  have hν : IsUnit1 (μ₂ * μ₁⁻¹) :=
    ⟨GodementSectionLocal.continuous_mul_inv hμ₂.1 hμ₁.1, fun x => by simp [hμ₁.2, hμ₂.2]⟩
  obtain ⟨hKm, hKi⟩ := h4 F ψ hψ (μ₂ * μ₁⁻¹) c hν hc s hs
  have h5'' : m2 ψ = C5 • Measure.map (polarMap (F := F)) (m.prod (polarMeas (F := F))) := h5'
  have hI : Integrable (triI (μ₂ * μ₁⁻¹) c s φ₁ Ψ φ₃) ((m2 ψ).prod ((m2 ψ).prod (m2 ψ))) :=
    integrable_triI m C5 h5'' hc hs hKm hKi hφ₁ hΨ hφ₃
  refine ⟨hI, ?_⟩
  set I := Iker ψ (μ₂ * μ₁⁻¹) c s φ₁ φ₃ with hIdef
  set G : (Fin 2 → F) → ℂ := fun r => Ψ r * I r with hG
  have hfib : ∀ r, ∫ q, triI (μ₂ * μ₁⁻¹) c s φ₁ Ψ φ₃ (r, q) ∂((m2 ψ).prod (m2 ψ)) = G r := fun r => by
    simp only [hG, hIdef, Iker, triI]
    exact integral_const_mul _ _
  have hG1 : ∫ p, triI (μ₂ * μ₁⁻¹) c s φ₁ Ψ φ₃ p ∂((m2 ψ).prod ((m2 ψ).prod (m2 ψ))) = ∫ r, G r ∂m2 ψ := by
    rw [integral_prod _ hI]
    exact integral_congr_ae (ae_of_all _ hfib)
  have hGint : Integrable G (m2 ψ) := by
    have := hI.integral_prod_left
    simpa only [hfib] using this
  have hmap : Measure.map (polarMap (F := F)) (m.prod (polarMeas (F := F))) = C5⁻¹ • m2 ψ := by
    conv_rhs => rw [h5'']
    rw [smul_smul, inv_mul_cancel₀ hC5, one_smul]
  have hGm : Integrable G (Measure.map (polarMap (F := F)) (m.prod (polarMeas (F := F)))) := by
    rw [hmap]
    exact hGint.smul_measure_nnreal
  have hcomp : Integrable (fun p => G (polarMap p)) (m.prod (polarMeas (F := F))) :=
    (integrable_map_measure hGm.aestronglyMeasurable measurable_polarMap.aemeasurable).1 hGm
  have hG2 : ∫ r, G r ∂m2 ψ = ((C5 : ℝ) : ℂ) * ∫ p, G (polarMap p) ∂(m.prod (polarMeas (F := F))) := by
    conv_lhs => rw [h5'']
    rw [integral_smul_nnreal_measure, integral_map measurable_polarMap.aemeasurable hGm.aestronglyMeasurable,
      NNReal.smul_def, Complex.real_smul]
  have hpt : ∀ κ : integralGL F 2,
      GodementSectionLocal.localSection c c⁻¹ s Ψ κ.1 * Av (W2 ψ μ₁ μ₂ φ₁) (W2 ψ μ₁ μ₂ φ₃) c s κ.1 =
        (C3 * gam ψ c⁻¹ (1 - s)) * ∫ z, G (polarMap (κ, z)) ∂polarMeas (F := F) := by
    intro κ
    have hm : GodementSectionLocal.modPow ((GeneralLinearGroup.det κ.1 : Fˣ) : F) s = 1 := mp_det_of_mem κ.2 s
    rw [Av_row h1 hψ hμ₂ hφ₁ hφ₃ c s κ.2,
      h3' μ₁ μ₂ c hμ₁ hμ₂ hc _ _ (h1 F ψ hψ μ₁ μ₂ φ₁ κ.1 hφ₁).1 (h1 F ψ hψ μ₁ μ₂ φ₃ κ.1 hφ₃).1 s hs]
    simp only [hG, hIdef]
    rw [integral_polar, Iker_row ψ _ c s φ₁ φ₃ κ.2, GodementSectionLocal.localSection,
      GodementSectionLocal.detU, hm]
    ring
  have hZ : Zv m (W2 ψ μ₁ μ₂ φ₁) (W2 ψ μ₁ μ₂ φ₃) Ψ c s =
      (C3 * gam ψ c⁻¹ (1 - s)) * ∫ p, G (polarMap p) ∂(m.prod (polarMeas (F := F))) := by
    rw [integral_prod _ hcomp, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ hpt)
  rw [hG1, hG2, hZ]
  field_simp

end GlobalTheory.CompanionTheory.RankinSelberg.Trilinear

end
