import Mathlib
import GroundTheory.LocalFields.LocalZeta
import GroundTheory.AutomorphicForms.GLnLocal

open MeasureTheory Matrix Filter Topology
open scoped NNReal ValuativeRel

namespace GroundTheory.Automorphic.GodementSectionLocal

open GroundTheory.LocalField

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

variable (F) in

def schwartzBruhat2 : Submodule ℂ ((Fin 2 → F) → ℂ) where
  carrier := {Φ | IsLocallyConstant Φ ∧ HasCompactSupport Φ}
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c _ hf := ⟨hf.1.comp (c • ·), hf.2.smul_left (f := fun _ ↦ c)⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_schwartzBruhat2 {Φ : (Fin 2 → F) → ℂ} :
    Φ ∈ schwartzBruhat2 F ↔ IsLocallyConstant Φ ∧ HasCompactSupport Φ := Iff.rfl

def slice (Φ : (Fin 2 → F) → ℂ) (g : GL (Fin 2) F) : F → ℂ :=
  fun t ↦ Φ (![0, t] ᵥ* (g : Matrix (Fin 2) (Fin 2) F))

/- English proof (translation)
Use extensionality with `j`. Simplify using `[Matrix.vecMul, dotProduct, Fin.sum_univ_two]`.
-/
theorem vecMul_zero_cons (t : F) (A : Matrix (Fin 2) (Fin 2) F) :
    ![0, t] ᵥ* A = fun j ↦ t * A 1 j := by
  ext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/- English proof (translation)
Establish `hrow : ∃ j, (g : Matrix (Fin 2) (Fin 2) F) 1 j ≠ 0`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hdet` using `(Matrix.GeneralLinearGroup.det g).ne_zero`. Rewrite `hdet` using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h 0, h 1]`.

Simplify using `at hdet`. Take `⟨j, hj⟩` from `hrow`. Establish `hcont : Continuous fun t : F ↦ ![0, t] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)`. Repeatedly rewrite using `[vecMul_zero_cons]`. Conclude with `continuous_pi fun i ↦ continuous_id.mul continuous_const`.

Establish `hemb : IsClosedEmbedding fun t : F ↦ ![0, t] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)` using `Function.LeftInverse.isClosedEmbedding (f := fun y : Fin 2 → F ↦ y j / (g : Matrix (Fin 2) (Fin 2) F) 1 j) (fun t ↦ by simp [vecMul_zero_cons, hj]) ((continuous_apply j).div_const _) hcont`. Conclude with `⟨hΦ.1.comp_continuous hcont, hΦ.2.comp_isClosedEmbedding hemb⟩`.
-/
theorem slice_mem {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) (g : GL (Fin 2) F) :
    slice Φ g ∈ schwartzBruhat F := by
  have hrow : ∃ j, (g : Matrix (Fin 2) (Fin 2) F) 1 j ≠ 0 := by
    by_contra h
    push Not at h
    have hdet := (Matrix.GeneralLinearGroup.det g).ne_zero
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h 0, h 1] at hdet
    simp at hdet
  obtain ⟨j, hj⟩ := hrow
  have hcont : Continuous fun t : F ↦ ![0, t] ᵥ* (g : Matrix (Fin 2) (Fin 2) F) := by
    simp_rw [vecMul_zero_cons]
    exact continuous_pi fun i ↦ continuous_id.mul continuous_const
  have hemb : IsClosedEmbedding fun t : F ↦ ![0, t] ᵥ* (g : Matrix (Fin 2) (Fin 2) F) :=
    Function.LeftInverse.isClosedEmbedding
      (f := fun y : Fin 2 → F ↦ y j / (g : Matrix (Fin 2) (Fin 2) F) 1 j)
      (fun t ↦ by simp [vecMul_zero_cons, hj]) ((continuous_apply j).div_const _) hcont
  exact ⟨hΦ.1.comp_continuous hcont, hΦ.2.comp_isClosedEmbedding hemb⟩

def modPow (x : F) (s : ℂ) : ℂ := ((modulus x : ℝ) : ℂ) ^ s

/- English proof (translation)
Simplify using `only [modPow, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]`. Conclude with `Complex.mul_cpow_ofReal_nonneg (modulus x).2 (modulus y).2 s`.
-/
theorem modPow_mul (x y : F) (s : ℂ) : modPow (x * y) s = modPow x s * modPow y s := by
  simp only [modPow, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (modulus x).2 (modulus y).2 s

/- English proof (translation)
The claim follows from `Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (by exact_mod_cast modulus_ne_zero hx))`.
-/
theorem modPow_add {x : F} (hx : x ≠ 0) (s t : ℂ) : modPow x (s + t) = modPow x s * modPow x t :=
  Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (by exact_mod_cast modulus_ne_zero hx))

/- English proof (translation)
The claim follows from `modulus_cpow_eq_zpow u s`.
-/
theorem modPow_units_eq_zpow (u : Fˣ) (s : ℂ) :
    modPow (u : F) s = ((residueCard F : ℂ) ^ (-s)) ^ ord (u : F) :=
  modulus_cpow_eq_zpow u s

def borelElt (a d : Fˣ) (x : F) : GL (Fin 2) F where
  val := !![(a : F), x; 0, (d : F)]
  inv := !![((a⁻¹ : Fˣ) : F), -(x * ((a⁻¹ : Fˣ) : F) * ((d⁻¹ : Fˣ) : F)); 0, ((d⁻¹ : Fˣ) : F)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val]
    all_goals field_simp
    all_goals ring
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val]
    all_goals field_simp
    all_goals ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem borelElt_val (a d : Fˣ) (x : F) :
    (borelElt a d x : Matrix (Fin 2) (Fin 2) F) = !![(a : F), x; 0, (d : F)] := rfl

/- English proof (translation)
Use `ext`. Simplify using `[Matrix.GeneralLinearGroup.val_det_apply, borelElt_val, Matrix.det_fin_two]`.
-/
theorem det_borelElt (a d : Fˣ) (x : F) :
    Matrix.GeneralLinearGroup.det (borelElt a d x) = a * d := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, borelElt_val, Matrix.det_fin_two]

/- English proof (translation)
Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp [borelElt_val, Matrix.vecMul, dotProduct, Fin.sum_univ_two]`.
-/
theorem vecMul_borelElt (a d : Fˣ) (x t : F) :
    ![0, t] ᵥ* (borelElt a d x : Matrix (Fin 2) (Fin 2) F) = ![0, t * d] := by
  ext i
  fin_cases i <;> simp [borelElt_val, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

abbrev detU (g : GL (Fin 2) F) : Fˣ := Matrix.GeneralLinearGroup.det g

/- English proof (translation)
The claim follows from `map_mul _ g h`.
-/
theorem detU_mul (g h : GL (Fin 2) F) : detU (g * h) = detU g * detU h := map_mul _ g h

def principalSeries (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) : Submodule ℂ (GL (Fin 2) F → ℂ) where
  carrier := {f | ∀ (a d : Fˣ) (x : F) (g : GL (Fin 2) F),
    f (borelElt a d x * g) =
      (χ₁ a : ℂ) * (χ₂ d : ℂ) * modPow (a : F) s * modPow (d : F) (-s) * f g}
  add_mem' {f₁ f₂} h₁ h₂ a d x g := by
    simp only [Pi.add_apply, h₁ a d x g, h₂ a d x g]; ring
  zero_mem' a d x g := by simp
  smul_mem' c f h a d x g := by
    simp only [Pi.smul_apply, smul_eq_mul, h a d x g]; ring

def IsSmooth (f : GL (Fin 2) F → ℂ) : Prop :=
  ∃ m : ℕ, ∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, f (g * u) = f g

variable [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Use `set G : Fˣ → ℂ := fun x ↦ f x * ((μ x : ℂˣ) : ℂ) * modPow (x : F) s with hG`. Establish `h1 : modPow (d : F) (-s) * modPow (d : F) s = 1`. Rewrite using `[← modPow_add d.ne_zero, neg_add_cancel]`. Simplify using `[modPow]`. Establish `h2 : (((μ d)⁻¹ : ℂˣ) : ℂ) * ((μ d : ℂˣ) : ℂ) = 1`.

Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `hpt : ∀ x : Fˣ, f ((x : F) * d) * ((μ x : ℂˣ) : ℂ) * modPow (x : F) s = (((μ d)⁻¹ : ℂˣ) : ℂ) * modPow (d : F) (-s) * G (d * x)`. Introduce `x`. Simplify using `only [hG, Units.val_mul, map_mul, modPow_mul]`. Rewrite using `[mul_comm (d : F) (x : F)]`.

Take the linear combination `(-(f ((x : F) * d) * ((μ x : ℂˣ) : ℂ) * modPow (x : F) s)) * ((((μ d)⁻¹ : ℂˣ) : ℂ) * ((μ d : ℂˣ) : ℂ) * h1 + h2)`. Establish `: localZeta (fun t ↦ f (t * d)) μ s = ∫ x, (((μ d)⁻¹ : ℂˣ) : ℂ) * modPow (d : F) (-s) * G (d * x) ∂multHaar F` using `integral_congr_ae (Eventually.of_forall fun x ↦ hpt x)`. Rewrite using `[this, integral_const_mul, integral_mul_left_eq_self G d]`. Both sides reduce to the same expression.
-/
theorem localZeta_mul_right (f : F → ℂ) (μ : Fˣ →* ℂˣ) (s : ℂ) (d : Fˣ) :
    localZeta (fun t ↦ f (t * d)) μ s =
      (((μ d)⁻¹ : ℂˣ) : ℂ) * modPow (d : F) (-s) * localZeta f μ s := by
  set G : Fˣ → ℂ := fun x ↦ f x * ((μ x : ℂˣ) : ℂ) * modPow (x : F) s with hG
  have h1 : modPow (d : F) (-s) * modPow (d : F) s = 1 := by
    rw [← modPow_add d.ne_zero, neg_add_cancel]; simp [modPow]
  have h2 : (((μ d)⁻¹ : ℂˣ) : ℂ) * ((μ d : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hpt : ∀ x : Fˣ, f ((x : F) * d) * ((μ x : ℂˣ) : ℂ) * modPow (x : F) s =
      (((μ d)⁻¹ : ℂˣ) : ℂ) * modPow (d : F) (-s) * G (d * x) := by
    intro x
    simp only [hG, Units.val_mul, map_mul, modPow_mul]
    rw [mul_comm (d : F) (x : F)]
    linear_combination (-(f ((x : F) * d) * ((μ x : ℂˣ) : ℂ) * modPow (x : F) s)) *
      ((((μ d)⁻¹ : ℂˣ) : ℂ) * ((μ d : ℂˣ) : ℂ) * h1 + h2)
  have : localZeta (fun t ↦ f (t * d)) μ s =
      ∫ x, (((μ d)⁻¹ : ℂˣ) : ℂ) * modPow (d : F) (-s) * G (d * x) ∂multHaar F :=
    integral_congr_ae (Eventually.of_forall fun x ↦ hpt x)
  rw [this, integral_const_mul, integral_mul_left_eq_self G d]
  rfl

def localSection (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) (Φ : (Fin 2 → F) → ℂ) (g : GL (Fin 2) F) : ℂ :=
  (χ₁ (detU g) : ℂ) * modPow (detU g : F) s * localZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s)

/- English proof (translation)
The claim follows from `h₁.mul (continuous_quasiChar_inv h₂)`.
-/
theorem continuous_mul_inv {χ₁ χ₂ : Fˣ →* ℂˣ} (h₁ : Continuous χ₁) (h₂ : Continuous χ₂) :
    Continuous (χ₁ * χ₂⁻¹) :=
  h₁.mul (continuous_quasiChar_inv h₂)

/- English proof (translation)
The claim follows from `integrable_localZeta (slice_mem hΦ g) (continuous_mul_inv h₁ h₂) (by simpa using hs)`.
-/
theorem integrable_localSectionIntegrand {χ₁ χ₂ : Fˣ →* ℂˣ} (h₁ : Continuous χ₁)
    (h₂ : Continuous χ₂) {s : ℂ} (hs : -quasiCharExponent (χ₁ * χ₂⁻¹) < 2 * s.re)
    {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) (g : GL (Fin 2) F) :
    Integrable (fun u : Fˣ ↦ slice Φ g u * (((χ₁ * χ₂⁻¹) u : ℂˣ) : ℂ) *
      ((modulus (u : F) : ℝ) : ℂ) ^ (2 * s)) (multHaar F) :=
  integrable_localZeta (slice_mem hΦ g) (continuous_mul_inv h₁ h₂) (by simpa using hs)

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [slice, Units.val_mul, ← Matrix.vecMul_vecMul, vecMul_borelElt]`.
-/
theorem slice_borelElt_mul (Φ : (Fin 2 → F) → ℂ) (a d : Fˣ) (x : F) (g : GL (Fin 2) F) :
    slice Φ (borelElt a d x * g) = fun t ↦ slice Φ g (t * d) := by
  funext t
  simp only [slice, Units.val_mul, ← Matrix.vecMul_vecMul, vecMul_borelElt]

/- English proof (translation)
Simplify using `only [localSection, slice_borelElt_mul, localZeta_mul_right, det_borelElt, map_mul, Units.val_mul, modPow_mul]`. Establish `hμ : (((χ₁ * χ₂⁻¹) d)⁻¹ : ℂˣ) = (χ₁ d)⁻¹ * χ₂ d`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv]`. Establish `h1 : modPow (d : F) s * modPow (d : F) (-(2 * s)) = modPow (d : F) (-s)`. Rewrite using `[← modPow_add d.ne_zero]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ((χ₁ d : ℂˣ) : ℂ) * (((χ₁ d)⁻¹ : ℂˣ) : ℂ) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Rewrite using `[hμ, Units.val_mul, ← h1]`.

Take the linear combination `((χ₁ a : ℂˣ) : ℂ) * ((χ₂ d : ℂˣ) : ℂ) * modPow (a : F) s * modPow (d : F) s * modPow (d : F) (-(2 * s)) * ((χ₁ (detU g) : ℂˣ) : ℂ) * modPow (detU g : F) s * localZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s) * h2`.
-/
theorem localSection_borelElt_mul (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) (Φ : (Fin 2 → F) → ℂ) (a d : Fˣ)
    (x : F) (g : GL (Fin 2) F) :
    localSection χ₁ χ₂ s Φ (borelElt a d x * g) =
      (χ₁ a : ℂ) * (χ₂ d : ℂ) * modPow (a : F) s * modPow (d : F) (-s) *
        localSection χ₁ χ₂ s Φ g := by
  simp only [localSection, slice_borelElt_mul, localZeta_mul_right, det_borelElt,
    map_mul, Units.val_mul, modPow_mul]
  have hμ : (((χ₁ * χ₂⁻¹) d)⁻¹ : ℂˣ) = (χ₁ d)⁻¹ * χ₂ d := by
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv]
  have h1 : modPow (d : F) s * modPow (d : F) (-(2 * s)) = modPow (d : F) (-s) := by
    rw [← modPow_add d.ne_zero]; congr 1; ring
  have h2 : ((χ₁ d : ℂˣ) : ℂ) * (((χ₁ d)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hμ, Units.val_mul, ← h1]
  linear_combination ((χ₁ a : ℂˣ) : ℂ) * ((χ₂ d : ℂˣ) : ℂ) * modPow (a : F) s *
    modPow (d : F) s * modPow (d : F) (-(2 * s)) * ((χ₁ (detU g) : ℂˣ) : ℂ) *
    modPow (detU g : F) s * localZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s) * h2

/- English proof (translation)
The claim follows from `fun a d x g ↦ localSection_borelElt_mul χ₁ χ₂ s Φ a d x g`.
-/
theorem localSection_mem_principalSeries (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) (Φ : (Fin 2 → F) → ℂ) :
    localSection χ₁ χ₂ s Φ ∈ principalSeries χ₁ χ₂ s :=
  fun a d x g ↦ localSection_borelElt_mul χ₁ χ₂ s Φ a d x g

def rightTranslate (h : GL (Fin 2) F) (Φ : (Fin 2 → F) → ℂ) : (Fin 2 → F) → ℂ :=
  fun x ↦ Φ (x ᵥ* (h : Matrix (Fin 2) (Fin 2) F))

/- English proof (translation)
Establish `hs : slice Φ (g * h) = slice (rightTranslate h Φ) g`. Use function extensionality and compare the values at `t`. Simplify using `only [slice, rightTranslate, Units.val_mul, Matrix.vecMul_vecMul]`. Simplify using `only [localSection, hs, map_mul, Units.val_mul, modPow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem localSection_mul (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) (Φ : (Fin 2 → F) → ℂ) (g h : GL (Fin 2) F) :
    localSection χ₁ χ₂ s Φ (g * h) =
      (χ₁ (detU h) : ℂ) * modPow (detU h : F) s * localSection χ₁ χ₂ s (rightTranslate h Φ) g := by
  have hs : slice Φ (g * h) = slice (rightTranslate h Φ) g := by
    funext t
    simp only [slice, rightTranslate, Units.val_mul, Matrix.vecMul_vecMul]
  simp only [localSection, hs, map_mul, Units.val_mul, modPow_mul]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `g`. Establish `hZ : localZeta (slice (Φ + Ψ) g) (χ₁ * χ₂⁻¹) (2 * s) = localZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s) + localZeta (slice Ψ g) (χ₁ * χ₂⁻¹) (2 * s)`. Simplify using `only [localZeta]`. Rewrite using `[← integral_add (integrable_localSectionIntegrand h₁ h₂ hs hΦ g) (integrable_localSectionIntegrand h₁ h₂ hs hΨ g)]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Simplify using `only [slice, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [localSection, Pi.add_apply, hZ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem localSection_add {χ₁ χ₂ : Fˣ →* ℂˣ} (h₁ : Continuous χ₁) (h₂ : Continuous χ₂) {s : ℂ}
    (hs : -quasiCharExponent (χ₁ * χ₂⁻¹) < 2 * s.re) {Φ Ψ : (Fin 2 → F) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 F) (hΨ : Ψ ∈ schwartzBruhat2 F) :
    localSection χ₁ χ₂ s (Φ + Ψ) = localSection χ₁ χ₂ s Φ + localSection χ₁ χ₂ s Ψ := by
  funext g
  have hZ : localZeta (slice (Φ + Ψ) g) (χ₁ * χ₂⁻¹) (2 * s) =
      localZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s) + localZeta (slice Ψ g) (χ₁ * χ₂⁻¹) (2 * s) := by
    simp only [localZeta]
    rw [← integral_add (integrable_localSectionIntegrand h₁ h₂ hs hΦ g)
      (integrable_localSectionIntegrand h₁ h₂ hs hΨ g)]
    congr 1
    funext t
    simp only [slice, Pi.add_apply]
    ring
  simp only [localSection, Pi.add_apply, hZ]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `g`. Establish `hZ : localZeta (slice (c • Φ) g) (χ₁ * χ₂⁻¹) (2 * s) = c * localZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s)`. Simplify using `only [localZeta]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Simplify using `only [slice, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [localSection, Pi.smul_apply, smul_eq_mul, hZ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem localSection_smul (χ₁ χ₂ : Fˣ →* ℂˣ) (s c : ℂ) (Φ : (Fin 2 → F) → ℂ) :
    localSection χ₁ χ₂ s (c • Φ) = c • localSection χ₁ χ₂ s Φ := by
  funext g
  have hZ : localZeta (slice (c • Φ) g) (χ₁ * χ₂⁻¹) (2 * s) =
      c * localZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s) := by
    simp only [localZeta]
    rw [← integral_const_mul]
    congr 1
    funext t
    simp only [slice, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [localSection, Pi.smul_apply, smul_eq_mul, hZ]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `g`. Establish `hs : slice (fun x ↦ Φ ((a : F) • x)) g = fun t ↦ slice Φ g (t * a)`. Use function extensionality and compare the values at `t`. Simplify using `only [slice, vecMul_zero_cons]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [localSection, hs, localZeta_mul_right, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem localSection_smul_arg (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) (Φ : (Fin 2 → F) → ℂ) (a : Fˣ) :
    localSection χ₁ χ₂ s (fun x ↦ Φ ((a : F) • x)) =
      (((((χ₁ * χ₂⁻¹) a)⁻¹ : ℂˣ) : ℂ) * modPow (a : F) (-(2 * s))) • localSection χ₁ χ₂ s Φ := by
  funext g
  have hs : slice (fun x ↦ Φ ((a : F) • x)) g = fun t ↦ slice Φ g (t * a) := by
    funext t
    simp only [slice, vecMul_zero_cons]
    congr 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp only [localSection, hs, localZeta_mul_right, Pi.smul_apply, smul_eq_mul]
  ring

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Rewrite `hf`, the goal using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`. Take `⟨V, hV, hxV, hfV⟩` from `hf x`. Distinguish the cases in `hx : x ∈ S`. Use `⟨V ∩ S, hV.inter hS.isOpen, ⟨hxV, hx⟩, fun y hy ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.indicator_of_mem hy.2, Set.indicator_of_mem hx, hfV y hy.1]`. Use `⟨V ∩ Sᶜ, hV.inter hS.compl.isOpen, ⟨hxV, hx⟩, fun y hy ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[Set.indicator_of_notMem hy.2, Set.indicator_of_notMem hx]`.
-/
theorem isLocallyConstant_indicator {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClopen S)
    {f : X → ℂ} (hf : IsLocallyConstant f) : IsLocallyConstant (S.indicator f) := by
  rw [IsLocallyConstant.iff_exists_open] at hf ⊢
  intro x
  obtain ⟨V, hV, hxV, hfV⟩ := hf x
  by_cases hx : x ∈ S
  · refine ⟨V ∩ S, hV.inter hS.isOpen, ⟨hxV, hx⟩, fun y hy ↦ ?_⟩
    rw [Set.indicator_of_mem hy.2, Set.indicator_of_mem hx, hfV y hy.1]
  · refine ⟨V ∩ Sᶜ, hV.inter hS.compl.isOpen, ⟨hxV, hx⟩, fun y hy ↦ ?_⟩
    rw [Set.indicator_of_notMem hy.2, Set.indicator_of_notMem hx]

variable (F) in

def box (n : ℤ) : AddSubgroup (Fin 2 → F) := AddSubgroup.pi Set.univ fun _ ↦ valBall F n

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Simplify using `[box, AddSubgroup.mem_pi]`.
-/
theorem mem_box {n : ℤ} {x : Fin 2 → F} : x ∈ box F n ↔ ∀ i, x i ∈ valBall F n := by
  simp [box, AddSubgroup.mem_pi]

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Use extensionality with `x`. Simplify using `[mem_box]`.
-/
theorem coe_box (n : ℤ) :
    (box F n : Set (Fin 2 → F)) = Set.pi Set.univ fun _ ↦ (valBall F n : Set F) := by
  ext x
  simp [mem_box]

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
The claim follows from `fun _ hx ↦ mem_box.2 fun i ↦ valBall_antitone h (mem_box.1 hx i)`.
-/
theorem box_antitone {m n : ℤ} (h : m ≤ n) : box F n ≤ box F m := fun _ hx ↦
  mem_box.2 fun i ↦ valBall_antitone h (mem_box.1 hx i)

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Rewrite using `[coe_box]`. Conclude with `⟨isClosed_set_pi fun _ _ ↦ isClosed_valBall n, isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_valBall n⟩`.
-/
theorem isClopen_box (n : ℤ) : IsClopen (box F n : Set (Fin 2 → F)) := by
  rw [coe_box]
  exact ⟨isClosed_set_pi fun _ _ ↦ isClosed_valBall n,
    isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_valBall n⟩

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Rewrite using `[coe_box]`. Conclude with `isCompact_univ_pi fun _ ↦ isCompact_valBall n`.
-/
theorem isCompact_box (n : ℤ) : IsCompact (box F n : Set (Fin 2 → F)) := by
  rw [coe_box]
  exact isCompact_univ_pi fun _ ↦ isCompact_valBall n

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Rewrite `hU` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hsub⟩` from `hU`. Establish `ht' : ∀ i, t i ∈ 𝓝 (0 : F)` using `fun i ↦ by simpa using ht i`. Use `choose n hn using fun i ↦ (hasBasis_nhds_zero_valBall (K := F)).mem_iff.1 (ht' i)`. Use `⟨max (n 0) (n 1), fun x hx ↦ hsub fun i _ ↦ (hn i).2 ?_⟩` and prove the remaining obligations.

Use `valBall_antitone ?_ (mem_box.1 hx i)` and prove the remaining obligations. Use `fin_cases i`. Conclude with `le_max_left _ _`. Conclude with `le_max_right _ _`.
-/
theorem exists_box_subset {U : Set (Fin 2 → F)} (hU : U ∈ 𝓝 (0 : Fin 2 → F)) :
    ∃ n : ℤ, (box F n : Set (Fin 2 → F)) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  have ht' : ∀ i, t i ∈ 𝓝 (0 : F) := fun i ↦ by simpa using ht i
  choose n hn using fun i ↦ (hasBasis_nhds_zero_valBall (K := F)).mem_iff.1 (ht' i)
  refine ⟨max (n 0) (n 1), fun x hx ↦ hsub fun i _ ↦ (hn i).2 ?_⟩
  refine valBall_antitone ?_ (mem_box.1 hx i)
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Take `⟨a, ha⟩` from `exists_mem_valBall_neg_nat (x 0)`. Take `⟨b, hb⟩` from `exists_mem_valBall_neg_nat (x 1)`. Use `⟨max a b, mem_box.2 fun i ↦ ?_⟩` and prove the remaining obligations. Use `fin_cases i`. Conclude with `valBall_antitone (by omega) ha`.

Conclude with `valBall_antitone (by omega) hb`.
-/
theorem exists_mem_box_neg (x : Fin 2 → F) : ∃ m : ℕ, x ∈ box F (-(m : ℤ)) := by
  obtain ⟨a, ha⟩ := exists_mem_valBall_neg_nat (x 0)
  obtain ⟨b, hb⟩ := exists_mem_valBall_neg_nat (x 1)
  refine ⟨max a b, mem_box.2 fun i ↦ ?_⟩
  fin_cases i
  · exact valBall_antitone (by omega) ha
  · exact valBall_antitone (by omega) hb

omit [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
Take `⟨hlc, hcs⟩` from `hΦ`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : ℕ, tsupport Φ ⊆ (box F (-(m : ℤ)) : Set (Fin 2 → F)) := by`. Use `hcs.isCompact.elim_directed_cover (fun m : ℕ ↦ (box F (-(m : ℤ)) : Set (Fin 2 → F))) (fun m ↦ (isClopen_box _).isOpen) ?_ ?_` and prove the remaining obligations. Introduce `x _`. Simplify using `only [Set.mem_iUnion]`.

Conclude with `exists_mem_box_neg x`. Conclude with `Monotone.directed_le fun a b hab ↦ box_antitone (by omega)`. Establish `hloc : ∀ x : Fin 2 → F, ∃ n : ℤ, ∀ h ∈ box F n, Φ (x + h) = Φ x`. Introduce `x`. Establish `ho : IsOpen {h : Fin 2 → F | Φ (x + h) = Φ x}` using `(hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)`.

Take `⟨n, hn⟩` from `exists_box_subset (ho.mem_nhds (by simp))`. Conclude with `⟨n, fun h hh ↦ hn hh⟩`. Use `choose n hn using hloc`. Take `⟨t, -, ht⟩` from `hcs.isCompact.elim_nhds_subcover (fun x ↦ {z : Fin 2 → F | z - x ∈ box F (n x)}) (fun x _ ↦ (((isClopen_box _).isOpen).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp))`. Take `⟨N₀, hN⟩` from `(t.image n).exists_le`.

Use `set N := max N₀ (-(m : ℤ)) with hNdef`. Establish `hval : ∀ y ∈ tsupport Φ, ∀ h ∈ box F N, Φ (y + h) = Φ y`. Introduce `y hy h hh`. Use `ht hy` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`.

Take `⟨x, hxt, hyx⟩` from `this`. Establish `hN' : box F N ≤ box F (n x)` using `box_antitone ((hN _ (Finset.mem_image_of_mem n hxt)).trans (le_max_left _ _))`. Establish `e1 : Φ y = Φ x`. Use `hn x (y - x) hyx` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis.

Establish `e2 : Φ (y + h) = Φ x`. Use `hn x (y + h - x) (by rw [show y + h - x = (y - x) + h by abel]; exact add_mem hyx (hN' hh))` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Rewrite using `[e1, e2]`. Use `⟨N, -(m : ℤ), le_max_right _ _, fun y h hh ↦ ?_, fun x hx ↦ hm (subset_tsupport Φ hx)⟩` and prove the remaining obligations.

Distinguish the cases in `hy : y ∈ tsupport Φ`. Conclude with `hval y hy h hh`. Distinguish the cases in `hyh : y + h ∈ tsupport Φ`. Use `hval (y + h) hyh (-h) (neg_mem hh)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_right]`.

Conclude with `this.symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]`.
-/
theorem exists_invariant_of_mem_schwartzBruhat2 {Φ : (Fin 2 → F) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 F) :
    ∃ N M : ℤ, M ≤ N ∧ (∀ x, ∀ h ∈ box F N, Φ (x + h) = Φ x) ∧
      ∀ x, Φ x ≠ 0 → x ∈ box F M := by
  obtain ⟨hlc, hcs⟩ := hΦ
  obtain ⟨m, hm⟩ : ∃ m : ℕ, tsupport Φ ⊆ (box F (-(m : ℤ)) : Set (Fin 2 → F)) := by
    refine hcs.isCompact.elim_directed_cover (fun m : ℕ ↦ (box F (-(m : ℤ)) : Set (Fin 2 → F)))
      (fun m ↦ (isClopen_box _).isOpen) ?_ ?_
    · intro x _
      simp only [Set.mem_iUnion]
      exact exists_mem_box_neg x
    · exact Monotone.directed_le fun a b hab ↦ box_antitone (by omega)
  have hloc : ∀ x : Fin 2 → F, ∃ n : ℤ, ∀ h ∈ box F n, Φ (x + h) = Φ x := by
    intro x
    have ho : IsOpen {h : Fin 2 → F | Φ (x + h) = Φ x} :=
      (hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)
    obtain ⟨n, hn⟩ := exists_box_subset (ho.mem_nhds (by simp))
    exact ⟨n, fun h hh ↦ hn hh⟩
  choose n hn using hloc
  obtain ⟨t, -, ht⟩ := hcs.isCompact.elim_nhds_subcover
    (fun x ↦ {z : Fin 2 → F | z - x ∈ box F (n x)})
    (fun x _ ↦ (((isClopen_box _).isOpen).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simp))
  obtain ⟨N₀, hN⟩ := (t.image n).exists_le
  set N := max N₀ (-(m : ℤ)) with hNdef
  have hval : ∀ y ∈ tsupport Φ, ∀ h ∈ box F N, Φ (y + h) = Φ y := by
    intro y hy h hh
    have := ht hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hxt, hyx⟩ := this
    have hN' : box F N ≤ box F (n x) :=
      box_antitone ((hN _ (Finset.mem_image_of_mem n hxt)).trans (le_max_left _ _))
    have e1 : Φ y = Φ x := by
      have := hn x (y - x) hyx
      rwa [add_sub_cancel] at this
    have e2 : Φ (y + h) = Φ x := by
      have := hn x (y + h - x)
        (by rw [show y + h - x = (y - x) + h by abel]; exact add_mem hyx (hN' hh))
      rwa [add_sub_cancel] at this
    rw [e1, e2]
  refine ⟨N, -(m : ℤ), le_max_right _ _, fun y h hh ↦ ?_, fun x hx ↦ hm (subset_tsupport Φ hx)⟩
  by_cases hy : y ∈ tsupport Φ
  · exact hval y hy h hh
  by_cases hyh : y + h ∈ tsupport Φ
  · have := hval (y + h) hyh (-h) (neg_mem hh)
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Distinguish the cases in `hy : y = 0`. Simplify using `[hy]`. Rewrite using `[mem_valBall_iff_le_ord (mul_ne_zero a.ne_zero hy), mem_valBall_iff_le_ord hy, ord_mul a.ne_zero hy]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mul_mem_valBall_iff (a : Fˣ) (n : ℤ) (y : F) :
    (a : F) * y ∈ valBall F n ↔ y ∈ valBall F (n - ord (a : F)) := by
  by_cases hy : y = 0
  · simp [hy]
  rw [mem_valBall_iff_le_ord (mul_ne_zero a.ne_zero hy), mem_valBall_iff_le_ord hy,
    ord_mul a.ne_zero hy]
  omega

omit [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
Simplify using `only [mem_box, Pi.smul_apply, smul_eq_mul, mul_mem_valBall_iff]`.
-/
theorem smul_mem_box_iff (a : Fˣ) (n : ℤ) (x : Fin 2 → F) :
    (a : F) • x ∈ box F n ↔ x ∈ box F (n - ord (a : F)) := by
  simp only [mem_box, Pi.smul_apply, smul_eq_mul, mul_mem_valBall_iff]

variable (F) in

def shell : Set (Fin 2 → F) := (box F 0 : Set (Fin 2 → F)) \ box F 1

variable (F) in

def shellAt (m : ℤ) : Set (Fin 2 → F) := (box F m : Set (Fin 2 → F)) \ box F (m + 1)

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
The claim follows from `(isClopen_box m).diff (isClopen_box (m + 1))`.
-/
theorem isClopen_shellAt (m : ℤ) : IsClopen (shellAt F m) :=
  (isClopen_box m).diff (isClopen_box (m + 1))

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Simplify using `[shellAt, shell]`.
-/
theorem shellAt_zero : shellAt F 0 = shell F := by simp [shellAt, shell]

abbrev unifPow (k : ℤ) : Fˣ := unifUnit F ^ k

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
The claim follows from `ord_unifUnit_zpow k`.
-/
theorem ord_unifPow (k : ℤ) : ord ((unifPow k : Fˣ) : F) = k := ord_unifUnit_zpow k

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Simplify using `only [shellAt, Set.mem_sdiff, SetLike.mem_coe, smul_mem_box_iff, ord_unifPow]`. Rewrite using `[show m + 1 - k = m - k + 1 by ring]`.
-/
theorem smul_mem_shellAt_iff (k m : ℤ) (x : Fin 2 → F) :
    ((unifPow k : Fˣ) : F) • x ∈ shellAt F m ↔ x ∈ shellAt F (m - k) := by
  simp only [shellAt, Set.mem_sdiff, SetLike.mem_coe, smul_mem_box_iff, ord_unifPow]
  rw [show m + 1 - k = m - k + 1 by ring]

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Establish `h : unifPow k * unifPow (-k) = (1 : Fˣ)`. Rewrite using `[unifPow, unifPow, _root_.zpow_neg, mul_inv_cancel]`. Rewrite using `[smul_smul, ← Units.val_mul, h, Units.val_one, one_smul]`.
-/
theorem unifPow_smul_unifPow_smul (k : ℤ) (x : Fin 2 → F) :
    ((unifPow k : Fˣ) : F) • ((unifPow (-k) : Fˣ) : F) • x = x := by
  have h : unifPow k * unifPow (-k) = (1 : Fˣ) := by
    rw [unifPow, unifPow, _root_.zpow_neg, mul_inv_cancel]
  rw [smul_smul, ← Units.val_mul, h, Units.val_one, one_smul]

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨hΦ.1.comp_continuous (continuous_const_smul (a : F)), hΦ.2.comp_homeomorph (Homeomorph.smulOfNeZero (a : F) a.ne_zero)⟩`.
-/
theorem comp_smul_mem_schwartzBruhat2 {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F)
    (a : Fˣ) : (fun x ↦ Φ ((a : F) • x)) ∈ schwartzBruhat2 F :=
  ⟨hΦ.1.comp_continuous (continuous_const_smul (a : F)),
    hΦ.2.comp_homeomorph (Homeomorph.smulOfNeZero (a : F) a.ne_zero)⟩

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨isLocallyConstant_indicator hS hf, HasCompactSupport.intro (isCompact_box n) fun _ hx ↦ Set.indicator_of_notMem (fun h ↦ hx (hSn h)) f⟩`.
-/
theorem indicator_mem_schwartzBruhat2 {S : Set (Fin 2 → F)} (hS : IsClopen S) {n : ℤ}
    (hSn : S ⊆ box F n) {f : (Fin 2 → F) → ℂ} (hf : IsLocallyConstant f) :
    S.indicator f ∈ schwartzBruhat2 F :=
  ⟨isLocallyConstant_indicator hS hf, HasCompactSupport.intro (isCompact_box n) fun _ hx ↦
    Set.indicator_of_notMem (fun h ↦ hx (hSn h)) f⟩

variable (F) in

def boxInd (n : ℤ) : (Fin 2 → F) → ℂ := (box F n : Set (Fin 2 → F)).indicator 1

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
The claim follows from `indicator_mem_schwartzBruhat2 (isClopen_box n) le_rfl (IsLocallyConstant.const 1)`.
-/
theorem boxInd_mem (n : ℤ) : boxInd F n ∈ schwartzBruhat2 F :=
  indicator_mem_schwartzBruhat2 (isClopen_box n) le_rfl (IsLocallyConstant.const 1)

def shellPiece (Φ : (Fin 2 → F) → ℂ) (m : ℤ) : (Fin 2 → F) → ℂ :=
  (shell F).indicator fun y ↦ Φ (((unifPow m : Fˣ) : F) • y)

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Use `indicator_mem_schwartzBruhat2 (n := 0) ?_ (fun x hx ↦ hx.1) (comp_smul_mem_schwartzBruhat2 hΦ _).1` and prove the remaining obligations. Rewrite using `[← shellAt_zero]`. Conclude with `isClopen_shellAt 0`.
-/
theorem shellPiece_mem {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) (m : ℤ) :
    shellPiece Φ m ∈ schwartzBruhat2 F := by
  refine indicator_mem_schwartzBruhat2 (n := 0) ?_ (fun x hx ↦ hx.1)
    (comp_smul_mem_schwartzBruhat2 hΦ _).1
  rw [← shellAt_zero]
  exact isClopen_shellAt 0

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
The claim follows from `Set.support_indicator_subset`.
-/
theorem support_shellPiece_subset (Φ : (Fin 2 → F) → ℂ) (m : ℤ) :
    Function.support (shellPiece Φ m) ⊆ shell F :=
  Set.support_indicator_subset

omit [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [shellPiece]`. Rewrite using `[← shellAt_zero]`. Distinguish the cases in `hx : x ∈ shellAt F m`. Establish `hx' : ((unifPow (-m) : Fˣ) : F) • x ∈ shellAt F 0`.

Rewrite using `[smul_mem_shellAt_iff]`. Simplify using `using hx`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem hx', unifPow_smul_unifPow_smul]`. Establish `hx' : ((unifPow (-m) : Fˣ) : F) • x ∉ shellAt F 0`. Rewrite using `[smul_mem_shellAt_iff]`.

Simplify using `using hx`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']`.
-/
theorem indicator_shellAt_eq (Φ : (Fin 2 → F) → ℂ) (m : ℤ) :
    (shellAt F m).indicator Φ = fun x ↦ shellPiece Φ m (((unifPow (-m) : Fˣ) : F) • x) := by
  funext x
  simp only [shellPiece]
  rw [← shellAt_zero]
  by_cases hx : x ∈ shellAt F m
  · have hx' : ((unifPow (-m) : Fˣ) : F) • x ∈ shellAt F 0 := by
      rw [smul_mem_shellAt_iff]; simpa using hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', unifPow_smul_unifPow_smul]
  · have hx' : ((unifPow (-m) : Fˣ) : F) • x ∉ shellAt F 0 := by
      rw [smul_mem_shellAt_iff]; simpa using hx
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']

omit [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
Establish `hcount : ∀ x ∈ box F M, ∀ n, M ≤ n → (∑ m ∈ Finset.Ico M n, (shellAt F m).indicator (1 : (Fin 2 → F) → ℂ) x) + boxInd F n x = 1`. Introduce `x hx n hn`. Proceed by induction on `n, hn using Int.leInduction with`. Consider the case `base => simp [boxInd, Set.indicator_of_mem hx]`. Consider the case `succ n hn ih`.

Establish `hI : Finset.Ico M (n + 1) = insert n (Finset.Ico M n)`. Use extensionality with `k`. Simplify using `only [Finset.mem_Ico, Finset.mem_insert]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hI, Finset.sum_insert (by simp), add_comm (Set.indicator _ _ x), add_assoc, ← ih]`.

Use `congr 1`. Distinguish the cases in `h1 : x ∈ box F (n + 1)`. Establish `h0 : x ∈ box F n` using `box_antitone (by omega) h1`. Establish `hs : x ∉ shellAt F n` using `fun h ↦ h.2 h1`. Simplify using `[boxInd, Set.indicator_of_mem h1, Set.indicator_of_mem h0, Set.indicator_of_notMem hs]`.

Distinguish the cases in `h0 : x ∈ box F n`. Establish `hs : x ∈ shellAt F n` using `⟨h0, h1⟩`. Simplify using `[boxInd, Set.indicator_of_notMem h1, Set.indicator_of_mem h0, Set.indicator_of_mem hs]`. Establish `hs : x ∉ shellAt F n` using `fun h ↦ h0 h.1`. Simplify using `[boxInd, Set.indicator_of_notMem h1, Set.indicator_of_notMem h0, Set.indicator_of_notMem hs]`.

Use function extensionality and compare the values at `x`. Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `hx : x ∈ box F M`. Establish `hind : ∀ m, (shellAt F m).indicator Φ x = (shellAt F m).indicator (1 : (Fin 2 → F) → ℂ) x * Φ x`. Introduce `m`.

Distinguish the cases in `h : x ∈ shellAt F m`. Simplify using `[Set.indicator_of_mem h]`. Simplify using `[Set.indicator_of_notMem h]`. Establish `hbox : Φ 0 * boxInd F N x = boxInd F N x * Φ x`. Distinguish the cases in `h : x ∈ box F N`.

Use `hinv 0 x h` as an intermediate fact. Rewrite `this` using `[zero_add]`. Simplify using `[boxInd, Set.indicator_of_mem h, this]`. Simplify using `[boxInd, Set.indicator_of_notMem h]`. Simplify using `only [hind, hbox, ← Finset.sum_mul, ← add_mul, hcount x hx N hMN, one_mul]`.

Establish `h0 : Φ x = 0`. Assume the negation of the conclusion as `h`. Conclude with `hx (hsupp x h)`. Establish `hN : x ∉ box F N` using `fun h ↦ hx (box_antitone hMN h)`. Simplify using `only [h0, boxInd, Set.indicator_of_notMem hN, mul_zero, add_zero]`.

Use `(Finset.sum_eq_zero fun c _ ↦ ?_).symm` and prove the remaining obligations. Distinguish the cases in `h : x ∈ shellAt F c`. Rewrite using `[Set.indicator_of_mem h, h0]`. Rewrite using `[Set.indicator_of_notMem h]`.
-/
theorem eq_sum_shells {Φ : (Fin 2 → F) → ℂ} {N M : ℤ} (hMN : M ≤ N)
    (hinv : ∀ x, ∀ h ∈ box F N, Φ (x + h) = Φ x) (hsupp : ∀ x, Φ x ≠ 0 → x ∈ box F M) :
    Φ = (∑ m ∈ Finset.Ico M N, (shellAt F m).indicator Φ) + Φ 0 • boxInd F N := by
  have hcount : ∀ x ∈ box F M, ∀ n, M ≤ n →
      (∑ m ∈ Finset.Ico M n, (shellAt F m).indicator (1 : (Fin 2 → F) → ℂ) x) +
        boxInd F n x = 1 := by
    intro x hx n hn
    induction n, hn using Int.leInduction with
    | base => simp [boxInd, Set.indicator_of_mem hx]
    | succ n hn ih =>
      have hI : Finset.Ico M (n + 1) = insert n (Finset.Ico M n) := by
        ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hI, Finset.sum_insert (by simp), add_comm (Set.indicator _ _ x), add_assoc, ← ih]
      congr 1
      by_cases h1 : x ∈ box F (n + 1)
      · have h0 : x ∈ box F n := box_antitone (by omega) h1
        have hs : x ∉ shellAt F n := fun h ↦ h.2 h1
        simp [boxInd, Set.indicator_of_mem h1, Set.indicator_of_mem h0,
          Set.indicator_of_notMem hs]
      · by_cases h0 : x ∈ box F n
        · have hs : x ∈ shellAt F n := ⟨h0, h1⟩
          simp [boxInd, Set.indicator_of_notMem h1, Set.indicator_of_mem h0,
            Set.indicator_of_mem hs]
        · have hs : x ∉ shellAt F n := fun h ↦ h0 h.1
          simp [boxInd, Set.indicator_of_notMem h1, Set.indicator_of_notMem h0,
            Set.indicator_of_notMem hs]
  funext x
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ box F M
  · have hind : ∀ m, (shellAt F m).indicator Φ x =
        (shellAt F m).indicator (1 : (Fin 2 → F) → ℂ) x * Φ x := by
      intro m
      by_cases h : x ∈ shellAt F m
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    have hbox : Φ 0 * boxInd F N x = boxInd F N x * Φ x := by
      by_cases h : x ∈ box F N
      · have := hinv 0 x h
        rw [zero_add] at this
        simp [boxInd, Set.indicator_of_mem h, this]
      · simp [boxInd, Set.indicator_of_notMem h]
    simp only [hind, hbox, ← Finset.sum_mul, ← add_mul, hcount x hx N hMN, one_mul]
  · have h0 : Φ x = 0 := by
      by_contra h
      exact hx (hsupp x h)
    have hN : x ∉ box F N := fun h ↦ hx (box_antitone hMN h)
    simp only [h0, boxInd, Set.indicator_of_notMem hN, mul_zero, add_zero]
    refine (Finset.sum_eq_zero fun c _ ↦ ?_).symm
    by_cases h : x ∈ shellAt F c
    · rw [Set.indicator_of_mem h, h0]
    · rw [Set.indicator_of_notMem h]

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Simplify using `using localSection_smul χ₁ χ₂ s 0 (0 : (Fin 2 → F) → ℂ)`. Consider the case `insert i t hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, localSection_add h₁ h₂ hs (hΦ i (Finset.mem_insert_self i t)) (sum_mem fun j hj ↦ hΦ j (Finset.mem_insert_of_mem hj)), ih fun j hj ↦ hΦ j (Finset.mem_insert_of_mem hj)]`.
-/
theorem localSection_finset_sum {χ₁ χ₂ : Fˣ →* ℂˣ} (h₁ : Continuous χ₁) (h₂ : Continuous χ₂)
    {s : ℂ} (hs : -quasiCharExponent (χ₁ * χ₂⁻¹) < 2 * s.re) {ι : Type*} (t : Finset ι)
    {Φ : ι → (Fin 2 → F) → ℂ} (hΦ : ∀ i ∈ t, Φ i ∈ schwartzBruhat2 F) :
    localSection χ₁ χ₂ s (∑ i ∈ t, Φ i) = ∑ i ∈ t, localSection χ₁ χ₂ s (Φ i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simpa using localSection_smul χ₁ χ₂ s 0 (0 : (Fin 2 → F) → ℂ)
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      localSection_add h₁ h₂ hs (hΦ i (Finset.mem_insert_self i t))
        (sum_mem fun j hj ↦ hΦ j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hΦ j (Finset.mem_insert_of_mem hj)]

/- English proof (translation)
Rewrite using `[localSection_smul_arg]`. Use `congr 1`. Establish `h1 : ((((χ₁ * χ₂⁻¹) (unifPow (-k)))⁻¹ : ℂˣ) : ℂ) = (((χ₁ * χ₂⁻¹) (unifUnit F) : ℂˣ) : ℂ) ^ k`. Rewrite using `[unifPow, map_zpow, ← _root_.zpow_neg, neg_neg, Units.val_zpow_eq_zpow_val]`. Establish `h2 : modPow ((unifPow (-k) : Fˣ) : F) (-(2 * s)) = ((residueCard F : ℂ) ^ (-(2 * s))) ^ k`.

Rewrite using `[modPow_units_eq_zpow, ord_unifPow, neg_neg, Complex.cpow_neg, _root_.inv_zpow']`. Rewrite using `[h1, h2]`.
-/
theorem localSection_dilate (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) (Ψ : (Fin 2 → F) → ℂ) (k : ℤ) :
    localSection χ₁ χ₂ s (fun x ↦ Ψ (((unifPow (-k) : Fˣ) : F) • x)) =
      ((((χ₁ * χ₂⁻¹) (unifUnit F) : ℂˣ) : ℂ) ^ k * ((residueCard F : ℂ) ^ (-(2 * s))) ^ k) •
        localSection χ₁ χ₂ s Ψ := by
  rw [localSection_smul_arg]
  congr 1
  have h1 : ((((χ₁ * χ₂⁻¹) (unifPow (-k)))⁻¹ : ℂˣ) : ℂ) =
      (((χ₁ * χ₂⁻¹) (unifUnit F) : ℂˣ) : ℂ) ^ k := by
    rw [unifPow, map_zpow, ← _root_.zpow_neg, neg_neg, Units.val_zpow_eq_zpow_val]
  have h2 : modPow ((unifPow (-k) : Fˣ) : F) (-(2 * s)) =
      ((residueCard F : ℂ) ^ (-(2 * s))) ^ k := by
    rw [modPow_units_eq_zpow, ord_unifPow, neg_neg, Complex.cpow_neg, _root_.inv_zpow']
  rw [h1, h2]

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `hiff : ((unifPow (-1) : Fˣ) : F) • x ∈ box F n ↔ x ∈ box F (n + 1)`. Rewrite using `[smul_mem_box_iff, ord_unifPow, sub_neg_eq_add]`. Simplify using `only [boxInd]`. Distinguish the cases in `hx : x ∈ box F (n + 1)`.

Establish `hx' : ((unifPow (-1) : Fˣ) : F) • x ∈ (box F n : Set (Fin 2 → F))` using `hiff.2 hx`. Rewrite using `[Set.indicator_of_mem (show x ∈ (box F (n + 1) : Set (Fin 2 → F)) from hx), Set.indicator_of_mem hx']`. Both sides reduce to the same expression. Establish `hx' : ((unifPow (-1) : Fˣ) : F) • x ∉ (box F n : Set (Fin 2 → F))` using `mt hiff.1 hx`. Rewrite using `[Set.indicator_of_notMem (show x ∉ (box F (n + 1) : Set (Fin 2 → F)) from hx), Set.indicator_of_notMem hx']`.
-/
theorem boxInd_succ (n : ℤ) :
    boxInd F (n + 1) = fun x ↦ boxInd F n (((unifPow (-1) : Fˣ) : F) • x) := by
  funext x
  have hiff : ((unifPow (-1) : Fˣ) : F) • x ∈ box F n ↔ x ∈ box F (n + 1) := by
    rw [smul_mem_box_iff, ord_unifPow, sub_neg_eq_add]
  simp only [boxInd]
  by_cases hx : x ∈ box F (n + 1)
  · have hx' : ((unifPow (-1) : Fˣ) : F) • x ∈ (box F n : Set (Fin 2 → F)) := hiff.2 hx
    rw [Set.indicator_of_mem (show x ∈ (box F (n + 1) : Set (Fin 2 → F)) from hx),
      Set.indicator_of_mem hx']
    rfl
  · have hx' : ((unifPow (-1) : Fˣ) : F) • x ∉ (box F n : Set (Fin 2 → F)) := mt hiff.1 hx
    rw [Set.indicator_of_notMem (show x ∉ (box F (n + 1) : Set (Fin 2 → F)) from hx),
      Set.indicator_of_notMem hx']

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [Pi.add_apply, boxInd]`. Distinguish the cases in `h1 : x ∈ box F (n + 1)`. Establish `h0 : x ∈ box F n` using `box_antitone (by omega) h1`. Establish `hs : x ∉ shellAt F n` using `fun h ↦ h.2 h1`.

Simplify using `[Set.indicator_of_mem h1, Set.indicator_of_mem h0, Set.indicator_of_notMem hs]`. Distinguish the cases in `h0 : x ∈ box F n`. Establish `hs : x ∈ shellAt F n` using `⟨h0, h1⟩`. Simplify using `[Set.indicator_of_notMem h1, Set.indicator_of_mem h0, Set.indicator_of_mem hs]`. Establish `hs : x ∉ shellAt F n` using `fun h ↦ h0 h.1`.

Simplify using `[Set.indicator_of_notMem h1, Set.indicator_of_notMem h0, Set.indicator_of_notMem hs]`.
-/
theorem boxInd_eq_add (n : ℤ) :
    boxInd F n = boxInd F (n + 1) + (shellAt F n).indicator 1 := by
  funext x
  simp only [Pi.add_apply, boxInd]
  by_cases h1 : x ∈ box F (n + 1)
  · have h0 : x ∈ box F n := box_antitone (by omega) h1
    have hs : x ∉ shellAt F n := fun h ↦ h.2 h1
    simp [Set.indicator_of_mem h1, Set.indicator_of_mem h0, Set.indicator_of_notMem hs]
  · by_cases h0 : x ∈ box F n
    · have hs : x ∈ shellAt F n := ⟨h0, h1⟩
      simp [Set.indicator_of_notMem h1, Set.indicator_of_mem h0, Set.indicator_of_mem hs]
    · have hs : x ∉ shellAt F n := fun h ↦ h0 h.1
      simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h0, Set.indicator_of_notMem hs]

variable (F) in

def shellInd : (Fin 2 → F) → ℂ := (shell F).indicator 1

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
The claim follows from `indicator_mem_schwartzBruhat2 (n := 0) (shellAt_zero (F := F) ▸ isClopen_shellAt 0) (fun _ hx ↦ hx.1) (IsLocallyConstant.const 1)`.
-/
theorem shellInd_mem : shellInd F ∈ schwartzBruhat2 F :=
  indicator_mem_schwartzBruhat2 (n := 0) (shellAt_zero (F := F) ▸ isClopen_shellAt 0)
    (fun _ hx ↦ hx.1) (IsLocallyConstant.const 1)

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
The claim follows from `indicator_shellAt_eq 1 n`.
-/
theorem indicator_shellAt_one (n : ℤ) :
    (shellAt F n).indicator (1 : (Fin 2 → F) → ℂ) =
      fun x ↦ shellInd F (((unifPow (-n) : Fˣ) : F) • x) :=
  indicator_shellAt_eq 1 n

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
The claim follows from `indicator_mem_schwartzBruhat2 (isClopen_shellAt m) (fun _ hx ↦ hx.1) hΦ.1`.
-/
theorem indicator_shellAt_mem {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) (m : ℤ) :
    (shellAt F m).indicator Φ ∈ schwartzBruhat2 F :=
  indicator_mem_schwartzBruhat2 (isClopen_shellAt m) (fun _ hx ↦ hx.1) hΦ.1

/- English proof (translation)
Establish `hsplit` using `congrArg (localSection χ₁ χ₂ s) (boxInd_eq_add (F := F) N)`. Rewrite `hsplit` using `[localSection_add h₁ h₂ hs (boxInd_mem _) (indicator_mem_schwartzBruhat2 (f := 1) (isClopen_shellAt N) (fun _ hx ↦ hx.1) (IsLocallyConstant.const 1))]`. Rewrite `hsplit` using `[boxInd_succ, localSection_dilate, indicator_shellAt_one, localSection_dilate]`. Simplify using `only [zpow_one] at hsplit`. Rewrite using `[sub_smul, one_smul]`.

Use `nth_rewrite 1 [hsplit]`. Normalize the expressions using the abelian group laws.
-/
theorem one_sub_mul_localSection_boxInd {χ₁ χ₂ : Fˣ →* ℂˣ} (h₁ : Continuous χ₁)
    (h₂ : Continuous χ₂) {s : ℂ} (hs : -quasiCharExponent (χ₁ * χ₂⁻¹) < 2 * s.re) (N : ℤ) :
    (1 - (((χ₁ * χ₂⁻¹) (unifUnit F) : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-(2 * s))) •
        localSection χ₁ χ₂ s (boxInd F N) =
      ((((χ₁ * χ₂⁻¹) (unifUnit F) : ℂˣ) : ℂ) ^ N * ((residueCard F : ℂ) ^ (-(2 * s))) ^ N) •
        localSection χ₁ χ₂ s (shellInd F) := by
  have hsplit := congrArg (localSection χ₁ χ₂ s) (boxInd_eq_add (F := F) N)
  rw [localSection_add h₁ h₂ hs (boxInd_mem _) (indicator_mem_schwartzBruhat2 (f := 1)
    (isClopen_shellAt N) (fun _ hx ↦ hx.1) (IsLocallyConstant.const 1))] at hsplit
  rw [boxInd_succ, localSection_dilate, indicator_shellAt_one, localSection_dilate] at hsplit
  simp only [zpow_one] at hsplit
  rw [sub_smul, one_smul]
  nth_rewrite 1 [hsplit]
  abel

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [shellPiece, shellInd, Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `hy : y ∈ shell F`. Establish `hb : ((unifPow N : Fˣ) : F) • y ∈ box F N`. Rewrite using `[smul_mem_box_iff, ord_unifPow, sub_self]`.

Conclude with `hy.1`. Use `hinv 0 _ hb` as an intermediate fact. Rewrite `this` using `[zero_add]`. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hy, Pi.one_apply, mul_one]`. Conclude with `this`.

Simplify using `[Set.indicator_of_notMem hy]`.
-/
theorem shellPiece_eq_smul_shellInd {Φ : (Fin 2 → F) → ℂ} {N : ℤ}
    (hinv : ∀ x, ∀ h ∈ box F N, Φ (x + h) = Φ x) : shellPiece Φ N = Φ 0 • shellInd F := by
  funext y
  simp only [shellPiece, shellInd, Pi.smul_apply, smul_eq_mul]
  by_cases hy : y ∈ shell F
  · have hb : ((unifPow N : Fˣ) : F) • y ∈ box F N := by
      rw [smul_mem_box_iff, ord_unifPow, sub_self]
      exact hy.1
    have := hinv 0 _ hb
    rw [zero_add] at this
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Pi.one_apply, mul_one]
    exact this
  · simp [Set.indicator_of_notMem hy]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨v, hv, hv1⟩ : ∃ v ∈ unitFiltrationUnits F 0, (χ₁ * χ₂⁻¹) v ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hμ fun v hv ↦ MonoidHom.mem_ker.2 (h v hv)`. Establish `hord : ord (v : F) = 0` using `mem_unitFiltrationUnits_zero_iff_ord.1 hv`.

Establish `hinv : (fun x ↦ boxInd F N ((v : F) • x)) = boxInd F N`. Use function extensionality and compare the values at `x`. Establish `hiff : (v : F) • x ∈ box F N ↔ x ∈ box F N`. Rewrite using `[smul_mem_box_iff, hord, sub_zero]`. Distinguish the cases in `hx : x ∈ box F N`.

Simplify using `[boxInd, Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]`. Simplify using `[boxInd, Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hiff.1 hx)]`. Establish `h` using `localSection_smul_arg χ₁ χ₂ s (boxInd F N) v`. Rewrite `h` using `[hinv, modPow_units_eq_zpow, hord, zpow_zero, mul_one]`. Establish `hne : ((((χ₁ * χ₂⁻¹) v)⁻¹ : ℂˣ) : ℂ) ≠ 1`.

Introduce `h1`. Apply `hv1` to reduce the goal to its premises. Establish `: ((χ₁ * χ₂⁻¹) v)⁻¹ = 1` using `Units.ext h1`. Conclude with `inv_eq_one.1 this`. Use function extensionality and compare the values at `g`.

Conclude with `eq_zero_of_eq_mul_of_ne_one hne (congrFun h g)`.
-/
theorem localSection_boxInd_of_not_isUnramified (χ₁ χ₂ : Fˣ →* ℂˣ)
    (hμ : ¬ IsUnramifiedChar (χ₁ * χ₂⁻¹)) (s : ℂ) (N : ℤ) :
    localSection χ₁ χ₂ s (boxInd F N) = 0 := by
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ unitFiltrationUnits F 0, (χ₁ * χ₂⁻¹) v ≠ 1 := by
    by_contra h
    push Not at h
    exact hμ fun v hv ↦ MonoidHom.mem_ker.2 (h v hv)
  have hord : ord (v : F) = 0 := mem_unitFiltrationUnits_zero_iff_ord.1 hv
  have hinv : (fun x ↦ boxInd F N ((v : F) • x)) = boxInd F N := by
    funext x
    have hiff : (v : F) • x ∈ box F N ↔ x ∈ box F N := by
      rw [smul_mem_box_iff, hord, sub_zero]
    by_cases hx : x ∈ box F N
    · simp [boxInd, Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]
    · simp [boxInd, Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hiff.1 hx)]
  have h := localSection_smul_arg χ₁ χ₂ s (boxInd F N) v
  rw [hinv, modPow_units_eq_zpow, hord, zpow_zero, mul_one] at h
  have hne : ((((χ₁ * χ₂⁻¹) v)⁻¹ : ℂˣ) : ℂ) ≠ 1 := by
    intro h1
    apply hv1
    have : ((χ₁ * χ₂⁻¹) v)⁻¹ = 1 := Units.ext h1
    exact inv_eq_one.1 this
  funext g
  exact eq_zero_of_eq_mul_of_ne_one hne (congrFun h g)

/- English proof (translation)
Take `⟨N, M, hMN, hinv, hsupp⟩` from `exists_invariant_of_mem_schwartzBruhat2 hΦ`. Use `set c : ℂ := (((χ₁ * χ₂⁻¹) (unifUnit F) : ℂˣ) : ℂ) with hc`. Establish `hc0 : c ≠ 0` using `Units.ne_zero _`. Establish `hsum : ∀ s : ℂ, -quasiCharExponent (χ₁ * χ₂⁻¹) < 2 * s.re → localSection χ₁ χ₂ s Φ = (∑ m ∈ Finset.Ico M N, (c ^ m * ((residueCard F : ℂ) ^ (-(2 * s))) ^ m) • localSection χ₁ χ₂ s (shellPiece Φ m)) + Φ 0 • localSection χ₁ χ₂ s (boxInd F N)`. Introduce `s hs`.

Use `conv_lhs => rw [eq_sum_shells hMN hinv hsupp]`. Rewrite using `[localSection_add h₁ h₂ hs (sum_mem fun m _ ↦ indicator_shellAt_mem hΦ m) (Submodule.smul_mem _ _ (boxInd_mem N)), localSection_finset_sum h₁ h₂ hs _ (fun m _ ↦ indicator_shellAt_mem hΦ m), localSection_smul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun m _ ↦ ?_` and prove the remaining obligations. Rewrite using `[indicator_shellAt_eq, localSection_dilate]`.

Distinguish the cases in `hμ : IsUnramifiedChar (χ₁ * χ₂⁻¹)`. Use `⟨Finset.Ico M (N + 1), shellPiece Φ, fun m ↦ if m < N then LaurentPolynomial.C (c ^ m) * LaurentPolynomial.T m - LaurentPolynomial.C (c ^ (m + 1)) * LaurentPolynomial.T (m + 1) else LaurentPolynomial.C (c ^ N) * LaurentPolynomial.T N, fun m ↦ ⟨shellPiece_mem hΦ m, support_shellPi …` and prove the remaining obligations. Establish `hT0 : T ≠ 0` using `qpow_ne_zero _`. Establish `hne : 1 - c * T ≠ 0` using `one_sub_quasiChar_unifUnit_mul_qpow_ne_zero (continuous_mul_inv h₁ h₂) (by simpa using hs)`. Establish `hL : localLFactor (χ₁ * χ₂⁻¹) (2 * s) = (1 - c * T)⁻¹` using `localLFactor_of_isUnramified hμ _`.

Establish `hbox` using `one_sub_mul_localSection_boxInd h₁ h₂ hs N`. Rewrite `hbox` using `[← hc, ← hT]`. Establish `hbox' : localSection χ₁ χ₂ s (boxInd F N) = ((1 - c * T)⁻¹ * (c ^ N * T ^ N)) • localSection χ₁ χ₂ s (shellInd F)`. Rewrite using `[mul_smul, ← hbox, smul_smul, inv_mul_cancel₀ hne, one_smul]`. Establish `hI : Finset.Ico M (N + 1) = insert N (Finset.Ico M N)`.

Use extensionality with `k`. Simplify using `only [Finset.mem_Ico, Finset.mem_insert]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hsum s hs, hL, hI, Finset.sum_insert (by simp)]`. Use `beta_reduce`.

Rewrite using `[if_neg (lt_irrefl N), evalQpow_C_mul_T, ← hT, shellPiece_eq_smul_shellInd hinv, localSection_smul, hbox', smul_add]`. Use `conv_rhs => rw [add_comm]`. Use `congr 1`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun m hm ↦ ?_` and prove the remaining obligations.

Establish `hmN : m < N` using `(Finset.mem_Ico.1 hm).2`. Rewrite using `[if_pos hmN, evalQpow_sub, evalQpow_C_mul_T, evalQpow_C_mul_T, ← hT, smul_smul]`. Use `congr 1`. Rewrite using `[zpow_add₀ hc0, zpow_add₀ hT0, zpow_one, zpow_one]`. Clear the denominators using the available nonvanishing facts.

Simplify using `only [smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `⟨Finset.Ico M N, shellPiece Φ, fun m ↦ LaurentPolynomial.C (c ^ m) * LaurentPolynomial.T m, fun m ↦ ⟨shellPiece_mem hΦ m, support_shellPiece_subset Φ m⟩, fun s hs ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[hsum s hs, localSection_boxInd_of_not_isUnramified χ₁ χ₂ hμ, smul_zero, add_zero, localLFactor_of_not_isUnramified hμ, one_smul]`.

Use `Finset.sum_congr rfl fun m _ ↦ ?_` and prove the remaining obligations. Rewrite using `[evalQpow_C_mul_T]`.
-/
theorem exists_localSection_eq_localLFactor_mul {χ₁ χ₂ : Fˣ →* ℂˣ} (h₁ : Continuous χ₁)
    (h₂ : Continuous χ₂) {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) :
    ∃ (t : Finset ℤ) (Ψ : ℤ → (Fin 2 → F) → ℂ) (P : ℤ → LaurentPolynomial ℂ),
      (∀ m, Ψ m ∈ schwartzBruhat2 F ∧ Function.support (Ψ m) ⊆ shell F) ∧
      ∀ s : ℂ, -quasiCharExponent (χ₁ * χ₂⁻¹) < 2 * s.re →
        localSection χ₁ χ₂ s Φ = localLFactor (χ₁ * χ₂⁻¹) (2 * s) •
          ∑ m ∈ t, evalQpow F (P m) (2 * s) • localSection χ₁ χ₂ s (Ψ m) := by
  obtain ⟨N, M, hMN, hinv, hsupp⟩ := exists_invariant_of_mem_schwartzBruhat2 hΦ
  set c : ℂ := (((χ₁ * χ₂⁻¹) (unifUnit F) : ℂˣ) : ℂ) with hc
  have hc0 : c ≠ 0 := Units.ne_zero _

  have hsum : ∀ s : ℂ, -quasiCharExponent (χ₁ * χ₂⁻¹) < 2 * s.re →
      localSection χ₁ χ₂ s Φ = (∑ m ∈ Finset.Ico M N,
        (c ^ m * ((residueCard F : ℂ) ^ (-(2 * s))) ^ m) • localSection χ₁ χ₂ s (shellPiece Φ m)) +
        Φ 0 • localSection χ₁ χ₂ s (boxInd F N) := by
    intro s hs
    conv_lhs => rw [eq_sum_shells hMN hinv hsupp]
    rw [localSection_add h₁ h₂ hs (sum_mem fun m _ ↦ indicator_shellAt_mem hΦ m)
      (Submodule.smul_mem _ _ (boxInd_mem N)), localSection_finset_sum h₁ h₂ hs _
      (fun m _ ↦ indicator_shellAt_mem hΦ m), localSection_smul]
    congr 1
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [indicator_shellAt_eq, localSection_dilate]
  by_cases hμ : IsUnramifiedChar (χ₁ * χ₂⁻¹)
  · refine ⟨Finset.Ico M (N + 1), shellPiece Φ, fun m ↦ if m < N then
      LaurentPolynomial.C (c ^ m) * LaurentPolynomial.T m -
        LaurentPolynomial.C (c ^ (m + 1)) * LaurentPolynomial.T (m + 1)
      else LaurentPolynomial.C (c ^ N) * LaurentPolynomial.T N,
      fun m ↦ ⟨shellPiece_mem hΦ m, support_shellPiece_subset Φ m⟩, fun s hs ↦ ?_⟩
    set T : ℂ := (residueCard F : ℂ) ^ (-(2 * s)) with hT
    have hT0 : T ≠ 0 := qpow_ne_zero _
    have hne : 1 - c * T ≠ 0 :=
      one_sub_quasiChar_unifUnit_mul_qpow_ne_zero (continuous_mul_inv h₁ h₂) (by simpa using hs)
    have hL : localLFactor (χ₁ * χ₂⁻¹) (2 * s) = (1 - c * T)⁻¹ := localLFactor_of_isUnramified hμ _
    have hbox := one_sub_mul_localSection_boxInd h₁ h₂ hs N
    rw [← hc, ← hT] at hbox
    have hbox' : localSection χ₁ χ₂ s (boxInd F N) =
        ((1 - c * T)⁻¹ * (c ^ N * T ^ N)) • localSection χ₁ χ₂ s (shellInd F) := by
      rw [mul_smul, ← hbox, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have hI : Finset.Ico M (N + 1) = insert N (Finset.Ico M N) := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hsum s hs, hL, hI, Finset.sum_insert (by simp)]
    beta_reduce
    rw [if_neg (lt_irrefl N), evalQpow_C_mul_T,
      ← hT, shellPiece_eq_smul_shellInd hinv, localSection_smul, hbox', smul_add]
    conv_rhs => rw [add_comm]
    congr 1
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      have hmN : m < N := (Finset.mem_Ico.1 hm).2
      rw [if_pos hmN, evalQpow_sub, evalQpow_C_mul_T, evalQpow_C_mul_T, ← hT, smul_smul]
      congr 1
      rw [zpow_add₀ hc0, zpow_add₀ hT0, zpow_one, zpow_one]
      field_simp
    · simp only [smul_smul]
      congr 1
      ring
  · refine ⟨Finset.Ico M N, shellPiece Φ,
      fun m ↦ LaurentPolynomial.C (c ^ m) * LaurentPolynomial.T m,
      fun m ↦ ⟨shellPiece_mem hΦ m, support_shellPiece_subset Φ m⟩, fun s hs ↦ ?_⟩
    rw [hsum s hs, localSection_boxInd_of_not_isUnramified χ₁ χ₂ hμ, smul_zero, add_zero,
      localLFactor_of_not_isUnramified hμ, one_smul]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [evalQpow_C_mul_T]

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Use `mem_box.2 fun j ↦ ?_` and prove the remaining obligations. Simplify using `only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]`. Establish `h : ∀ i, x i * (k : Matrix (Fin 2) (Fin 2) F) i j ∈ valBall F n` using `fun i ↦ by`. Simplify using `using mul_mem_valBall (mem_box.1 hx i) (mem_valBall_zero_iff.2 (hk i j))`. Conclude with `add_mem (h 0) (h 1)`.
-/
theorem vecMul_mem_box {k : GL (Fin 2) F} (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F])
    {n : ℤ} {x : Fin 2 → F} (hx : x ∈ box F n) :
    x ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∈ box F n := by
  refine mem_box.2 fun j ↦ ?_
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have h : ∀ i, x i * (k : Matrix (Fin 2) (Fin 2) F) i j ∈ valBall F n := fun i ↦ by
    simpa using mul_mem_valBall (mem_box.1 hx i) (mem_valBall_zero_iff.2 (hk i j))
  exact add_mem (h 0) (h 1)

omit [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
Take `⟨hk1, hk2⟩` from `(GLnLocal.mem_integralGL_iff F 2).1 hk`. Use `⟨fun h ↦ ?_, vecMul_mem_box hk1⟩` and prove the remaining obligations. Use `vecMul_mem_box (k := k⁻¹) hk2 h` as an intermediate fact. Rewrite `this` using `[Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]`. Then use the resulting hypothesis.
-/
theorem vecMul_mem_box_iff {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) (n : ℤ)
    (x : Fin 2 → F) : x ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∈ box F n ↔ x ∈ box F n := by
  obtain ⟨hk1, hk2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  refine ⟨fun h ↦ ?_, vecMul_mem_box hk1⟩
  have := vecMul_mem_box (k := k⁻¹) hk2 h
  rwa [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.vecMul_one] at this

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Simplify using `only [shell, Set.mem_sdiff, SetLike.mem_coe, vecMul_mem_box_iff hk]`.
-/
theorem vecMul_mem_shell_iff {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2)
    (x : Fin 2 → F) : x ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∈ shell F ↔ x ∈ shell F := by
  simp only [shell, Set.mem_sdiff, SetLike.mem_coe, vecMul_mem_box_iff hk]

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Use `⟨mem_box.2 fun i ↦ ?_, fun h ↦ ?_⟩` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> simp [mem_valBall_zero_iff, zero_mem, one_mem]`. Use `mem_box.1 h 1` as an intermediate fact. Rewrite `this` using `[mem_valBall_iff_le_ord (by simp)]`. Simplify using `[ord] at this`.
-/
theorem zero_one_mem_shell : (![0, 1] : Fin 2 → F) ∈ shell F := by
  refine ⟨mem_box.2 fun i ↦ ?_, fun h ↦ ?_⟩
  · fin_cases i <;> simp [mem_valBall_zero_iff, zero_mem, one_mem]
  · have := mem_box.1 h 1
    rw [mem_valBall_iff_le_ord (by simp)] at this
    simp [ord] at this

omit [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
Establish `hr` using `(vecMul_mem_shell_iff hk ![0, 1]).2 zero_one_mem_shell`. Establish `he : ![0, (t : F)] ᵥ* (k : Matrix (Fin 2) (Fin 2) F) = (t : F) • (![0, 1] ᵥ* (k : Matrix (Fin 2) (Fin 2) F))`. Rewrite using `[vecMul_zero_cons, vecMul_zero_cons]`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.

Rewrite using `[he]`. Simplify using `only [shell, Set.mem_sdiff, SetLike.mem_coe, smul_mem_box_iff, zero_sub]`. Take `⟨hr0, hr1⟩` from `hr`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ha, hb⟩`.

Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne hne with hlt | hgt` into its components or cases. Conclude with `hr1 (box_antitone (by omega) ha)`. Conclude with `hb (box_antitone (by omega) hr0)`. Introduce `h0`.

Rewrite using `[h0]`. Conclude with `⟨by simpa using hr0, by simpa using hr1⟩`.
-/
theorem vecMul_zero_cons_mem_shell_iff {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2)
    (t : Fˣ) : ![0, (t : F)] ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∈ shell F ↔ ord (t : F) = 0 := by
  have hr := (vecMul_mem_shell_iff hk ![0, 1]).2 zero_one_mem_shell
  have he : ![0, (t : F)] ᵥ* (k : Matrix (Fin 2) (Fin 2) F) =
      (t : F) • (![0, 1] ᵥ* (k : Matrix (Fin 2) (Fin 2) F)) := by
    rw [vecMul_zero_cons, vecMul_zero_cons]
    funext j
    simp
  rw [he]
  simp only [shell, Set.mem_sdiff, SetLike.mem_coe, smul_mem_box_iff, zero_sub]
  obtain ⟨hr0, hr1⟩ := hr
  constructor
  · rintro ⟨ha, hb⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hr1 (box_antitone (by omega) ha)
    · exact hb (box_antitone (by omega) hr0)
  · intro h0
    rw [h0]
    exact ⟨by simpa using hr0, by simpa using hr1⟩

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
The claim follows from `(mem_valBall_iff_le_ord hx0).1 (mem_valBall_zero_iff.2 hx)`.
-/
theorem ord_nonneg_of_mem_integers {x : F} (hx0 : x ≠ 0) (hx : x ∈ 𝒪[F]) : 0 ≤ ord x :=
  (mem_valBall_iff_le_ord hx0).1 (mem_valBall_zero_iff.2 hx)

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]`. Conclude with `sub_mem (mul_mem (hk 0 0) (hk 1 1)) (mul_mem (hk 0 1) (hk 1 0))`.
-/
theorem det_mem_integers {k : GL (Fin 2) F} (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F]) :
    (Matrix.GeneralLinearGroup.det k : F) ∈ 𝒪[F] := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  exact sub_mem (mul_mem (hk 0 0) (hk 1 1)) (mul_mem (hk 0 1) (hk 1 0))

omit [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
Take `⟨hk1, hk2⟩` from `(GLnLocal.mem_integralGL_iff F 2).1 hk`. Establish `h1` using `ord_nonneg_of_mem_integers (detU k).ne_zero (det_mem_integers hk1)`. Establish `h2` using `ord_nonneg_of_mem_integers (detU k⁻¹).ne_zero (det_mem_integers hk2)`. Establish `hinv : detU k⁻¹ = (detU k)⁻¹` using `map_inv _ k`. Rewrite `h2` using `[hinv, Units.val_inv_eq_inv_val, ord_inv (detU k).ne_zero]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem ord_det_eq_zero {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    ord (detU k : F) = 0 := by
  obtain ⟨hk1, hk2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  have h1 := ord_nonneg_of_mem_integers (detU k).ne_zero (det_mem_integers hk1)
  have h2 := ord_nonneg_of_mem_integers (detU k⁻¹).ne_zero (det_mem_integers hk2)
  have hinv : detU k⁻¹ = (detU k)⁻¹ := map_inv _ k
  rw [hinv, Units.val_inv_eq_inv_val, ord_inv (detU k).ne_zero] at h2
  omega

/- English proof (translation)
Establish `hdet : modPow (detU k : F) s = 1`. Rewrite using `[modPow_units_eq_zpow, ord_det_eq_zero hk, zpow_zero]`. Simplify using `only [localSection, hdet, mul_one, localZeta]`. Use `congr 1`. Use `integral_congr_ae (Eventually.of_forall fun u ↦ ?_)` and prove the remaining obligations.

Distinguish the cases in `hu : slice Ψ k u = 0`. Simplify using `[hu]`. Establish `hord : ord (u : F) = 0` using `(vecMul_zero_cons_mem_shell_iff hk u).1 (hΨ hu)`. Establish `: ((modulus (u : F) : ℝ) : ℂ) ^ (2 * s) = 1`. Rewrite using `[← modPow, modPow_units_eq_zpow, hord, zpow_zero]`.

Simplify using `only [this, mul_one]`.
-/
theorem localSection_eq_of_support_subset_shell (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ)
    {Ψ : (Fin 2 → F) → ℂ} (hΨ : Function.support Ψ ⊆ shell F) {k : GL (Fin 2) F}
    (hk : k ∈ GLnLocal.integralGL F 2) :
    localSection χ₁ χ₂ s Ψ k = (χ₁ (detU k) : ℂ) *
      ∫ u, slice Ψ k u * (((χ₁ * χ₂⁻¹) u : ℂˣ) : ℂ) ∂multHaar F := by
  have hdet : modPow (detU k : F) s = 1 := by
    rw [modPow_units_eq_zpow, ord_det_eq_zero hk, zpow_zero]
  simp only [localSection, hdet, mul_one, localZeta]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
  by_cases hu : slice Ψ k u = 0
  · simp [hu]
  · have hord : ord (u : F) = 0 :=
      (vecMul_zero_cons_mem_shell_iff hk u).1 (hΨ hu)
    have : ((modulus (u : F) : ℝ) : ℂ) ^ (2 * s) = 1 := by
      rw [← modPow, modPow_units_eq_zpow, hord, zpow_zero]
    simp only [this, mul_one]

/- English proof (translation)
Rewrite using `[localSection_eq_of_support_subset_shell χ₁ χ₂ s hΨ hk, localSection_eq_of_support_subset_shell χ₁ χ₂ s' hΨ hk]`.
-/
theorem localSection_flat (χ₁ χ₂ : Fˣ →* ℂˣ) (s s' : ℂ) {Ψ : (Fin 2 → F) → ℂ}
    (hΨ : Function.support Ψ ⊆ shell F) {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    localSection χ₁ χ₂ s Ψ k = localSection χ₁ χ₂ s' Ψ k := by
  rw [localSection_eq_of_support_subset_shell χ₁ χ₂ s hΨ hk,
    localSection_eq_of_support_subset_shell χ₁ χ₂ s' hΨ hk]

/- English proof (translation)
The claim follows from `isUnramifiedChar_iff.1 h u hu`.
-/
theorem apply_eq_one_of_isUnramified {χ : Fˣ →* ℂˣ} (h : IsUnramifiedChar χ) {u : Fˣ}
    (hu : ord (u : F) = 0) : χ u = 1 :=
  isUnramifiedChar_iff.1 h u hu

/- English proof (translation)
Rewrite using `[localSection_eq_of_support_subset_shell χ₁ χ₂ s (Ψ := shellInd F) Set.support_indicator_subset hk, apply_eq_one_of_isUnramified hu₁ (ord_det_eq_zero hk), Units.val_one, one_mul]`. Establish `hpt : (fun u : Fˣ ↦ slice (shellInd F) k u * (((χ₁ * χ₂⁻¹) u : ℂˣ) : ℂ)) = (ordShell F 0).indicator 1`. Use function extensionality and compare the values at `u`. Distinguish the cases in `hu : ord (u : F) = 0`. Establish `hmem : ![0, (u : F)] ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∈ shell F` using `(vecMul_zero_cons_mem_shell_iff hk u).2 hu`.

Establish `h1 : χ₁ u = 1` using `apply_eq_one_of_isUnramified hu₁ hu`. Establish `h2 : χ₂ u = 1` using `apply_eq_one_of_isUnramified hu₂ hu`. Simplify using `[slice, shellInd, Set.indicator_of_mem hmem, h1, h2, Set.indicator_of_mem (show u ∈ ordShell F 0 from hu)]`. Establish `hmem : ![0, (u : F)] ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∉ shell F` using `fun h ↦ hu ((vecMul_zero_cons_mem_shell_iff hk u).1 h)`. Simplify using `[slice, shellInd, Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show u ∉ ordShell F 0 from hu)]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[integral_indicator (measurableSet_ordShell 0)]`. Simplify using `[measureReal_def, multHaar_ordShell]`.
-/
theorem localSection_shellInd_of_mem {χ₁ χ₂ : Fˣ →* ℂˣ} (hu₁ : IsUnramifiedChar χ₁)
    (hu₂ : IsUnramifiedChar χ₂) (s : ℂ) {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    localSection χ₁ χ₂ s (shellInd F) k = 1 := by
  rw [localSection_eq_of_support_subset_shell χ₁ χ₂ s (Ψ := shellInd F) Set.support_indicator_subset hk,
    apply_eq_one_of_isUnramified hu₁ (ord_det_eq_zero hk), Units.val_one, one_mul]
  have hpt : (fun u : Fˣ ↦ slice (shellInd F) k u * (((χ₁ * χ₂⁻¹) u : ℂˣ) : ℂ)) =
      (ordShell F 0).indicator 1 := by
    funext u
    by_cases hu : ord (u : F) = 0
    · have hmem : ![0, (u : F)] ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∈ shell F :=
        (vecMul_zero_cons_mem_shell_iff hk u).2 hu
      have h1 : χ₁ u = 1 := apply_eq_one_of_isUnramified hu₁ hu
      have h2 : χ₂ u = 1 := apply_eq_one_of_isUnramified hu₂ hu
      simp [slice, shellInd, Set.indicator_of_mem hmem, h1, h2,
        Set.indicator_of_mem (show u ∈ ordShell F 0 from hu)]
    · have hmem : ![0, (u : F)] ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∉ shell F :=
        fun h ↦ hu ((vecMul_zero_cons_mem_shell_iff hk u).1 h)
      simp [slice, shellInd, Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem (show u ∉ ordShell F 0 from hu)]
  calc ∫ u, slice (shellInd F) k u * (((χ₁ * χ₂⁻¹) u : ℂˣ) : ℂ) ∂multHaar F
      = ∫ u, (ordShell F 0).indicator (1 : Fˣ → ℂ) u ∂multHaar F := by rw [hpt]
    _ = 1 := by
      rw [integral_indicator (measurableSet_ordShell 0)]
      simp [measureReal_def, multHaar_ordShell]

/- English proof (translation)
Establish `hμ : IsUnramifiedChar (χ₁ * χ₂⁻¹)`. Rewrite using `[isUnramifiedChar_iff]`. Introduce `u hu`. Simplify using `[apply_eq_one_of_isUnramified hu₁ hu, apply_eq_one_of_isUnramified hu₂ hu]`. Establish `hne : 1 - (((χ₁ * χ₂⁻¹) (unifUnit F) : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-(2 * s)) ≠ 0` using `one_sub_quasiChar_unifUnit_mul_qpow_ne_zero (continuous_mul_inv h₁ h₂) (by simpa using hs)`.

Establish `h` using `congrFun (one_sub_mul_localSection_boxInd h₁ h₂ hs 0) k`. Simplify using `only [Pi.smul_apply, smul_eq_mul, zpow_zero, mul_one, one_mul, localSection_shellInd_of_mem hu₁ hu₂ s hk] at h`. Rewrite using `[localLFactor_of_isUnramified hμ]`. Conclude with `eq_inv_of_mul_eq_one_right h`.
-/
theorem localSection_boxInd_zero_of_mem {χ₁ χ₂ : Fˣ →* ℂˣ} (h₁ : Continuous χ₁)
    (h₂ : Continuous χ₂) (hu₁ : IsUnramifiedChar χ₁) (hu₂ : IsUnramifiedChar χ₂) {s : ℂ}
    (hs : -quasiCharExponent (χ₁ * χ₂⁻¹) < 2 * s.re) {k : GL (Fin 2) F}
    (hk : k ∈ GLnLocal.integralGL F 2) :
    localSection χ₁ χ₂ s (boxInd F 0) k = localLFactor (χ₁ * χ₂⁻¹) (2 * s) := by
  have hμ : IsUnramifiedChar (χ₁ * χ₂⁻¹) := by
    rw [isUnramifiedChar_iff]
    intro u hu
    simp [apply_eq_one_of_isUnramified hu₁ hu, apply_eq_one_of_isUnramified hu₂ hu]
  have hne : 1 - (((χ₁ * χ₂⁻¹) (unifUnit F) : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-(2 * s)) ≠ 0 :=
    one_sub_quasiChar_unifUnit_mul_qpow_ne_zero (continuous_mul_inv h₁ h₂) (by simpa using hs)
  have h := congrFun (one_sub_mul_localSection_boxInd h₁ h₂ hs 0) k
  simp only [Pi.smul_apply, smul_eq_mul, zpow_zero, mul_one, one_mul,
    localSection_shellInd_of_mem hu₁ hu₂ s hk] at h
  rw [localLFactor_of_isUnramified hμ]
  exact eq_inv_of_mul_eq_one_right h

/- English proof (translation)
Establish `hR : rightTranslate k (boxInd F 0) = boxInd F 0`. Use function extensionality and compare the values at `x`. Simplify using `only [rightTranslate, boxInd]`. Distinguish the cases in `hx : x ∈ box F 0`. Establish `h' : x ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∈ (box F 0 : Set (Fin 2 → F))` using `(vecMul_mem_box_iff hk 0 x).2 hx`.

Rewrite using `[Set.indicator_of_mem (show x ∈ (box F 0 : Set (Fin 2 → F)) from hx), Set.indicator_of_mem h']`. Both sides reduce to the same expression. Establish `h' : x ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∉ (box F 0 : Set (Fin 2 → F))` using `fun h ↦ hx ((vecMul_mem_box_iff hk 0 x).1 h)`. Rewrite using `[Set.indicator_of_notMem (show x ∉ (box F 0 : Set (Fin 2 → F)) from hx), Set.indicator_of_notMem h']`. Rewrite using `[localSection_mul, hR, apply_eq_one_of_isUnramified hu₁ (ord_det_eq_zero hk), modPow_units_eq_zpow, ord_det_eq_zero hk]`.

Simplify using the standard rewrite rules.
-/
theorem localSection_boxInd_zero_mul {χ₁ χ₂ : Fˣ →* ℂˣ} (hu₁ : IsUnramifiedChar χ₁) (s : ℂ)
    (g : GL (Fin 2) F) {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    localSection χ₁ χ₂ s (boxInd F 0) (g * k) = localSection χ₁ χ₂ s (boxInd F 0) g := by
  have hR : rightTranslate k (boxInd F 0) = boxInd F 0 := by
    funext x
    simp only [rightTranslate, boxInd]
    by_cases hx : x ∈ box F 0
    · have h' : x ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∈ (box F 0 : Set (Fin 2 → F)) :=
        (vecMul_mem_box_iff hk 0 x).2 hx
      rw [Set.indicator_of_mem (show x ∈ (box F 0 : Set (Fin 2 → F)) from hx),
        Set.indicator_of_mem h']
      rfl
    · have h' : x ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∉ (box F 0 : Set (Fin 2 → F)) :=
        fun h ↦ hx ((vecMul_mem_box_iff hk 0 x).1 h)
      rw [Set.indicator_of_notMem (show x ∉ (box F 0 : Set (Fin 2 → F)) from hx),
        Set.indicator_of_notMem h']
  rw [localSection_mul, hR, apply_eq_one_of_isUnramified hu₁ (ord_det_eq_zero hk),
    modPow_units_eq_zpow, ord_det_eq_zero hk]
  simp

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Rewrite `hy` using `[← map_pow, ← normalizedValuation_le_iff, map_pow, normalizedValuation_uniformizer (GLnLocal.irreducible_uniformizer F), ← WithZero.exp_nsmul]`. Rewrite using `[mem_valBall]`. Simplify using `using hy`.
-/
theorem mem_valBall_of_valuation_le {y : F} {m : ℕ}
    (hy : ValuativeRel.valuation F y ≤ ValuativeRel.valuation F (GLnLocal.uniformizer F : F) ^ m) :
    y ∈ valBall F m := by
  rw [← map_pow, ← normalizedValuation_le_iff, map_pow,
    normalizedValuation_uniformizer (GLnLocal.irreducible_uniformizer F), ← WithZero.exp_nsmul]
    at hy
  rw [mem_valBall]
  simpa using hy

omit [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
The claim follows from `mem_valBall_of_valuation_le (((GLnLocal.mem_congruenceSubgroup_iff F 2).1 hu).2 i j)`.
-/
theorem sub_one_mem_valBall_of_mem_congruenceSubgroup {m : ℕ} {u : GL (Fin 2) F}
    (hu : u ∈ GLnLocal.congruenceSubgroup F 2 m) (i j : Fin 2) :
    (u : Matrix (Fin 2) (Fin 2) F) i j - (1 : Matrix (Fin 2) (Fin 2) F) i j ∈ valBall F m :=
  mem_valBall_of_valuation_le (((GLnLocal.mem_congruenceSubgroup_iff F 2).1 hu).2 i j)

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Establish `h` using `sub_one_mem_valBall_of_mem_congruenceSubgroup hu`. Establish `h00` using `h 0 0`. Establish `h01` using `h 0 1`. Establish `h10` using `h 1 0`. Establish `h11` using `h 1 1`.

Simplify using `only [Matrix.one_apply_eq, ne_eq, zero_ne_one, not_false_eq_true, Matrix.one_apply_ne, one_ne_zero, sub_zero] at h00 h01 h10 h11`. Establish `hmm : valBall F ((m : ℤ) + m) ≤ valBall F m` using `valBall_antitone (by omega)`. Establish `e : (detU u : F) - 1 = ((u : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) + ((u : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) + ((u : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) * ((u : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) - (u : Matrix (Fin 2) (Fin 2) F) 0 1 * (u : Matrix (Fin 2) (Fin 2) F) 1 0`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `sub_mem (add_mem (add_mem h00 h11) (hmm (mul_mem_valBall h00 h11))) (hmm (mul_mem_valBall h01 h10))`.
-/
theorem det_sub_one_mem_valBall {m : ℕ} {u : GL (Fin 2) F}
    (hu : u ∈ GLnLocal.congruenceSubgroup F 2 m) : (detU u : F) - 1 ∈ valBall F m := by
  have h := sub_one_mem_valBall_of_mem_congruenceSubgroup hu
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp only [Matrix.one_apply_eq, ne_eq, zero_ne_one, not_false_eq_true, Matrix.one_apply_ne,
    one_ne_zero, sub_zero] at h00 h01 h10 h11
  have hmm : valBall F ((m : ℤ) + m) ≤ valBall F m := valBall_antitone (by omega)
  have e : (detU u : F) - 1 = ((u : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) +
      ((u : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) +
      ((u : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) * ((u : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) -
      (u : Matrix (Fin 2) (Fin 2) F) 0 1 * (u : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    ring
  rw [e]
  exact sub_mem (add_mem (add_mem h00 h11) (hmm (mul_mem_valBall h00 h11)))
    (hmm (mul_mem_valBall h01 h10))

/- English proof (translation)
Take `⟨N, M, hMN, hinv, hsupp⟩` from `exists_invariant_of_mem_schwartzBruhat2 hΦ`. Use `⟨max (N - M).toNat (max (quasiCharConductor χ₁) 1), fun g u hu ↦ ?_⟩` and prove the remaining obligations. Use `set m := max (N - M).toNat (max (quasiCharConductor χ₁) 1) with hm`. Establish `hu0 : u ∈ GLnLocal.integralGL F 2` using `GLnLocal.congruenceSubgroup_le F 2 m hu`. Establish `hR : rightTranslate u Φ = Φ`.

Use function extensionality and compare the values at `x`. Simplify using `only [rightTranslate]`. Distinguish the cases in `hx : x ∈ box F M`. Use `set D : Matrix (Fin 2) (Fin 2) F := (u : Matrix (Fin 2) (Fin 2) F) - 1 with hD`. Establish `hxD : x ᵥ* D ∈ box F N`.

Use `box_antitone (show N ≤ M + m by omega) (mem_box.2 fun j ↦ ?_)` and prove the remaining obligations. Simplify using `only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]`. Conclude with `add_mem (mul_mem_valBall (mem_box.1 hx 0) (sub_one_mem_valBall_of_mem_congruenceSubgroup hu 0 j)) (mul_mem_valBall (mem_box.1 hx 1) (sub_one_mem_valBall_of_mem_congruenceSubgroup hu 1 j))`. Establish `he : x ᵥ* (u : Matrix (Fin 2) (Fin 2) F) = x + x ᵥ* D`. Rewrite using `[hD, Matrix.vecMul_sub, Matrix.vecMul_one]`.

Normalize the expressions using the abelian group laws. Rewrite using `[he, hinv x _ hxD]`. Establish `h0 : Φ x = 0`. Assume the negation of the conclusion as `h`. Conclude with `hx (hsupp x h)`.

Establish `h1 : Φ (x ᵥ* (u : Matrix (Fin 2) (Fin 2) F)) = 0`. Assume the negation of the conclusion as `h`. Conclude with `hx ((vecMul_mem_box_iff hu0 M x).1 (hsupp _ h))`. Rewrite using `[h0, h1]`. Establish `hdet : χ₁ (detU u) = 1`.

Establish `hmem : detU u ∈ unitFiltrationUnits F m` using `(mem_unitFiltrationUnits_iff_valBall (by omega)).2 (det_sub_one_mem_valBall hu)`. Conclude with `unitFiltrationUnits_quasiCharConductor_le_ker h₁ (unitFiltrationUnits_antitone (by omega) hmem)`. Rewrite using `[localSection_mul, hR, hdet, modPow_units_eq_zpow, ord_det_eq_zero hu0]`. Simplify using the standard rewrite rules.
-/
theorem isSmooth_localSection {χ₁ : Fˣ →* ℂˣ} (h₁ : Continuous χ₁) (χ₂ : Fˣ →* ℂˣ) (s : ℂ)
    {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) :
    IsSmooth (localSection χ₁ χ₂ s Φ) := by
  obtain ⟨N, M, hMN, hinv, hsupp⟩ := exists_invariant_of_mem_schwartzBruhat2 hΦ
  refine ⟨max (N - M).toNat (max (quasiCharConductor χ₁) 1), fun g u hu ↦ ?_⟩
  set m := max (N - M).toNat (max (quasiCharConductor χ₁) 1) with hm
  have hu0 : u ∈ GLnLocal.integralGL F 2 := GLnLocal.congruenceSubgroup_le F 2 m hu
  have hR : rightTranslate u Φ = Φ := by
    funext x
    simp only [rightTranslate]
    by_cases hx : x ∈ box F M
    · set D : Matrix (Fin 2) (Fin 2) F := (u : Matrix (Fin 2) (Fin 2) F) - 1 with hD
      have hxD : x ᵥ* D ∈ box F N := by
        refine box_antitone (show N ≤ M + m by omega) (mem_box.2 fun j ↦ ?_)
        simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
        exact add_mem (mul_mem_valBall (mem_box.1 hx 0)
            (sub_one_mem_valBall_of_mem_congruenceSubgroup hu 0 j))
          (mul_mem_valBall (mem_box.1 hx 1)
            (sub_one_mem_valBall_of_mem_congruenceSubgroup hu 1 j))
      have he : x ᵥ* (u : Matrix (Fin 2) (Fin 2) F) = x + x ᵥ* D := by
        rw [hD, Matrix.vecMul_sub, Matrix.vecMul_one]
        abel
      rw [he, hinv x _ hxD]
    · have h0 : Φ x = 0 := by
        by_contra h
        exact hx (hsupp x h)
      have h1 : Φ (x ᵥ* (u : Matrix (Fin 2) (Fin 2) F)) = 0 := by
        by_contra h
        exact hx ((vecMul_mem_box_iff hu0 M x).1 (hsupp _ h))
      rw [h0, h1]
  have hdet : χ₁ (detU u) = 1 := by
    have hmem : detU u ∈ unitFiltrationUnits F m :=
      (mem_unitFiltrationUnits_iff_valBall (by omega)).2 (det_sub_one_mem_valBall hu)
    exact unitFiltrationUnits_quasiCharConductor_le_ker h₁
      (unitFiltrationUnits_antitone (by omega) hmem)
  rw [localSection_mul, hR, hdet, modPow_units_eq_zpow, ord_det_eq_zero hu0]
  simp

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
The claim follows from `fun g u hu ↦ hf g u (GLnLocal.congruenceSubgroup_antitone F 2 h hu)`.
-/
theorem IsSmooth.mono {f : GL (Fin 2) F → ℂ} {m : ℕ}
    (hf : ∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, f (g * u) = f g) {m' : ℕ} (h : m ≤ m') :
    ∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m', f (g * u) = f g :=
  fun g u hu ↦ hf g u (GLnLocal.congruenceSubgroup_antitone F 2 h hu)

def smoothPrincipalSeries (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) : Submodule ℂ (GL (Fin 2) F → ℂ) where
  carrier := {f | f ∈ principalSeries χ₁ χ₂ s ∧ IsSmooth f}
  add_mem' {f₁ f₂} h₁ h₂ := by
    refine ⟨add_mem h₁.1 h₂.1, ?_⟩
    obtain ⟨m₁, hm₁⟩ := h₁.2
    obtain ⟨m₂, hm₂⟩ := h₂.2
    refine ⟨max m₁ m₂, fun g u hu ↦ ?_⟩
    simp only [Pi.add_apply, IsSmooth.mono hm₁ (le_max_left _ _) g u hu,
      IsSmooth.mono hm₂ (le_max_right _ _) g u hu]
  zero_mem' := ⟨zero_mem _, 0, fun _ _ _ ↦ rfl⟩
  smul_mem' c f h := by
    refine ⟨Submodule.smul_mem _ c h.1, ?_⟩
    obtain ⟨m, hm⟩ := h.2
    exact ⟨m, fun g u hu ↦ by simp only [Pi.smul_apply, hm g u hu]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨localSection_mem_principalSeries χ₁ χ₂ s Φ, isSmooth_localSection h₁ χ₂ s hΦ⟩`.
-/
theorem localSection_mem_smoothPrincipalSeries {χ₁ : Fˣ →* ℂˣ} (h₁ : Continuous χ₁)
    (χ₂ : Fˣ →* ℂˣ) (s : ℂ) {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) :
    localSection χ₁ χ₂ s Φ ∈ smoothPrincipalSeries χ₁ χ₂ s :=
  ⟨localSection_mem_principalSeries χ₁ χ₂ s Φ, isSmooth_localSection h₁ χ₂ s hΦ⟩

end

end GroundTheory.Automorphic.GodementSectionLocal
