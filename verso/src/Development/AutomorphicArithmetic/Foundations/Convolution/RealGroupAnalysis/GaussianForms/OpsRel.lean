import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.FtBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.MeasScale

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

/- English proof (translation)
Simplify using `[ψ]`.
-/
private lemma psi_zero {F : Type} [Field F] [NumberField F] : ψ (0 : A F) = 1 := by
  simp [ψ]

/- English proof (translation)
Simplify using `[ψ, AddChar.map_add_eq_mul]`.
-/
private lemma psi_add {F : Type} [Field F] [NumberField F] (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp [ψ, AddChar.map_add_eq_mul]

/- English proof (translation)
Simplify using `[ab]`.
-/
private lemma ab_one {F : Type} [Field F] [NumberField F] : ab (1 : (A F)ˣ) = 1 := by
  simp [ab]

/- English proof (translation)
Simplify using `[ab]`.
-/
private lemma ab_mul {F : Type} [Field F] [NumberField F] (a a' : (A F)ˣ) : ab (a * a') = ab a * ab a' := by
  simp [ab]

/- English proof (translation)
Simplify using `only [q4]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma quadraticForm_scalar_mul {F : Type} [Field F] [NumberField F] (δ : F) (a : A F) (v : V4 F) :
    q4 δ (fun i => a * v i) = a ^ 2 * q4 δ v := by
  simp only [q4]; ring

/- English proof (translation)
Establish `h : (a : A F) * ((a⁻¹ : (A F)ˣ) : A F) = 1` using `a.mul_inv`. Simplify using `only [B4]`. Take the linear combination `(2 * (y 2 * v 2 - rt δ * (y 3 * v 3)) - y 1 * v 0 - y 0 * v 1) * h`.
-/
private lemma quaternaryForm_unit_scaling {F : Type} [Field F] [NumberField F] (δ : F) (a : (A F)ˣ) (y v : V4 F) :
    B4 δ (fun i => (a : A F) * y i) (fun i => ((a⁻¹ : (A F)ˣ) : A F) * v i) = B4 δ y v := by
  have h : (a : A F) * ((a⁻¹ : (A F)ˣ) : A F) = 1 := a.mul_inv
  simp only [B4]
  linear_combination (2 * (y 2 * v 2 - rt δ * (y 3 * v 3)) - y 1 * v 0 - y 0 * v 1) * h

/- English proof (translation)
Introduce `F _ _ δ η O hδ hη`. Establish `hinv : ∀ a : (A F)ˣ, η a⁻¹ = η a`. Introduce `a`. Rewrite using `[map_inv, inv_eq_iff_mul_eq_one, ← pow_two, hη]`. Establish `habinv : ∀ a : (A F)ˣ, ab a⁻¹ = (ab a)⁻¹`.

Introduce `a`. Establish `h1 : ab a * ab a⁻¹ = 1` using `by rw [← ab_mul, mul_inv_cancel, ab_one]`. Conclude with `eq_inv_of_mul_eq_one_right h1`. Establish `habpos : ∀ a : (A F)ˣ, ab a ≠ 0`. Introduce `a h`.

Establish `h1 : ab a * ab a⁻¹ = 1` using `by rw [← ab_mul, mul_inv_cancel, ab_one]`. Simplify using `[h] at h1`. Establish `hWW : ∀ (φ : S4 F) v, (O.W (O.W φ)).1 v = φ.1 (-v)`. Introduce `φ v`. Rewrite using `[O.W_apply]`.

Establish `: (O.W φ).1 = ft4 δ φ.1` using `funext (O.W_apply φ)`. Rewrite using `[this]`. Conclude with `(ftBasic F δ hδ φ.1 φ.2).2.1 v`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `φ v`.

Simplify using `[O.N_apply, psi_zero]`. Introduce `b c`. Use extensionality with `φ v`. Simplify using `only [Module.End.mul_apply, O.N_apply, add_mul, psi_add]`. Expand and normalize the polynomial expressions, which then agree.

Use extensionality with `φ v`. Simplify using `[O.M_apply, ab_one]`. Introduce `a a'`. Use extensionality with `φ v`. Simplify using `only [Module.End.mul_apply, O.M_apply, ab_mul, map_mul, Units.val_mul]`.

Use `push_cast`. Establish `: (fun i => (a : A F) * (a' : A F) * v i) = fun i => (a' : A F) * ((a : A F) * v i)`. Use function extensionality and compare the values at `i`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `a b`. Use extensionality with `φ v`. Simplify using `only [Module.End.mul_apply, O.M_apply, O.N_apply, quadraticForm_scalar_mul]`. Establish `: b * ((a : A F) ^ 2 * q4 δ v) = (a : A F) ^ 2 * b * q4 δ v` using `by ring`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Introduce `a`. Use extensionality with `φ v`. Simplify using `only [Module.End.mul_apply]`.

Rewrite using `[O.W_apply, O.M_apply, O.W_apply]`. Establish `hM : (O.M a φ).1 = fun y => ((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 fun i => (a : A F) * y i`. Use function extensionality and compare the values at `(O.M_apply a φ)`. Rewrite using `[hM, hinv, habinv]`. Establish `hs` using `measScale F a (fun y => φ.1 y * ψ (B4 δ y (fun i => ((a⁻¹ : (A F)ˣ) : A F) * v i)))`.

Simplify using `only [quaternaryForm_unit_scaling] at hs`. Simplify using `only [ft4]`. Establish `hl : ∀ y, ((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 (fun i => (a : A F) * y i) * ψ (B4 δ y v) = (((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ)) * (φ.1 (fun i => (a : A F) * y i) * ψ (B4 δ y v))`. Introduce `y`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hl]`. Rewrite using `[MeasureTheory.integral_const_mul, hs]`. Establish `hne : ((ab a : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast habpos a`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Use `⟨⟨O.W, O.W * O.W * O.W, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Use extensionality with `φ v`. Simplify using `only [Module.End.mul_apply, Module.End.one_apply]`. Rewrite using `[hWW, hWW]`. Simplify using the standard rewrite rules.

Use extensionality with `φ v`. Simplify using `only [Module.End.mul_apply, Module.End.one_apply]`. Rewrite using `[hWW, hWW]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.ConvolutionTheory.R2.C.opsRel :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ) (O : Ops δ η), δ ≠ 0 → (∀ a, η a ^ 2 = 1) → Rel O.N O.M O.W := by
  intro F _ _ δ η O hδ hη
  have hinv : ∀ a : (A F)ˣ, η a⁻¹ = η a := by
    intro a
    rw [map_inv, inv_eq_iff_mul_eq_one, ← pow_two, hη]
  have habinv : ∀ a : (A F)ˣ, ab a⁻¹ = (ab a)⁻¹ := by
    intro a
    have h1 : ab a * ab a⁻¹ = 1 := by rw [← ab_mul, mul_inv_cancel, ab_one]
    exact eq_inv_of_mul_eq_one_right h1
  have habpos : ∀ a : (A F)ˣ, ab a ≠ 0 := by
    intro a h
    have h1 : ab a * ab a⁻¹ = 1 := by rw [← ab_mul, mul_inv_cancel, ab_one]
    simp [h] at h1
  have hWW : ∀ (φ : S4 F) v, (O.W (O.W φ)).1 v = φ.1 (-v) := by
    intro φ v
    rw [O.W_apply]
    have : (O.W φ).1 = ft4 δ φ.1 := funext (O.W_apply φ)
    rw [this]
    exact (ftBasic F δ hδ φ.1 φ.2).2.1 v
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext φ v
    simp [O.N_apply, psi_zero]
  · intro b c
    ext φ v
    simp only [Module.End.mul_apply, O.N_apply, add_mul, psi_add]
    ring
  · ext φ v
    simp [O.M_apply, ab_one]
  · intro a a'
    ext φ v
    simp only [Module.End.mul_apply, O.M_apply, ab_mul, map_mul, Units.val_mul]
    push_cast
    have : (fun i => (a : A F) * (a' : A F) * v i) = fun i => (a' : A F) * ((a : A F) * v i) := by
      funext i; ring
    rw [this]
    ring
  · intro a b
    ext φ v
    simp only [Module.End.mul_apply, O.M_apply, O.N_apply, quadraticForm_scalar_mul]
    have : b * ((a : A F) ^ 2 * q4 δ v) = (a : A F) ^ 2 * b * q4 δ v := by ring
    rw [this]
    ring
  · intro a
    ext φ v
    simp only [Module.End.mul_apply]
    rw [O.W_apply, O.M_apply, O.W_apply]
    have hM : (O.M a φ).1 = fun y => ((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 fun i => (a : A F) * y i :=
      funext (O.M_apply a φ)
    rw [hM, hinv, habinv]
    have hs := measScale F a (fun y => φ.1 y * ψ (B4 δ y (fun i => ((a⁻¹ : (A F)ˣ) : A F) * v i)))
    simp only [quaternaryForm_unit_scaling] at hs
    simp only [ft4]
    have hl : ∀ y, ((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 (fun i => (a : A F) * y i) * ψ (B4 δ y v)
        = (((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ)) * (φ.1 (fun i => (a : A F) * y i) * ψ (B4 δ y v)) := by
      intro y; ring
    simp only [hl]
    rw [MeasureTheory.integral_const_mul, hs]
    have hne : ((ab a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast habpos a
    push_cast
    field_simp
  · refine ⟨⟨O.W, O.W * O.W * O.W, ?_, ?_⟩, rfl⟩
    · ext φ v
      simp only [Module.End.mul_apply, Module.End.one_apply]
      rw [hWW, hWW]
      simp
    · ext φ v
      simp only [Module.End.mul_apply, Module.End.one_apply]
      rw [hWW, hWW]
      simp
