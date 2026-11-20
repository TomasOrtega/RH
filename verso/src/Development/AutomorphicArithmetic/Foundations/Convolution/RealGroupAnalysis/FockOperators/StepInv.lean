import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.PsiShift
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.QuadraticFormAddExpand
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.WeilSignAnticommuteOperator
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

/- English proof (translation)
Simplify using `[cw, map_add]`.
-/
private lemma cw_add' {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (a b : A F) :
    cw w (a + b) = cw w a + cw w b := by
  simp [cw, map_add]

/- English proof (translation)
Simplify using `[cw, map_mul]`.
-/
private lemma cw_mul' {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (a b : A F) :
    cw w (a * b) = cw w a * cw w b := by
  simp [cw, map_mul]

/- English proof (translation)
Simplify using `[cw, map_one]`.
-/
private lemma cw_one' {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) :
    cw w (1 : A F) = 1 := by
  simp [cw, map_one]

/- English proof (translation)
Simplify using `[cw, map_zero]`.
-/
private lemma cw_zero' {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) :
    cw w (0 : A F) = 0 := by
  simp [cw, map_zero]

/- English proof (translation)
Simplify using `[cw, map_neg]`.
-/
private lemma cw_neg' {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (a : A F) :
    cw w (-a) = -cw w a := by
  simp [cw, map_neg]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[← mul_assoc, h₁, mul_assoc, add_mul, smul_mul_assoc, smul_mul_assoc, k₁, k₂]`. Simplify using `only [mul_add, mul_smul_comm, smul_add, smul_smul, add_smul, mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[← mul_assoc, h₂, mul_assoc, add_mul, smul_mul_assoc, smul_mul_assoc, k₁, k₂]`.

Simplify using `only [mul_add, mul_smul_comm, smul_add, smul_smul, add_smul, mul_assoc]`. Normalize the expressions using the abelian group laws.
-/
private lemma step_mul {M : Type} [AddCommGroup M] [Module ℂ M] (d p X Y : Module.End ℂ M)
    (a b c e a' b' c' e' : ℂ)
    (h₁ : d * X = X * (a • d + b • p)) (h₂ : p * X = X * (c • d + e • p))
    (k₁ : d * Y = Y * (a' • d + b' • p)) (k₂ : p * Y = Y * (c' • d + e' • p)) :
    d * (X * Y) = (X * Y) * ((a * a' + b * c') • d + (a * b' + b * e') • p) ∧
      p * (X * Y) = (X * Y) * ((c * a' + e * c') • d + (c * b' + e * e') • p) := by
  constructor
  · rw [← mul_assoc, h₁, mul_assoc, add_mul, smul_mul_assoc, smul_mul_assoc, k₁, k₂]
    simp only [mul_add, mul_smul_comm, smul_add, smul_smul, add_smul, mul_assoc]
    abel
  · rw [← mul_assoc, h₂, mul_assoc, add_mul, smul_mul_assoc, smul_mul_assoc, k₁, k₂]
    simp only [mul_add, mul_smul_comm, smul_add, smul_smul, add_smul, mul_assoc]
    abel

/- English proof (translation)
Establish `k₁ : (e • d + (-b) • p) * X = X * d`. Rewrite using `[add_mul, smul_mul_assoc, smul_mul_assoc, h₁, h₂, ← mul_smul_comm, ← mul_smul_comm, ← mul_add]`. Use `congr 1`. Establish `: e • (a • d + b • p) + (-b) • (c • d + e • p) = (a * e - b * c) • d` using `by module`. Rewrite using `[this, hd, one_smul]`.

Establish `k₂ : ((-c) • d + a • p) * X = X * p`. Rewrite using `[add_mul, smul_mul_assoc, smul_mul_assoc, h₁, h₂, ← mul_smul_comm, ← mul_smul_comm, ← mul_add]`. Use `congr 1`. Establish `: (-c) • (a • d + b • p) + a • (c • d + e • p) = (a * e - b * c) • p` using `by module`. Rewrite using `[this, hd, one_smul]`.

Prove the components needed by the constructor for the conclusion. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma step_inv {M : Type} [AddCommGroup M] [Module ℂ M] (d p X X' : Module.End ℂ M)
    (a b c e : ℂ) (hd : a * e - b * c = 1) (hl : X' * X = 1) (hr : X * X' = 1)
    (h₁ : d * X = X * (a • d + b • p)) (h₂ : p * X = X * (c • d + e • p)) :
    d * X' = X' * (e • d + (-b) • p) ∧ p * X' = X' * ((-c) • d + a • p) := by
  have k₁ : (e • d + (-b) • p) * X = X * d := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, h₁, h₂, ← mul_smul_comm, ← mul_smul_comm, ← mul_add]
    congr 1
    have : e • (a • d + b • p) + (-b) • (c • d + e • p) = (a * e - b * c) • d := by
      module
    rw [this, hd, one_smul]
  have k₂ : ((-c) • d + a • p) * X = X * p := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, h₁, h₂, ← mul_smul_comm, ← mul_smul_comm, ← mul_add]
    congr 1
    have : (-c) • (a • d + b • p) + a • (c • d + e • p) = (a * e - b * c) • p := by
      module
    rw [this, hd, one_smul]
  constructor
  · calc d * X' = X' * (X * d) * X' := by rw [← mul_assoc, hl, one_mul]
      _ = X' * (e • d + (-b) • p) := by rw [← k₁, mul_assoc, mul_assoc, hr, mul_one]
  · calc p * X' = X' * (X * p) * X' := by rw [← mul_assoc, hl, one_mul]
      _ = X' * ((-c) • d + a • p) := by rw [← k₂, mul_assoc, mul_assoc, hr, mul_one]

/- English proof (translation)
Simplify using `[Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
private lemma ent_mul {R : Type} [CommRing R] (g h : Matrix.SpecialLinearGroup (Fin 2) R) :
    (g * h) 0 0 = g 0 0 * h 0 0 + g 0 1 * h 1 0 ∧ (g * h) 0 1 = g 0 0 * h 0 1 + g 0 1 * h 1 1 ∧
      (g * h) 1 0 = g 1 0 * h 0 0 + g 1 1 * h 1 0 ∧ (g * h) 1 1 = g 1 0 * h 0 1 + g 1 1 * h 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Simplify using `[Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]`.
-/
private lemma ent_inv {R : Type} [CommRing R] (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    g⁻¹ 0 0 = g 1 1 ∧ g⁻¹ 0 1 = -g 0 1 ∧ g⁻¹ 1 0 = -g 1 0 ∧ g⁻¹ 1 1 = g 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D W O g`. Establish `hg : g ∈ Subgroup.closure (Set.range (nU (F` using `F)) ∪ {wW F}) := by`. Rewrite using `[(UpperTheory.ConvolutionTheory.R2.gen F).1]`. Conclude with `Subgroup.mem_top g`. Proceed by induction on `hg using Subgroup.closure_induction with`.

Consider the case `mem x hx`. Introduce `w i`. Break down `hx with ⟨b, rfl⟩ | hx` into its components or cases. Establish `hp : O.p D.δ w i * W.Om (nU b) = W.Om (nU b) * O.p D.δ w i`. Establish `hx` using `fun k => (dN F E D W O w k b).2`.

Use `fin_cases i`. Use `all_goals`. Simplify using `only [Ops.p]`. Use `show (_ • O.x w _) * _ = _ * (_ • O.x w _)`. Rewrite using `[smul_mul_assoc, mul_smul_comm, hx]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify `(dN F E D W O w i b).1` using `[nU, cw_one', cw_zero']`. Simplify `hp` using `[nU, cw_one', cw_zero']`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify `dW F E D W O w i` using `[wW, cw_one', cw_zero']`. Simplify `pW F E D W O w i` using `[wW, cw_one', cw_zero', cw_neg']`. Consider the case `one`. Introduce `w i`.

Simplify using `[cw_one', cw_zero']`. Consider the case `mul x y _ _ hx hy`. Introduce `w i`. Take `⟨h₁, h₂⟩` from `hx w i`. Take `⟨k₁, k₂⟩` from `hy w i`.

Take `⟨e₁, e₂, e₃, e₄⟩` from `ent_mul x y`. Use `step_mul _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ k₁ k₂` as an intermediate fact. Rewrite using `[map_mul, e₁, e₂, e₃, e₄]`. Simplify `this` using `only [cw_add', cw_mul']`. Consider the case `inv x _ hx`.

Introduce `w i`. Take `⟨h₁, h₂⟩` from `hx w i`. Take `⟨e₁, e₂, e₃, e₄⟩` from `ent_inv x`. Establish `hdet : cw w (x 0 0) * cw w (x 1 1) - cw w (x 0 1) * cw w (x 1 0) = 1`. Establish `h` using `x.det_coe`.

Rewrite `h` using `[Matrix.det_fin_two]`. Use `congrArg (cw w) h` as an intermediate fact. Rewrite `this` using `[sub_eq_add_neg, cw_add', cw_neg', cw_mul', cw_mul', cw_one']`. Rewrite using `[sub_eq_add_neg]`. Conclude with `this`.

Establish `hl : W.Om x⁻¹ * W.Om x = 1` using `by rw [← map_mul, inv_mul_cancel, map_one]`. Establish `hr : W.Om x * W.Om x⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Use `step_inv _ _ _ _ _ _ _ _ hdet hl hr h₁ h₂` as an intermediate fact. Rewrite using `[e₁, e₂, e₃, e₄, cw_neg', cw_neg']`. Conclude with `this`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Fo.Heisenberg₂ :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) (g : G1 F) w i,
    O.d w i * W.Om g = W.Om g * (cw w (g 0 0) • O.d w i + cw w (g 0 1) • O.p D.δ w i) ∧
    O.p D.δ w i * W.Om g = W.Om g * (cw w (g 1 0) • O.d w i + cw w (g 1 1) • O.p D.δ w i) := by
  intro F E _ _ _ _ _ _ _ D W O g
  have hg : g ∈ Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) := by
    rw [(UpperTheory.ConvolutionTheory.R2.gen F).1]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    intro w i
    rcases hx with ⟨b, rfl⟩ | hx
    · have hp : O.p D.δ w i * W.Om (nU b) = W.Om (nU b) * O.p D.δ w i := by
        have hx := fun k => (dN F E D W O w k b).2
        fin_cases i
        all_goals
          simp only [Ops.p]
          show (_ • O.x w _) * _ = _ * (_ • O.x w _)
          rw [smul_mul_assoc, mul_smul_comm, hx]
      refine ⟨?_, ?_⟩
      · simpa [nU, cw_one', cw_zero'] using (dN F E D W O w i b).1
      · simpa [nU, cw_one', cw_zero'] using hp
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨?_, ?_⟩
      · simpa [wW, cw_one', cw_zero'] using dW F E D W O w i
      · simpa [wW, cw_one', cw_zero', cw_neg'] using pW F E D W O w i
  | one =>
    intro w i
    simp [cw_one', cw_zero']
  | mul x y _ _ hx hy =>
    intro w i
    obtain ⟨h₁, h₂⟩ := hx w i
    obtain ⟨k₁, k₂⟩ := hy w i
    obtain ⟨e₁, e₂, e₃, e₄⟩ := ent_mul x y
    have := step_mul _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ k₁ k₂
    rw [map_mul, e₁, e₂, e₃, e₄]
    simpa only [cw_add', cw_mul'] using this
  | inv x _ hx =>
    intro w i
    obtain ⟨h₁, h₂⟩ := hx w i
    obtain ⟨e₁, e₂, e₃, e₄⟩ := ent_inv x
    have hdet : cw w (x 0 0) * cw w (x 1 1) - cw w (x 0 1) * cw w (x 1 0) = 1 := by
      have h := x.det_coe
      rw [Matrix.det_fin_two] at h
      have := congrArg (cw w) h
      rw [sub_eq_add_neg, cw_add', cw_neg', cw_mul', cw_mul', cw_one'] at this
      rw [sub_eq_add_neg]
      exact this
    have hl : W.Om x⁻¹ * W.Om x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have hr : W.Om x * W.Om x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have := step_inv _ _ _ _ _ _ _ _ hdet hl hr h₁ h₂
    rw [e₁, e₂, e₃, e₄, cw_neg', cw_neg']
    exact this
