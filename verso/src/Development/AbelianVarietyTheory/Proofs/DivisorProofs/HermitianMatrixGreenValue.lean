import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalInnerProductLift
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSmallSecTrivShift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame

open scoped ComplexOrder

namespace GlobalTheory.TautDensity

def frameMat (w : ReciprocityTheory.L2DbarEstimates.V 1) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  fromBlocks 1 0 (of fun _ _ => w 0) 1

def gramMat (w : ReciprocityTheory.L2DbarEstimates.V 1) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  fromBlocks (of fun _ _ => 1 + w 0 * starRingEnd ℂ (w 0)) (of fun _ _ => w 0)
    (of fun _ _ => starRingEnd ℂ (w 0)) 1

/- English proof (translation)
Apply the tactic sequence `ext (a | a) (b | b) <;>`. Simplify using `[gramMat, frameMat, mul_apply, Subsingleton.elim a 0, Subsingleton.elim b 0]`.
-/
theorem gramMat_eq (w : ReciprocityTheory.L2DbarEstimates.V 1) : gramMat w = (frameMat w)ᵀ * 1 * (frameMat w)ᴴᵀ := by
  ext (a | a) (b | b) <;>
    simp [gramMat, frameMat, mul_apply, Subsingleton.elim a 0, Subsingleton.elim b 0]

/- English proof (translation)
Rewrite using `[frameMat, det_fromBlocks_zero₁₂]`. Simplify using the standard rewrite rules.
-/
theorem det_frameMat (w : ReciprocityTheory.L2DbarEstimates.V 1) : (frameMat w).det = 1 := by
  rw [frameMat, det_fromBlocks_zero₁₂]; simp

/- English proof (translation)
The claim follows from `(EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1) : ReciprocityTheory.L2DbarEstimates.V 1 →L[ℂ] ℂ).hasFDerivAt`.
-/
theorem hasFDerivAt_crd (z : ReciprocityTheory.L2DbarEstimates.V 1) :
    HasFDerivAt (fun w : ReciprocityTheory.L2DbarEstimates.V 1 => w 0)
      (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1) : ReciprocityTheory.L2DbarEstimates.V 1 →L[ℂ] ℂ) z :=
  (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1) : ReciprocityTheory.L2DbarEstimates.V 1 →L[ℂ] ℂ).hasFDerivAt

/- English proof (translation)
Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Use `exacts [contDiffAt_const, contDiffAt_const, (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1) : ReciprocityTheory.L2DbarEstimates.V 1 →L[ℂ] ℂ).contDiff.contDiffAt, contDiffAt_const]`.
-/
theorem contDiffAt_frameMat (z : ReciprocityTheory.L2DbarEstimates.V 1) (a b : Fin 1 ⊕ Fin 1) :
    ContDiffAt ℂ 1 (fun w => frameMat w a b) z := by
  rcases a with a | a <;> rcases b with b | b
  exacts [contDiffAt_const, contDiffAt_const,
    (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1) : ReciprocityTheory.L2DbarEstimates.V 1 →L[ℂ] ℂ).contDiff.contDiffAt,
    contDiffAt_const]

/- English proof (translation)
Introduce `a b` and use `(contDiffAt_frameMat z a b).restrict_scalars ℝ`.
-/
theorem mContDiffAt_frameMat (z : ReciprocityTheory.L2DbarEstimates.V 1) : MContDiffAt 1 frameMat z :=
  fun a b => (contDiffAt_frameMat z a b).restrict_scalars ℝ

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[mdbar_apply, dbar_eq_zero ((contDiffAt_frameMat z a b).differentiableAt one_ne_zero)]`. Both sides reduce to the same expression.
-/
theorem mdbar_frameMat (z η : ReciprocityTheory.L2DbarEstimates.V 1) : mdbar frameMat z η = 0 := by
  ext a b
  rw [mdbar_apply, dbar_eq_zero ((contDiffAt_frameMat z a b).differentiableAt one_ne_zero)]
  rfl

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[mdel_apply, del_eq_fderiv ((contDiffAt_frameMat z a b).differentiableAt one_ne_zero)]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Simplify using `[frameMat]`. Simplify using `[frameMat]`.

Express the relevant statement in the definitionally equal form `fderiv ℂ (fun w : ReciprocityTheory.L2DbarEstimates.V 1 => w 0) z ξ = ξ 0`. Rewrite using `[(hasFDerivAt_crd z).fderiv]`. Both sides reduce to the same expression. Simplify using `[frameMat]`.
-/
theorem mdel_frameMat (z ξ : ReciprocityTheory.L2DbarEstimates.V 1) :
    mdel frameMat z ξ = fromBlocks 0 0 (of fun _ _ => ξ 0) 0 := by
  ext a b
  rw [mdel_apply, del_eq_fderiv ((contDiffAt_frameMat z a b).differentiableAt one_ne_zero)]
  rcases a with a | a <;> rcases b with b | b
  · simp [frameMat]
  · simp [frameMat]
  · change fderiv ℂ (fun w : ReciprocityTheory.L2DbarEstimates.V 1 => w 0) z ξ = ξ 0
    rw [(hasFDerivAt_crd z).fderiv]; rfl
  · simp [frameMat]

/- English proof (translation)
Rewrite using `[funext gramMat_eq]`. Conclude with `((mContDiffAt_frameMat z).transpose.mul (mContDiffAt_const 1)).mul (mContDiffAt_frameMat z).conjTranspose.transpose`.
-/
theorem mContDiffAt_gramMat (z : ReciprocityTheory.L2DbarEstimates.V 1) : MContDiffAt 1 gramMat z := by
  rw [funext gramMat_eq]
  exact ((mContDiffAt_frameMat z).transpose.mul (mContDiffAt_const 1)).mul
    (mContDiffAt_frameMat z).conjTranspose.transpose

/- English proof (translation)
Rewrite using `[gramMat_eq]`. Conclude with `posDef_chg ((isUnit_iff_isUnit_det _).2 (by rw [det_frameMat]; exact isUnit_one)) PosDef.one`.
-/
theorem posDef_gramMat (w : ReciprocityTheory.L2DbarEstimates.V 1) : (gramMat w).PosDef := by
  rw [gramMat_eq]
  exact posDef_chg ((isUnit_iff_isUnit_det _).2 (by rw [det_frameMat]; exact isUnit_one)) PosDef.one

/- English proof (translation)
Establish `hu : IsUnit (frameMat z).det` using `by rw [det_frameMat]; exact isUnit_one`. Establish `hi : (frameMat z)⁻¹ = fromBlocks 1 0 (of fun _ _ => -z 0) 1`. Use `inv_eq_left_inv ?_` and prove the remaining obligations. Apply the tactic sequence `ext (a | a) (b | b) <;> obtain rfl := Subsingleton.elim a 0 <;>`. Apply the tactic sequence `obtain rfl := Subsingleton.elim b 0 <;> simp [frameMat, mul_apply]`.

Rewrite using `[secondForm_eq, funext gramMat_eq, conn_changeFrame (H := fun _ => 1) (mContDiffAt_const 1) (by simp) (mContDiffAt_frameMat z) hu (mdbar_frameMat z), conn_const, Matrix.zero_mul, zero_add, mdel_frameMat, hi, fromBlocks_multiply, toBlocks_fromBlocks₂₁]`. Simplify using the standard rewrite rules.
-/
theorem secondForm_gramMat (z ξ : ReciprocityTheory.L2DbarEstimates.V 1) :
    secondForm gramMat z ξ = of fun _ _ => ξ 0 := by
  have hu : IsUnit (frameMat z).det := by rw [det_frameMat]; exact isUnit_one
  have hi : (frameMat z)⁻¹ = fromBlocks 1 0 (of fun _ _ => -z 0) 1 := by
    refine inv_eq_left_inv ?_
    ext (a | a) (b | b) <;> obtain rfl := Subsingleton.elim a 0 <;>
      obtain rfl := Subsingleton.elim b 0 <;> simp [frameMat, mul_apply]
  rw [secondForm_eq, funext gramMat_eq, conn_changeFrame (H := fun _ => 1) (mContDiffAt_const 1)
    (by simp) (mContDiffAt_frameMat z) hu (mdbar_frameMat z), conn_const, Matrix.zero_mul, zero_add,
    mdel_frameMat, hi, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  simp

/- English proof (translation)
Rewrite using `[Complex.mul_conj, Complex.normSq_apply, ArithHeightModel.u]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ofReal_u (z : ReciprocityTheory.L2DbarEstimates.V 1) :
    ((ArithHeightModel.u z : ℝ) : ℂ) = 1 + z 0 * starRingEnd ℂ (z 0) := by
  rw [Complex.mul_conj, Complex.normSq_apply, ArithHeightModel.u]
  push_cast; ring

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[Ring.inverse_eq_inv', Subsingleton.elim a 0, Subsingleton.elim b 0]`.
-/
theorem inv_of_const (c : ℂ) : (of fun _ _ => c : Matrix (Fin 1) (Fin 1) ℂ)⁻¹ = of fun _ _ => c⁻¹ := by
  ext a b
  simp [Ring.inverse_eq_inv', Subsingleton.elim a 0, Subsingleton.elim b 0]

/- English proof (translation)
Rewrite using `[ofReal_u]`. Both sides reduce to the same expression.
-/
theorem subGram_gramMat (z : ReciprocityTheory.L2DbarEstimates.V 1) :
    subGram (gramMat z) = of fun _ _ => ((ArithHeightModel.u z : ℝ) : ℂ) := by
  rw [ofReal_u]; rfl

/- English proof (translation)
Establish `h0 : ((ArithHeightModel.u z : ℝ) : ℂ) ≠ 0`. Conclude with `(ArithHeightModel.u_pos z).ne'` after adjusting the coercions. Rewrite using `[quotGram, gramMat, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, ← ofReal_u, inv_of_const]`. Use extensionality with `a b`. Simplify using `only [Subsingleton.elim a 0, Subsingleton.elim b 0, Matrix.sub_apply, one_apply_eq, mul_apply, Fin.sum_univ_one, of_apply]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[ofReal_u]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quotGram_gramMat (z : ReciprocityTheory.L2DbarEstimates.V 1) :
    quotGram (gramMat z) = of fun _ _ => ((ArithHeightModel.u z : ℝ) : ℂ)⁻¹ := by
  have h0 : ((ArithHeightModel.u z : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ArithHeightModel.u_pos z).ne'
  rw [quotGram, gramMat, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, ← ofReal_u, inv_of_const]
  ext a b
  simp only [Subsingleton.elim a 0, Subsingleton.elim b 0, Matrix.sub_apply, one_apply_eq, mul_apply,
    Fin.sum_univ_one, of_apply]
  field_simp
  rw [ofReal_u]; ring

/- English proof (translation)
Introduce `v`. Express the relevant statement in the definitionally equal form `2 * diagVal (extTrace gramMat v) (EuclideanSpace.single 0 1) = _`. Establish `e : -Complex.I * kappa = ((1 / (2 * Real.pi) : ℝ) : ℂ)`. Rewrite using `[kappa, ← mul_div_assoc, neg_mul, Complex.I_mul_I]`. Simplify using the standard rewrite rules.

Establish `ht : (secondForm gramMat v (EuclideanSpace.single 0 1) * secondFormAdj gramMat v (EuclideanSpace.single 0 1)).trace = (((ArithHeightModel.u v ^ 2)⁻¹ : ℝ) : ℂ)`. Rewrite using `[secondFormAdj, secondForm_gramMat, subGram_gramMat, quotGram_gramMat, adj, ← transpose_nonsing_inv, inv_of_const]`. Simplify using `[trace, mul_apply, sq]`. Rewrite using `[diagVal, extTrace_eq (mContDiffAt_gramMat v) (.of_forall posDef_gramMat), ← mul_assoc, e, Complex.re_ofReal_mul, ht, Complex.ofReal_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem density_eq : ∀ v : ReciprocityTheory.L2DbarEstimates.V 1, 2 * diagVal (extTrace (fun w : ReciprocityTheory.L2DbarEstimates.V 1 => (Matrix.fromBlocks (Matrix.of fun _ _ => 1 + w 0 * starRingEnd ℂ (w 0)) (Matrix.of fun _ _ => w 0) (Matrix.of fun _ _ => starRingEnd ℂ (w 0)) 1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ)) v) (EuclideanSpace.single 0 1) = 1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹ := by
  intro v
  change 2 * diagVal (extTrace gramMat v) (EuclideanSpace.single 0 1) = _
  have e : -Complex.I * kappa = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    rw [kappa, ← mul_div_assoc, neg_mul, Complex.I_mul_I]; simp
  have ht : (secondForm gramMat v (EuclideanSpace.single 0 1) *
      secondFormAdj gramMat v (EuclideanSpace.single 0 1)).trace =
      (((ArithHeightModel.u v ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [secondFormAdj, secondForm_gramMat, subGram_gramMat, quotGram_gramMat, adj,
      ← transpose_nonsing_inv, inv_of_const]
    simp [trace, mul_apply, sq]
  rw [diagVal, extTrace_eq (mContDiffAt_gramMat v) (.of_forall posDef_gramMat), ← mul_assoc, e,
    Complex.re_ofReal_mul, ht, Complex.ofReal_re]
  ring

end GlobalTheory.TautDensity
