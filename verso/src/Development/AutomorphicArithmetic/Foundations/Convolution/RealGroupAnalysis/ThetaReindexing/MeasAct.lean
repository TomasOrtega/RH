import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.DetAE
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.D.MeasureActionUnipotent

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] AdeleBaseChange.algebraAdeleRing

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.
-/
private theorem aE_mul_nU {K : Type} [Field K] [NumberField K] (a : (A K)ˣ) (b : A K) :
    aE a * gl (nU b) = gl (nU ((a : A K) * b)) * aE a := by
  apply Units.ext
  change !![(a : A K), 0; 0, 1] * !![1, b; 0, 1] = !![1, (a : A K) * b; 0, 1] * !![(a : A K), 0; 0, 1]
  simp [Matrix.mul_fin_two]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.
-/
private theorem nU_add {K : Type} [Field K] [NumberField K] (b c : A K) :
    nU (b + c) = nU b * nU c := by
  apply Subtype.ext
  change !![1, b + c; 0, 1] = !![1, b; 0, 1] * !![1, c; 0, 1]
  simp [Matrix.mul_fin_two, add_comm]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.
-/
private theorem w_rel (K : Type) [Field K] [NumberField K] :
    nU 1 * wW K * nU 1 = wW K * nU (-1) * wW K := by
  apply Subtype.ext
  change !![1, 1; 0, 1] * !![0, 1; -1, 0] * !![1, 1; 0, 1] = !![0, 1; -1, 0] * !![1, -1; 0, 1] * !![0, 1; -1, 0]
  simp [Matrix.mul_fin_two]

private def twoU (K : Type) [Field K] [NumberField K] : (A K)ˣ :=
  Units.map (algebraMap K (A K) : K →* A K) (Units.mk0 2 two_ne_zero)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem coe_twoU (K : Type) [Field K] [NumberField K] : ((twoU K : (A K)ˣ) : A K) = 2 := by
  simp [twoU, map_ofNat]

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem gl_mul {K : Type} [Field K] [NumberField K] (x y : G1 K) : gl (x * y) = gl x * gl y :=
  map_mul _ _ _

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem hom_nU {K G : Type} [Field K] [NumberField K] [CommGroup G] (f : GL (Fin 2) (A K) →* G) (b : A K) :
    f (gl (nU b)) = 1 := by
  have h1 := congrArg f (aE_mul_nU (twoU K) b)
  rw [map_mul, map_mul, mul_comm, coe_twoU, two_mul, nU_add, gl_mul, map_mul] at h1
  have h2 := mul_right_cancel h1
  exact (mul_eq_left.mp h2.symm)

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem hom_w {K G : Type} [Field K] [NumberField K] [CommGroup G] (f : GL (Fin 2) (A K) →* G) :
    f (gl (wW K)) = 1 := by
  have h1 := congrArg (fun g => f (gl g)) (w_rel K)
  simp only [gl_mul, map_mul, hom_nU, mul_one, one_mul] at h1
  exact (mul_eq_left.mp h1.symm)

variable (D : Dat F E)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem co_add (z w : A E) (i : Fin 2) : D.co (z + w) i = D.co z i + D.co w i := by
  simp [Dat.co]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem co_mul (u : A F) (w : A E) (i : Fin 2) :
    D.co (AdeleBaseChange.adeleMap F E u * w) i = u * D.co w i := by
  have h : AdeleBaseChange.adeleMap F E u * w = u • w := by
    rw [Algebra.smul_def, AdeleBaseChange.algebraMap_adeleRing]
  rw [h]
  simp [Dat.co]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem one_eq : (1 : A E) = AdeleBaseChange.adeleBasis D.b 0 := by
  rw [AdeleBaseChange.adeleBasis_apply, D.b0, map_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem theta_eq : rt D.θ = AdeleBaseChange.adeleBasis D.b 1 := by
  rw [AdeleBaseChange.adeleBasis_apply, D.b1]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem coordinate_one_zero : D.co 1 0 = 1 := by
  simp [Dat.co, one_eq D]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem coordinate_one_one : D.co 1 1 = 0 := by
  simp [Dat.co, one_eq D]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem coordinate_squareRoot_zero : D.co (rt D.θ) 0 = 0 := by
  simp [Dat.co, theta_eq D]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem coordinate_squareRoot_one : D.co (rt D.θ) 1 = 1 := by
  simp [Dat.co, theta_eq D]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem act_aE (α : (A E)ˣ) (v : V4 F) :
    D.act (aE α) v = ![v 0, v 1 * D.co ((α : A E) * D.bar α) 0,
      v 2 * D.co (α : A E) 0 + v 3 * D.co ((α : A E) * rt D.θ) 0,
      v 2 * D.co (α : A E) 1 + v 3 * D.co ((α : A E) * rt D.θ) 1] := by
  have h1 : (aE α).val = !![(α : A E), 0; 0, 1] := rfl
  have h2 : ((aE α).val.map D.bar)ᵀ = !![D.bar α, 0; 0, 1] := by
    rw [h1]; ext i j; fin_cases i <;> fin_cases j <;> simp
  have hm : (aE α).val * D.herm v * ((aE α).val.map D.bar)ᵀ =
      !![AdeleBaseChange.adeleMap F E (v 1) * ((α : A E) * D.bar α),
         AdeleBaseChange.adeleMap F E (v 2) * (α : A E) + AdeleBaseChange.adeleMap F E (v 3) * ((α : A E) * rt D.θ);
         D.mkE (v 2) (-v 3) * D.bar α, AdeleBaseChange.adeleMap F E (v 0) * 1] := by
    rw [h2, h1, Dat.herm]
    simp only [Matrix.mul_fin_two, Dat.mkE]
    simp
    constructor
    · ring
    · ring
  have e0 : D.co (AdeleBaseChange.adeleMap F E (v 0)) 0 = v 0 := by
    have := co_mul D (v 0) 1 0
    rwa [mul_one, coordinate_one_zero, mul_one] at this
  rw [Dat.act, hm]
  ext i
  fin_cases i
  · simp [Dat.unherm, e0]
  · simp [Dat.unherm, co_mul]
  · simp [Dat.unherm, co_mul, co_add]
  · simp [Dat.unherm, co_mul, co_add]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem rho_aE (ρ : GL (Fin 2) (A E) →* GL (Fin 4) (A F)) (hρ : ∀ h v, D.act h v = (ρ h).val *ᵥ v) (α : (A E)ˣ) :
    (ρ (aE α)).val = !![1, 0, 0, 0; 0, D.co ((α : A E) * D.bar α) 0, 0, 0;
      0, 0, D.co (α : A E) 0, D.co ((α : A E) * rt D.θ) 0;
      0, 0, D.co (α : A E) 1, D.co ((α : A E) * rt D.θ) 1] := by
  apply Matrix.mulVec_injective
  funext v
  rw [← hρ, act_aE]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, mul_comm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
private theorem norm_eq (α : A E) : Algebra.norm (A F) α =
    D.co α 0 * D.co (α * rt D.θ) 1 - D.co (α * rt D.θ) 0 * D.co α 1 := by
  rw [Algebra.norm_eq_matrix_det (AdeleBaseChange.adeleBasis D.b), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, ← one_eq D, ← theta_eq D, mul_one]
  rfl

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
private theorem nu_aE (α : (A E)ˣ) : nu F (aE α) = ideleNorm F E α := by
  have : Matrix.GeneralLinearGroup.det (aE α) = α := by
    apply Units.ext
    change Matrix.det !![(α : A E), 0; 0, 1] = α
    simp [Matrix.det_fin_two]
  rw [nu, this]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem c_eq (ρ : GL (Fin 2) (A E) →* GL (Fin 4) (A F))
    (hq : ∀ h v, q4 D.δ (D.act h v) = (nu F h : A F) * q4 D.δ v) (α : (A E)ˣ) :
    D.co ((α : A E) * D.bar α) 0 = ((ideleNorm F E α : (A F)ˣ) : A F) := by
  have h := hq (aE α) ![1, 1, 0, 0]
  rw [act_aE, nu_aE] at h
  simpa [q4] using h

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem det_aE (ρ : GL (Fin 2) (A E) →* GL (Fin 4) (A F)) (hρ : ∀ h v, D.act h v = (ρ h).val *ᵥ v)
    (hq : ∀ h v, q4 D.δ (D.act h v) = (nu F h : A F) * q4 D.δ v) (α : (A E)ˣ) :
    Matrix.GeneralLinearGroup.det (ρ (aE α)) = ideleNorm F E α ^ 2 := by
  apply Units.ext
  have h1 : ((Matrix.GeneralLinearGroup.det (ρ (aE α)) : (A F)ˣ) : A F) = (ρ (aE α)).val.det := rfl
  rw [h1, rho_aE D ρ hρ, c_eq D ρ hq, Units.val_pow_eq_pow_val, coe_ideleNorm, norm_eq D]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_three]
  ring

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem key (ρ : GL (Fin 2) (A E) →* GL (Fin 4) (A F)) (hρ : ∀ h v, D.act h v = (ρ h).val *ᵥ v)
    (hq : ∀ h v, q4 D.δ (D.act h v) = (nu F h : A F) * q4 D.δ v) (h : GL (Fin 2) (A E)) :
    IdeleGroup.ideleModule F (Matrix.GeneralLinearGroup.det (ρ h)) = IdeleGroup.ideleModule F (nu F h) ^ 2 := by
  let f₁ : GL (Fin 2) (A E) →* {r : ℝ // 0 < r} :=
    (IdeleGroup.ideleModule F).comp ((Matrix.GeneralLinearGroup.det (n := Fin 4) (R := A F)).comp ρ)
  let f₂ : GL (Fin 2) (A E) →* {r : ℝ // 0 < r} :=
    ((IdeleGroup.ideleModule F).comp ((ideleNorm F E).comp (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := A E)))) ^ 2
  have hf : f₁ = f₂ := by
    apply MonoidHom.eq_of_eqOn_dense (UpperTheory.ConvolutionTheory.R2.D.genE E)
    rintro g ((⟨b, rfl⟩ | rfl) | ⟨α, rfl⟩)
    · simp only [hom_nU]
    · simp only [hom_w]
    · change IdeleGroup.ideleModule F (Matrix.GeneralLinearGroup.det (ρ (aE α))) = IdeleGroup.ideleModule F (nu F (aE α)) ^ 2
      rw [det_aE D ρ hρ hq, nu_aE, map_pow]
  exact DFunLike.congr_fun hf h

end UpperTheory.ConvolutionTheory.R2.D.MeasureActionUnipotent

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.R2.D.measAct :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (h : GL (Fin 2) (A E)),
    Measure.map (D.act h) (adeleMeasurePi F) = ENNReal.ofReal ((ab (nu F h))⁻¹ ^ 2) • adeleMeasurePi F (ι := Fin 4) := by
  intro F E _ _ _ _ _ D h
  obtain ⟨ρ, hρ, hq, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  let g : GL (Fin 4) (A F) := ⟨(ρ h).valᵀ, ((ρ h)⁻¹).valᵀ,
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩
  have hfun : D.act h = fun x => x ᵥ* (g : Matrix (Fin 4) (Fin 4) (A F)) := by
    funext v
    rw [hρ]
    exact (Matrix.vecMul_transpose _ _).symm
  have hdet : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (ρ h) := by
    apply Units.ext
    exact Matrix.det_transpose _
  rw [hfun, GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi, hdet,
    UpperTheory.ConvolutionTheory.R2.D.MeasureActionUnipotent.key D ρ hρ hq h]
  congr 1
  congr 1
  simp [ab, inv_pow]
