import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.EigenformTranslates
import GroundTheory.AutomorphicForms.GL2Classical.WeightOperators
import GroundTheory.AutomorphicForms.GL2Classical.ZFinite
import GroundTheory.AutomorphicForms.GL2Classical.KFinite
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable

open NumberField Matrix CongruenceSubgroup ModularForm Complex
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

attribute [local instance 100] LieRing.ofAssociativeRing

def raiseMat : Matrix (Fin 2) (Fin 2) ℂ := !![-I, 1; 1, I]

def lowerMat : Matrix (Fin 2) (Fin 2) ℂ := !![I, 1; 1, -I]

def rotMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem rot_raise : rotMat * raiseMat - raiseMat * rotMat = (2 * I) • raiseMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, raiseMat] <;> ring_nf <;> simp only [I_sq] <;> ring

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem rot_lower : rotMat * lowerMat - lowerMat * rotMat = (-2 * I) • lowerMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, lowerMat] <;> ring_nf <;> simp only [I_sq] <;> ring

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem lower_raise : lowerMat * raiseMat - raiseMat * lowerMat = (4 * I) • rotMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, lowerMat, raiseMat] <;> ring_nf

def cuspOp (B : Matrix (Fin 2) (Fin 2) ℂ) : Module.End ℂ (cuspForms ℚ 2) :=
  (gkModuleCusp ℚ 2).ρ (lieOfRealMat (reMat B)) + I • (gkModuleCusp ℚ 2).ρ (lieOfRealMat (imMat B))

def cuspToArch (ψ : cuspForms ℚ 2) : archSmooth ℚ 2 :=
  ⟨ψ, ψ.2.1.isSmooth.1⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_cuspOp (B : Matrix (Fin 2) (Fin 2) ℂ) (ψ : cuspForms ℚ 2) :
    ((cuspOp B ψ : cuspForms ℚ 2) : AdelicGL ℚ 2 → ℂ) = (complexOpGL2 B (cuspToArch ψ) : AdelicGL ℚ 2 → ℂ) :=
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cuspToArch_cuspOp (B : Matrix (Fin 2) (Fin 2) ℂ) (ψ : cuspForms ℚ 2) :
    cuspToArch (cuspOp B ψ) = complexOpGL2 B (cuspToArch ψ) :=
  Subtype.ext (coe_cuspOp B ψ)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem cuspToArch_injective : Function.Injective cuspToArch := fun a b h =>
  Subtype.ext (by have := congrArg Subtype.val h; exact this)

/- English proof (translation)
By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Both sides reduce to the same expression.
-/
theorem cuspOp_add (B C : Matrix (Fin 2) (Fin 2) ℂ) : cuspOp (B + C) = cuspOp B + cuspOp C := by
  ext ψ : 1
  apply cuspToArch_injective
  rw [LinearMap.add_apply, cuspToArch_cuspOp, complexOpGL2_add]
  apply Subtype.ext
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Both sides reduce to the same expression.
-/
theorem cuspOp_smul (c : ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) : cuspOp (c • B) = c • cuspOp B := by
  ext ψ : 1
  apply cuspToArch_injective
  rw [LinearMap.smul_apply, cuspToArch_cuspOp, complexOpGL2_smul]
  apply Subtype.ext
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities.
-/
theorem cuspOp_lie (B C : Matrix (Fin 2) (Fin 2) ℂ) :
    cuspOp (B * C - C * B) = cuspOp B * cuspOp C - cuspOp C * cuspOp B := by
  ext ψ : 1
  apply cuspToArch_injective
  rw [cuspToArch_cuspOp, complexOpGL2_lie, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  apply Subtype.ext
  change _ = ((complexOpGL2 B (cuspToArch (cuspOp C ψ)) - complexOpGL2 C (cuspToArch (cuspOp B ψ)) :
    archSmooth ℚ 2) : AdelicGL ℚ 2 → ℂ)
  rw [cuspToArch_cuspOp, cuspToArch_cuspOp]

/- English proof (translation)
By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem gkModuleCusp_ρ_eq_cuspOp (X : (isExpLieAlgebra ℚ 2).lieSubalgebra) :
    (gkModuleCusp ℚ 2).ρ X = cuspOp ((lieRealMat X).map (↑)) := by
  ext ψ : 1
  apply cuspToArch_injective
  rw [cuspToArch_cuspOp, complexOpGL2_map_ofReal, realOpGL2, lieOfRealMat_lieRealMat]
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem cuspOp_finRepCusp (B : Matrix (Fin 2) (Fin 2) ℂ) (g : FiniteAdelicGL ℚ 2) (ψ : cuspForms ℚ 2) :
    cuspOp B (finRepCusp ℚ 2 g ψ) = finRepCusp ℚ 2 g (cuspOp B ψ) := by
  simp only [cuspOp, LinearMap.add_apply, LinearMap.smul_apply, gkModuleCusp_ρ_finRepCusp, map_add, map_smul]

variable {N : ℕ} [NeZero N] {k : ℤ}

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem cuspOp_liftCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) {B : Matrix (Fin 2) (Fin 2) ℂ}
    (hB : gl2HolCoeff B = 0) : cuspOp B (liftCusp f) = gl2WeightChar k B • liftCusp f := by
  have hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), (f : ℍ → ℂ) ∣[k] γ = f :=
    fun γ hγ => SlashInvariantForm.slash_action_eqn f.toSlashInvariantForm γ hγ
  apply cuspToArch_injective
  rw [cuspToArch_cuspOp]
  have e : cuspToArch (liftCusp f) = ⟨adelicLift N k f, isArchSmooth_adelicLift hf f.holo'⟩ := rfl
  rw [e, ← gl2ArchRep_ι, gl2ArchRep_ι_adelicLift_of_holCoeff hf f.holo' hB]
  rfl

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Treat this case separately.

Treat this case separately. Treat this case separately.
-/
theorem cuspOp_translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {B : Matrix (Fin 2) (Fin 2) ℂ} (hB : gl2HolCoeff B = 0) {t : cuspForms ℚ 2} (ht : t ∈ translateSpanCusp f) :
    cuspOp B t = gl2WeightChar k B • t := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    rw [cuspOp_finRepCusp, cuspOp_liftCusp f hB, map_smul]
  | zero => rw [map_zero, smul_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

/- English proof (translation)
Simplify using the standard rewrite rules. Put the polynomial expressions in normal form. Simplify using the standard rewrite rules.
-/
theorem holCoeff_lowerMat : gl2HolCoeff lowerMat = 0 := by
  simp [gl2HolCoeff, lowerMat]; ring_nf; simp [I_sq]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem holCoeff_rotMat : gl2HolCoeff rotMat = 0 := by
  simp [gl2HolCoeff, rotMat]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem holCoeff_one : gl2HolCoeff (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  simp [gl2HolCoeff]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem weightChar_lowerMat : gl2WeightChar k lowerMat = 0 := by
  simp [gl2WeightChar, lowerMat]

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weightChar_rotMat : gl2WeightChar k rotMat = I * k := by
  simp [gl2WeightChar, rotMat]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weightChar_one : gl2WeightChar k (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  simp [gl2WeightChar]
  ring

abbrev kMat (x : archCompact ℚ 2) : GL (Fin 2) ℝ := archToReal (x : archGroup ℚ 2)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem realPart_realEmb (h : GL (Fin 2) ℝ) : realPart (realEmb h) = h := by
  apply realInf_injective
  rw [realInf_realPart, prodEquiv_realEmb]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_kGL_of_mem_archCompact (x : archCompact ℚ 2) :
    ∃ (w : ℂ) (hw : w ≠ 0), ‖w‖ = 1 ∧ (kMat x = kGL w hw ∨ kMat x = toReal epsilon * kGL w hw) := by
  have hx : infEmb ℚ 2 (x : archGroup ℚ 2) ∈ Reduction.maxCompact := x.2
  rw [infEmb_eq_realEmb] at hx
  obtain ⟨h1, h2, h3⟩ := realPart_orthogonal hx
  rw [realPart_realEmb] at h1 h2 h3
  exact exists_eq_kGL_of_orthogonal _ h1 h2 h3

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem archCompactRepCusp_apply_coe (x : archCompact ℚ 2) (ψ : cuspForms ℚ 2) (g : AdelicGL ℚ 2) :
    ((archCompactRepCusp ℚ 2 x ψ : cuspForms ℚ 2) : AdelicGL ℚ 2 → ℂ) g =
      (ψ : AdelicGL ℚ 2 → ℂ) (g * realEmb (kMat x)) := by
  change (ψ : AdelicGL ℚ 2 → ℂ) (g * infEmb ℚ 2 (x : archGroup ℚ 2)) = _
  rw [infEmb_eq_realEmb]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem archCompactRepCusp_translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (x : archCompact ℚ 2) {w : ℂ} (hw : w ≠ 0) (h1 : ‖w‖ = 1) (hK : kMat x = kGL w hw)
    {t : cuspForms ℚ 2} (ht : t ∈ translateSpanCusp f) : archCompactRepCusp ℚ 2 x t = w ^ (-k) • t := by
  apply Subtype.ext
  funext g
  rw [archCompactRepCusp_apply_coe, hK, right_kGL_of_mem_translateSpan (liftEquiv N k f.toSlashInvariantForm).2.right_kGL
    (coe_mem_translateSpan f ht), h1]
  simp

/- English proof (translation)
By extensionality, compare the relevant components. Both sides reduce to the same expression.
-/
theorem archRealEquiv_coe (g : archGroup ℚ 2) :
    archRealEquiv ((g : (ArchMatrix ℚ 2)ˣ) : ArchMatrix ℚ 2) = (archToReal g : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem archToReal_inv (g : archGroup ℚ 2) : archToReal g⁻¹ = (archToReal g)⁻¹ := by
  simp [archToReal, map_inv]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem archCompactRepCusp_rho (x : archCompact ℚ 2) (A : Matrix (Fin 2) (Fin 2) ℝ) (ψ : cuspForms ℚ 2) :
    archCompactRepCusp ℚ 2 x ((gkModuleCusp ℚ 2).ρ (lieOfRealMat A) ψ) =
      (gkModuleCusp ℚ 2).ρ (lieOfRealMat ((kMat x : Matrix (Fin 2) (Fin 2) ℝ) * A *
        ((kMat x)⁻¹ : GL (Fin 2) ℝ))) (archCompactRepCusp ℚ 2 x ψ) := by
  have key := (gkModuleCusp ℚ 2).map_ρ x ⟨archRealEquiv.symm A, Submodule.mem_top⟩ ψ
  have e1 : (isExpLieAlgebra ℚ 2).toLie ⟨archRealEquiv.symm A, Submodule.mem_top⟩ = lieOfRealMat A := rfl
  have e2 : (isExpLieAlgebra ℚ 2).toLie ((isExpLieAlgebra ℚ 2).Ad (x : archGroup ℚ 2)
      ⟨archRealEquiv.symm A, Submodule.mem_top⟩) =
      lieOfRealMat ((kMat x : Matrix (Fin 2) (Fin 2) ℝ) * A * ((kMat x)⁻¹ : GL (Fin 2) ℝ)) := by
    apply Subtype.ext
    change (((x : archGroup ℚ 2) : (ArchMatrix ℚ 2)ˣ) : ArchMatrix ℚ 2) * archRealEquiv.symm A *
      ((((x : archGroup ℚ 2)⁻¹ : archGroup ℚ 2) : (ArchMatrix ℚ 2)ˣ) : ArchMatrix ℚ 2) =
        archRealEquiv.symm _
    apply archRealEquiv.injective
    rw [RingEquiv.apply_symm_apply, map_mul, map_mul, RingEquiv.apply_symm_apply, archRealEquiv_coe,
      archRealEquiv_coe, archToReal_inv]
  rw [e1, e2] at key
  exact key

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem reMat_conj (K : GL (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    reMat ((K : Matrix (Fin 2) (Fin 2) ℝ).map (↑) * B * ((K⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map (↑)) =
      (K : Matrix (Fin 2) (Fin 2) ℝ) * reMat B * ((K⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  simp [reMat, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem imMat_conj (K : GL (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    imMat ((K : Matrix (Fin 2) (Fin 2) ℝ).map (↑) * B * ((K⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map (↑)) =
      (K : Matrix (Fin 2) (Fin 2) ℝ) * imMat B * ((K⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  simp [imMat, Matrix.mul_apply, Fin.sum_univ_two]

abbrev kMatC (x : archCompact ℚ 2) : Matrix (Fin 2) (Fin 2) ℂ := (kMat x : Matrix (Fin 2) (Fin 2) ℝ).map (↑)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem archCompactRepCusp_cuspOp (x : archCompact ℚ 2) {B B' : Matrix (Fin 2) (Fin 2) ℂ}
    (h : kMatC x * B = B' * kMatC x) (ψ : cuspForms ℚ 2) :
    archCompactRepCusp ℚ 2 x (cuspOp B ψ) = cuspOp B' (archCompactRepCusp ℚ 2 x ψ) := by
  have hKK : (kMat x : Matrix (Fin 2) (Fin 2) ℝ) * (((kMat x)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hKi : kMatC x * (((kMat x)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map (↑) = 1 := by
    rw [kMatC, show ((kMat x : Matrix (Fin 2) (Fin 2) ℝ).map ((↑) : ℝ → ℂ)) *
        (((kMat x)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map (↑) =
        ((kMat x : Matrix (Fin 2) (Fin 2) ℝ) * (((kMat x)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)).map
          Complex.ofRealHom from (Matrix.map_mul (f := Complex.ofRealHom)).symm, hKK]
    ext i j
    simp [Matrix.one_apply]
  have hB' : B' = kMatC x * B * (((kMat x)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map (↑) := by
    rw [h, Matrix.mul_assoc, hKi, Matrix.mul_one]
  rw [hB']
  simp only [cuspOp, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, archCompactRepCusp_rho]
  rw [kMatC, reMat_conj, imMat_conj]

abbrev kgc (w : ℂ) (hw : w ≠ 0) : Matrix (Fin 2) (Fin 2) ℂ := (kGL w hw : Matrix (Fin 2) (Fin 2) ℝ).map (↑)

abbrev epsC : Matrix (Fin 2) (Fin 2) ℂ := (toReal epsilon : Matrix (Fin 2) (Fin 2) ℝ).map (↑)

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem kgc_lowerMat (w : ℂ) (hw : w ≠ 0) : kgc w hw * lowerMat = w • lowerMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kgc, coe_kGL, lowerMat, Matrix.mul_apply, Complex.ext_iff]

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem lowerMat_kgc (w : ℂ) (hw : w ≠ 0) : lowerMat * kgc w hw = (starRingEnd ℂ w) • lowerMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kgc, coe_kGL, lowerMat, Matrix.mul_apply, Complex.ext_iff]

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem kgc_raiseMat (w : ℂ) (hw : w ≠ 0) : kgc w hw * raiseMat = (starRingEnd ℂ w) • raiseMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kgc, coe_kGL, raiseMat, Matrix.mul_apply, Complex.ext_iff]

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem raiseMat_kgc (w : ℂ) (hw : w ≠ 0) : raiseMat * kgc w hw = w • raiseMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kgc, coe_kGL, raiseMat, Matrix.mul_apply, Complex.ext_iff]

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem kgc_rotMat (w : ℂ) (hw : w ≠ 0) : kgc w hw * rotMat = rotMat * kgc w hw := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kgc, coe_kGL, rotMat, Matrix.mul_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem epsC_lowerMat : epsC * lowerMat = -(raiseMat * epsC) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsC, coe_toReal_epsilon, lowerMat, raiseMat, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two]

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem epsC_raiseMat : epsC * raiseMat = -(lowerMat * epsC) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsC, coe_toReal_epsilon, lowerMat, raiseMat, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two]

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem epsC_rotMat : epsC * rotMat = -(rotMat * epsC) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsC, coe_toReal_epsilon, rotMat, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem conj_ne_zero' {w : ℂ} (hw : w ≠ 0) : starRingEnd ℂ w ≠ 0 := (map_ne_zero _).2 hw

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem plus_lowerMat (w : ℂ) (hw : w ≠ 0) :
    kgc w hw * lowerMat = ((w / starRingEnd ℂ w) • lowerMat) * kgc w hw := by
  rw [Matrix.smul_mul, lowerMat_kgc, smul_smul, div_mul_cancel₀ _ (conj_ne_zero' hw), kgc_lowerMat]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem plus_raiseMat (w : ℂ) (hw : w ≠ 0) :
    kgc w hw * raiseMat = ((starRingEnd ℂ w / w) • raiseMat) * kgc w hw := by
  rw [Matrix.smul_mul, raiseMat_kgc, smul_smul, div_mul_cancel₀ _ hw, kgc_raiseMat]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem minus_lowerMat (w : ℂ) (hw : w ≠ 0) :
    epsC * kgc w hw * lowerMat = ((-(w / starRingEnd ℂ w)) • raiseMat) * (epsC * kgc w hw) := by
  have hRe : raiseMat * epsC = -(epsC * lowerMat) := by rw [epsC_lowerMat, neg_neg]
  rw [Matrix.mul_assoc, kgc_lowerMat, Matrix.mul_smul, epsC_lowerMat, Matrix.smul_mul, ← Matrix.mul_assoc, hRe,
    Matrix.neg_mul, Matrix.mul_assoc, lowerMat_kgc, Matrix.mul_smul, epsC_lowerMat]
  simp only [smul_neg, neg_neg, smul_smul]
  rw [neg_mul, div_mul_cancel₀ _ (conj_ne_zero' hw)]
  exact (_root_.neg_smul w _).symm

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem minus_raiseMat (w : ℂ) (hw : w ≠ 0) :
    epsC * kgc w hw * raiseMat = ((-(starRingEnd ℂ w / w)) • lowerMat) * (epsC * kgc w hw) := by
  have hLe : lowerMat * epsC = -(epsC * raiseMat) := by rw [epsC_raiseMat, neg_neg]
  rw [Matrix.mul_assoc, kgc_raiseMat, Matrix.mul_smul, epsC_raiseMat, Matrix.smul_mul, ← Matrix.mul_assoc, hLe,
    Matrix.neg_mul, Matrix.mul_assoc, raiseMat_kgc, Matrix.mul_smul, epsC_raiseMat]
  simp only [smul_neg, neg_neg, smul_smul]
  rw [neg_mul, div_mul_cancel₀ _ hw]
  exact (_root_.neg_smul _ _).symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem minus_rotMat (w : ℂ) (hw : w ≠ 0) :
    epsC * kgc w hw * rotMat = ((-1 : ℂ) • rotMat) * (epsC * kgc w hw) := by
  rw [Matrix.mul_assoc, kgc_rotMat, ← Matrix.mul_assoc, epsC_rotMat, neg_one_smul, Matrix.neg_mul,
    Matrix.neg_mul, Matrix.mul_assoc]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem kMatC_of_plus {x : archCompact ℚ 2} {w : ℂ} {hw : w ≠ 0} (hK : kMat x = kGL w hw) :
    kMatC x = kgc w hw := by
  rw [kMatC, hK]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem kMatC_of_minus {x : archCompact ℚ 2} {w : ℂ} {hw : w ≠ 0} (hK : kMat x = toReal epsilon * kGL w hw) :
    kMatC x = epsC * kgc w hw := by
  rw [kMatC, hK, Units.val_mul]
  exact Matrix.map_mul (f := Complex.ofRealHom)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem archCompactRepCusp_cuspOp_one (x : archCompact ℚ 2) (ψ : cuspForms ℚ 2) :
    archCompactRepCusp ℚ 2 x (cuspOp 1 ψ) = cuspOp 1 (archCompactRepCusp ℚ 2 x ψ) :=
  archCompactRepCusp_cuspOp x (by rw [Matrix.mul_one, Matrix.one_mul]) ψ

end GL2Classical

end

end GroundTheory.Automorphic
