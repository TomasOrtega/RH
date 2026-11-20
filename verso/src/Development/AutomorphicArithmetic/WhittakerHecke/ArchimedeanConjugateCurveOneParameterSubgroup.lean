import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem nC_zero' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] : nC (0 : Cinf E) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nC]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem nC_add' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (a b : Cinf E) :
    nC (a + b) = nC a * nC b := by
  apply Units.ext
  ext i j : 2
  fin_cases i <;> fin_cases j <;> simp [nC, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem nC_val' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (t : ℝ) (z : Cinf E) :
    (nC (t • z)).val = 1 + t • (!![0, z; 0, 0] : Matrix (Fin 2) (Fin 2) (Cinf E)) := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;> simp [nC]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem cv_val' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E)
    (k : GL (Fin 2) (A E)) (t : ℝ) : (cv D k t).val = 1 + t • XB D k := by
  have h : ((kInf k)⁻¹).val * (kInf k).val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [cv, XB, Units.val_mul, nC_val', mul_add, add_mul, mul_one, h, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.archimedeanConjugateCurve_oneParameterSubgroup :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (k : GL (Fin 2) (A E)),
        cv D k 0 = 1 ∧ (∀ s t, cv D k (s + t) = cv D k s * cv D k t) ∧ HasDerivAt (fun t => toL (cv D k t).val) (toL (XB D k)) 0 ∧
        Continuous fun k : GL (Fin 2) (A E) => toL (XB D k) := by
  intro E _ _ _ D k
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [cv, nC_zero']
  · intro s t
    simp only [cv, add_smul, nC_add']
    group
  · have h : (fun t : ℝ => toL (cv D k t).val) =
        fun t : ℝ => toL (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) + t • toL (XB D k) := by
      funext t
      rw [cv_val']
      rfl
    rw [h]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toL (XB D k))).const_add
      (toL (1 : Matrix (Fin 2) (Fin 2) (Cinf E)))
  · have hK : Continuous fun k : GL (Fin 2) (A E) => kInf k := ContAut.continuous_map_pInf E 2
    have h1 : Continuous fun k : GL (Fin 2) (A E) => (kInf k).val := Units.continuous_val.comp hK
    have h2 : Continuous fun k : GL (Fin 2) (A E) => ((kInf k)⁻¹).val :=
      Units.continuous_val.comp hK.inv
    exact (h2.matrix_mul continuous_const).matrix_mul h1
