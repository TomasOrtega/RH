import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLine

set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDiscDeg

variable {F : Type} [Field F] {σ : Type}

def CoeffDeg (e : ℕ) (P : Polynomial (MvPolynomial σ F)) : Prop :=
  ∀ k, (P.coeff k).totalDegree ≤ e

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem CoeffDeg.mono {e e' : ℕ} {P : Polynomial (MvPolynomial σ F)} (h : CoeffDeg e P) (he : e ≤ e') :
    CoeffDeg e' P := fun k => (h k).trans he

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem coeffDeg_C {e : ℕ} {a : MvPolynomial σ F} (ha : a.totalDegree ≤ e) :
    CoeffDeg e (Polynomial.C a) := by
  intro k
  rw [Polynomial.coeff_C]
  split_ifs
  · exact ha
  · simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeffDeg_one : CoeffDeg 0 (1 : Polynomial (MvPolynomial σ F)) := by
  rw [← Polynomial.C_1]
  exact coeffDeg_C (by simp)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem coeffDeg_X : CoeffDeg 0 (Polynomial.X : Polynomial (MvPolynomial σ F)) := by
  intro k
  rw [Polynomial.coeff_X]
  split_ifs <;> simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem CoeffDeg.add {e : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) (hQ : CoeffDeg e Q) :
    CoeffDeg e (P + Q) := by
  intro k
  rw [Polynomial.coeff_add]
  exact (totalDegree_add _ _).trans (max_le (hP k) (hQ k))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem CoeffDeg.mul {e e' : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P)
    (hQ : CoeffDeg e' Q) : CoeffDeg (e + e') (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact totalDegree_finsetSum_le fun x _ => (totalDegree_mul _ _).trans (add_le_add (hP _) (hQ _))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeffDeg_sum {ι : Type} (s : Finset ι) {e : ℕ} (P : ι → Polynomial (MvPolynomial σ F))
    (h : ∀ i ∈ s, CoeffDeg e (P i)) : CoeffDeg e (∑ i ∈ s, P i) := by
  intro k
  rw [Polynomial.finset_sum_coeff]
  exact totalDegree_finsetSum_le fun i hi => h i hi k

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeffDeg_prod {ι : Type} [DecidableEq ι] (s : Finset ι) (e : ι → ℕ)
    (P : ι → Polynomial (MvPolynomial σ F)) (h : ∀ i ∈ s, CoeffDeg (e i) (P i)) :
    CoeffDeg (∑ i ∈ s, e i) (∏ i ∈ s, P i) := by
  induction s using Finset.induction_on with
  | empty => simpa using coeffDeg_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem CoeffDeg.pow {e : ℕ} {P : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) (n : ℕ) :
    CoeffDeg (n * e) (P ^ n) := by
  induction n with
  | zero => simpa using coeffDeg_one
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hP

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem CoeffDeg.derivative {e : ℕ} {P : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) :
    CoeffDeg e (Polynomial.derivative P) := by
  intro k
  rw [Polynomial.coeff_derivative]
  have h1 : ((k : MvPolynomial σ F) + 1) = C ((k : F) + 1) := by simp
  rw [h1]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, add_zero]
  exact hP (k + 1)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Treat this case separately. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem totalDegree_resultant_le {e : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P)
    (hQ : CoeffDeg e Q) (m n : ℕ) : (Polynomial.resultant P Q m n).totalDegree ≤ (m + n) * e := by
  have hH : ∀ i j, (Polynomial.sylvester P Q m n i j).totalDegree ≤ e := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hQ _
      · simp
    | right j =>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hP _
      · simp
  rw [Polynomial.resultant, Matrix.det_apply]
  refine totalDegree_finsetSum_le fun s _ => ?_
  refine (totalDegree_smul_le _ _).trans ((totalDegree_finsetProd _ _).trans ?_)
  simpa using Finset.sum_le_card_nsmul Finset.univ _ e fun i _ => hH (s i) i

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem coeffDeg_line {D N δ : ℕ} (f : MvPolynomial (Fin (D + 1) × Fin N) F)
    (hf : IsMultiHomogeneous (fun _ => δ) f) (ξ₀ ξ₁ : Fin N → F) :
    CoeffDeg (D * δ) (line (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F))
      (fun j => C (ξ₀ j)) (fun j => C (ξ₁ j)) f) := by
  rw [line, aeval_def, eval₂_eq']
  refine coeffDeg_sum _ _ fun d hd => ?_
  have hc : CoeffDeg 0 (algebraMap F (Polynomial (MvPolynomial (Fin D × Fin N) F)) (coeff d f)) := by
    rw [Polynomial.algebraMap_apply]
    exact coeffDeg_C (by rw [MvPolynomial.algebraMap_eq, totalDegree_C])
  have hw : ∀ p : Fin (D + 1) × Fin N, CoeffDeg (if p.1 = Fin.last D then 0 else 1)
      (join (fun i j => Polynomial.C (X (i, j) : MvPolynomial (Fin D × Fin N) F))
        (fun j => Polynomial.C (C (ξ₀ j)) + Polynomial.C (C (ξ₁ j)) * Polynomial.X) p) := by
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [join, Fin.lastCases_last, if_true]
      exact (coeffDeg_C (totalDegree_C _).le).add ((coeffDeg_C (e := 0) (totalDegree_C _).le).mul coeffDeg_X)
    · simp only [join, Fin.lastCases_castSucc, if_neg (Fin.castSucc_ne_last i)]
      exact coeffDeg_C (totalDegree_X _).le
  refine (hc.mul (coeffDeg_prod Finset.univ _ _ fun p _ => (hw p).pow (d p))).mono (le_of_eq ?_)
  rw [zero_add, Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  have h := hf d hd
  simp [Fin.castSucc_ne_last, h]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation.
-/
theorem totalDegree_disc_le (F : Type) [Field F] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F)
    (hf : IsMultiHomogeneous (fun _ => δ) f) (ξ₀ ξ₁ : Fin N → F) :
    (disc δ (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F))
      (fun j => C (ξ₀ j)) (fun j => C (ξ₁ j)) f).totalDegree ≤ 2 * D * δ ^ 2 := by
  have h := coeffDeg_line f hf ξ₀ ξ₁
  refine (totalDegree_resultant_le h h.derivative δ (δ - 1)).trans ?_
  calc (δ + (δ - 1)) * (D * δ) ≤ (2 * δ) * (D * δ) := Nat.mul_le_mul_right _ (by omega)
    _ = 2 * D * δ ^ 2 := by ring

end GlobalTheory.PencilDiscDeg
