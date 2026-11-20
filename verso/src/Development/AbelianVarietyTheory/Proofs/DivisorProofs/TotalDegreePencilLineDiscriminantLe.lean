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
Introduce `k` and use `(h k).trans he`.
-/
theorem CoeffDeg.mono {e e' : ℕ} {P : Polynomial (MvPolynomial σ F)} (h : CoeffDeg e P) (he : e ≤ e') :
    CoeffDeg e' P := fun k => (h k).trans he

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.coeff_C]`. Use `split_ifs`. Conclude with `ha`. Simplify using the standard rewrite rules.
-/
theorem coeffDeg_C {e : ℕ} {a : MvPolynomial σ F} (ha : a.totalDegree ≤ e) :
    CoeffDeg e (Polynomial.C a) := by
  intro k
  rw [Polynomial.coeff_C]
  split_ifs
  · exact ha
  · simp

/- English proof (translation)
Rewrite using `[← Polynomial.C_1]`. Conclude with `coeffDeg_C (by simp)`.
-/
theorem coeffDeg_one : CoeffDeg 0 (1 : Polynomial (MvPolynomial σ F)) := by
  rw [← Polynomial.C_1]
  exact coeffDeg_C (by simp)

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.coeff_X]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem coeffDeg_X : CoeffDeg 0 (Polynomial.X : Polynomial (MvPolynomial σ F)) := by
  intro k
  rw [Polynomial.coeff_X]
  split_ifs <;> simp

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.coeff_add]`. Conclude with `(totalDegree_add _ _).trans (max_le (hP k) (hQ k))`.
-/
theorem CoeffDeg.add {e : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) (hQ : CoeffDeg e Q) :
    CoeffDeg e (P + Q) := by
  intro k
  rw [Polynomial.coeff_add]
  exact (totalDegree_add _ _).trans (max_le (hP k) (hQ k))

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.coeff_mul]`. Conclude with `totalDegree_finsetSum_le fun x _ => (totalDegree_mul _ _).trans (add_le_add (hP _) (hQ _))`.
-/
theorem CoeffDeg.mul {e e' : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P)
    (hQ : CoeffDeg e' Q) : CoeffDeg (e + e') (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact totalDegree_finsetSum_le fun x _ => (totalDegree_mul _ _).trans (add_le_add (hP _) (hQ _))

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.finset_sum_coeff]`. Conclude with `totalDegree_finsetSum_le fun i hi => h i hi k`.
-/
theorem coeffDeg_sum {ι : Type} (s : Finset ι) {e : ℕ} (P : ι → Polynomial (MvPolynomial σ F))
    (h : ∀ i ∈ s, CoeffDeg e (P i)) : CoeffDeg e (∑ i ∈ s, P i) := by
  intro k
  rw [Polynomial.finset_sum_coeff]
  exact totalDegree_finsetSum_le fun i hi => h i hi k

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using coeffDeg_one`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `(h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
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
Proceed by induction on `n with`. Consider the case `zero => simpa using coeffDeg_one`. Consider the case `succ n ih`. Rewrite using `[pow_succ, Nat.succ_mul]`. Conclude with `ih.mul hP`.
-/
theorem CoeffDeg.pow {e : ℕ} {P : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) (n : ℕ) :
    CoeffDeg (n * e) (P ^ n) := by
  induction n with
  | zero => simpa using coeffDeg_one
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hP

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.coeff_derivative]`. Establish `h1 : ((k : MvPolynomial σ F) + 1) = C ((k : F) + 1)` using `by simp`. Rewrite using `[h1]`. Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[totalDegree_C, add_zero]`. Conclude with `hP (k + 1)`.
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
Establish `hH : ∀ i j, (Polynomial.sylvester P Q m n i j).totalDegree ≤ e`. Introduce `i j`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left j`. Simplify using `only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]`.

Use `split_ifs`. Conclude with `hQ _`. Simplify using the standard rewrite rules. Consider the case `right j`. Simplify using `only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]`.

Use `split_ifs`. Conclude with `hP _`. Simplify using the standard rewrite rules. Rewrite using `[Polynomial.resultant, Matrix.det_apply]`. Use `totalDegree_finsetSum_le fun s _ => ?_` and prove the remaining obligations.

Use `(totalDegree_smul_le _ _).trans ((totalDegree_finsetProd _ _).trans ?_)` and prove the remaining obligations. Simplify using `using Finset.sum_le_card_nsmul Finset.univ _ e fun i _ => hH (s i) i`.
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
Rewrite using `[line, aeval_def, eval₂_eq']`. Use `coeffDeg_sum _ _ fun d hd => ?_` and prove the remaining obligations. Establish `hc : CoeffDeg 0 (algebraMap F (Polynomial (MvPolynomial (Fin D × Fin N) F)) (coeff d f))`. Rewrite using `[Polynomial.algebraMap_apply]`. Conclude with `coeffDeg_C (by rw [MvPolynomial.algebraMap_eq, totalDegree_C])`.

Establish `hw : ∀ p : Fin (D + 1) × Fin N, CoeffDeg (if p.1 = Fin.last D then 0 else 1) (join (fun i j => Polynomial.C (X (i, j) : MvPolynomial (Fin D × Fin N) F)) (fun j => Polynomial.C (C (ξ₀ j)) + Polynomial.C (C (ξ₁ j)) * Polynomial.X) p)`. Introduce and unpack `⟨i, j⟩`. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `only [join, Fin.lastCases_last, if_true]`. Conclude with `(coeffDeg_C (totalDegree_C _).le).add ((coeffDeg_C (e := 0) (totalDegree_C _).le).mul coeffDeg_X)`.

Simplify using `only [join, Fin.lastCases_castSucc, if_neg (Fin.castSucc_ne_last i)]`. Conclude with `coeffDeg_C (totalDegree_X _).le`. Use `(hc.mul (coeffDeg_prod Finset.univ _ _ fun p _ => (hw p).pow (d p))).mono (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[zero_add, Fintype.sum_prod_type, Fin.sum_univ_castSucc]`. Establish `h` using `hf d hd`.

Simplify using `[Fin.castSucc_ne_last, h]`.
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
Establish `h` using `coeffDeg_line f hf ξ₀ ξ₁`. Use `(totalDegree_resultant_le h h.derivative δ (δ - 1)).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
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
