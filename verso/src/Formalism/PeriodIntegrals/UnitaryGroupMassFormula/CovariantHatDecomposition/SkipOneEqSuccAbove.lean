import Mathlib
import Formalism.PeriodIntegrals.ContractionsCovariantIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatDecomposition.InjDecomp

open Finset Matrix Formalism.REAL Formalism.FourierDecayAlt.Q

namespace PI.QnCovHatW

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Unfold `skip1`. Distinguish the cases in `h : (j : ℕ) < (i : ℕ)`. Rewrite using `[if_pos h, Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using h)]`. Both sides reduce to the same expression.

Rewrite using `[if_neg h, Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp only [Fin.coe_castSucc]; omega)]`. Both sides reduce to the same expression.
-/
theorem skip_one_eq_succAbove {m : ℕ} (i : Fin (m + 1)) (j : Fin m) : skip1 (t := m + 1) i j = i.succAbove j := by
  apply Fin.ext
  unfold skip1
  by_cases h : (j : ℕ) < (i : ℕ)
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using h)]
    rfl
  · rw [if_neg h, Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp only [Fin.coe_castSucc]; omega)]
    rfl

/- English proof (translation)
Establish `h1 : (fun k : Fin m => skip1 (t` using `m + 1) i k) = i.succAbove := funext (skip_one_eq_succAbove i)`. Establish `h2 : (fun k : Fin m => skip1 (t` using `m + 1) j k) = j.succAbove := funext (skip_one_eq_succAbove j)`. Rewrite using `[← h1, ← h2]`.
-/
theorem qminor_skip {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A)
    (i j : Fin (m + 1)) (u : ℂ) :
    qminor E (skip1 i) (skip1 j) u = qminor (t := m) E i.succAbove j.succAbove u := by
  have h1 : (fun k : Fin m => skip1 (t := m + 1) i k) = i.succAbove := funext (skip_one_eq_succAbove i)
  have h2 : (fun k : Fin m => skip1 (t := m + 1) j k) = j.succAbove := funext (skip_one_eq_succAbove j)
  rw [← h1, ← h2]

/- English proof (translation)
Rewrite using `[Algebra.smul_def, map_intCast]`.
-/
theorem int_smul_eq {A : Type} [Ring A] [Algebra ℂ A] (k : ℤ) (x : A) :
    ((k : ℂ)) • x = (k : A) * x := by
  rw [Algebra.smul_def, map_intCast]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i' _ => Finset.sum_comm`. Use `_ = ∑ i', ∑ i, ∑ j', ∑ j, f i j i' j' := Finset.sum_comm`.

Use `_ = ∑ i', ∑ j', ∑ i, ∑ j, f i j i' j' := Finset.sum_congr rfl fun i' _ => Finset.sum_comm`.
-/
theorem swap4 {M : Type*} [AddCommMonoid M] {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → M) :
    ∑ i, ∑ j, ∑ i', ∑ j', f i j i' j' = ∑ i', ∑ j', ∑ i, ∑ j, f i j i' j' := by
  calc ∑ i, ∑ j, ∑ i', ∑ j', f i j i' j' = ∑ i, ∑ i', ∑ j', ∑ j, f i j i' j' := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i' _ => Finset.sum_comm
    _ = ∑ i', ∑ i, ∑ j', ∑ j, f i j i' j' := Finset.sum_comm
    _ = ∑ i', ∑ j', ∑ i, ∑ j, f i j i' j' :=
        Finset.sum_congr rfl fun i' _ => Finset.sum_comm

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Both sides reduce to the same expression.
-/
theorem det_sub_eq {m : ℕ} (P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (i' i : Fin (m + 1)) :
    ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, P ((i'.succAbove ∘ σ) k) (i.succAbove k) =
      (P.submatrix i'.succAbove i.succAbove).det := by
  rw [Matrix.det_apply']
  rfl

/- English proof (translation)
Rewrite using `[← Matrix.det_transpose, Matrix.det_apply']`. Both sides reduce to the same expression.
-/
theorem det_sub_eq' {m : ℕ} (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (j j' : Fin (m + 1)) :
    ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, Q (j.succAbove k) ((j'.succAbove ∘ σ) k) =
      (Q.submatrix j.succAbove j'.succAbove).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

/- English proof (translation)
Establish `hsign : ∀ i j : Fin (m + 1), ((-1 : ℂ)) ^ ((i : ℕ) + (j : ℕ)) = (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * ((-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)))`. Introduce `i j`. Rewrite using `[← pow_add, ← pow_add]`. Establish `h : (i' : ℕ) + j' + ((i' : ℕ) + i + ((j : ℕ) + j')) = ((i : ℕ) + j) + 2 * ((i' : ℕ) + j')` using `by ring`. Rewrite using `[h, pow_add (-1 : ℂ) ((i : ℕ) + (j : ℕ)), pow_mul]`.

Evaluate the numerical expressions. Establish `hX : ∑ i : Fin (m + 1), (β ᵥ* P) i * ((-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) * (P.submatrix i'.succAbove i.succAbove).det) = P.det * β i'`. Establish `h1 : ∀ i : Fin (m + 1), (-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) * (P.submatrix i'.succAbove i.succAbove).det = P.adjugate i i'` using `fun i => (Matrix.adjugate_fin_succ_eq_det_submatrix P i i').symm`. Repeatedly rewrite using `[h1]`. Establish `h2 : ∑ i, (β ᵥ* P) i * P.adjugate i i' = (β ᵥ* P ᵥ* P.adjugate) i'` using `rfl`.

Rewrite using `[h2, Matrix.vecMul_vecMul, Matrix.mul_adjugate]`. Use `first`. Consider the case `(rw [Matrix.vecMul_smul, Matrix.vecMul_one]; rfl)`. Consider the case `simp [Matrix.vecMul, dotProduct, Matrix.one_apply, mul_comm]`. Establish `hY : ∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (Q.submatrix j.succAbove j'.succAbove).det) * (Q *ᵥ a) j = Q.det * a j'`.

Establish `h1 : ∀ j : Fin (m + 1), (-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (Q.submatrix j.succAbove j'.succAbove).det = Q.adjugate j' j` using `fun j => (Matrix.adjugate_fin_succ_eq_det_submatrix Q j' j).symm`. Repeatedly rewrite using `[h1]`. Establish `h2 : ∑ j, Q.adjugate j' j * (Q *ᵥ a) j = (Q.adjugate *ᵥ (Q *ᵥ a)) j'` using `rfl`. Rewrite using `[h2, Matrix.mulVec_mulVec, Matrix.adjugate_mul]`. Use `first`.

Consider the case `(rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]; rfl)`. Consider the case `simp [Matrix.mulVec, dotProduct, Matrix.one_apply]`. Establish `hdet : P.det * Q.det = 1`. Rewrite using `[← Matrix.det_mul, hPQ, Matrix.det_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hsign i j]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * β i' * a j' := by`. Rewrite using `[hX, hY]`. Take the linear combination `(-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * β i' * a j' * hdet`.
-/
theorem scal {m : ℕ} (P Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hPQ : P * Q = 1)
    (a β : Fin (m + 1) → ℂ) (i' j' : Fin (m + 1)) :
    ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * (β ᵥ* P) i * (Q *ᵥ a) j) *
          ((P.submatrix i'.succAbove i.succAbove).det * (Q.submatrix j.succAbove j'.succAbove).det) =
      (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * β i' * a j' := by
  have hsign : ∀ i j : Fin (m + 1), ((-1 : ℂ)) ^ ((i : ℕ) + (j : ℕ)) =
      (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * ((-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ))) := by
    intro i j
    rw [← pow_add, ← pow_add]
    have h : (i' : ℕ) + j' + ((i' : ℕ) + i + ((j : ℕ) + j')) = ((i : ℕ) + j) + 2 * ((i' : ℕ) + j') := by ring
    rw [h, pow_add (-1 : ℂ) ((i : ℕ) + (j : ℕ)), pow_mul]
    norm_num
  have hX : ∑ i : Fin (m + 1), (β ᵥ* P) i * ((-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) *
      (P.submatrix i'.succAbove i.succAbove).det) = P.det * β i' := by
    have h1 : ∀ i : Fin (m + 1), (-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) *
        (P.submatrix i'.succAbove i.succAbove).det = P.adjugate i i' :=
      fun i => (Matrix.adjugate_fin_succ_eq_det_submatrix P i i').symm
    simp_rw [h1]
    have h2 : ∑ i, (β ᵥ* P) i * P.adjugate i i' = (β ᵥ* P ᵥ* P.adjugate) i' := rfl
    rw [h2, Matrix.vecMul_vecMul, Matrix.mul_adjugate]
    first
    | (rw [Matrix.vecMul_smul, Matrix.vecMul_one]; rfl)
    | simp [Matrix.vecMul, dotProduct, Matrix.one_apply, mul_comm]
  have hY : ∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) *
      (Q.submatrix j.succAbove j'.succAbove).det) * (Q *ᵥ a) j = Q.det * a j' := by
    have h1 : ∀ j : Fin (m + 1), (-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) *
        (Q.submatrix j.succAbove j'.succAbove).det = Q.adjugate j' j :=
      fun j => (Matrix.adjugate_fin_succ_eq_det_submatrix Q j' j).symm
    simp_rw [h1]
    have h2 : ∑ j, Q.adjugate j' j * (Q *ᵥ a) j = (Q.adjugate *ᵥ (Q *ᵥ a)) j' := rfl
    rw [h2, Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    first
    | (rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]; rfl)
    | simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hdet : P.det * Q.det = 1 := by
    rw [← Matrix.det_mul, hPQ, Matrix.det_one]
  calc _ = (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) *
        ((∑ i : Fin (m + 1), (β ᵥ* P) i * ((-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) *
          (P.submatrix i'.succAbove i.succAbove).det)) *
        (∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) *
          (Q.submatrix j.succAbove j'.succAbove).det) * (Q *ᵥ a) j)) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsign i j]
        ring
    _ = (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * β i' * a j' := by
        rw [hX, hY]
        linear_combination (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * β i' * a j' * hdet

/- English proof (translation)
Introduce `A _ _ n E P Q hE hQP hPQ u a β`. Consider the cases of `n with`. Consider the case `zero => simp [chatA]`. Consider the case `succ m`. Establish `rskew : ∀ (d c : Fin m → Fin (m + 1)) (σ : Equiv.Perm (Fin m)), qminor E (c ∘ σ) d u = ((Equiv.Perm.sign σ : ℤ) : ℂ) • qminor E c d u`.

Introduce `d c σ`. Rewrite using `[int_smul_eq]`. Conclude with `quantumMinorRowSkew_holds A (m + 1) m E c d σ u`. Establish `rzero : ∀ (d c : Fin m → Fin (m + 1)), ¬ Function.Injective c → qminor E c d u = 0`. Introduce `d c hc`.

Take `⟨p, q, hpq, hne⟩` from `Function.not_injective_iff.mp hc`. Conclude with `quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c d u p q hne hpq`. Establish `cskew : ∀ (c d : Fin m → Fin (m + 1)) (σ : Equiv.Perm (Fin m)), qminor E c (d ∘ σ) u = ((Equiv.Perm.sign σ : ℤ) : ℂ) • qminor E c d u`. Introduce `c d σ`. Rewrite using `[int_smul_eq]`.

Conclude with `quantumMinorColSkew_holds A (m + 1) m E hE c d σ u`. Establish `czero : ∀ (c d : Fin m → Fin (m + 1)), ¬ Function.Injective d → qminor E c d u = 0`. Introduce `c d hd`. Take `⟨p, q, hpq, hne⟩` from `Function.not_injective_iff.mp hd`. Conclude with `quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE c d u p q hne hpq`.

Establish `key : ∀ i j : Fin (m + 1), qminor (Econj E P Q) i.succAbove j.succAbove u = ∑ i' : Fin (m + 1), ∑ j' : Fin (m + 1), ((P.submatrix i'.succAbove i.succAbove).det * (Q.submatrix j.succAbove j'.succAbove).det) • qminor E i'.succAbove j'.succAbove u`. Introduce `i j`. Rewrite using `[hL A (m + 1) m E P Q hQP i.succAbove j.succAbove u]`. Repeatedly rewrite using `[mul_smul]`. Repeatedly rewrite using `[← Finset.smul_sum]`.

Establish `inner : ∀ c : Fin m → Fin (m + 1), ∑ d : Fin m → Fin (m + 1), (∏ k, Q (j.succAbove k) (d k)) • qminor E c d u = ∑ j' : Fin (m + 1), (Q.submatrix j.succAbove j'.succAbove).det • qminor E c j'.succAbove u`. Introduce `c`. Rewrite using `[alt_sum (fun d => qminor E c d u) (cskew c) (czero c)]`. Use `Finset.sum_congr rfl fun j' _ => ?_` and prove the remaining obligations. Rewrite using `[det_sub_eq']`.

Repeatedly rewrite using `[inner]`. Rewrite using `[alt_sum (fun c => ∑ j' : Fin (m + 1), (Q.submatrix j.succAbove j'.succAbove).det • qminor E c j'.succAbove u) ?_ ?_]`. Use `Finset.sum_congr rfl fun i' _ => ?_` and prove the remaining obligations. Rewrite using `[det_sub_eq, Finset.smul_sum]`. Introduce `c σ`.

Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j' _ => ?_` and prove the remaining obligations. Rewrite using `[rskew, smul_comm]`. Introduce `c hc`. Use `Finset.sum_eq_zero fun j' _ => ?_` and prove the remaining obligations.

Rewrite using `[rzero _ c hc, smul_zero]`. Simplify using `only [chatA, qminor_skip]`. Repeatedly rewrite using `[key, Finset.smul_sum, smul_smul]`. Rewrite using `[swap4]`. Use `Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_` and prove the remaining obligations.

Repeatedly rewrite using `[← Finset.sum_smul]`. Rewrite using `[scal P Q hPQ a β i' j']`.
-/
theorem qnCovHat_of_lin (hL : PI.QnCovLin) : PI.QnCovHat := by
  intro A _ _ n E P Q hE hQP hPQ u a β
  cases n with
  | zero => simp [chatA]
  | succ m =>
  have rskew : ∀ (d c : Fin m → Fin (m + 1)) (σ : Equiv.Perm (Fin m)),
      qminor E (c ∘ σ) d u = ((Equiv.Perm.sign σ : ℤ) : ℂ) • qminor E c d u := by
    intro d c σ
    rw [int_smul_eq]
    exact quantumMinorRowSkew_holds A (m + 1) m E c d σ u
  have rzero : ∀ (d c : Fin m → Fin (m + 1)), ¬ Function.Injective c → qminor E c d u = 0 := by
    intro d c hc
    obtain ⟨p, q, hpq, hne⟩ := Function.not_injective_iff.mp hc
    exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c d u p q hne hpq
  have cskew : ∀ (c d : Fin m → Fin (m + 1)) (σ : Equiv.Perm (Fin m)),
      qminor E c (d ∘ σ) u = ((Equiv.Perm.sign σ : ℤ) : ℂ) • qminor E c d u := by
    intro c d σ
    rw [int_smul_eq]
    exact quantumMinorColSkew_holds A (m + 1) m E hE c d σ u
  have czero : ∀ (c d : Fin m → Fin (m + 1)), ¬ Function.Injective d → qminor E c d u = 0 := by
    intro c d hd
    obtain ⟨p, q, hpq, hne⟩ := Function.not_injective_iff.mp hd
    exact quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE c d u p q hne hpq
  have key : ∀ i j : Fin (m + 1), qminor (Econj E P Q) i.succAbove j.succAbove u =
      ∑ i' : Fin (m + 1), ∑ j' : Fin (m + 1),
        ((P.submatrix i'.succAbove i.succAbove).det * (Q.submatrix j.succAbove j'.succAbove).det) •
          qminor E i'.succAbove j'.succAbove u := by
    intro i j
    rw [hL A (m + 1) m E P Q hQP i.succAbove j.succAbove u]
    simp_rw [mul_smul]
    simp_rw [← Finset.smul_sum]
    have inner : ∀ c : Fin m → Fin (m + 1),
        ∑ d : Fin m → Fin (m + 1), (∏ k, Q (j.succAbove k) (d k)) • qminor E c d u =
          ∑ j' : Fin (m + 1), (Q.submatrix j.succAbove j'.succAbove).det • qminor E c j'.succAbove u := by
      intro c
      rw [alt_sum (fun d => qminor E c d u) (cskew c) (czero c)]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [det_sub_eq']
    simp_rw [inner]
    rw [alt_sum (fun c => ∑ j' : Fin (m + 1),
        (Q.submatrix j.succAbove j'.succAbove).det • qminor E c j'.succAbove u) ?_ ?_]
    · refine Finset.sum_congr rfl fun i' _ => ?_
      rw [det_sub_eq, Finset.smul_sum]
    · intro c σ
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [rskew, smul_comm]
    · intro c hc
      refine Finset.sum_eq_zero fun j' _ => ?_
      rw [rzero _ c hc, smul_zero]
  simp only [chatA, qminor_skip]
  simp_rw [key, Finset.smul_sum, smul_smul]
  rw [swap4]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
  simp_rw [← Finset.sum_smul]
  rw [scal P Q hPQ a β i' j']

end PI.QnCovHatW
