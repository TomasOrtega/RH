import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.LaplaceExpansionColumn

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def ql_U : (N : ℕ) → (Fin N → Finset (Fin n)) → Finset (Fin n)
  | 0, _ => ∅
  | N + 1, D => D 0 ∪ ql_U N (Fin.tail D)

def ql_sW (R : Type*) [CommRing R] : (N : ℕ) → (Fin N → Finset (Fin n)) → R
  | 0, _ => 1
  | N + 1, D => wedgeSign R (D 0) (ql_U N (Fin.tail D)) * ql_sW R N (Fin.tail D)

def wedgeCoeff (R : Type*) [CommRing R] {N : ℕ} (D : Fin N → Finset (Fin n)) (L : Finset (Fin n)) : R :=
  if ql_U N D = L then ql_sW R N D else 0

variable {R : Type*} [CommRing R]

/- English proof (translation)
Simplify using `only [wedgeCoeff, mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true, ql_U, ql_sW, ql_w, ite_mul, zero_mul]`. Reduce the equality to equality of the corresponding arguments.
-/
lemma ql_W_succ {N : ℕ} (D : Fin (N + 1) → Finset (Fin n)) (L : Finset (Fin n)) :
    wedgeCoeff R D L = ∑ M, ql_w R (D 0) M L * wedgeCoeff R (Fin.tail D) M := by
  simp only [wedgeCoeff, mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true, ql_U, ql_sW, ql_w, ite_mul, zero_mul]
  congr

/- English proof (translation)
The claim follows from `| 0, _ => by simp [ql_sW] | N + 1, D => by simp only [ql_sW, Int.cast_mul, ql_s_cast, ql_sW_cast N]`.
-/
lemma ql_sW_cast : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)), ((ql_sW ℤ N D : ℤ) : R) = ql_sW R N D
  | 0, _ => by simp [ql_sW]
  | N + 1, D => by simp only [ql_sW, Int.cast_mul, ql_s_cast, ql_sW_cast N]

/- English proof (translation)
Unfold `wedgeCoeff`. Use `split_ifs`. Conclude with `ql_sW_cast N D`. Simplify using the standard rewrite rules.
-/
lemma ql_W_cast {N : ℕ} (D : Fin N → Finset (Fin n)) (L : Finset (Fin n)) :
    ((wedgeCoeff ℤ D L : ℤ) : R) = wedgeCoeff R D L := by
  unfold wedgeCoeff; split_ifs
  · exact ql_sW_cast N D
  · simp

/- English proof (translation)
The claim follows from `| 0, _, a => by simp [ql_U] | N + 1, D, a => by rw [ql_U, mem_union, ql_mem_U N, Fin.exists_fin_succ]; rfl`.
-/
lemma ql_mem_U : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)) (a : Fin n), a ∈ ql_U N D ↔ ∃ j, a ∈ D j
  | 0, _, a => by simp [ql_U]
  | N + 1, D, a => by
    rw [ql_U, mem_union, ql_mem_U N, Fin.exists_fin_succ]; rfl

/- English proof (translation)
The claim follows from `| 0, _, _ => by simp [ql_sW] | N + 1, D, h => by rw [ql_sW] refine IsUnit.mul (ql_s_isUnit ?_) (ql_sW_isUnit N _ fun i j hij => h _ _ (by simpa using hij)) rw [Finset.disjoint_left] intro a ha hU obtain ⟨j, hj⟩ := (ql_mem_U N _ a).1 hU exact Finset.disjoint_left.1 (h 0 j.succ (Fi …`.
-/
lemma ql_sW_isUnit : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)), (∀ i j, i ≠ j → Disjoint (D i) (D j)) →
    IsUnit (ql_sW R N D)
  | 0, _, _ => by simp [ql_sW]
  | N + 1, D, h => by
    rw [ql_sW]
    refine IsUnit.mul (ql_s_isUnit ?_) (ql_sW_isUnit N _ fun i j hij => h _ _ (by simpa using hij))
    rw [Finset.disjoint_left]
    intro a ha hU
    obtain ⟨j, hj⟩ := (ql_mem_U N _ a).1 hU
    exact Finset.disjoint_left.1 (h 0 j.succ (Fin.succ_ne_zero j).symm) ha hj

/- English proof (translation)
Rewrite using `[← (Fin.consEquiv (fun _ => Finset (Fin n))).sum_comp, Fintype.sum_prod_type]`. Both sides reduce to the same expression.
-/
lemma ql_sum_cons {N : ℕ} (φ : (Fin (N + 1) → Finset (Fin n)) → R) :
    ∑ D, φ D = ∑ a, ∑ D', φ (Fin.cons a D') := by
  rw [← (Fin.consEquiv (fun _ => Finset (Fin n))).sum_comp, Fintype.sum_prod_type]; rfl

/- English proof (translation)
Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`.
-/
lemma ql_prod_sum {N : ℕ} (G : Fin N → Finset (Fin n) → R) :
    ∏ j, ∑ a, G j a = ∑ x : Fin N → Finset (Fin n), ∏ j, G j (x j) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

variable (g : Matrix (Fin n) (Fin n) R)

/- English proof (translation)
The claim follows from `| 0, D, L => by simp [wedgeCoeff, ql_U, ql_sW, ql_mn_empty, eq_comm] | N + 1, D, L => by rw [ql_sum_cons] calc ∑ a, ∑ D' : Fin N → Finset (Fin n), (∏ j, qs_mn g ((Fin.cons a D' : Fin (N + 1) → _) j) (D j)) * wedgeCoeff R (Fin.cons a D' : Fin (N + 1) → _) L = ∑ a, ∑ M, qs_mn g a ( …`.
-/
theorem ql_W_equiv : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)) (L : Finset (Fin n)),
    ∑ D' : Fin N → Finset (Fin n), (∏ j, qs_mn g (D' j) (D j)) * wedgeCoeff R D' L = ∑ L', qs_mn g L L' * wedgeCoeff R D L'
  | 0, D, L => by
    simp [wedgeCoeff, ql_U, ql_sW, ql_mn_empty, eq_comm]
  | N + 1, D, L => by
    rw [ql_sum_cons]
    calc ∑ a, ∑ D' : Fin N → Finset (Fin n), (∏ j, qs_mn g ((Fin.cons a D' : Fin (N + 1) → _) j) (D j)) *
            wedgeCoeff R (Fin.cons a D' : Fin (N + 1) → _) L
        = ∑ a, ∑ M, qs_mn g a (D 0) * ql_w R a M L *
            ∑ D' : Fin N → Finset (Fin n), (∏ j, qs_mn g (D' j) (Fin.tail D j)) * wedgeCoeff R D' M := by
          refine sum_congr rfl fun a _ => ?_
          simp only [ql_W_succ (Fin.cons a _), Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail_cons,
            mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun M _ => sum_congr rfl fun D' _ => by simp only [Fin.tail]; ring
      _ = ∑ a, ∑ M, qs_mn g a (D 0) * ql_w R a M L * ∑ M', qs_mn g M M' * wedgeCoeff R (Fin.tail D) M' := by
          simp only [ql_W_equiv N]
      _ = ∑ M', wedgeCoeff R (Fin.tail D) M' * ∑ a, ∑ M, qs_mn g a (D 0) * qs_mn g M M' * ql_w R a M L := by
          simp only [mul_sum]
          symm
          rw [sum_comm]; refine sum_congr rfl fun a _ => ?_
          rw [sum_comm]; exact sum_congr rfl fun M _ => sum_congr rfl fun M' _ => by ring
      _ = ∑ L', qs_mn g L L' * wedgeCoeff R D L' := by
          simp only [ql_lapM, ql_W_succ D, mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun M _ => sum_congr rfl fun D' _ => by ring

def ql_P (R : Type*) [CommRing R] {N : ℕ} (k : Fin N → Finset (Fin n)) (L : Finset (Fin n))
    (i : Fin N → Finset (Fin n)) : R :=
  ∑ D : Fin N → Finset (Fin n), (∏ j, ql_w R (k j) (D j) (i j)) * wedgeCoeff R D L

/- English proof (translation)
Simplify using `only [ql_P, Int.cast_sum, Int.cast_mul, Int.cast_prod, ql_w_cast, ql_W_cast]`.
-/
lemma ql_P_cast {N : ℕ} (k : Fin N → Finset (Fin n)) (L : Finset (Fin n)) (i : Fin N → Finset (Fin n)) :
    ((ql_P ℤ k L i : ℤ) : R) = ql_P R k L i := by
  simp only [ql_P, Int.cast_sum, Int.cast_mul, Int.cast_prod, ql_w_cast, ql_W_cast]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `sum_congr rfl fun k' _ => ?_` and prove the remaining obligations. Simplify using `only [ql_P, mul_sum]`. Rewrite using `[sum_comm]`. Conclude with `sum_congr rfl fun D _ => sum_congr rfl fun L' _ => by ring`.

Use `_ = ∑ D' : Fin N → Finset (Fin n), wedgeCoeff R D' L * ∑ k' : Fin N → Finset (Fin n), ∑ D : Fin N → Finset (Fin n), ∏ j, qs_mn g (k j) (k' j) * qs_mn g (D' j) (D j) * ql_w R (k' j) (D j) (i j) := by`. Simplify using `only [← ql_W_equiv, mul_sum, prod_mul_distrib]`. Use `symm`. Rewrite using `[sum_comm]`. Use `sum_congr rfl fun k' _ => ?_` and prove the remaining obligations.

Rewrite using `[sum_comm]; exact sum_congr rfl fun D _ => sum_congr rfl fun D' _ => by ring`. Use `_ = ∑ D' : Fin N → Finset (Fin n), wedgeCoeff R D' L * ∏ j, ∑ a, ∑ d, qs_mn g (k j) a * qs_mn g (D' j) d * ql_w R a d (i j) := by`. Use `sum_congr rfl fun D' _ => ?_` and prove the remaining obligations. Rewrite using `[ql_prod_sum (fun j a => ∑ d, qs_mn g (k j) a * qs_mn g (D' j) d * ql_w R a d (i j))]`. Use `congrArg _ (sum_congr rfl fun k' _ => ?_)` and prove the remaining obligations.

Conclude with `(ql_prod_sum (fun j d => qs_mn g (k j) (k' j) * qs_mn g (D' j) d * ql_w R (k' j) d (i j))).symm`. Use `_ = ∑ D' : Fin N → Finset (Fin n), wedgeCoeff R D' L * ∑ i' : Fin N → Finset (Fin n), ∏ j, ql_w R (k j) (D' j) (i' j) * qs_mn g (i' j) (i j) := by`. Simplify using `only [ql_lapT, ql_prod_sum]`. Use `_ = ∑ i' : Fin N → Finset (Fin n), ql_P R k L i' * ∏ j, qs_mn g (i' j) (i j) := by`. Simplify using `only [ql_P, mul_sum, sum_mul, prod_mul_distrib]`.

Rewrite using `[sum_comm]`. Conclude with `sum_congr rfl fun D _ => sum_congr rfl fun L' _ => by ring`.
-/
theorem ql_P_equiv {N : ℕ} (k : Fin N → Finset (Fin n)) (L : Finset (Fin n)) (i : Fin N → Finset (Fin n)) :
    ∑ k' : Fin N → Finset (Fin n), ∑ L', (∏ j, qs_mn g (k j) (k' j)) * qs_mn g L L' * ql_P R k' L' i =
      ∑ i' : Fin N → Finset (Fin n), ql_P R k L i' * ∏ j, qs_mn g (i' j) (i j) := by
  calc ∑ k' : Fin N → Finset (Fin n), ∑ L', (∏ j, qs_mn g (k j) (k' j)) * qs_mn g L L' * ql_P R k' L' i
      = ∑ k' : Fin N → Finset (Fin n), ∑ D : Fin N → Finset (Fin n),
          (∏ j, qs_mn g (k j) (k' j)) * (∏ j, ql_w R (k' j) (D j) (i j)) * ∑ L', qs_mn g L L' * wedgeCoeff R D L' := by
        refine sum_congr rfl fun k' _ => ?_
        simp only [ql_P, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun D _ => sum_congr rfl fun L' _ => by ring
    _ = ∑ D' : Fin N → Finset (Fin n), wedgeCoeff R D' L * ∑ k' : Fin N → Finset (Fin n), ∑ D : Fin N → Finset (Fin n),
          ∏ j, qs_mn g (k j) (k' j) * qs_mn g (D' j) (D j) * ql_w R (k' j) (D j) (i j) := by
        simp only [← ql_W_equiv, mul_sum, prod_mul_distrib]
        symm
        rw [sum_comm]; refine sum_congr rfl fun k' _ => ?_
        rw [sum_comm]; exact sum_congr rfl fun D _ => sum_congr rfl fun D' _ => by ring
    _ = ∑ D' : Fin N → Finset (Fin n), wedgeCoeff R D' L *
          ∏ j, ∑ a, ∑ d, qs_mn g (k j) a * qs_mn g (D' j) d * ql_w R a d (i j) := by
        refine sum_congr rfl fun D' _ => ?_
        rw [ql_prod_sum (fun j a => ∑ d, qs_mn g (k j) a * qs_mn g (D' j) d * ql_w R a d (i j))]
        refine congrArg _ (sum_congr rfl fun k' _ => ?_)
        exact (ql_prod_sum (fun j d => qs_mn g (k j) (k' j) * qs_mn g (D' j) d * ql_w R (k' j) d (i j))).symm
    _ = ∑ D' : Fin N → Finset (Fin n), wedgeCoeff R D' L *
          ∑ i' : Fin N → Finset (Fin n), ∏ j, ql_w R (k j) (D' j) (i' j) * qs_mn g (i' j) (i j) := by
        simp only [ql_lapT, ql_prod_sum]
    _ = ∑ i' : Fin N → Finset (Fin n), ql_P R k L i' * ∏ j, qs_mn g (i' j) (i j) := by
        simp only [ql_P, mul_sum, sum_mul, prod_mul_distrib]
        rw [sum_comm]
        exact sum_congr rfl fun D _ => sum_congr rfl fun L' _ => by ring

/- English proof (translation)
Establish `h0 : ∀ D : Fin N → Finset (Fin n), D ≠ (fun j => i j \ k j) → (∏ j, ql_w R (k j) (D j) (i j)) * wedgeCoeff R D (ql_U N fun j => i j \ k j) = 0`. Introduce `D hD`. Take `⟨j, hj⟩` from `Function.ne_iff.1 hD`. Rewrite using `[prod_eq_zero (mem_univ j), zero_mul]`. Rewrite using `[ql_w]`.

Use `split_ifs with h`. Rewrite using `[wedgeSign, if_neg]`. Introduce `hdis`. Apply `hj` to reduce the goal to its premises. Rewrite using `[← h, union_sdiff_cancel_left hdis]`.

Both sides reduce to the same expression. Rewrite using `[ql_P, sum_eq_single _ (fun D _ hD => h0 D hD) (fun h => absurd (mem_univ _) h)]`. Use `IsUnit.mul ?_ ?_` and prove the remaining obligations. Use `Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun j _ => ?_` and prove the remaining obligations. Rewrite using `[ql_w, if_pos (union_sdiff_of_subset (hk j))]`.

Conclude with `ql_s_isUnit disjoint_sdiff`. Rewrite using `[wedgeCoeff, if_pos rfl]`. Conclude with `ql_sW_isUnit N _ hd`.
-/
lemma ql_P_unit {N : ℕ} (k i : Fin N → Finset (Fin n)) (hk : ∀ j, k j ⊆ i j)
    (hd : ∀ j j', j ≠ j' → Disjoint (i j \ k j) (i j' \ k j')) :
    IsUnit (ql_P R k (ql_U N fun j => i j \ k j) i) := by
  have h0 : ∀ D : Fin N → Finset (Fin n), D ≠ (fun j => i j \ k j) →
      (∏ j, ql_w R (k j) (D j) (i j)) * wedgeCoeff R D (ql_U N fun j => i j \ k j) = 0 := by
    intro D hD
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hD
    rw [prod_eq_zero (mem_univ j), zero_mul]
    rw [ql_w]
    split_ifs with h
    · rw [wedgeSign, if_neg]
      intro hdis
      apply hj
      rw [← h, union_sdiff_cancel_left hdis]
    · rfl
  rw [ql_P, sum_eq_single _ (fun D _ hD => h0 D hD) (fun h => absurd (mem_univ _) h)]
  refine IsUnit.mul ?_ ?_
  · refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun j _ => ?_
    rw [ql_w, if_pos (union_sdiff_of_subset (hk j))]
    exact ql_s_isUnit disjoint_sdiff
  · rw [wedgeCoeff, if_pos rfl]
    exact ql_sW_isUnit N _ hd

end Formalism.InvariantFactorPaths.ColumnFamilies
