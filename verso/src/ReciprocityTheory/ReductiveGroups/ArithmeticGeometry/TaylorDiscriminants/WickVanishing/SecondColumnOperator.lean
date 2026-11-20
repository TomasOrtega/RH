import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SecondColumnDegree

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator

open SecondColumnDegree

variable {k : Type} [CommRing k] [Algebra ℚ k]

section General

variable {σ : Type} [Fintype σ]

def trunc (N : ℕ) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  ∑ j ∈ range (N + 1), homogeneousComponent j

/- English proof (translation)
Rewrite using `[trunc, LinearMap.sum_apply]`.
-/
theorem trunc_apply (N : ℕ) (x : MvPolynomial σ k) :
    trunc N x = ∑ j ∈ range (N + 1), homogeneousComponent j x := by
  rw [trunc, LinearMap.sum_apply]

/- English proof (translation)
Rewrite using `[trunc_apply]`. Use `(totalDegree_finset_sum _ _).trans (Finset.sup_le fun j hj => ?_)` and prove the remaining obligations. Distinguish the cases in `h0 : homogeneousComponent j x = 0`. Rewrite using `[h0, totalDegree_zero]`. Conclude with `Nat.zero_le _`.

Rewrite using `[(homogeneousComponent_isHomogeneous j x).totalDegree h0]`. Conclude with `Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)`.
-/
theorem trunc_deg (N : ℕ) (x : MvPolynomial σ k) : (trunc N x).totalDegree ≤ N := by
  rw [trunc_apply]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j hj => ?_)
  by_cases h0 : homogeneousComponent j x = 0
  · rw [h0, totalDegree_zero]
    exact Nat.zero_le _
  · rw [(homogeneousComponent_isHomogeneous j x).totalDegree h0]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)

/- English proof (translation)
Rewrite using `[trunc_apply]`. Use `conv_rhs => rw [← sum_homogeneousComponent x]`. Use `symm`. Use `Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hx)) ?_` and prove the remaining obligations. Introduce `j hj hj'`.

Apply `homogeneousComponent_eq_zero` to reduce the goal to its premises. Simplify using `only [Finset.mem_range] at hj hj'`. Use linear arithmetic over natural numbers and integers.
-/
theorem trunc_id (N : ℕ) (x : MvPolynomial σ k) (hx : x.totalDegree ≤ N) : trunc N x = x := by
  rw [trunc_apply]
  conv_rhs => rw [← sum_homogeneousComponent x]
  symm
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hx)) ?_
  intro j hj hj'
  apply homogeneousComponent_eq_zero
  simp only [Finset.mem_range] at hj hj'
  omega

/- English proof (translation)
Unfold `secondOrder`. Simplify using `only [map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem so_coef_add (c1 c2 : σ → σ → k) (P : MvPolynomial σ k) :
    secondOrder k (fun p q => c1 p q + c2 p q) P = secondOrder k c1 P + secondOrder k c2 P := by
  unfold secondOrder
  simp only [map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
The claim follows from `| 0, _ => rfl | i + 1, y => by rw [Function.iterate_succ_apply, so_smul, so_iter_smul c r i, ← Function.iterate_succ_apply]`.
-/
theorem so_iter_smul (c : σ → σ → k) (r : k) :
    ∀ (i : ℕ) (y : MvPolynomial σ k), (secondOrder k c)^[i] (r • y) = r • (secondOrder k c)^[i] y
  | 0, _ => rfl
  | i + 1, y => by
    rw [Function.iterate_succ_apply, so_smul, so_iter_smul c r i, ← Function.iterate_succ_apply]

def soL (c : σ → σ → k) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k where
  toFun := secondOrder k c
  map_add' := so_add c
  map_smul' := so_smul c

def opA (c : σ → σ → k) (t : k) (N : ℕ) : Module.End ℚ (MvPolynomial σ k) :=
  ((t • (soL c ∘ₗ trunc N)) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k).restrictScalars ℚ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem opA_apply (c : σ → σ → k) (t : k) (N : ℕ) (x : MvPolynomial σ k) :
    opA c t N x = t • secondOrder k c (trunc N x) := rfl

/- English proof (translation)
Use `conv_lhs => rw [MvPolynomial.as_sum y]`. Rewrite using `[map_sum]`. Use `(totalDegree_finset_sum _ _).trans (Finset.sup_le fun s hs => ?_)` and prove the remaining obligations. Rewrite using `[pderiv_monomial]`. Use `le_trans ?_ (le_totalDegree hs)` and prove the remaining obligations.

Use `Finset.sup_le fun u hu => ?_` and prove the remaining obligations. Establish `hu'` using `MvPolynomial.support_monomial_subset hu`. Rewrite `hu'` using `[Finset.mem_singleton]`. Substitute `hu'` using the available equality. Establish `hts : s - Finsupp.single i 1 ≤ s` using `tsub_le_self`.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem totalDegree_pderiv_le' (i : σ) (y : MvPolynomial σ k) :
    (pderiv i y).totalDegree ≤ y.totalDegree := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum y]
  rw [map_sum]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [pderiv_monomial]
  refine le_trans ?_ (le_totalDegree hs)
  refine Finset.sup_le fun u hu => ?_
  have hu' := MvPolynomial.support_monomial_subset hu
  rw [Finset.mem_singleton] at hu'
  subst hu'
  have hts : s - Finsupp.single i 1 ≤ s := tsub_le_self
  calc (s - Finsupp.single i 1).sum (fun _ e => e)
      ≤ (s - Finsupp.single i 1).sum (fun _ e => e) +
          (s - (s - Finsupp.single i 1)).sum (fun _ e => e) := Nat.le_add_right _ _
    _ = ((s - Finsupp.single i 1) + (s - (s - Finsupp.single i 1))).sum (fun _ e => e) :=
        (Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)).symm
    _ = s.sum (fun _ e => e) := by rw [add_tsub_cancel_of_le hts]

/- English proof (translation)
Unfold `secondOrder`. Use `(totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)` and prove the remaining obligations. Use `(totalDegree_finset_sum _ _).trans (Finset.sup_le fun l' _ => ?_)` and prove the remaining obligations. Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Rewrite using `[totalDegree_C, zero_add]`.

Conclude with `((totalDegree_pderiv_le' _ _).trans (totalDegree_pderiv_le' _ _)).trans (trunc_deg N x)`.
-/
theorem deg_so_trunc (c : σ → σ → k) (N : ℕ) (x : MvPolynomial σ k) :
    (secondOrder k c (trunc N x)).totalDegree ≤ N := by
  unfold secondOrder
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun l' _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact ((totalDegree_pderiv_le' _ _).trans (totalDegree_pderiv_le' _ _)).trans (trunc_deg N x)

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro x hx`. Conclude with `hx`. Consider the case `succ i ih`.

Introduce `x hx`. Rewrite using `[Function.iterate_succ_apply']`. Establish `h` using `deg_so_trunc c M ((secondOrder k c)^[i] x)`. Rewrite `h` using `[trunc_id M _ (ih x hx)]`. Then use the resulting hypothesis.
-/
private theorem totalDegree_iterate_secondOrder_le (c : σ → σ → k) (M : ℕ) :
    ∀ (i : ℕ) (x : MvPolynomial σ k), x.totalDegree ≤ M →
      ((secondOrder k c)^[i] x).totalDegree ≤ M := by
  intro i
  induction i with
  | zero => intro x hx; exact hx
  | succ i ih =>
    intro x hx
    rw [Function.iterate_succ_apply']
    have h := deg_so_trunc c M ((secondOrder k c)^[i] x)
    rwa [trunc_id M _ (ih x hx)] at h

/- English proof (translation)
The claim follows from `| 0, x, _ => by simp | i + 1, x, hx => by rw [pow_succ', Module.End.mul_apply, opA_pow_apply c t N i x hx, opA_apply, trunc_id] · rw [so_smul, smul_smul, ← pow_succ', ← Function.iterate_succ_apply' (f := secondOrder k c)] · exact (totalDegree_smul_le _ _).trans ((so_iter_deg_le c …`.
-/
theorem opA_pow_apply (c : σ → σ → k) (t : k) (N : ℕ) :
    ∀ (i : ℕ) (x : MvPolynomial σ k), x.totalDegree ≤ N →
      ((opA c t N) ^ i) x = t ^ i • (secondOrder k c)^[i] x
  | 0, x, _ => by simp
  | i + 1, x, hx => by
    rw [pow_succ', Module.End.mul_apply, opA_pow_apply c t N i x hx, opA_apply, trunc_id]
    · rw [so_smul, smul_smul, ← pow_succ', ← Function.iterate_succ_apply' (f := secondOrder k c)]
    · exact (totalDegree_smul_le _ _).trans ((so_iter_deg_le c i x).trans hx)

/- English proof (translation)
Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Establish `hy : (opA c t N x).totalDegree ≤ N`. Rewrite using `[opA_apply]`. Conclude with `(totalDegree_smul_le _ _).trans (deg_so_trunc c N x)`. Rewrite using `[pow_succ, Module.End.mul_apply, opA_pow_apply c t N N _ hy, opA_apply, so_iter_smul, ← Function.iterate_succ_apply, so_iter_eq_zero c (N + 1) (trunc N x) (Nat.lt_succ_of_le (trunc_deg N x)), smul_zero, smul_zero, LinearMap.zero_apply]`.
-/
theorem opA_pow_eq_zero (c : σ → σ → k) (t : k) (N : ℕ) : (opA c t N) ^ (N + 1) = 0 := by
  refine LinearMap.ext fun x => ?_
  have hy : (opA c t N x).totalDegree ≤ N := by
    rw [opA_apply]
    exact (totalDegree_smul_le _ _).trans (deg_so_trunc c N x)
  rw [pow_succ, Module.End.mul_apply, opA_pow_apply c t N N _ hy, opA_apply, so_iter_smul,
    ← Function.iterate_succ_apply,
    so_iter_eq_zero c (N + 1) (trunc N x) (Nat.lt_succ_of_le (trunc_deg N x)),
    smul_zero, smul_zero, LinearMap.zero_apply]

/- English proof (translation)
Assemble the required witnesses or components as `⟨N + 1, opA_pow_eq_zero c t N⟩`.
-/
theorem opA_nilp (c : σ → σ → k) (t : k) (N : ℕ) : IsNilpotent (opA c t N) := ⟨N + 1, opA_pow_eq_zero c t N⟩

/- English proof (translation)
Use `show opA c1 t N * opA c2 t N = opA c2 t N * opA c1 t N`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Establish `d1 : (opA c1 t N x).totalDegree ≤ N`. Rewrite using `[opA_apply]`. Conclude with `(totalDegree_smul_le _ _).trans (deg_so_trunc c1 N x)`.

Establish `d2 : (opA c2 t N x).totalDegree ≤ N`. Rewrite using `[opA_apply]`. Conclude with `(totalDegree_smul_le _ _).trans (deg_so_trunc c2 N x)`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, opA_apply c1 t N (opA c2 t N x), trunc_id N _ d2, opA_apply c2 t N (opA c1 t N x), trunc_id N _ d1, opA_apply, opA_apply, so_smul, so_smul, so_comm]`.
-/
theorem opA_comm (c1 c2 : σ → σ → k) (t : k) (N : ℕ) : Commute (opA c1 t N) (opA c2 t N) := by
  show opA c1 t N * opA c2 t N = opA c2 t N * opA c1 t N
  refine LinearMap.ext fun x => ?_
  have d1 : (opA c1 t N x).totalDegree ≤ N := by
    rw [opA_apply]
    exact (totalDegree_smul_le _ _).trans (deg_so_trunc c1 N x)
  have d2 : (opA c2 t N x).totalDegree ≤ N := by
    rw [opA_apply]
    exact (totalDegree_smul_le _ _).trans (deg_so_trunc c2 N x)
  rw [Module.End.mul_apply, Module.End.mul_apply, opA_apply c1 t N (opA c2 t N x), trunc_id N _ d2,
    opA_apply c2 t N (opA c1 t N x), trunc_id N _ d1, opA_apply, opA_apply, so_smul, so_smul,
    so_comm]

/- English proof (translation)
Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, opA_apply, so_coef_add, smul_add]`.
-/
theorem opA_add (c1 c2 : σ → σ → k) (t : k) (N : ℕ) :
    opA (fun p q => c1 p q + c2 p q) t N = opA c1 t N + opA c2 t N := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, opA_apply, so_coef_add, smul_add]

/- English proof (translation)
Rewrite using `[IsNilpotent.exp_eq_sum (opA_pow_eq_zero c t N), LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, opA_pow_apply c t N i x hx, mul_smul, algebraMap_smul]`.
-/
theorem exp_opA_apply (c : σ → σ → k) (t : k) (N : ℕ) (x : MvPolynomial σ k) (hx : x.totalDegree ≤ N) :
    IsNilpotent.exp (opA c t N) x = ∑ i ∈ range (N + 1),
      (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * t ^ i) • (secondOrder k c)^[i] x := by
  rw [IsNilpotent.exp_eq_sum (opA_pow_eq_zero c t N), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, opA_pow_apply c t N i x hx, mul_smul, algebraMap_smul]

end General

section Columns

variable {ι : Type} [Fintype ι] {n : ℕ}

def prodQ (Q : Fin n → MvPolynomial ι k) : MvPolynomial (ι × Fin n) k := ∏ b, colE b (Q b)

def E1 (c : ι → ι → k) (t : k) (N : ℕ) (y : MvPolynomial ι k) : MvPolynomial ι k :=
  ∑ i ∈ range (N + 1), (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * t ^ i) • (secondOrder k c)^[i] y

/- English proof (translation)
Unfold `E1`. Use `(totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)` and prove the remaining obligations. Conclude with `(totalDegree_smul_le _ _).trans (totalDegree_iterate_secondOrder_le c _ i y le_rfl)`.
-/
theorem totalDegree_second_exp_le (c : ι → ι → k) (t : k) (N : ℕ) (y : MvPolynomial ι k) :
    (E1 c t N y).totalDegree ≤ y.totalDegree := by
  unfold E1
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
  exact (totalDegree_smul_le _ _).trans (totalDegree_iterate_secondOrder_le c _ i y le_rfl)

/- English proof (translation)
Unfold `prodQ`. Use `(totalDegree_finset_prod _ _).trans (Finset.sum_le_sum fun b _ => ?_)` and prove the remaining obligations. Unfold `colE`. Conclude with `totalDegree_rename_le _ _`.
-/
theorem prodQ_deg (Q : Fin n → MvPolynomial ι k) : (prodQ Q).totalDegree ≤ ∑ b, (Q b).totalDegree := by
  unfold prodQ
  refine (totalDegree_finset_prod _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  unfold colE
  exact totalDegree_rename_le _ _

/- English proof (translation)
Unfold `prodQ`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ b0)]`. Use `congr 1`. Simplify using `[Function.update_apply]`. Conclude with `Finset.prod_congr rfl fun b hb => by simp [Function.update_apply, Finset.ne_of_mem_erase hb]`.
-/
theorem prodQ_update (Q : Fin n → MvPolynomial ι k) (b0 : Fin n) (y : MvPolynomial ι k) :
    prodQ (Function.update Q b0 y) = colE b0 y * ∏ b ∈ univ.erase b0, colE b (Q b) := by
  unfold prodQ
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b0)]
  congr 1
  · simp [Function.update_apply]
  · exact Finset.prod_congr rfl fun b hb => by simp [Function.update_apply, Finset.ne_of_mem_erase hb]

/- English proof (translation)
Unfold `prodQ`. Conclude with `(Finset.mul_prod_erase _ _ (Finset.mem_univ b0)).symm`.
-/
theorem prodQ_eq (Q : Fin n → MvPolynomial ι k) (b0 : Fin n) :
    prodQ Q = colE b0 (Q b0) * ∏ b ∈ univ.erase b0, colE b (Q b) := by
  unfold prodQ
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ b0)).symm

/- English proof (translation)
Rewrite using `[exp_opA_apply _ t N _ hdeg, prodQ_update, prodQ_eq Q b0]`. Establish `hR : ∀ l : ι, pderiv (l, b0) (∏ b ∈ univ.erase b0, colE b (Q b)) = 0` using `fun l => pderiv_prod_colE b0 _ (Finset.notMem_erase b0 _) Q l`. Unfold `E1`. Rewrite using `[map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[so_colB_iter c b0 _ hR i, map_smul, smul_mul_assoc]`.
-/
theorem exp_col (c : ι → ι → k) (t : k) (N : ℕ) (Q : Fin n → MvPolynomial ι k) (b0 : Fin n)
    (hdeg : (prodQ Q).totalDegree ≤ N) :
    IsNilpotent.exp (opA (cB c b0) t N) (prodQ Q) = prodQ (Function.update Q b0 (E1 c t N (Q b0))) := by
  rw [exp_opA_apply _ t N _ hdeg, prodQ_update, prodQ_eq Q b0]
  have hR : ∀ l : ι, pderiv (l, b0) (∏ b ∈ univ.erase b0, colE b (Q b)) = 0 :=
    fun l => pderiv_prod_colE b0 _ (Finset.notMem_erase b0 _) Q l
  unfold E1
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [so_colB_iter c b0 _ hR i, map_smul, smul_mul_assoc]

def cS (c : ι → ι → k) (S : Finset (Fin n)) : ι × Fin n → ι × Fin n → k :=
  fun p q => ∑ b ∈ S, cB c b p q

/- English proof (translation)
Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `Q _`. Establish `h0 : opA (cS c (∅ : Finset (Fin n))) t N = 0`.

Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[opA_apply, so_def]`. Simplify using `[cS]`. Rewrite using `[h0, IsNilpotent.exp_zero]`. Simplify using the standard rewrite rules.

Consider the case `insert a S ha ih`. Introduce `Q hQ`. Establish `hcs : cS c (insert a S) = fun p q => cB c a p q + cS c S p q`. Use function extensionality and compare the values at `p q`. Simplify using `only [cS, Finset.sum_insert ha]`.

Establish `hdeg : (prodQ fun b => if b ∈ S then E1 c t N (Q b) else Q b).totalDegree ≤ N`. Use `(prodQ_deg _).trans (le_trans (Finset.sum_le_sum fun b _ => ?_) hD)` and prove the remaining obligations. Use `split_ifs`. Conclude with `(totalDegree_second_exp_le c t N (Q b)).trans (hQ b)`. Conclude with `hQ b`.

Rewrite using `[hcs, opA_add, IsNilpotent.exp_add_of_commute (opA_comm _ _ t N) (opA_nilp _ t N) (opA_nilp _ t N), Module.End.mul_apply, ih Q hQ, exp_col c t N _ a hdeg]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality.

Simplify using `[ha]`. Simplify using `[hb, Finset.mem_insert]`.
-/
theorem exp_cols (c : ι → ι → k) (t : k) (N : ℕ) (D : Fin n → ℕ) (hD : ∑ b, D b ≤ N) :
    ∀ (S : Finset (Fin n)) (Q : Fin n → MvPolynomial ι k), (∀ b, (Q b).totalDegree ≤ D b) →
      IsNilpotent.exp (opA (cS c S) t N) (prodQ Q) =
        prodQ (fun b => if b ∈ S then E1 c t N (Q b) else Q b) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro Q _
    have h0 : opA (cS c (∅ : Finset (Fin n))) t N = 0 := by
      refine LinearMap.ext fun x => ?_
      rw [opA_apply, so_def]
      simp [cS]
    rw [h0, IsNilpotent.exp_zero]
    simp
  | insert a S ha ih =>
    intro Q hQ
    have hcs : cS c (insert a S) = fun p q => cB c a p q + cS c S p q := by
      funext p q
      simp only [cS, Finset.sum_insert ha]
    have hdeg : (prodQ fun b => if b ∈ S then E1 c t N (Q b) else Q b).totalDegree ≤ N := by
      refine (prodQ_deg _).trans (le_trans (Finset.sum_le_sum fun b _ => ?_) hD)
      split_ifs
      · exact (totalDegree_second_exp_le c t N (Q b)).trans (hQ b)
      · exact hQ b
    rw [hcs, opA_add, IsNilpotent.exp_add_of_commute (opA_comm _ _ t N) (opA_nilp _ t N)
      (opA_nilp _ t N), Module.End.mul_apply, ih Q hQ, exp_col c t N _ a hdeg]
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb
      simp [ha]
    · simp [hb, Finset.mem_insert]

/- English proof (translation)
Unfold `cS cB`. Use function extensionality and compare the values at `p q`. Distinguish the cases in `h : p.2 = q.2`. Rewrite using `[if_pos h]`. Simplify using `only [← h, and_self, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Rewrite using `[if_neg h]`. Use `Finset.sum_eq_zero fun b _ => if_neg ?_` and prove the remaining obligations. Introduce and unpack `⟨h1, h2⟩`. Conclude with `h (h1.trans h2.symm)`.
-/
theorem cS_univ (c : ι → ι → k) :
    cS c (univ : Finset (Fin n)) = fun p q => if p.2 = q.2 then c p.1 q.1 else 0 := by
  unfold cS cB
  funext p q
  by_cases h : p.2 = q.2
  · rw [if_pos h]
    simp only [← h, and_self, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b _ => if_neg ?_
    rintro ⟨h1, h2⟩
    exact h (h1.trans h2.symm)

end Columns

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
