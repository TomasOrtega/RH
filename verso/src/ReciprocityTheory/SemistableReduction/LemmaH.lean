import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix InnerProductSpace

/- English proof (translation)
Set `std` to `EuclideanSpace.basisFun (Fin n) ℂ`. Set `f : Fin n → EuclideanSpace ℂ (Fin n)` to `fun j => (EuclideanSpace.equiv (Fin n) ℂ).symm (fun i => x i j)`. Establish `hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n)` using `by simp`. Set `e` to `gramSchmidtOrthonormalBasis hdim f`. Establish `hstd : std.toBasis.toMatrix f = x`.

Use extensionality with `i j`. Simplify using `[Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, f, std]`. Establish `hnorm : ∀ j, ‖f j‖ ^ 2 = colNormSq x j`. Introduce `j`. Rewrite using `[EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]`.

Simplify using `[colNormSq, f]`. Use `⟨std.toBasis.toMatrix e.toBasis, e.toBasis.toMatrix f, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary std e` using `[OrthonormalBasis.coe_toBasis]`. Conclude with `gramSchmidtOrthonormalBasis_inv_blockTriangular hdim f`. Rewrite using `[Module.Basis.toMatrix_mul_toMatrix, hstd]`.

Introduce `j`. Rewrite using `[← hnorm j, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]`. Establish `h1 : ‖inner ℂ (e j) (f j)‖ ≤ ‖f j‖`. Combine the equalities or inequalities in the displayed calculation. Conclude with `pow_le_pow_left₀ (norm_nonneg _) h1 2`.
-/
theorem exists_unitary_mul_upper {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) :
    ∃ k b : Matrix (Fin n) (Fin n) ℂ, k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ b.BlockTriangular id ∧
      x = k * b ∧ ∀ j, ‖b j j‖ ^ 2 ≤ colNormSq x j := by
  classical
  let std := EuclideanSpace.basisFun (Fin n) ℂ
  let f : Fin n → EuclideanSpace ℂ (Fin n) := fun j => (EuclideanSpace.equiv (Fin n) ℂ).symm (fun i => x i j)
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by simp
  let e := gramSchmidtOrthonormalBasis hdim f
  have hstd : std.toBasis.toMatrix f = x := by
    ext i j
    simp [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, f, std]
  have hnorm : ∀ j, ‖f j‖ ^ 2 = colNormSq x j := by
    intro j
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [colNormSq, f]
  refine ⟨std.toBasis.toMatrix e.toBasis, e.toBasis.toMatrix f, ?_, ?_, ?_, ?_⟩
  · simpa [OrthonormalBasis.coe_toBasis] using OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary std e
  · exact gramSchmidtOrthonormalBasis_inv_blockTriangular hdim f
  · rw [Module.Basis.toMatrix_mul_toMatrix, hstd]
  · intro j
    rw [← hnorm j, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    have h1 : ‖inner ℂ (e j) (f j)‖ ≤ ‖f j‖ := by
      calc ‖inner ℂ (e j) (f j)‖ ≤ ‖e j‖ * ‖f j‖ := norm_inner_le_norm _ _
        _ = ‖f j‖ := by rw [e.orthonormal.1 j, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert s S hs ih`. Establish `hy : ∀ t, ((fun t => if t ∈ S then k t * b t else k t) t).det ≠ 0`. Introduce `t`.

Distinguish the cases in `ht : t ∈ S`. Simplify using `only [ht, if_true, Matrix.det_mul]`. Conclude with `mul_ne_zero (hk t) (hb t)`. Simplify using `only [ht, if_false]`. Conclude with `hk t`.

Establish `heq : (fun t => if t ∈ insert s S then k t * b t else k t) = Function.update (fun t => if t ∈ S then k t * b t else k t) s ((fun t => if t ∈ S then k t * b t else k t) s * b s)`. Use function extensionality and compare the values at `t`. Distinguish the cases in `hts : t = s`. Substitute `hts` using the available equality. Simplify using `[hs]`.

Simplify using `[hts]`. Rewrite using `[heq, hP _ s (b s) hy (hb s) (hbt s), ih, Finset.prod_insert hs, mul_assoc]`.
-/
private theorem P_ite_mul_eq_prod_triChar_mul {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
    (a : ∀ s, Fin (p s) → ℕ) (P : (∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) → ℂ)
    (hP : ∀ (x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (s : ι) (b : Matrix (Fin (p s)) (Fin (p s)) ℂ),
      (∀ t, (x t).det ≠ 0) → b.det ≠ 0 → b.BlockTriangular id →
      P (Function.update x s (x s * b)) = triChar (a s) b * P x)
    (k b : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (hk : ∀ s, (k s).det ≠ 0)
    (hb : ∀ s, (b s).det ≠ 0) (hbt : ∀ s, (b s).BlockTriangular id) (S : Finset ι) :
    P (fun t => if t ∈ S then k t * b t else k t) =
      (∏ s ∈ S, triChar (a s) (b s)) * P k := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert s S hs ih =>
    have hy : ∀ t, ((fun t => if t ∈ S then k t * b t else k t) t).det ≠ 0 := by
      intro t
      by_cases ht : t ∈ S
      · simp only [ht, if_true, Matrix.det_mul]
        exact mul_ne_zero (hk t) (hb t)
      · simp only [ht, if_false]
        exact hk t
    have heq : (fun t => if t ∈ insert s S then k t * b t else k t) =
        Function.update (fun t => if t ∈ S then k t * b t else k t) s
          ((fun t => if t ∈ S then k t * b t else k t) s * b s) := by
      funext t
      by_cases hts : t = s
      · subst hts
        simp [hs]
      · simp [hts]
    rw [heq, hP _ s (b s) hy (hb s) (hbt s), ih, Finset.prod_insert hs, mul_assoc]

/- English proof (translation)
Introduce `ι _ _ p a P C R hP hC hR x hx hcol`. Use `choose k b hk hbt hkb hdiag using fun s => exists_unitary_mul_upper (x s)`. Establish `hkdet : ∀ s, (k s).det ≠ 0`. Introduce `s`. Conclude with `(Matrix.UnitaryGroup.det_isUnit ⟨k s, hk s⟩).ne_zero`.

Establish `hbdet : ∀ s, (b s).det ≠ 0`. Introduce `s h`. Apply `hx s` to reduce the goal to its premises. Rewrite using `[hkb s, Matrix.det_mul, h, mul_zero]`. Establish `hxk : x = fun t => if t ∈ (Finset.univ : Finset ι) then k t * b t else k t`.

Use function extensionality and compare the values at `t`. Simplify using `[← hkb t]`. Establish `hmain` using `P_ite_mul_eq_prod_triChar_mul p a P hP k b hkdet hbdet hbt Finset.univ`. Rewrite `hmain` using `[← hxk]`. Establish `hC0 : 0 ≤ C`.

Establish `h1` using `hC (fun s => 1) (fun s => one_mem _)`. Conclude with `(norm_nonneg _).trans h1`. Establish `hbR : ∀ s i, ‖b s i i‖ ≤ R`. Introduce `s i`. Establish `h1` using `(hdiag s i).trans (hcol s i)`.

Use polynomial arithmetic with `[norm_nonneg (b s i i)]`. Establish `hprod : ‖∏ s, triChar (a s) (b s)‖ ≤ R ^ (∑ s, ∑ i, a s i)`. Rewrite using `[norm_prod, ← Finset.prod_pow_eq_pow_sum]`. Apply `Finset.prod_le_prod (fun _ _ => norm_nonneg _)` to reduce the goal to its premises. Introduce `s _`.

Rewrite using `[triChar, norm_prod, ← Finset.prod_pow_eq_pow_sum]`. Apply `Finset.prod_le_prod (fun _ _ => norm_nonneg _)` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[norm_pow]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (hbR s i) _`.

Rewrite using `[hmain, norm_mul, mul_comm C]`. Conclude with `mul_le_mul hprod (hC k hk) (norm_nonneg _) (pow_nonneg hR _)`.
-/
theorem lemmaH_holds : LemmaHStatement := by
  intro ι _ _ p a P C R hP hC hR x hx hcol
  classical
  choose k b hk hbt hkb hdiag using fun s => exists_unitary_mul_upper (x s)
  have hkdet : ∀ s, (k s).det ≠ 0 := by
    intro s
    exact (Matrix.UnitaryGroup.det_isUnit ⟨k s, hk s⟩).ne_zero
  have hbdet : ∀ s, (b s).det ≠ 0 := by
    intro s h
    apply hx s
    rw [hkb s, Matrix.det_mul, h, mul_zero]
  have hxk : x = fun t => if t ∈ (Finset.univ : Finset ι) then k t * b t else k t := by
    funext t
    simp [← hkb t]
  have hmain := P_ite_mul_eq_prod_triChar_mul p a P hP k b hkdet hbdet hbt Finset.univ
  rw [← hxk] at hmain
  have hC0 : 0 ≤ C := by
    have h1 := hC (fun s => 1) (fun s => one_mem _)
    exact (norm_nonneg _).trans h1
  have hbR : ∀ s i, ‖b s i i‖ ≤ R := by
    intro s i
    have h1 := (hdiag s i).trans (hcol s i)
    nlinarith [norm_nonneg (b s i i)]
  have hprod : ‖∏ s, triChar (a s) (b s)‖ ≤ R ^ (∑ s, ∑ i, a s i) := by
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro s _
    rw [triChar, norm_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro i _
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbR s i) _
  rw [hmain, norm_mul, mul_comm C]
  exact mul_le_mul hprod (hC k hk) (norm_nonneg _) (pow_nonneg hR _)

end ReciprocityTheory.MultiplicativeHeights
