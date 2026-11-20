import Mathlib

open Matrix

/- English proof (translation)
Establish `hk : ∀ k : ℕ, ∑ i, al i ^ k • u i = 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hs`. Consider the case `succ k ih`.

Establish `h` using `congrArg A.mulVec ih`. Rewrite `h` using `[Matrix.mulVec_zero, Matrix.mulVec_sum]`. Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, hu, smul_smul, pow_succ]`.

Introduce `i`. Use function extensionality and compare the values at `j`. Establish `h : (fun i => u i j) = 0`. Apply `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hal` to reduce the goal to its premises. Introduce `k`.

Use `congrFun (hk k) j` as an intermediate fact. Simplify `this` using `[Finset.sum_apply, mul_comm]`. Conclude with `congrFun h i`.
-/
private theorem eig_sum_zero {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (al : Fin n → O) (hal : Function.Injective al)
    (u : Fin n → Fin n → O) (hu : ∀ i, A.mulVec (u i) = al i • u i) (hs : ∑ i, u i = 0) :
    ∀ i, u i = 0 := by
  have hk : ∀ k : ℕ, ∑ i, al i ^ k • u i = 0 := by
    intro k
    induction k with
    | zero => simpa using hs
    | succ k ih =>
      have h := congrArg A.mulVec ih
      rw [Matrix.mulVec_zero, Matrix.mulVec_sum] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_smul, hu, smul_smul, pow_succ]
  intro i
  funext j
  have h : (fun i => u i j) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hal
    intro k
    have := congrFun (hk k) j
    simpa [Finset.sum_apply, mul_comm] using this
  exact congrFun h i

/- English proof (translation)
Introduce `O _ _ n A al hal hc`. Establish `hw : ∀ i, ∃ w : Fin n → O, w ≠ 0 ∧ A.mulVec w = al i • w`. Introduce `i`. Establish `h0 : (Matrix.scalar (Fin n) (al i) - A).det = 0`. Rewrite using `[← Matrix.eval_charpoly, hc, Polynomial.eval_prod]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp)`. Take `⟨w, hw0, hw⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Use `⟨w, hw0, ?_⟩` and prove the remaining obligations. Rewrite `hw` using `[Matrix.sub_mulVec, sub_eq_zero]`. Rewrite using `[← hw]`.

Use function extensionality and compare the values at `j`. Simplify using `[Matrix.scalar_apply, Matrix.mulVec_diagonal]`. Use `choose w hw0 hw using hw`. Use `⟨∑ i, w i, fun Y hY hv => ?_⟩` and prove the remaining obligations. Establish `hYw : ∀ i, Y.mulVec (w i) = 0`.

Apply `eig_sum_zero A al hal (fun i => Y.mulVec (w i))` to reduce the goal to its premises. Introduce `i`. Rewrite using `[Matrix.mulVec_mulVec, hY, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]`. Rewrite using `[← Matrix.mulVec_sum, hv]`. Establish `hdet : (Matrix.of w).det ≠ 0`.

Introduce `h0`. Take `⟨c, hc0, hc⟩` from `Matrix.exists_vecMul_eq_zero_iff.mpr h0`. Apply `hc0` to reduce the goal to its premises. Establish `h` using `eig_sum_zero A al hal (fun i => c i • w i) (fun i => by rw [Matrix.mulVec_smul, hw, smul_comm]) (by`. Use function extensionality and compare the values at `j`.

Use `congrFun hc j` as an intermediate fact. Simplify `this)` using `[Matrix.vecMul, dotProduct, Finset.sum_apply]`. Use function extensionality and compare the values at `i`. Conclude with `(smul_eq_zero.mp (h i)).resolve_right (hw0 i)`. Use extensionality with `r j`.

Establish `h : Y r = 0`. Apply `Matrix.eq_zero_of_mulVec_eq_zero hdet` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `congrFun (hYw i) r` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, mul_comm]`.

Conclude with `congrFun h j`.
-/
theorem UpperTheory.Reformulated.B.ExistsCyclic.exists_cyc :
    ∀ {O : Type} [inst : CommRing O] [IsDomain O] {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (al : Fin n → O),
      Function.Injective al →
        A.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : O → Polynomial O) (al i)) →
          ∃ (v : Fin n → O),
            ∀ (Y : Matrix (Fin n) (Fin n) O),
              A * Y = Y * A → Y.mulVec v = (0 : Fin n → O) → Y = (0 : Matrix (Fin n) (Fin n) O) := by
  intro O _ _ n A al hal hc
  have hw : ∀ i, ∃ w : Fin n → O, w ≠ 0 ∧ A.mulVec w = al i • w := by
    intro i
    have h0 : (Matrix.scalar (Fin n) (al i) - A).det = 0 := by
      rw [← Matrix.eval_charpoly, hc, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine ⟨w, hw0, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hw
    rw [← hw]
    funext j
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  choose w hw0 hw using hw
  refine ⟨∑ i, w i, fun Y hY hv => ?_⟩
  have hYw : ∀ i, Y.mulVec (w i) = 0 := by
    apply eig_sum_zero A al hal (fun i => Y.mulVec (w i))
    · intro i
      rw [Matrix.mulVec_mulVec, hY, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
    · rw [← Matrix.mulVec_sum, hv]
  have hdet : (Matrix.of w).det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hc0
    have h := eig_sum_zero A al hal (fun i => c i • w i)
      (fun i => by rw [Matrix.mulVec_smul, hw, smul_comm])
      (by
        funext j
        have := congrFun hc j
        simpa [Matrix.vecMul, dotProduct, Finset.sum_apply] using this)
    funext i
    exact (smul_eq_zero.mp (h i)).resolve_right (hw0 i)
  ext r j
  have h : Y r = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    funext i
    have := congrFun (hYw i) r
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  exact congrFun h j
