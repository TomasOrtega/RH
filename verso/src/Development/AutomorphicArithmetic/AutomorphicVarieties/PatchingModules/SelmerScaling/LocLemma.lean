import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagTriangular
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.OrdExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TriProdZero
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TriDiag
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qk9.tri_diag A B hA hB i`.
-/
private theorem tri_diag {R : Type} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) :
    (A * B) i i = A i i * B i i :=
  _root_.UpperTheory.Reformulated.B.Qk9.tri_diag A B hA hB i

/- English proof (translation)
Set `V : Matrix (Fin n) (Fin n) R` to `Matrix.of fun i j => f j i j`. Establish `hV : V.BlockTriangular id` using `fun i j h => ht j h`. Establish `hVd : ∀ i, V i i = 1` using `hd`. Establish `hdet : V.det = 1` using `by rw [Matrix.det_of_upperTriangular hV]; simp [hVd]`. Establish `hu : IsUnit V.det` using `by rw [hdet]; exact isUnit_one`.

Use `letI := Matrix.invertibleOfIsUnitDet V hu`. Establish `hVi : V⁻¹.BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular hV`. Establish `hl : V⁻¹ * V = 1` using `Matrix.nonsing_inv_mul V hu`. Establish `hr : V * V⁻¹ = 1` using `Matrix.mul_nonsing_inv V hu`. Establish `e1 : ∀ a, f a * V = V * single a a 1`.

Introduce `a`. Use extensionality with `i j`. Establish `: (f a * V) i j = (f a * f j) i j` using `by simp only [Matrix.mul_apply]; rfl`. Rewrite using `[this]`. Distinguish the cases in `h : j = a`.

Substitute `h` using the available equality. Rewrite using `[(hf.idem j).eq, Matrix.mul_single_apply_same, mul_one]`. Both sides reduce to the same expression. Rewrite using `[hf.ortho (Ne.symm h), Matrix.mul_single_apply_of_ne _ _ _ _ _ h]`. Both sides reduce to the same expression.

Establish `e2 : ∀ a, V⁻¹ * f a = single a a 1 * V⁻¹`. Introduce `a`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, mul_assoc, hr, mul_one]`. Use `_ = _ := by rw [e1, ← mul_assoc, hl, one_mul]`.

Establish `e3 : ∀ a b, (V⁻¹ * M * V) a b = (V⁻¹ * (f a * M * f b) * V) a b`. Introduce `a b`. Establish `: V⁻¹ * (f a * M * f b) * V = single a a 1 * (V⁻¹ * M * V) * single b b 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Establish `hT : (V⁻¹ * M * V).BlockTriangular id`. Introduce `a b h`. Rewrite using `[e3, h0 a b h]`. Simplify using the standard rewrite rules.

Establish `hM : M = V * (V⁻¹ * M * V) * V⁻¹`. Combine the equalities or inequalities in the displayed calculation. Establish `hMt : M.BlockTriangular id`. Rewrite using `[hM]`. Conclude with `(hV.mul hT).mul hVi`.

Use `⟨hMt, fun i => ?_⟩` and prove the remaining obligations. Establish `h2 : M * V = V * (V⁻¹ * M * V)`. Rewrite using `[← mul_assoc, ← mul_assoc, hr, one_mul]`. Establish `h3` using `congrFun (congrFun h2 i) i`. Rewrite `h3` using `[tri_diag _ _ hMt hV, tri_diag _ _ hV hT, hVd, mul_one, one_mul, e3, h1, mul_smul_comm, smul_mul_assoc, mul_assoc, e1, ← mul_assoc, hl]`.

Simplify using `using h3`.
-/
private theorem tri_of_idem {R : Type} [CommRing R] {n : ℕ} (f : Fin n → Matrix (Fin n) (Fin n) R)
    (hf : OrthogonalIdempotents f) (ht : ∀ i, (f i).BlockTriangular id) (hd : ∀ i, f i i i = 1)
    (M : Matrix (Fin n) (Fin n) R) (c : Fin n → R) (h0 : ∀ a b, b < a → f a * M * f b = 0)
    (h1 : ∀ a, f a * M * f a = c a • f a) : M.BlockTriangular id ∧ ∀ i, M i i = c i := by
  let V : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => f j i j
  have hV : V.BlockTriangular id := fun i j h => ht j h
  have hVd : ∀ i, V i i = 1 := hd
  have hdet : V.det = 1 := by rw [Matrix.det_of_upperTriangular hV]; simp [hVd]
  have hu : IsUnit V.det := by rw [hdet]; exact isUnit_one
  letI := Matrix.invertibleOfIsUnitDet V hu
  have hVi : V⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hV
  have hl : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hu
  have hr : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V hu
  have e1 : ∀ a, f a * V = V * single a a 1 := by
    intro a
    ext i j
    have : (f a * V) i j = (f a * f j) i j := by simp only [Matrix.mul_apply]; rfl
    rw [this]
    by_cases h : j = a
    · subst h
      rw [(hf.idem j).eq, Matrix.mul_single_apply_same, mul_one]; rfl
    · rw [hf.ortho (Ne.symm h), Matrix.mul_single_apply_of_ne _ _ _ _ _ h]; rfl
  have e2 : ∀ a, V⁻¹ * f a = single a a 1 * V⁻¹ := by
    intro a
    calc V⁻¹ * f a = V⁻¹ * (f a * V) * V⁻¹ := by
          rw [mul_assoc, mul_assoc, hr, mul_one]
      _ = _ := by rw [e1, ← mul_assoc, hl, one_mul]
  have e3 : ∀ a b, (V⁻¹ * M * V) a b = (V⁻¹ * (f a * M * f b) * V) a b := by
    intro a b
    have : V⁻¹ * (f a * M * f b) * V = single a a 1 * (V⁻¹ * M * V) * single b b 1 := by
      calc _ = (V⁻¹ * f a) * M * (f b * V) := by simp only [mul_assoc]
        _ = _ := by rw [e1, e2]; simp only [mul_assoc]
    rw [this]
    simp
  have hT : (V⁻¹ * M * V).BlockTriangular id := by
    intro a b h
    rw [e3, h0 a b h]; simp
  have hM : M = V * (V⁻¹ * M * V) * V⁻¹ := by
    calc M = (V * V⁻¹) * M * (V * V⁻¹) := by rw [hr]; simp
      _ = _ := by simp only [mul_assoc]
  have hMt : M.BlockTriangular id := by
    rw [hM]; exact (hV.mul hT).mul hVi
  refine ⟨hMt, fun i => ?_⟩
  have h2 : M * V = V * (V⁻¹ * M * V) := by
    rw [← mul_assoc, ← mul_assoc, hr, one_mul]
  have h3 := congrFun (congrFun h2 i) i
  rw [tri_diag _ _ hMt hV, tri_diag _ _ hV hT, hVd, mul_one, one_mul, e3, h1, mul_smul_comm,
    smul_mul_assoc, mul_assoc, e1, ← mul_assoc, hl] at h3
  simpa using h3

/- English proof (translation)
Establish `key : ∀ s : Finset (Fin n), (Polynomial.aeval Q (∏ j ∈ s, (Polynomial.X - Polynomial.C (a j)))).BlockTriangular id ∧ (Polynomial.aeval Q (∏ j ∈ s, (Polynomial.X - Polynomial.C (a j)))) i i = ∏ j ∈ s, (a i - a j)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [Matrix.blockTriangular_one]`. Consider the case `insert k s hk ih`.

Establish `hb : (Q - algebraMap R (Matrix (Fin n) (Fin n) R) (a k)).BlockTriangular id`. Use `hQ.sub ?_` and prove the remaining obligations. Rewrite using `[Matrix.algebraMap_eq_diagonal]`. Conclude with `Matrix.blockTriangular_diagonal _`. Rewrite using `[Finset.prod_insert hk, Finset.prod_insert hk, map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]`.

Use `⟨hb.mul ih.1, ?_⟩` and prove the remaining obligations. Rewrite using `[tri_diag _ _ hb ih.1, ih.2, Matrix.sub_apply, hd, Matrix.algebraMap_matrix_apply]`. Simplify using the standard rewrite rules. Take `⟨k1, k2⟩` from `key (Finset.univ.erase i)`. Unfold `lag`.

Use `⟨fun x y h => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, k1 h, smul_zero]`. Rewrite using `[Matrix.smul_apply, k2, smul_eq_mul]`. Conclude with `Ring.inverse_mul_cancel _ (IsUnit.prod_iff.2 fun j hj => hu i j (Finset.ne_of_mem_erase hj).symm)`.
-/
private theorem lag_tri {R : Type} [CommRing R] {n : ℕ} (a : Fin n → R) (Q : Matrix (Fin n) (Fin n) R)
    (hQ : Q.BlockTriangular id) (hd : ∀ i, Q i i = a i) (hu : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (i : Fin n) : (lag a Q i).BlockTriangular id ∧ lag a Q i i i = 1 := by
  have key : ∀ s : Finset (Fin n),
      (Polynomial.aeval Q (∏ j ∈ s, (Polynomial.X - Polynomial.C (a j)))).BlockTriangular id ∧
      (Polynomial.aeval Q (∏ j ∈ s, (Polynomial.X - Polynomial.C (a j)))) i i
        = ∏ j ∈ s, (a i - a j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Matrix.blockTriangular_one]
    | insert k s hk ih =>
      have hb : (Q - algebraMap R (Matrix (Fin n) (Fin n) R) (a k)).BlockTriangular id := by
        refine hQ.sub ?_
        rw [Matrix.algebraMap_eq_diagonal]; exact Matrix.blockTriangular_diagonal _
      rw [Finset.prod_insert hk, Finset.prod_insert hk, map_mul, map_sub, Polynomial.aeval_X,
        Polynomial.aeval_C]
      refine ⟨hb.mul ih.1, ?_⟩
      rw [tri_diag _ _ hb ih.1, ih.2, Matrix.sub_apply, hd, Matrix.algebraMap_matrix_apply]
      simp
  obtain ⟨k1, k2⟩ := key (Finset.univ.erase i)
  unfold lag
  refine ⟨fun x y h => ?_, ?_⟩
  · rw [Matrix.smul_apply, k1 h, smul_zero]
  · rw [Matrix.smul_apply, k2, smul_eq_mul]
    exact Ring.inverse_mul_cancel _
      (IsUnit.prod_iff.2 fun j hj => hu i j (Finset.ne_of_mem_erase hj).symm)

/- English proof (translation)
Establish `h1 : IsNilpotent (u - algebraMap F R (e u))` using `he _ (by simp)`. Establish `h2 : IsNilpotent ((⟨u, hu⟩ : S) - algebraMap F S (e u))`. Take `⟨k, hk⟩` from `h1`. Conclude with `⟨k, Subtype.ext (by simpa using hk)⟩`. Establish `h3 : IsUnit (⟨u, hu⟩ : S)`.

Use `h2.isUnit_add_right_of_commute ((IsUnit.mk0 _ h).map (algebraMap F S)) (Commute.all _ _)` as an intermediate fact. Simplify using `using this`. Take `⟨v, hv⟩` from `h3.exists_right_inv`. Establish `hv' : u * (v : R) = 1` using `congrArg Subtype.val hv`. Establish `hU : IsUnit u` using `IsUnit.of_mul_eq_one _ hv'`.

Use `⟨hU, ?_⟩` and prove the remaining obligations. Establish `: Ring.inverse u = v`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`. Conclude with `v.2`.
-/
private theorem unit_sub {F R : Type} [Field F] [CommRing R] [Algebra F R] (e : R →ₐ[F] F)
    (he : ∀ a, e a = 0 → IsNilpotent a) (S : Subalgebra F R) (u : R) (hu : u ∈ S) (h : e u ≠ 0) :
    IsUnit u ∧ Ring.inverse u ∈ S := by
  have h1 : IsNilpotent (u - algebraMap F R (e u)) := he _ (by simp)
  have h2 : IsNilpotent ((⟨u, hu⟩ : S) - algebraMap F S (e u)) := by
    obtain ⟨k, hk⟩ := h1
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have h3 : IsUnit (⟨u, hu⟩ : S) := by
    have := h2.isUnit_add_right_of_commute ((IsUnit.mk0 _ h).map (algebraMap F S)) (Commute.all _ _)
    simpa using this
  obtain ⟨v, hv⟩ := h3.exists_right_inv
  have hv' : u * (v : R) = 1 := congrArg Subtype.val hv
  have hU : IsUnit u := IsUnit.of_mul_eq_one _ hv'
  refine ⟨hU, ?_⟩
  have : Ring.inverse u = v := by
    calc Ring.inverse u = Ring.inverse u * (u * v) := by rw [hv', mul_one]
      _ = v := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hU, one_mul]
  rw [this]; exact v.2

/- English proof (translation)
Establish `key : ∀ s : Finset ι, (Polynomial.aeval P (∏ j ∈ s, (Polynomial.X - Polynomial.C (a j)))) ∈ E`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using E.one_mem`. Consider the case `insert k s hk ih`.

Rewrite using `[Finset.prod_insert hk, map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]`. Conclude with `E.mul_mem (E.sub_mem hP (ha k)) ih`. Establish `h` using `unit_sub e he (E.comap (IsScalarTower.toAlgHom F R A)) (∏ j ∈ Finset.univ.erase i, (a i - a j)) (Subalgebra.prod_mem _ fun j _ => Subalgebra.sub_mem _ (ha i) (ha j)) (by`. Rewrite using `[map_prod]`. Use `Finset.prod_ne_zero_iff.2 fun j hj => ?_` and prove the remaining obligations.

Rewrite using `[map_sub, sub_ne_zero]`. Conclude with `hne i j (Finset.ne_of_mem_erase hj).symm)`. Unfold `lag`. Rewrite using `[Algebra.smul_def]`. Conclude with `E.mul_mem h.2 (key _)`.
-/
private theorem lag_mem {F R A ι : Type} [Field F] [CommRing R] [Algebra F R] [Ring A] [Algebra R A]
    [Algebra F A] [IsScalarTower F R A] [Fintype ι] [DecidableEq ι] (e : R →ₐ[F] F)
    (he : ∀ a, e a = 0 → IsNilpotent a) (E : Subalgebra F A) (a : ι → R) (P : A) (hP : P ∈ E)
    (ha : ∀ i, algebraMap R A (a i) ∈ E) (hne : ∀ i j, i ≠ j → e (a i) ≠ e (a j)) (i : ι) :
    lag a P i ∈ E := by
  have key : ∀ s : Finset ι,
      (Polynomial.aeval P (∏ j ∈ s, (Polynomial.X - Polynomial.C (a j)))) ∈ E := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using E.one_mem
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
      exact E.mul_mem (E.sub_mem hP (ha k)) ih
  have h := unit_sub e he (E.comap (IsScalarTower.toAlgHom F R A))
    (∏ j ∈ Finset.univ.erase i, (a i - a j))
    (Subalgebra.prod_mem _ fun j _ => Subalgebra.sub_mem _ (ha i) (ha j)) (by
      rw [map_prod]
      refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
      rw [map_sub, sub_ne_zero]
      exact hne i j (Finset.ne_of_mem_erase hj).symm)
  unfold lag
  rw [Algebra.smul_def]
  exact E.mul_mem h.2 (key _)

/- English proof (translation)
Establish `h0 : π Y = 0`. Establish `: ∑ i, π (f' i * f i) = ∑ i, π (f i)` using `Finset.sum_congr rfl fun i _ => by rw [map_mul, hπ, ← map_mul, (hf.idem i).eq]`. Rewrite using `[hY, map_sub, map_sum, this, ← map_sum, hf.complete, sub_self]`. Establish `hYY : Y * Y = 0` using `hsq _ _ h0 h0`. Establish `hU : 1 - Y = ∑ i, f' i * f i` using `by rw [hY, sub_sub_cancel]`.

Establish `h1 : ∀ a, (1 - Y) * f a = f' a * (1 - Y)`. Introduce `a`. Rewrite using `[hU, Finset.sum_mul, Finset.mul_sum, Finset.sum_eq_single a, Finset.sum_eq_single a, mul_assoc, (hf.idem a).eq, ← mul_assoc, (hf'.idem a).eq]`. Introduce `b _ hb`. Rewrite using `[← mul_assoc, hf'.ortho hb.symm, zero_mul]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[mul_assoc, hf.ortho hb, mul_zero]`. Simplify using the standard rewrite rules. Establish `hl : (1 + Y) * (1 - Y) = 1`.

Rewrite using `[add_mul, mul_sub, mul_sub, hYY]`. Simplify using the standard rewrite rules. Establish `hr : (1 - Y) * (1 + Y) = 1`. Rewrite using `[sub_mul, mul_add, mul_add, hYY]`. Simplify using the standard rewrite rules.

Establish `h2 : ∀ a, (1 + Y) * f' a * (1 - Y) = f a`. Introduce `a`. Rewrite using `[mul_assoc, ← h1, ← mul_assoc, hl, one_mul]`. Use `⟨h0, h2, fun r₀ r₁ hr' a b => ?_⟩` and prove the remaining obligations. Establish `hd : π (r₁ - r₀) = 0` using `by rw [map_sub, hr', sub_self]`.

Establish `e1 : r₁ * Y = r₀ * Y` using `by rw [← sub_eq_zero, ← sub_mul]; exact hsq _ _ hd h0`. Establish `e2 : Y * r₁ = Y * r₀` using `by rw [← sub_eq_zero, ← mul_sub]; exact hsq _ _ h0 hd`. Establish `e3 : Y * r₁ * Y = 0` using `hsq _ _ (by rw [map_mul, h0, zero_mul]) h0`. Establish `e4 : r₁ - (r₀ * Y - Y * r₀) = (1 + Y) * r₁ * (1 - Y)`. Rewrite using `[add_mul, add_mul, mul_sub, mul_sub, e3, one_mul, mul_one, mul_one, e1, e2]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e4, ← h2 a, ← h2 b]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = _ := by rw [hr]; simp only [mul_assoc, one_mul, mul_one]`.
-/
private theorem move_idem {A B ι : Type} [Ring A] [Ring B] [Fintype ι] (π : A →+* B)
    (hsq : ∀ x y, π x = 0 → π y = 0 → x * y = 0) (f f' : ι → A)
    (hf : CompleteOrthogonalIdempotents f) (hf' : CompleteOrthogonalIdempotents f')
    (hπ : ∀ i, π (f' i) = π (f i)) (Y : A) (hY : Y = 1 - ∑ i, f' i * f i) :
    π Y = 0 ∧ (∀ a, (1 + Y) * f' a * (1 - Y) = f a) ∧
      ∀ r₀ r₁, π r₁ = π r₀ → ∀ a b, f a * (r₁ - (r₀ * Y - Y * r₀)) * f b =
        (1 + Y) * (f' a * r₁ * f' b) * (1 - Y) := by
  classical
  have h0 : π Y = 0 := by
    have : ∑ i, π (f' i * f i) = ∑ i, π (f i) :=
      Finset.sum_congr rfl fun i _ => by rw [map_mul, hπ, ← map_mul, (hf.idem i).eq]
    rw [hY, map_sub, map_sum, this, ← map_sum, hf.complete, sub_self]
  have hYY : Y * Y = 0 := hsq _ _ h0 h0
  have hU : 1 - Y = ∑ i, f' i * f i := by rw [hY, sub_sub_cancel]
  have h1 : ∀ a, (1 - Y) * f a = f' a * (1 - Y) := by
    intro a
    rw [hU, Finset.sum_mul, Finset.mul_sum, Finset.sum_eq_single a, Finset.sum_eq_single a,
      mul_assoc, (hf.idem a).eq, ← mul_assoc, (hf'.idem a).eq]
    · intro b _ hb
      rw [← mul_assoc, hf'.ortho hb.symm, zero_mul]
    · simp
    · intro b _ hb
      rw [mul_assoc, hf.ortho hb, mul_zero]
    · simp
  have hl : (1 + Y) * (1 - Y) = 1 := by
    rw [add_mul, mul_sub, mul_sub, hYY]; simp
  have hr : (1 - Y) * (1 + Y) = 1 := by
    rw [sub_mul, mul_add, mul_add, hYY]; simp
  have h2 : ∀ a, (1 + Y) * f' a * (1 - Y) = f a := by
    intro a
    rw [mul_assoc, ← h1, ← mul_assoc, hl, one_mul]
  refine ⟨h0, h2, fun r₀ r₁ hr' a b => ?_⟩
  have hd : π (r₁ - r₀) = 0 := by rw [map_sub, hr', sub_self]
  have e1 : r₁ * Y = r₀ * Y := by rw [← sub_eq_zero, ← sub_mul]; exact hsq _ _ hd h0
  have e2 : Y * r₁ = Y * r₀ := by rw [← sub_eq_zero, ← mul_sub]; exact hsq _ _ h0 hd
  have e3 : Y * r₁ * Y = 0 := hsq _ _ (by rw [map_mul, h0, zero_mul]) h0
  have e4 : r₁ - (r₀ * Y - Y * r₀) = (1 + Y) * r₁ * (1 - Y) := by
    rw [add_mul, add_mul, mul_sub, mul_sub, e3, one_mul, mul_one, mul_one, e1, e2]; abel
  rw [e4, ← h2 a, ← h2 b]
  calc _ = (1 + Y) * f' a * ((1 - Y) * (1 + Y)) * r₁ * ((1 - Y) * (1 + Y)) * f' b * (1 - Y) := by
        simp only [mul_assoc]
    _ = _ := by rw [hr]; simp only [mul_assoc, one_mul, mul_one]

/- English proof (translation)
Establish `hinj : Function.Injective (fun i => ((e : R →* F).comp (ψ i) : H →* F))`. Introduce `i j h`. Assume the negation of the conclusion as `hij`. Take `⟨g, hg⟩` from `hψ i j hij`. Conclude with `hg (DFunLike.congr_fun h g)`.

Establish `hli : LinearIndependent F (fun i => (((e : R →* F).comp (ψ i) : H →* F) : H → F))` using `(linearIndependent_monoidHom H F).comp _ hinj`. Establish `hspan` using `span_flip_eq_top_iff_linearIndependent.2 hli`. Establish `key : ∀ t : Fin n → F, ∃ z, G z ∧ ∀ i, e (MonoidAlgebra.lift R R H (ψ i) z) = t i`. Introduce `t`. Establish `ht : t ∈ Submodule.span F (Set.range (flip (fun i => (((e : R →* F).comp (ψ i) : H →* F) : H → F))))` using `by rw [hspan]; trivial`.

Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, rfl⟩` from `hx`. Conclude with `⟨MonoidAlgebra.of R H g, g1 g, fun i => by rw [MonoidAlgebra.lift_of]; rfl⟩`. Consider the case `zero => exact ⟨0, g0, fun i => by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨a, h1, ha⟩` from `hx`. Take `⟨b, h2, hb⟩` from `hy`. Conclude with `⟨a + b, ga _ _ h1 h2, fun i => by rw [map_add, map_add, ha, hb]; rfl⟩`. Consider the case `smul c x _ hx`.

Take `⟨a, h1, ha⟩` from `hx`. Conclude with `⟨algebraMap F R c • a, gs _ _ h1, fun i => by`. Rewrite using `[map_smul, smul_eq_mul, map_mul, ha, AlgHom.commutes]`. Use the proof step `rfl⟩`. Take `⟨z, hG, hz⟩` from `key (fun i => Infinite.natEmbedding F i)`.

Use `⟨z, hG, fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[hz, hz]`. Conclude with `fun h => hij (Fin.ext ((Infinite.natEmbedding F).injective h))`.
-/
private theorem sep_good {F R H : Type} [Field F] [Infinite F] [CommRing R] [Algebra F R] [Monoid H]
    {n : ℕ} (e : R →ₐ[F] F) (ψ : Fin n → H →* R)
    (hψ : ∀ i j, i ≠ j → ∃ g, e (ψ i g) ≠ e (ψ j g)) (G : MonoidAlgebra R H → Prop)
    (g1 : ∀ g, G (MonoidAlgebra.of R H g)) (g0 : G 0) (ga : ∀ x y, G x → G y → G (x + y))
    (gs : ∀ (c : F) x, G x → G (algebraMap F R c • x)) :
    ∃ z, G z ∧ ∀ i j, i ≠ j →
      e (MonoidAlgebra.lift R R H (ψ i) z) ≠ e (MonoidAlgebra.lift R R H (ψ j) z) := by
  have hinj : Function.Injective (fun i => ((e : R →* F).comp (ψ i) : H →* F)) := by
    intro i j h
    by_contra hij
    obtain ⟨g, hg⟩ := hψ i j hij
    exact hg (DFunLike.congr_fun h g)
  have hli : LinearIndependent F (fun i => (((e : R →* F).comp (ψ i) : H →* F) : H → F)) :=
    (linearIndependent_monoidHom H F).comp _ hinj
  have hspan := span_flip_eq_top_iff_linearIndependent.2 hli
  have key : ∀ t : Fin n → F, ∃ z, G z ∧ ∀ i, e (MonoidAlgebra.lift R R H (ψ i) z) = t i := by
    intro t
    have ht : t ∈ Submodule.span F (Set.range (flip
      (fun i => (((e : R →* F).comp (ψ i) : H →* F) : H → F)))) := by rw [hspan]; trivial
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨MonoidAlgebra.of R H g, g1 g, fun i => by rw [MonoidAlgebra.lift_of]; rfl⟩
    | zero => exact ⟨0, g0, fun i => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, h1, ha⟩ := hx
      obtain ⟨b, h2, hb⟩ := hy
      exact ⟨a + b, ga _ _ h1 h2, fun i => by rw [map_add, map_add, ha, hb]; rfl⟩
    | smul c x _ hx =>
      obtain ⟨a, h1, ha⟩ := hx
      exact ⟨algebraMap F R c • a, gs _ _ h1, fun i => by
        rw [map_smul, smul_eq_mul, map_mul, ha, AlgHom.commutes]; rfl⟩
  obtain ⟨z, hG, hz⟩ := key (fun i => Infinite.natEmbedding F i)
  refine ⟨z, hG, fun i j hij => ?_⟩
  rw [hz, hz]
  exact fun h => hij (Fin.ext ((Infinite.natEmbedding F).injective h))

private def cj {R : Type} [CommRing R] {n : ℕ} (w wi : Matrix (Fin n) (Fin n) R) (h1 : w * wi = 1)
    (h2 : wi * w = 1) : Matrix (Fin n) (Fin n) R →ₐ[R] Matrix (Fin n) (Fin n) R where
  toFun X := wi * X * w
  map_one' := by rw [mul_one, h2]
  map_zero' := by simp
  map_add' x y := by rw [mul_add, add_mul]
  map_mul' x y := by
    calc wi * (x * y) * w = wi * x * (w * wi) * y * w := by rw [h1]; simp only [mul_assoc, one_mul]
      _ = _ := by simp only [mul_assoc]
  commutes' c := by rw [mul_assoc, Algebra.commutes, ← mul_assoc, h2, one_mul]

/- English proof (translation)
Introduce `F R H _ _ _ _ _ n e I E ρ₀ ρ₁ ψ₀ ψ₁ w wi he hI hw1 hw2 htri hρ hψ hsep hord hρE hψE`. Establish `hII : ∀ a ∈ I, ∀ b ∈ I, a * b = 0` using `fun a ha b hb => by`. Use `Ideal.mul_mem_mul ha hb` as an intermediate fact. Rewrite `this` using `[hI, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `heI : ∀ a ∈ I, e a = 0` using `fun a ha => by`.

Use `congrArg e (hII a ha a ha)` as an intermediate fact. Rewrite `this` using `[map_mul, map_zero]`. Conclude with `mul_self_eq_zero.1 this`. Set `π` to `(Ideal.Quotient.mk I).mapMatrix (m := Fin n)`. Establish `hπ : ∀ X, π X = 0 ↔ ∀ i j, X i j ∈ I` using `fun X => by`.

Rewrite using `[← Matrix.ext_iff]`. Simplify using `[π, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hsq : ∀ x y, π x = 0 → π y = 0 → x * y = 0` using `fun x y hx hy => by`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`.

Conclude with `Finset.sum_eq_zero fun k _ => hII _ ((hπ x).1 hx _ _) _ ((hπ y).1 hy _ _)`. Establish `hρπ : ∀ g, π (ρ₁ g) = π (ρ₀ g)` using `fun g => by`. Rewrite using `[← sub_eq_zero, ← map_sub]`. Conclude with `(hπ _).2 (hρ g)`. Set `c` to `cj w wi hw1 hw2`.

Establish `hc : ∀ X, c X = wi * X * w` using `fun _ => rfl`. Establish `hcinj : ∀ X, c X = 0 → X = 0` using `fun X hX => by`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← mul_assoc, hw1, one_mul, mul_assoc, hw1, mul_one]`. Use `_ = 0 := by rw [← hc, hX]; simp`.

Establish `htri1 : ∀ g, (c (ρ₀ g)).BlockTriangular id` using `fun g i j h => (htri g).1 i j h`. Establish `htri2 : ∀ g i, c (ρ₀ g) i i = ψ₀ i g` using `fun g => (htri g).2`. Establish `hord0 : ∀ g : Fin n → H, (List.ofFn fun i => ρ₀ (g i) - algebraMap R (Matrix (Fin n) (Fin n) R) (ψ₀ i (g i))).prod = 0`. Introduce `g`. Apply `hcinj` to reduce the goal to its premises.

Rewrite using `[map_list_prod, List.map_ofFn]`. Use `tri_prod_zero _ (fun k i j h => ?_) (fun k => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp, map_sub, AlgHom.commutes, Matrix.sub_apply]`. Rewrite using `[htri1 _ h, Matrix.algebraMap_matrix_apply, if_neg h.ne', sub_zero]`. Simplify using `only [Function.comp, map_sub, AlgHom.commutes, Matrix.sub_apply]`.

Rewrite using `[htri2, Matrix.algebraMap_matrix_apply, if_pos rfl]`. Simplify using the standard rewrite rules. Use `set L₀ := MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) H ρ₀ with hL₀`. Use `set L₁ := MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) H ρ₁ with hL₁`. Set `χ₀` to `fun i => MonoidAlgebra.lift R R H (ψ₀ i)`.

Set `χ₁` to `fun i => MonoidAlgebra.lift R R H (ψ₁ i)`. Establish `hL0 : ∀ g, L₀ (MonoidAlgebra.of R H g) = ρ₀ g` using `fun g => MonoidAlgebra.lift_of _ _`. Establish `hL1 : ∀ g, L₁ (MonoidAlgebra.of R H g) = ρ₁ g` using `fun g => MonoidAlgebra.lift_of _ _`. Establish `hχ0 : ∀ i g, χ₀ i (MonoidAlgebra.of R H g) = ψ₀ i g` using `fun i g => MonoidAlgebra.lift_of _ _`. Establish `hχ1 : ∀ i g, χ₁ i (MonoidAlgebra.of R H g) = ψ₁ i g` using `fun i g => MonoidAlgebra.lift_of _ _`.

Take `⟨z, ⟨⟨z1, z2, z3, z4⟩, ⟨z5, z6⟩, z7, z8⟩, hz⟩` from `sep_good e ψ₀ hsep (fun z => (L₀ z ∈ E ∧ L₁ z ∈ E ∧ (∀ i, algebraMap R (Matrix (Fin n) (Fin n) R) (χ₀ i z) ∈ E) ∧ ∀ i, algebraMap R (Matrix (Fin n) (Fin n) R) (χ₁ i z) ∈ E) ∧ ((∀ i j, L₁ z i j - L₀ z i j ∈ I) ∧ ∀ i, χ₁ i z - χ₀ i z ∈ I) ∧ (c (L₀ z)).BlockTriangular id ∧ ∀ i, c (L …`. Simplify using `only [hL0, hL1, hχ0, hχ1]`. Conclude with `⟨⟨(hρE g).1, (hρE g).2, fun i => (hψE i g).1, fun i => (hψE i g).2⟩, ⟨hρ g, fun i => hψ i g⟩, htri1 g, htri2 g⟩)`. Use the proof step `(by simp [Matrix.blockTriangular_zero])`. Use the proof step `(by`.

Introduce and unpack `x y ⟨⟨x1, x2, x3, x4⟩, ⟨x5, x6⟩, x7, x8⟩ ⟨⟨y1, y2, y3, y4⟩, ⟨y5, y6⟩, y7, y8⟩`. Simplify using `only [map_add, Matrix.add_apply, add_sub_add_comm]`. Conclude with `⟨⟨E.add_mem x1 y1, E.add_mem x2 y2, fun i => E.add_mem (x3 i) (y3 i), fun i => E.add_mem (x4 i) (y4 i)⟩, ⟨fun i j => I.add_mem (x5 i j) (y5 i j), fun i => I.add_mem (x6 i) (y6 i)⟩, x7.add y7, fun i => by rw [x8, y8]⟩)`. Use the proof step `(by`. Introduce and unpack `a x ⟨⟨x1, x2, x3, x4⟩, ⟨x5, x6⟩, x7, x8⟩`.

Establish `hs : ∀ X ∈ E, algebraMap F R a • X ∈ E` using `fun X hX => by`. Rewrite using `[algebraMap_smul]`. Conclude with `E.smul_mem hX a`. Establish `hs' : ∀ r : R, algebraMap R (Matrix (Fin n) (Fin n) R) r ∈ E → algebraMap R (Matrix (Fin n) (Fin n) R) (algebraMap F R a • r) ∈ E` using `fun r hr => by`. Rewrite using `[smul_eq_mul, map_mul, ← Algebra.smul_def]`.

Conclude with `hs _ hr`. Simplify using `only [map_smul, Matrix.smul_apply, ← smul_sub]`. Conclude with `⟨⟨hs _ x1, hs _ x2, fun i => hs' _ (x3 i), fun i => hs' _ (x4 i)⟩, ⟨fun i j => I.smul_mem _ (x5 i j), fun i => I.smul_mem _ (x6 i)⟩, fun i j h => by rw [Matrix.smul_apply, x7 h, smul_zero], fun i => by rw [x8]⟩)`. Establish `hz0 : ∀ i j, i ≠ j → e (χ₀ i z) ≠ e (χ₀ j z)` using `hz`. Establish `he1 : ∀ i, e (χ₁ i z) = e (χ₀ i z)` using `fun i => by`.

Rewrite using `[← sub_eq_zero, ← map_sub]`. Conclude with `heI _ (z6 i)`. Establish `hz1 : ∀ i j, i ≠ j → e (χ₁ i z) ≠ e (χ₁ j z)` using `fun i j h => by`. Rewrite using `[he1, he1]`. Conclude with `hz0 i j h`.

Establish `hu0 : ∀ i j, i ≠ j → IsUnit (χ₀ i z - χ₀ j z)` using `fun i j h => (unit_sub e he ⊤ _ trivial (by rw [map_sub, sub_ne_zero]; exact hz0 i j h)).1`. Establish `hu1 : ∀ i j, i ≠ j → IsUnit (χ₁ i z - χ₁ j z)` using `fun i j h => (unit_sub e he ⊤ _ trivial (by rw [map_sub, sub_ne_zero]; exact hz1 i j h)).1`. Take `⟨c0, -, -⟩` from `lag_triangular L₀ χ₀ z (ord_ext ρ₀ ψ₀ hord0) hu0`. Take `⟨c1, t1, d1⟩` from `lag_triangular L₁ χ₁ z (ord_ext ρ₁ ψ₁ hord) hu1`. Establish `m0` using `lag_mem e he E (fun i => χ₀ i z) (L₀ z) z1 z3 hz0`.

Establish `m1` using `lag_mem e he E (fun i => χ₁ i z) (L₁ z) z2 z4 hz1`. Establish `hcomm : ∀ r, π (algebraMap R _ r) = algebraMap (R ⧸ I) (Matrix (Fin n) (Fin n) (R ⧸ I)) (Ideal.Quotient.mk I r)` using `fun r => by`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [π, Matrix.algebraMap_matrix_apply, h]`. Establish `hπf : ∀ i, π (lag (fun i => χ₁ i z) (L₁ z) i) = π (lag (fun i => χ₀ i z) (L₀ z) i)`.

Introduce `i`. Rewrite using `[lag_map _ π _ _ hcomm hu1, lag_map _ π _ _ hcomm hu0]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `Ideal.Quotient.eq.2 (z6 j)`.

Rewrite using `[← sub_eq_zero, ← map_sub]`. Conclude with `(hπ _).2 z5`. Establish `hcf : ∀ i, (c (lag (fun i => χ₀ i z) (L₀ z) i)).BlockTriangular id ∧ c (lag (fun i => χ₀ i z) (L₀ z) i) i i = 1`. Introduce `i`. Use `lag_map (RingHom.id R) c.toRingHom (fun i => χ₀ i z) (L₀ z) c.commutes hu0 i` as an intermediate fact.

Establish `h2` using `lag_tri (fun i => χ₀ i z) (c (L₀ z)) z7 z8 hu0 i`. Conclude with `(show c (lag (fun i => χ₀ i z) (L₀ z) i) = lag (fun i => χ₀ i z) (c (L₀ z)) i from this) ▸ h2`. Use `set f := lag (fun i => χ₀ i z) (L₀ z)`. Use `set f' := lag (fun i => χ₁ i z) (L₁ z)`. Take `⟨Y, hY⟩ : ∃ Y, Y = 1 - ∑ i, f' i * f i` from `⟨_, rfl⟩`.

Take `⟨k0, k1, k2⟩` from `move_idem π hsq f f' c0 c1 hπf Y hY`. Use `⟨Y, ?_, (hπ Y).1 k0, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[hY]`. Conclude with `E.sub_mem E.one_mem (E.sum_mem fun i _ => E.mul_mem (m1 i) (m0 i))`. Take `⟨p1, p2⟩` from `tri_of_idem (fun i => c (f i)) (c0.toOrthogonalIdempotents.map c.toRingHom) (fun i => (hcf i).1) (fun i => (hcf i).2) (c (ρ₁ g - (ρ₀ g * Y - Y * ρ₀ g))) (fun i => ψ₁ i g) (fun a b h => by`.

Use `t1 (MonoidAlgebra.of R H g) a b h` as an intermediate fact. Rewrite `this` using `[hL1]`. Rewrite using `[← map_mul, ← map_mul, k2 _ _ (hρπ g), this]`. Use the proof step `simp)`. Use the proof step `(fun a => by`.

Use `d1 (MonoidAlgebra.of R H g) a` as an intermediate fact. Rewrite `this` using `[hL1, hχ1]`. Rewrite using `[← map_mul, ← map_mul, k2 _ _ (hρπ g), this, mul_smul_comm, smul_mul_assoc, k1, map_smul])`. Establish `hinv : ρ₀ g * ρ₀ g⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Establish `hβ : wi * ((ρ₁ g * ρ₀ g⁻¹ - 1) - (ρ₀ g * Y * ρ₀ g⁻¹ - Y)) * w = (c (ρ₁ g - (ρ₀ g * Y - Y * ρ₀ g)) - c (ρ₀ g)) * c (ρ₀ g⁻¹)`.

Rewrite using `[← hc, ← map_sub, ← map_mul, sub_mul, sub_mul, sub_mul, mul_assoc Y, hinv, mul_one]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite using `[hβ]`. Establish `hb` using `p1.sub (htri1 g)`.

Use `⟨fun i j h => (hb.mul (htri1 g⁻¹)) h, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[tri_diag _ _ hb (htri1 _), Matrix.sub_apply, p2, htri2, htri2, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]`.
-/
theorem UpperTheory.V.Pa.locLemma :
    ∀ (F R H : Type) [Field F] [Infinite F] [CommRing R] [Algebra F R] [Group H] (n : ℕ) (e : R →ₐ[F] F) (I : Ideal R) (E : Subalgebra F (Matrix (Fin n) (Fin n) R)) (ρ₀ ρ₁ : H →* Matrix (Fin n) (Fin n) R) (ψ₀ ψ₁ : Fin n → H →* R) (w wi : Matrix (Fin n) (Fin n) R), (∀ a, e a = 0 → IsNilpotent a) → I * I = ⊥ → w * wi = 1 → wi * w = 1 → (∀ g, (∀ i j, j < i → (wi * ρ₀ g * w) i j = 0) ∧ ∀ i, (wi * ρ₀ g * w) i i = ψ₀ i g) → (∀ g i j, ρ₁ g i j - ρ₀ g i j ∈ I) → (∀ i g, ψ₁ i g - ψ₀ i g ∈ I) → (∀ i j, i ≠ j → ∃ g, e (ψ₀ i g) ≠ e (ψ₀ j g)) → (∀ g : Fin n → H, (List.ofFn fun i => ρ₁ (g i) - algebraMap R (Matrix (Fin n) (Fin n) R) (ψ₁ i (g i))).prod = 0) → (∀ g, ρ₀ g ∈ E ∧ ρ₁ g ∈ E) → (∀ i g, algebraMap R (Matrix (Fin n) (Fin n) R) (ψ₀ i g) ∈ E ∧ algebraMap R (Matrix (Fin n) (Fin n) R) (ψ₁ i g) ∈ E) → ∃ Y ∈ E, (∀ i j, Y i j ∈ I) ∧ ∀ g, (∀ i j, j < i → (wi * ((ρ₁ g * ρ₀ g⁻¹ - 1) - (ρ₀ g * Y * ρ₀ g⁻¹ - Y)) * w) i j = 0) ∧ ∀ i, (wi * ((ρ₁ g * ρ₀ g⁻¹ - 1) - (ρ₀ g * Y * ρ₀ g⁻¹ - Y)) * w) i i * ψ₀ i g = ψ₁ i g - ψ₀ i g := by
  intro F R H _ _ _ _ _ n e I E ρ₀ ρ₁ ψ₀ ψ₁ w wi he hI hw1 hw2 htri hρ hψ hsep hord hρE hψE
  have hII : ∀ a ∈ I, ∀ b ∈ I, a * b = 0 := fun a ha b hb => by
    have := Ideal.mul_mem_mul ha hb
    rwa [hI, Ideal.mem_bot] at this
  have heI : ∀ a ∈ I, e a = 0 := fun a ha => by
    have := congrArg e (hII a ha a ha)
    rw [map_mul, map_zero] at this
    exact mul_self_eq_zero.1 this
  let π := (Ideal.Quotient.mk I).mapMatrix (m := Fin n)
  have hπ : ∀ X, π X = 0 ↔ ∀ i j, X i j ∈ I := fun X => by
    rw [← Matrix.ext_iff]
    simp [π, Ideal.Quotient.eq_zero_iff_mem]
  have hsq : ∀ x y, π x = 0 → π y = 0 → x * y = 0 := fun x y hx hy => by
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => hII _ ((hπ x).1 hx _ _) _ ((hπ y).1 hy _ _)
  have hρπ : ∀ g, π (ρ₁ g) = π (ρ₀ g) := fun g => by
    rw [← sub_eq_zero, ← map_sub]; exact (hπ _).2 (hρ g)
  let c := cj w wi hw1 hw2
  have hc : ∀ X, c X = wi * X * w := fun _ => rfl
  have hcinj : ∀ X, c X = 0 → X = 0 := fun X hX => by
    calc X = w * (wi * X * w) * wi := by
          rw [← mul_assoc, ← mul_assoc, hw1, one_mul, mul_assoc, hw1, mul_one]
      _ = 0 := by rw [← hc, hX]; simp
  have htri1 : ∀ g, (c (ρ₀ g)).BlockTriangular id := fun g i j h => (htri g).1 i j h
  have htri2 : ∀ g i, c (ρ₀ g) i i = ψ₀ i g := fun g => (htri g).2
  have hord0 : ∀ g : Fin n → H, (List.ofFn fun i => ρ₀ (g i) -
      algebraMap R (Matrix (Fin n) (Fin n) R) (ψ₀ i (g i))).prod = 0 := by
    intro g
    apply hcinj
    rw [map_list_prod, List.map_ofFn]
    refine tri_prod_zero _ (fun k i j h => ?_) (fun k => ?_)
    · simp only [Function.comp, map_sub, AlgHom.commutes, Matrix.sub_apply]
      rw [htri1 _ h, Matrix.algebraMap_matrix_apply, if_neg h.ne', sub_zero]
    · simp only [Function.comp, map_sub, AlgHom.commutes, Matrix.sub_apply]
      rw [htri2, Matrix.algebraMap_matrix_apply, if_pos rfl]
      simp
  set L₀ := MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) H ρ₀ with hL₀
  set L₁ := MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) H ρ₁ with hL₁
  let χ₀ := fun i => MonoidAlgebra.lift R R H (ψ₀ i)
  let χ₁ := fun i => MonoidAlgebra.lift R R H (ψ₁ i)
  have hL0 : ∀ g, L₀ (MonoidAlgebra.of R H g) = ρ₀ g := fun g => MonoidAlgebra.lift_of _ _
  have hL1 : ∀ g, L₁ (MonoidAlgebra.of R H g) = ρ₁ g := fun g => MonoidAlgebra.lift_of _ _
  have hχ0 : ∀ i g, χ₀ i (MonoidAlgebra.of R H g) = ψ₀ i g := fun i g => MonoidAlgebra.lift_of _ _
  have hχ1 : ∀ i g, χ₁ i (MonoidAlgebra.of R H g) = ψ₁ i g := fun i g => MonoidAlgebra.lift_of _ _
  obtain ⟨z, ⟨⟨z1, z2, z3, z4⟩, ⟨z5, z6⟩, z7, z8⟩, hz⟩ := sep_good e ψ₀ hsep
    (fun z => (L₀ z ∈ E ∧ L₁ z ∈ E ∧ (∀ i, algebraMap R (Matrix (Fin n) (Fin n) R) (χ₀ i z) ∈ E) ∧
      ∀ i, algebraMap R (Matrix (Fin n) (Fin n) R) (χ₁ i z) ∈ E) ∧
      ((∀ i j, L₁ z i j - L₀ z i j ∈ I) ∧ ∀ i, χ₁ i z - χ₀ i z ∈ I) ∧
      (c (L₀ z)).BlockTriangular id ∧ ∀ i, c (L₀ z) i i = χ₀ i z)
    (fun g => by
      simp only [hL0, hL1, hχ0, hχ1]
      exact ⟨⟨(hρE g).1, (hρE g).2, fun i => (hψE i g).1, fun i => (hψE i g).2⟩,
        ⟨hρ g, fun i => hψ i g⟩, htri1 g, htri2 g⟩)
    (by simp [Matrix.blockTriangular_zero])
    (by
      rintro x y ⟨⟨x1, x2, x3, x4⟩, ⟨x5, x6⟩, x7, x8⟩ ⟨⟨y1, y2, y3, y4⟩, ⟨y5, y6⟩, y7, y8⟩
      simp only [map_add, Matrix.add_apply, add_sub_add_comm]
      exact ⟨⟨E.add_mem x1 y1, E.add_mem x2 y2, fun i => E.add_mem (x3 i) (y3 i),
        fun i => E.add_mem (x4 i) (y4 i)⟩, ⟨fun i j => I.add_mem (x5 i j) (y5 i j),
        fun i => I.add_mem (x6 i) (y6 i)⟩, x7.add y7, fun i => by rw [x8, y8]⟩)
    (by
      rintro a x ⟨⟨x1, x2, x3, x4⟩, ⟨x5, x6⟩, x7, x8⟩
      have hs : ∀ X ∈ E, algebraMap F R a • X ∈ E := fun X hX => by
        rw [algebraMap_smul]; exact E.smul_mem hX a
      have hs' : ∀ r : R, algebraMap R (Matrix (Fin n) (Fin n) R) r ∈ E →
          algebraMap R (Matrix (Fin n) (Fin n) R) (algebraMap F R a • r) ∈ E := fun r hr => by
        rw [smul_eq_mul, map_mul, ← Algebra.smul_def]; exact hs _ hr
      simp only [map_smul, Matrix.smul_apply, ← smul_sub]
      exact ⟨⟨hs _ x1, hs _ x2, fun i => hs' _ (x3 i), fun i => hs' _ (x4 i)⟩,
        ⟨fun i j => I.smul_mem _ (x5 i j), fun i => I.smul_mem _ (x6 i)⟩,
        fun i j h => by rw [Matrix.smul_apply, x7 h, smul_zero], fun i => by rw [x8]⟩)
  have hz0 : ∀ i j, i ≠ j → e (χ₀ i z) ≠ e (χ₀ j z) := hz
  have he1 : ∀ i, e (χ₁ i z) = e (χ₀ i z) := fun i => by
    rw [← sub_eq_zero, ← map_sub]; exact heI _ (z6 i)
  have hz1 : ∀ i j, i ≠ j → e (χ₁ i z) ≠ e (χ₁ j z) := fun i j h => by
    rw [he1, he1]; exact hz0 i j h
  have hu0 : ∀ i j, i ≠ j → IsUnit (χ₀ i z - χ₀ j z) := fun i j h =>
    (unit_sub e he ⊤ _ trivial (by rw [map_sub, sub_ne_zero]; exact hz0 i j h)).1
  have hu1 : ∀ i j, i ≠ j → IsUnit (χ₁ i z - χ₁ j z) := fun i j h =>
    (unit_sub e he ⊤ _ trivial (by rw [map_sub, sub_ne_zero]; exact hz1 i j h)).1
  obtain ⟨c0, -, -⟩ := lag_triangular L₀ χ₀ z (ord_ext ρ₀ ψ₀ hord0) hu0
  obtain ⟨c1, t1, d1⟩ := lag_triangular L₁ χ₁ z (ord_ext ρ₁ ψ₁ hord) hu1
  have m0 := lag_mem e he E (fun i => χ₀ i z) (L₀ z) z1 z3 hz0
  have m1 := lag_mem e he E (fun i => χ₁ i z) (L₁ z) z2 z4 hz1
  have hcomm : ∀ r, π (algebraMap R _ r) =
      algebraMap (R ⧸ I) (Matrix (Fin n) (Fin n) (R ⧸ I)) (Ideal.Quotient.mk I r) := fun r => by
    ext i j
    by_cases h : i = j <;> simp [π, Matrix.algebraMap_matrix_apply, h]
  have hπf : ∀ i, π (lag (fun i => χ₁ i z) (L₁ z) i) = π (lag (fun i => χ₀ i z) (L₀ z) i) := by
    intro i
    rw [lag_map _ π _ _ hcomm hu1, lag_map _ π _ _ hcomm hu0]
    congr 1
    · funext j
      exact Ideal.Quotient.eq.2 (z6 j)
    · rw [← sub_eq_zero, ← map_sub]; exact (hπ _).2 z5
  have hcf : ∀ i, (c (lag (fun i => χ₀ i z) (L₀ z) i)).BlockTriangular id ∧
      c (lag (fun i => χ₀ i z) (L₀ z) i) i i = 1 := by
    intro i
    have := lag_map (RingHom.id R) c.toRingHom (fun i => χ₀ i z) (L₀ z) c.commutes hu0 i
    have h2 := lag_tri (fun i => χ₀ i z) (c (L₀ z)) z7 z8 hu0 i
    exact (show c (lag (fun i => χ₀ i z) (L₀ z) i) = lag (fun i => χ₀ i z) (c (L₀ z)) i from this) ▸ h2
  set f := lag (fun i => χ₀ i z) (L₀ z)
  set f' := lag (fun i => χ₁ i z) (L₁ z)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 1 - ∑ i, f' i * f i := ⟨_, rfl⟩
  obtain ⟨k0, k1, k2⟩ := move_idem π hsq f f' c0 c1 hπf Y hY
  refine ⟨Y, ?_, (hπ Y).1 k0, fun g => ?_⟩
  · rw [hY]
    exact E.sub_mem E.one_mem (E.sum_mem fun i _ => E.mul_mem (m1 i) (m0 i))
  obtain ⟨p1, p2⟩ := tri_of_idem (fun i => c (f i)) (c0.toOrthogonalIdempotents.map c.toRingHom)
    (fun i => (hcf i).1) (fun i => (hcf i).2) (c (ρ₁ g - (ρ₀ g * Y - Y * ρ₀ g))) (fun i => ψ₁ i g)
    (fun a b h => by
      have := t1 (MonoidAlgebra.of R H g) a b h
      rw [hL1] at this
      rw [← map_mul, ← map_mul, k2 _ _ (hρπ g), this]; simp)
    (fun a => by
      have := d1 (MonoidAlgebra.of R H g) a
      rw [hL1, hχ1] at this
      rw [← map_mul, ← map_mul, k2 _ _ (hρπ g), this, mul_smul_comm, smul_mul_assoc, k1, map_smul])
  have hinv : ρ₀ g * ρ₀ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hβ : wi * ((ρ₁ g * ρ₀ g⁻¹ - 1) - (ρ₀ g * Y * ρ₀ g⁻¹ - Y)) * w =
      (c (ρ₁ g - (ρ₀ g * Y - Y * ρ₀ g)) - c (ρ₀ g)) * c (ρ₀ g⁻¹) := by
    rw [← hc, ← map_sub, ← map_mul, sub_mul, sub_mul, sub_mul, mul_assoc Y, hinv, mul_one]
    congr 1
    abel
  rw [hβ]
  have hb := p1.sub (htri1 g)
  refine ⟨fun i j h => (hb.mul (htri1 g⁻¹)) h, fun i => ?_⟩
  rw [tri_diag _ _ hb (htri1 _), Matrix.sub_apply, p2, htri2, htri2, mul_assoc, ← map_mul,
    inv_mul_cancel, map_one, mul_one]
