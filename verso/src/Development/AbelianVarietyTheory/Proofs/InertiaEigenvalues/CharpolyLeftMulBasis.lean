import Mathlib
open Polynomial

namespace GlobalTheory.TraceDetSplit

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons r s ih`. Establish `h1 : (aeval N (X - C r)).det = (-1) ^ n * N.charpoly.eval r`. Establish `e : Matrix.scalar (Fin n) r - N = -(N - algebraMap K (Matrix (Fin n) (Fin n) K) r)`.

Rewrite using `[neg_sub, Matrix.algebraMap_eq_diagonal]`. Both sides reduce to the same expression. Rewrite using `[Matrix.eval_charpoly, e, Matrix.det_neg, Fintype.card_fin, map_sub, aeval_X, aeval_C, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]`. Simplify using `only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, map_mul, Matrix.det_mul, ih, h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_aeval_prod {K : Type} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K) (s : Multiset K) :
    (aeval N (s.map fun r => X - C r).prod).det
      = (-1) ^ (n * s.card) * (s.map N.charpoly.eval).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have h1 : (aeval N (X - C r)).det = (-1) ^ n * N.charpoly.eval r := by
      have e : Matrix.scalar (Fin n) r - N = -(N - algebraMap K (Matrix (Fin n) (Fin n) K) r) := by
        rw [neg_sub, Matrix.algebraMap_eq_diagonal]
        rfl
      rw [Matrix.eval_charpoly, e, Matrix.det_neg, Fintype.card_fin, map_sub, aeval_X, aeval_C,
        ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, map_mul, Matrix.det_mul, ih, h1]
    ring

/- English proof (translation)
Set `φ` to `algebraMap E (AlgebraicClosure E)`. Apply `φ.injective` to reduce the goal to its premises. Establish `hp' : (p.map φ).Monic` using `hp.map φ`. Establish `hs : (p.map φ).Splits` using `IsAlgClosed.splits _`. Establish `hd : (p.map φ).natDegree = p.natDegree` using `natDegree_map φ`.

Establish `key : φ.mapMatrix (aeval N p) = aeval (N.map φ) (p.map φ)`. Rewrite using `[aeval_map_algebraMap]`. Conclude with `(Polynomial.aeval_algHom_apply (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId E (AlgebraicClosure E))) N p).symm`. Rewrite using `[RingHom.map_det, key, map_mul, map_pow, map_neg, map_one, ← resultant_map_map, ← Matrix.charpoly_map]`. Use `conv_lhs => rw [hs.eq_prod_roots_of_monic hp']`.

Rewrite using `[det_aeval_prod, ← hs.natDegree_eq_card_roots, hd, ← hd, resultant_eq_prod_eval _ _ _ (by rw [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim]) hs, hp'.leadingCoeff, one_pow, one_mul]`.
-/
theorem det_aeval {E : Type} [Field E] {n : ℕ} (N : Matrix (Fin n) (Fin n) E) (p : E[X])
    (hp : p.Monic) :
    (aeval N p).det = (-1) ^ (n * p.natDegree) * resultant p N.charpoly := by
  classical
  let φ := algebraMap E (AlgebraicClosure E)
  apply φ.injective
  have hp' : (p.map φ).Monic := hp.map φ
  have hs : (p.map φ).Splits := IsAlgClosed.splits _
  have hd : (p.map φ).natDegree = p.natDegree := natDegree_map φ
  have key : φ.mapMatrix (aeval N p) = aeval (N.map φ) (p.map φ) := by
    rw [aeval_map_algebraMap]
    exact (Polynomial.aeval_algHom_apply
      (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId E (AlgebraicClosure E))) N p).symm
  rw [RingHom.map_det, key, map_mul, map_pow, map_neg, map_one, ← resultant_map_map,
    ← Matrix.charpoly_map]
  conv_lhs => rw [hs.eq_prod_roots_of_monic hp']
  rw [det_aeval_prod, ← hs.natDegree_eq_card_roots, hd, ← hd,
    resultant_eq_prod_eval _ _ _ (by rw [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim]) hs,
    hp'.leadingCoeff, one_pow, one_mul]

/- English proof (translation)
Establish `hM : (Matrix.of fun k l : Fin n => Algebra.trace E A (aeval g (q k) * e l)) = (Matrix.of fun k j : Fin n => (q k).coeff (j : ℕ)) * Matrix.of fun k l : Fin n => Algebra.trace E A (g ^ (k : ℕ) * e l)`. Use extensionality with `k l`. Simplify using `only [Matrix.of_apply, Matrix.mul_apply]`. Rewrite using `[aeval_eq_sum_range' (n := n) (by rw [hd k]; exact k.isLt), Finset.sum_mul, map_sum, ← Fin.sum_univ_eq_sum_range]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_mul_assoc, map_smul, smul_eq_mul]`. Establish `hC : (Matrix.of fun k j : Fin n => (q k).coeff (j : ℕ)).det = 1`. Rewrite using `[Matrix.det_of_isLowerTriangular]`. Use `Finset.prod_eq_one fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply]`.

Use `(hm k).coeff_natDegree` as an intermediate fact. Rewrite `this` using `[hd k]`. Then use the resulting hypothesis. Introduce `i j hij`. Simplify using `only [Matrix.of_apply]`. Apply `coeff_eq_zero_of_natDegree_lt` to reduce the goal to its premises.

Rewrite using `[hd i]`. Conclude with `hij`. Rewrite using `[hM, Matrix.det_mul, hC, one_mul]`.
-/
theorem det_trace_monic {E A : Type} [Field E] [CommRing A] [Algebra E A] {n : ℕ} (g : A)
    (e : Fin n → A) (q : Fin n → E[X]) (hd : ∀ k, (q k).natDegree = k) (hm : ∀ k, (q k).Monic) :
    (Matrix.of fun k l : Fin n => Algebra.trace E A (g ^ (k : ℕ) * e l)).det
      = (Matrix.of fun k l : Fin n => Algebra.trace E A (aeval g (q k) * e l)).det := by
  classical
  have hM : (Matrix.of fun k l : Fin n => Algebra.trace E A (aeval g (q k) * e l)) =
      (Matrix.of fun k j : Fin n => (q k).coeff (j : ℕ)) *
        Matrix.of fun k l : Fin n => Algebra.trace E A (g ^ (k : ℕ) * e l) := by
    ext k l
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [aeval_eq_sum_range' (n := n) (by rw [hd k]; exact k.isLt), Finset.sum_mul, map_sum,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul]
  have hC : (Matrix.of fun k j : Fin n => (q k).coeff (j : ℕ)).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_eq_one fun k _ => ?_
      simp only [Matrix.of_apply]
      have := (hm k).coeff_natDegree
      rwa [hd k] at this
    · intro i j hij
      simp only [Matrix.of_apply]
      apply coeff_eq_zero_of_natDegree_lt
      rw [hd i]
      exact hij
  rw [hM, Matrix.det_mul, hC, one_mul]

/- English proof (translation)
Rewrite using `[Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]`. Both sides reduce to the same expression.
-/
theorem charpoly_leftMul_basis {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] {n : ℕ} (g : A) (w : Module.Basis (Fin n) E A) :
    (Algebra.leftMulMatrix w g).charpoly = (LinearMap.mulLeft E g).charpoly := by
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
  rfl

/- English proof (translation)
Use extensionality with `k l`. Simplify using `only [Matrix.of_apply, Matrix.mul_apply, Algebra.leftMulMatrix_eq_repr_mul]`. Use `conv_lhs => rw [mul_assoc, ← w.sum_repr (h * w l)]`. Rewrite using `[Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_smul_comm, map_smul, smul_eq_mul, mul_comm]`.
-/
theorem trace_mul_eq {E A : Type} [Field E] [CommRing A] [Algebra E A] {n : ℕ} (x : Fin n → A)
    (h : A) (w : Module.Basis (Fin n) E A) :
    (Matrix.of fun k l : Fin n => Algebra.trace E A (x k * h * w l))
      = (Matrix.of fun k l : Fin n => Algebra.trace E A (x k * w l)) * Algebra.leftMulMatrix w h := by
  ext k l
  simp only [Matrix.of_apply, Matrix.mul_apply, Algebra.leftMulMatrix_eq_repr_mul]
  conv_lhs => rw [mul_assoc, ← w.sum_repr (h * w l)]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.TraceDetSplit

open GlobalTheory.TraceDetSplit in

/- English proof (translation)
Introduce `E A₁ A₂ _ _ _ _ _ _ _ g₁ g₂ a b u w _`. Establish `hdeg₁ : (LinearMap.mulLeft E g₁).charpoly.natDegree = a`. Rewrite using `[LinearMap.charpoly_natDegree, Module.finrank_eq_card_basis u, Fintype.card_fin]`. Establish `hCH : aeval g₁ (LinearMap.mulLeft E g₁).charpoly = 0`. Establish `h` using `LinearMap.aeval_self_charpoly (LinearMap.mulLeft E g₁)`.

Establish `h2 : aeval (LinearMap.mulLeft E g₁) (LinearMap.mulLeft E g₁).charpoly = Algebra.lmul E A₁ (aeval g₁ (LinearMap.mulLeft E g₁).charpoly)` using `Polynomial.aeval_algHom_apply (Algebra.lmul E A₁) g₁ _`. Rewrite `h` using `[h2]`. Simplify using `using LinearMap.congr_fun h 1`. Set `q : Fin (a + b) → E[X]` to `fun k => if (k : ℕ) < a then X ^ (k : ℕ) else X ^ ((k : ℕ) - a) * (LinearMap.mulLeft E g₁).charpoly`. Establish `hd : ∀ k, (q k).natDegree = k`.

Introduce `k`. Distinguish the cases in `hk : (k : ℕ) < a`. Simplify using `[q, hk]`. Simplify using `only [q, hk, if_false]`. Rewrite using `[(monic_X_pow _).natDegree_mul (LinearMap.charpoly_monic _), natDegree_X_pow, hdeg₁]`.

Use linear arithmetic over natural numbers and integers. Establish `hm : ∀ k, (q k).Monic`. Introduce `k`. Distinguish the cases in `hk : (k : ℕ) < a`. Simplify using `only [q, hk, if_true]`.

Conclude with `monic_X_pow _`. Simplify using `only [q, hk, if_false]`. Conclude with `(monic_X_pow _).mul (LinearMap.charpoly_monic _)`. Use `⟨(-1) ^ (a * b), by rw [← mul_pow, neg_one_mul, neg_neg, one_pow], ?_⟩` and prove the remaining obligations. Rewrite using `[det_trace_monic (g₁, g₂) _ q hd hm]`.

Set `M` to `Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂) (aeval (g₁, g₂) (q k) * Fin.addCases (fun i => ((u i, 0) : A₁ × A₂)) (fun j => (0, w j)) l)`. Set `T₁` to `Matrix.of fun k l : Fin a => Algebra.trace E A₁ (g₁ ^ (k : ℕ) * u l)`. Set `T₂` to `Matrix.of fun k l : Fin b => Algebra.trace E A₂ (g₂ ^ (k : ℕ) * w l)`. Set `S` to `Matrix.of fun k l : Fin b => Algebra.trace E A₂ (g₂ ^ (k : ℕ) * aeval g₂ (LinearMap.mulLeft E g₁).charpoly * w l)`. Establish `hblock : M.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks T₁ (Matrix.of fun i j => M (Fin.castAdd b i) (Fin.natAdd a j)) 0 S`.

Use extensionality with `(i | i) (l | l)`. Simplify using `[M, T₁, q, Algebra.trace_prod_apply, aeval_prod_apply]`. Simplify using `[M]`. Simplify using `[M, q, Algebra.trace_prod_apply, aeval_prod_apply, hCH]`. Simplify using `[M, S, q, Algebra.trace_prod_apply, aeval_prod_apply, mul_assoc]`.

Establish `hS : S = T₂ * Algebra.leftMulMatrix w (aeval g₂ (LinearMap.mulLeft E g₁).charpoly)` using `trace_mul_eq (fun k : Fin b => g₂ ^ (k : ℕ)) _ w`. Establish `hres : (Algebra.leftMulMatrix w (aeval g₂ (LinearMap.mulLeft E g₁).charpoly)).det = (-1) ^ (b * a) * resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly`. Rewrite using `[← Polynomial.aeval_algHom_apply, det_aeval _ _ (LinearMap.charpoly_monic _), charpoly_leftMul_basis, hdeg₁]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hS, Matrix.det_mul, hres]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.det_trace_pow_prod : ∀ (E A₁ A₂ : Type) [Field E] [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂) (a b : ℕ) (u : Module.Basis (Fin a) E A₁) (w : Module.Basis (Fin b) E A₂), ((LinearMap.mulLeft E g₁).charpoly * (LinearMap.mulLeft E g₂).charpoly).Separable → ∃ ε : E, ε * ε = 1 ∧ (Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂) ((g₁, g₂) ^ (k : ℕ) * Fin.addCases (fun i => (u i, 0)) (fun j => (0, w j)) l)).det = ε * resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly * (Matrix.of fun k l : Fin a => Algebra.trace E A₁ (g₁ ^ (k : ℕ) * u l)).det * (Matrix.of fun k l : Fin b => Algebra.trace E A₂ (g₂ ^ (k : ℕ) * w l)).det := by
  intro E A₁ A₂ _ _ _ _ _ _ _ g₁ g₂ a b u w _
  classical
  have hdeg₁ : (LinearMap.mulLeft E g₁).charpoly.natDegree = a := by
    rw [LinearMap.charpoly_natDegree, Module.finrank_eq_card_basis u, Fintype.card_fin]
  have hCH : aeval g₁ (LinearMap.mulLeft E g₁).charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft E g₁)
    have h2 : aeval (LinearMap.mulLeft E g₁) (LinearMap.mulLeft E g₁).charpoly =
        Algebra.lmul E A₁ (aeval g₁ (LinearMap.mulLeft E g₁).charpoly) :=
      Polynomial.aeval_algHom_apply (Algebra.lmul E A₁) g₁ _
    rw [h2] at h
    simpa using LinearMap.congr_fun h 1
  let q : Fin (a + b) → E[X] := fun k =>
    if (k : ℕ) < a then X ^ (k : ℕ) else X ^ ((k : ℕ) - a) * (LinearMap.mulLeft E g₁).charpoly
  have hd : ∀ k, (q k).natDegree = k := by
    intro k
    by_cases hk : (k : ℕ) < a
    · simp [q, hk]
    · simp only [q, hk, if_false]
      rw [(monic_X_pow _).natDegree_mul (LinearMap.charpoly_monic _), natDegree_X_pow, hdeg₁]
      omega
  have hm : ∀ k, (q k).Monic := by
    intro k
    by_cases hk : (k : ℕ) < a
    · simp only [q, hk, if_true]
      exact monic_X_pow _
    · simp only [q, hk, if_false]
      exact (monic_X_pow _).mul (LinearMap.charpoly_monic _)
  refine ⟨(-1) ^ (a * b), by rw [← mul_pow, neg_one_mul, neg_neg, one_pow], ?_⟩
  rw [det_trace_monic (g₁, g₂) _ q hd hm]
  let M := Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂)
    (aeval (g₁, g₂) (q k) * Fin.addCases (fun i => ((u i, 0) : A₁ × A₂)) (fun j => (0, w j)) l)
  let T₁ := Matrix.of fun k l : Fin a => Algebra.trace E A₁ (g₁ ^ (k : ℕ) * u l)
  let T₂ := Matrix.of fun k l : Fin b => Algebra.trace E A₂ (g₂ ^ (k : ℕ) * w l)
  let S := Matrix.of fun k l : Fin b =>
    Algebra.trace E A₂ (g₂ ^ (k : ℕ) * aeval g₂ (LinearMap.mulLeft E g₁).charpoly * w l)
  have hblock : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks T₁ (Matrix.of fun i j => M (Fin.castAdd b i) (Fin.natAdd a j)) 0 S := by
    ext (i | i) (l | l)
    · simp [M, T₁, q, Algebra.trace_prod_apply, aeval_prod_apply]
    · simp [M]
    · simp [M, q, Algebra.trace_prod_apply, aeval_prod_apply, hCH]
    · simp [M, S, q, Algebra.trace_prod_apply, aeval_prod_apply, mul_assoc]
  have hS : S = T₂ * Algebra.leftMulMatrix w (aeval g₂ (LinearMap.mulLeft E g₁).charpoly) :=
    trace_mul_eq (fun k : Fin b => g₂ ^ (k : ℕ)) _ w
  have hres : (Algebra.leftMulMatrix w (aeval g₂ (LinearMap.mulLeft E g₁).charpoly)).det =
      (-1) ^ (b * a) * resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly := by
    rw [← Polynomial.aeval_algHom_apply, det_aeval _ _ (LinearMap.charpoly_monic _),
      charpoly_leftMul_basis, hdeg₁]
  calc M.det = (M.submatrix finSumFinEquiv finSumFinEquiv).det :=
        (Matrix.det_submatrix_equiv_self _ _).symm
    _ = T₁.det * S.det := by rw [hblock, Matrix.det_fromBlocks_zero₂₁]
    _ = _ := by
      rw [hS, Matrix.det_mul, hres]
      ring
