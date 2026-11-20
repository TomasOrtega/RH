import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

namespace UpperTheory.V.Loc.SpFlag

open Polynomial

variable {R E : Type} [CommRing R] [CommRing E]

/- English proof (translation)
Use `Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)` and prove the remaining obligations. Rewrite using `[map_add, add_mul, hp, hq, ← mul_add, Matrix.diagonal_add]`. Simplify using `only [Polynomial.eval_add]`. Establish `e : h * Matrix.diagonal c ^ n = X ^ n * h` using `SemiconjBy.pow_right (show SemiconjBy h (Matrix.diagonal c) X from H.symm) n`. Rewrite using `[Polynomial.aeval_monomial, ← Algebra.smul_def, smul_mul_assoc, ← e, Matrix.diagonal_pow, ← mul_smul_comm]`.

Use `congr 1`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij, Polynomial.eval_monomial]`.
-/
theorem aeval_semi {X h : M4 R} {c : Fin 4 → R} (H : X * h = h * Matrix.diagonal c) (p : R[X]) :
    aeval X p * h = h * Matrix.diagonal fun a => p.eval (c a) := by
  refine Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add, add_mul, hp, hq, ← mul_add, Matrix.diagonal_add]
    simp only [Polynomial.eval_add]
  · have e : h * Matrix.diagonal c ^ n = X ^ n * h :=
      SemiconjBy.pow_right (show SemiconjBy h (Matrix.diagonal c) X from H.symm) n
    rw [Polynomial.aeval_monomial, ← Algebra.smul_def, smul_mul_assoc, ← e, Matrix.diagonal_pow,
      ← mul_smul_comm]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij, Polynomial.eval_monomial]

/- English proof (translation)
Use `Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)` and prove the remaining obligations. Rewrite using `[map_add, Matrix.map_add _ (map_add π), hp, hq, Matrix.diagonal_add]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Establish `H' : π.mapMatrix X = Matrix.diagonal fun a => π (c a)` using `H`. Express the relevant statement in the definitionally equal form `π.mapMatrix _ = _`. Rewrite using `[Polynomial.aeval_monomial, map_mul, map_pow, H', Matrix.diagonal_pow, RingHom.mapMatrix_apply, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero π), Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `[Polynomial.eval_monomial]`.
-/
theorem aeval_red (π : R →+* E) {X : M4 R} {c : Fin 4 → R} (H : X.map π = Matrix.diagonal fun a => π (c a)) (p : R[X]) :
    (aeval X p).map π = Matrix.diagonal fun a => π (p.eval (c a)) := by
  refine Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add, Matrix.map_add _ (map_add π), hp, hq, Matrix.diagonal_add]
    congr 1
    funext i
    simp
  · have H' : π.mapMatrix X = Matrix.diagonal fun a => π (c a) := H
    change π.mapMatrix _ = _
    rw [Polynomial.aeval_monomial, map_mul, map_pow, H', Matrix.diagonal_pow, RingHom.mapMatrix_apply,
      Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero π), Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [Polynomial.eval_monomial]

/- English proof (translation)
Use `Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)` and prove the remaining obligations. Rewrite using `[map_add]`. Conclude with `hp.add hq`. Rewrite using `[Polynomial.aeval_monomial]`. Conclude with `(Matrix.blockTriangular_algebraMap a).mul (H.pow n)`.
-/
theorem aeval_tri {X : M4 R} (H : X.BlockTriangular id) (p : R[X]) : (aeval X p).BlockTriangular id := by
  refine Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add]
    exact hp.add hq
  · rw [Polynomial.aeval_monomial]
    exact (Matrix.blockTriangular_algebraMap a).mul (H.pow n)

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Introduce `b _ hb`. Break down `lt_or_gt_of_ne hb with h | h` into its components or cases. Rewrite using `[hA h, zero_mul]`. Rewrite using `[hB h, mul_zero]`.

Simplify using the standard rewrite rules.
-/
theorem tri_mul_diag {A B : M4 R} (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin 4) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

def dd (c : Fin 4 → R) (i : Fin 4) : R := ∏ j ∈ Finset.univ.erase i, (c i - c j)

/- English proof (translation)
Unfold `dd`. Conclude with `Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun j hj => hd i j (Finset.ne_of_mem_erase hj).symm)`.
-/
theorem isUnit_dd {c : Fin 4 → R} (hd : ∀ i j, i ≠ j → IsUnit (c i - c j)) (i : Fin 4) : IsUnit (dd c i) := by
  unfold dd
  exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
    (fun j hj => hd i j (Finset.ne_of_mem_erase hj).symm)

/- English proof (translation)
Rewrite using `[eval_prod]`. Simplify using `only [eval_sub, eval_X, eval_C]`. Use `split_ifs with h`. Substitute `h` using the available equality. Both sides reduce to the same expression.

Conclude with `Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩) (sub_self _)`.
-/
theorem eval_prj (c : Fin 4 → R) (i a : Fin 4) :
    (∏ j ∈ Finset.univ.erase i, (Polynomial.X - C (c j)) : R[X]).eval (c a) = if a = i then dd c i else 0 := by
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  split_ifs with h
  · subst h; rfl
  · exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩) (sub_self _)

/- English proof (translation)
Establish `key : ∀ k, prj c X k * h = h * Matrix.diagonal fun a => if a = k then dd c k else 0`. Introduce `k`. Rewrite using `[prj, aeval_semi H]`. Simplify using `only [eval_prj]`. Establish `hprj : ∀ k, prj c X k = h * Matrix.diagonal (fun a => if a = k then dd c k else 0) * ((h⁻¹ : (M4 R)ˣ) : M4 R)`.

Introduce `k`. Rewrite using `[← key, Units.mul_inv_cancel_right]`. Establish `conj0 : ∀ W : M4 R, (h : M4 R) * W * ((h⁻¹ : (M4 R)ˣ) : M4 R) = 0 ↔ W = 0`. Introduce `W`. Prove the components needed by the constructor for the conclusion.

Introduce `h0`. Establish `e : W = ((h⁻¹ : (M4 R)ˣ) : M4 R) * ((h : M4 R) * W * ((h⁻¹ : (M4 R)ˣ) : M4 R)) * h`. Simplify using `[mul_assoc]`. Rewrite using `[e, h0, mul_zero, zero_mul]`. Introduce `h0`.

Rewrite using `[h0, mul_zero, zero_mul]`. Establish `e : prj c X j * M * prj c X i = (h : M4 R) * (Matrix.diagonal (fun a => if a = j then dd c j else 0) * (((h⁻¹ : (M4 R)ˣ) : M4 R) * M * h) * Matrix.diagonal (fun a => if a = i then dd c i else 0)) * ((h⁻¹ : (M4 R)ˣ) : M4 R)`. Rewrite using `[hprj j, hprj i]`. Simplify using `only [mul_assoc]`. Rewrite using `[e, conj0]`.

Establish `hW : ∀ a b, (Matrix.diagonal (fun a => if a = j then dd c j else 0) * (((h⁻¹ : (M4 R)ˣ) : M4 R) * M * h) * Matrix.diagonal (fun a => if a = i then dd c i else 0)) a b = (if a = j then dd c j else 0) * (((h⁻¹ : (M4 R)ˣ) : M4 R) * M * h) a b * (if b = i then dd c i else 0)`. Introduce `a b`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `h0`.

Establish `h1` using `hW j i`. Rewrite `h1` using `[h0]`. Simplify using `only [Matrix.zero_apply, if_pos rfl] at h1`. Conclude with `(isUnit_dd hd j).mul_right_eq_zero.mp ((isUnit_dd hd i).mul_left_eq_zero.mp h1.symm)`. Introduce `h0`.

Use extensionality with `a b`. Rewrite using `[hW]`. Distinguish the cases in `ha : a = j`. Distinguish the cases in `hb : b = i`. Substitute `ha hb` using the available equality.

Rewrite using `[if_pos rfl, if_pos rfl, h0, mul_zero, zero_mul, Matrix.zero_apply]`. Simplify using `[hb]`. Simplify using `[ha]`.
-/
theorem sandwich {X : M4 R} {h : (M4 R)ˣ} {c : Fin 4 → R} (hd : ∀ i j, i ≠ j → IsUnit (c i - c j))
    (H : X * h = h * Matrix.diagonal c) (M : M4 R) (i j : Fin 4) :
    prj c X j * M * prj c X i = 0 ↔ ((h⁻¹ : (M4 R)ˣ) * M * h : M4 R) j i = 0 := by
  have key : ∀ k, prj c X k * h = h * Matrix.diagonal fun a => if a = k then dd c k else 0 := by
    intro k
    rw [prj, aeval_semi H]
    simp only [eval_prj]
  have hprj : ∀ k, prj c X k =
      h * Matrix.diagonal (fun a => if a = k then dd c k else 0) * ((h⁻¹ : (M4 R)ˣ) : M4 R) := by
    intro k
    rw [← key, Units.mul_inv_cancel_right]
  have conj0 : ∀ W : M4 R, (h : M4 R) * W * ((h⁻¹ : (M4 R)ˣ) : M4 R) = 0 ↔ W = 0 := by
    intro W
    constructor
    · intro h0
      have e : W = ((h⁻¹ : (M4 R)ˣ) : M4 R) * ((h : M4 R) * W * ((h⁻¹ : (M4 R)ˣ) : M4 R)) * h := by
        simp [mul_assoc]
      rw [e, h0, mul_zero, zero_mul]
    · intro h0
      rw [h0, mul_zero, zero_mul]
  have e : prj c X j * M * prj c X i = (h : M4 R) * (Matrix.diagonal (fun a => if a = j then dd c j else 0) *
      (((h⁻¹ : (M4 R)ˣ) : M4 R) * M * h) * Matrix.diagonal (fun a => if a = i then dd c i else 0)) *
      ((h⁻¹ : (M4 R)ˣ) : M4 R) := by
    rw [hprj j, hprj i]
    simp only [mul_assoc]
  rw [e, conj0]
  have hW : ∀ a b, (Matrix.diagonal (fun a => if a = j then dd c j else 0) *
      (((h⁻¹ : (M4 R)ˣ) : M4 R) * M * h) * Matrix.diagonal (fun a => if a = i then dd c i else 0)) a b =
      (if a = j then dd c j else 0) * (((h⁻¹ : (M4 R)ˣ) : M4 R) * M * h) a b * (if b = i then dd c i else 0) := by
    intro a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  constructor
  · intro h0
    have h1 := hW j i
    rw [h0] at h1
    simp only [Matrix.zero_apply, if_pos rfl] at h1
    exact (isUnit_dd hd j).mul_right_eq_zero.mp ((isUnit_dd hd i).mul_left_eq_zero.mp h1.symm)
  · intro h0
    ext a b
    rw [hW]
    by_cases ha : a = j
    · by_cases hb : b = i
      · subst ha hb
        rw [if_pos rfl, if_pos rfl, h0, mul_zero, zero_mul, Matrix.zero_apply]
      · simp [hb]
    · simp [ha]

/- English proof (translation)
Establish `eig : ∀ b, X * prj c X b = c b • prj c X b`. Introduce `b`. Establish `h0 : aeval X ((Polynomial.X - C (c b)) * ∏ j ∈ Finset.univ.erase b, (Polynomial.X - C (c j))) = 0`. Rewrite using `[Finset.mul_prod_erase _ (fun j => Polynomial.X - C (c j)) (Finset.mem_univ b), ← hc, Matrix.aeval_self_charpoly]`. Rewrite `h0` using `[map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, sub_mul, sub_eq_zero, ← Algebra.smul_def]`.

Conclude with `h0`. Take `⟨u, hu⟩ : ∃ u : Fin 4 → R, u = fun b => (((isUnit_dd hd b).unit⁻¹ : Rˣ) : R)` from `⟨_, rfl⟩`. Establish `hu1 : ∀ b, u b * dd c b = 1` using `fun b => by`. Rewrite using `[hu]`. Conclude with `(isUnit_dd hd b).val_inv_mul`.

Establish `htri : X.BlockTriangular id → ∀ b, (prj c X b).BlockTriangular id` using `fun hT b => aeval_tri hT _`. Take `⟨K, hK⟩ : ∃ K : M4 R, K = Matrix.of fun a b => u b * prj c X b a b` from `⟨_, rfl⟩`. Establish `hXK : X * K = K * Matrix.diagonal c`. Use extensionality with `a b`. Establish `e` using `congrFun (congrFun (eig b) a) b`.

Rewrite `e` using `[Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[Matrix.mul_diagonal, Matrix.mul_apply]`. Simplify using `only [hK, Matrix.of_apply]`. Rewrite using `[show (∑ m, X a m * (u b * prj c X b m b)) = u b * ∑ m, X a m * prj c X b m b by`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun _ _ => by ring, e]`. Expand and normalize the polynomial expressions, which then agree. Establish `hred : ∀ b a, π (prj c X b a b) = if a = b then π (dd c b) else 0`. Introduce `b a`. Establish `e` using `congrFun (congrFun (aeval_red π H (∏ j ∈ Finset.univ.erase b, (Polynomial.X - C (c j)))) a) b`.

Rewrite `e` using `[Matrix.map_apply]`. Rewrite using `[prj, e, Matrix.diagonal_apply, eval_prj]`. Apply the tactic sequence `split_ifs <;> simp_all`. Establish `hKmap : K.map π = 1`. Use extensionality with `a b`.

Rewrite using `[Matrix.map_apply]`. Simplify using `only [hK, Matrix.of_apply, map_mul, hred, Matrix.one_apply]`. Use `split_ifs with hab`. Rewrite using `[← map_mul, hu1, map_one]`. Rewrite using `[mul_zero]`.

Establish `hKu : IsUnit K`. Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Apply `hπ` to reduce the goal to its premises. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hKmap, Matrix.det_one]`. Use `⟨hKu.unit, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[IsUnit.unit_spec]`. Conclude with `hXK`. Rewrite using `[IsUnit.unit_spec]`. Conclude with `hKmap`. Introduce `hT a b hab`.

Rewrite using `[IsUnit.unit_spec, hK, Matrix.of_apply, htri hT b hab, mul_zero]`.
-/
theorem exists_diag (π : R →+* E) (hπ : ∀ a, π a = 1 → IsUnit a) {X : M4 R} {c : Fin 4 → R}
    (hd : ∀ i j, i ≠ j → IsUnit (c i - c j)) (hc : X.charpoly = ∏ j, (Polynomial.X - C (c j)))
    (H : X.map π = Matrix.diagonal fun a => π (c a)) :
    ∃ k : (M4 R)ˣ, X * k = k * Matrix.diagonal c ∧ (k : M4 R).map π = 1 ∧
      (X.BlockTriangular id → (k : M4 R).BlockTriangular id) := by
  classical
  have eig : ∀ b, X * prj c X b = c b • prj c X b := by
    intro b
    have h0 : aeval X ((Polynomial.X - C (c b)) * ∏ j ∈ Finset.univ.erase b, (Polynomial.X - C (c j))) = 0 := by
      rw [Finset.mul_prod_erase _ (fun j => Polynomial.X - C (c j)) (Finset.mem_univ b), ← hc,
        Matrix.aeval_self_charpoly]
    rw [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, sub_mul, sub_eq_zero,
      ← Algebra.smul_def] at h0
    exact h0
  obtain ⟨u, hu⟩ : ∃ u : Fin 4 → R, u = fun b => (((isUnit_dd hd b).unit⁻¹ : Rˣ) : R) := ⟨_, rfl⟩
  have hu1 : ∀ b, u b * dd c b = 1 := fun b => by
    rw [hu]
    exact (isUnit_dd hd b).val_inv_mul
  have htri : X.BlockTriangular id → ∀ b, (prj c X b).BlockTriangular id := fun hT b => aeval_tri hT _
  obtain ⟨K, hK⟩ : ∃ K : M4 R, K = Matrix.of fun a b => u b * prj c X b a b := ⟨_, rfl⟩
  have hXK : X * K = K * Matrix.diagonal c := by
    ext a b
    have e := congrFun (congrFun (eig b) a) b
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at e
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [hK, Matrix.of_apply]
    rw [show (∑ m, X a m * (u b * prj c X b m b)) = u b * ∑ m, X a m * prj c X b m b by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring, e]
    ring
  have hred : ∀ b a, π (prj c X b a b) = if a = b then π (dd c b) else 0 := by
    intro b a
    have e := congrFun (congrFun (aeval_red π H (∏ j ∈ Finset.univ.erase b, (Polynomial.X - C (c j)))) a) b
    rw [Matrix.map_apply] at e
    rw [prj, e, Matrix.diagonal_apply, eval_prj]
    split_ifs <;> simp_all
  have hKmap : K.map π = 1 := by
    ext a b
    rw [Matrix.map_apply]
    simp only [hK, Matrix.of_apply, map_mul, hred, Matrix.one_apply]
    split_ifs with hab
    · rw [← map_mul, hu1, map_one]
    · rw [mul_zero]
  have hKu : IsUnit K := by
    rw [Matrix.isUnit_iff_isUnit_det]
    apply hπ
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hKmap, Matrix.det_one]
  refine ⟨hKu.unit, ?_, ?_, ?_⟩
  · rw [IsUnit.unit_spec]
    exact hXK
  · rw [IsUnit.unit_spec]
    exact hKmap
  · intro hT a b hab
    rw [IsUnit.unit_spec, hK, Matrix.of_apply, htri hT b hab, mul_zero]

/- English proof (translation)
Use extensionality with `i j`. Establish `hs : ∀ k : Fin 4, (sgn k : R) * sgn k = 1` using `fun k => by`. Establish `: sgn k * sgn k = 1` using `by revert k; decide`. Rewrite using `[← Int.cast_mul, this, Int.cast_one]`. Simplify using `only [adj_apply, Matrix.mul_apply, zsmul_eq_mul, Int.cast_mul, Finset.mul_sum]`.

Conclude with `Fintype.sum_equiv Fin.revPerm _ _ (fun k => by`. Simplify using `only [Fin.revPerm_apply, Fin.rev_rev]`. Take the linear combination `(-((sgn i : R) * sgn j * A j.rev k * B k i.rev)) * hs k.rev)`.
-/
theorem adj_mul (A B : M4 R) : adj (A * B) = adj B * adj A := by
  ext i j
  have hs : ∀ k : Fin 4, (sgn k : R) * sgn k = 1 := fun k => by
    have : sgn k * sgn k = 1 := by revert k; decide
    rw [← Int.cast_mul, this, Int.cast_one]
  simp only [adj_apply, Matrix.mul_apply, zsmul_eq_mul, Int.cast_mul, Finset.mul_sum]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun k => by
    simp only [Fin.revPerm_apply, Fin.rev_rev]
    linear_combination (-((sgn i : R) * sgn j * A j.rev k * B k i.rev)) * hs k.rev)

/- English proof (translation)
Use extensionality with `i j`. Establish `hr : ∀ k : Fin 4, (sgn k.rev : R) * sgn k = -1` using `fun k => by`. Establish `: sgn k.rev * sgn k = -1` using `by revert k; decide`. Rewrite using `[← Int.cast_mul, this, Int.cast_neg, Int.cast_one]`. Simplify using `only [adj_apply, Fin.rev_rev, zsmul_eq_mul, Int.cast_mul]`.

Take the linear combination `(A i j * sgn j.rev * sgn j) * hr i - A i j * hr j`.
-/
theorem adj_adj (A : M4 R) : adj (adj A) = A := by
  ext i j
  have hr : ∀ k : Fin 4, (sgn k.rev : R) * sgn k = -1 := fun k => by
    have : sgn k.rev * sgn k = -1 := by revert k; decide
    rw [← Int.cast_mul, this, Int.cast_neg, Int.cast_one]
  simp only [adj_apply, Fin.rev_rev, zsmul_eq_mul, Int.cast_mul]
  linear_combination (A i j * sgn j.rev * sgn j) * hr i - A i j * hr j

/- English proof (translation)
Use extensionality with `i j`. Establish `hs : ∀ k : Fin 4, (sgn k : R) * sgn k = 1` using `fun k => by`. Establish `: sgn k * sgn k = 1` using `by revert k; decide`. Rewrite using `[← Int.cast_mul, this, Int.cast_one]`. Simplify using `only [adj_apply, Matrix.diagonal_apply, Fin.rev_inj, zsmul_eq_mul, Int.cast_mul]`.

Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[hs]`. Simplify using `[h, Ne.symm h]`.
-/
theorem adj_diagonal (c : Fin 4 → R) : adj (Matrix.diagonal c) = Matrix.diagonal fun i => c i.rev := by
  ext i j
  have hs : ∀ k : Fin 4, (sgn k : R) * sgn k = 1 := fun k => by
    have : sgn k * sgn k = 1 := by revert k; decide
    rw [← Int.cast_mul, this, Int.cast_one]
  simp only [adj_apply, Matrix.diagonal_apply, Fin.rev_inj, zsmul_eq_mul, Int.cast_mul]
  by_cases h : j = i
  · subst h
    simp [hs]
  · simp [h, Ne.symm h]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[adj_apply]`.
-/
theorem adj_map (π : R →+* E) (A : M4 R) : (adj A).map π = adj (A.map π) := by
  ext i j
  simp [adj_apply]

/- English proof (translation)
Take `⟨N, hN⟩ : ∃ N : M4 R, N = adj (k : M4 R) * k` from `⟨_, rfl⟩`. Establish `hadj : adj (k : M4 R) * adj X = Matrix.diagonal (fun i : Fin 4 => c i.rev) * adj (k : M4 R)`. Rewrite using `[← adj_mul, hk, adj_mul, adj_diagonal]`. Establish `hGX : adj X * X = ν • 1` using `hX`. Establish `hrel : ν • N = Matrix.diagonal (fun i : Fin 4 => c i.rev) * N * Matrix.diagonal c`.

Establish `e : adj (k : M4 R) * adj X * (X * (k : M4 R)) = Matrix.diagonal (fun i : Fin 4 => c i.rev) * adj (k : M4 R) * ((k : M4 R) * Matrix.diagonal c)`. Rewrite using `[hadj, hk]`. Rewrite using `[hN]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hGX, mul_smul_comm, mul_one, smul_mul_assoc]`.

Use `_ = _ := by simpa only [mul_assoc] using e`. Establish `hoff : ∀ a b, a ≠ b → N a b = 0`. Introduce `a b hab`. Establish `e` using `congrFun (congrFun hrel a) b`. Rewrite `e` using `[Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal, Matrix.diagonal_mul, ← hν a]`.

Establish `e2 : c a.rev * (N a b * (c a - c b)) = 0` using `by linear_combination e`. Conclude with `(hd a b hab).mul_left_eq_zero.mp ((hu a.rev).mul_right_eq_zero.mp e2)`. Establish `hsym : adj N = N` using `by rw [hN, adj_mul, adj_adj]`. Establish `hs : ∀ b : Fin 4, sgn b * sgn b = 1` using `by decide`. Establish `hdiag : ∀ a, N a.rev a.rev = N a a`.

Introduce `a`. Establish `e` using `congrFun (congrFun hsym a) a`. Rewrite `e` using `[adj_apply, hs a, one_smul]`. Conclude with `e`. Establish `hNmap : N.map π = 1`.

Express the relevant statement in the definitionally equal form `π.mapMatrix N = 1`. Rewrite using `[hN, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, adj_map, hk1, mul_one, ← Matrix.diagonal_one, adj_diagonal]`. Establish `hNaa : ∀ a, π (N a a) = 1` using `fun a => by`. Establish `e` using `congrFun (congrFun hNmap a) a`. Simplify using `using e`.

Establish `hNu : ∀ a, IsUnit (N a a)` using `fun a => hπ _ (hNaa a)`. Take `⟨w, hw⟩ : ∃ w : Fin 4 → R, w = fun a => (((hNu a).unit⁻¹ : Rˣ) : R)` from `⟨_, rfl⟩`. Establish `hw1 : ∀ a, w a * N a a = 1` using `fun a => by`. Rewrite using `[hw]`. Conclude with `(hNu a).val_inv_mul`.

Establish `hwu : ∀ a, IsUnit (w a)` using `fun a => by`. Rewrite using `[hw]`. Conclude with `Units.isUnit _`. Establish `hwπ : ∀ a, π (w a) = 1` using `fun a => by`. Establish `e` using `congrArg π (hw1 a)`.

Rewrite `e` using `[map_mul, map_one, hNaa, mul_one]`. Conclude with `e`. Take `⟨d, hd'⟩ : ∃ d : Fin 4 → R, d = fun a : Fin 4 => if (a : ℕ) < 2 then w a else 1` from `⟨_, rfl⟩`. Establish `hdu : ∀ a, IsUnit (d a)` using `fun a => by`. Rewrite using `[hd']`.

Simplify using `only`. Use `split_ifs`. Conclude with `hwu a`. Conclude with `isUnit_one`. Establish `hdπ : ∀ a, π (d a) = 1` using `fun a => by`.

Rewrite using `[hd']`. Simplify using `only`. Use `split_ifs`. Conclude with `hwπ a`. Conclude with `map_one π`.

Establish `hkey : ∀ a, d a.rev * N a a * d a = 1`. Introduce `a`. Rewrite using `[hd']`. Simplify using `only`. Distinguish the cases in `ha : (a : ℕ) < 2`.

Establish `hr : ¬ ((a.rev : ℕ) < 2)`. Rewrite using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hr, if_pos ha, one_mul, mul_comm, hw1]`. Establish `hr : (a.rev : ℕ) < 2`.

Rewrite using `[Fin.val_rev]`. Use `a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_pos hr, if_neg ha, mul_one, ← hdiag a, hw1]`. Establish `hHu : IsUnit ((k : M4 R) * Matrix.diagonal d)` using `k.isUnit.mul (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr hdu))`.

Use `⟨hHu.unit, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, ← mul_assoc, hk, mul_assoc, mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Conclude with `mul_comm _ _`.

Rewrite using `[IsUnit.unit_spec]`. Express the relevant statement in the definitionally equal form `π.mapMatrix ((k : M4 R) * Matrix.diagonal d) = 1`. Rewrite using `[map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hk1, one_mul, Matrix.diagonal_map (map_zero π)]`. Simplify using `only [hdπ]`. Conclude with `Matrix.diagonal_one`.

Rewrite using `[IsUnit.unit_spec, IsGSp, adj_mul, adj_diagonal, one_smul]`. Establish `e : Matrix.diagonal (fun i : Fin 4 => d i.rev) * adj (k : M4 R) * ((k : M4 R) * Matrix.diagonal d) = Matrix.diagonal (fun i : Fin 4 => d i.rev) * N * Matrix.diagonal d`. Rewrite using `[hN]`. Simplify using `only [mul_assoc]`. Rewrite using `[e]`.

Use extensionality with `a b`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.one_apply]`. Use `split_ifs with hab`. Substitute `hab` using the available equality. Conclude with `hkey a`.

Rewrite using `[hoff a b hab, mul_zero, zero_mul]`.
-/
theorem exists_symp (π : R →+* E) (hπ : ∀ a, π a = 1 → IsUnit a) {X : M4 R} {c : Fin 4 → R} {ν : R}
    (hd : ∀ i j, i ≠ j → IsUnit (c i - c j)) (hu : ∀ i, IsUnit (c i)) (hν : ∀ i, c i.rev * c i = ν) (hX : IsGSp ν X)
    {k : (M4 R)ˣ} (hk : X * k = k * Matrix.diagonal c) (hk1 : (k : M4 R).map π = 1) :
    ∃ h : (M4 R)ˣ, X * h = h * Matrix.diagonal c ∧ (h : M4 R).map π = 1 ∧ IsGSp 1 (h : M4 R) := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : M4 R, N = adj (k : M4 R) * k := ⟨_, rfl⟩
  have hadj : adj (k : M4 R) * adj X = Matrix.diagonal (fun i : Fin 4 => c i.rev) * adj (k : M4 R) := by
    rw [← adj_mul, hk, adj_mul, adj_diagonal]
  have hGX : adj X * X = ν • 1 := hX
  have hrel : ν • N = Matrix.diagonal (fun i : Fin 4 => c i.rev) * N * Matrix.diagonal c := by
    have e : adj (k : M4 R) * adj X * (X * (k : M4 R)) =
        Matrix.diagonal (fun i : Fin 4 => c i.rev) * adj (k : M4 R) * ((k : M4 R) * Matrix.diagonal c) := by
      rw [hadj, hk]
    rw [hN]
    calc ν • (adj (k : M4 R) * k) = adj (k : M4 R) * (adj X * X) * k := by
          rw [hGX, mul_smul_comm, mul_one, smul_mul_assoc]
      _ = _ := by simpa only [mul_assoc] using e
  have hoff : ∀ a b, a ≠ b → N a b = 0 := by
    intro a b hab
    have e := congrFun (congrFun hrel a) b
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal, Matrix.diagonal_mul, ← hν a] at e
    have e2 : c a.rev * (N a b * (c a - c b)) = 0 := by linear_combination e
    exact (hd a b hab).mul_left_eq_zero.mp ((hu a.rev).mul_right_eq_zero.mp e2)
  have hsym : adj N = N := by rw [hN, adj_mul, adj_adj]
  have hs : ∀ b : Fin 4, sgn b * sgn b = 1 := by decide
  have hdiag : ∀ a, N a.rev a.rev = N a a := by
    intro a
    have e := congrFun (congrFun hsym a) a
    rw [adj_apply, hs a, one_smul] at e
    exact e
  have hNmap : N.map π = 1 := by
    change π.mapMatrix N = 1
    rw [hN, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, adj_map, hk1, mul_one,
      ← Matrix.diagonal_one, adj_diagonal]
  have hNaa : ∀ a, π (N a a) = 1 := fun a => by
    have e := congrFun (congrFun hNmap a) a
    simpa using e
  have hNu : ∀ a, IsUnit (N a a) := fun a => hπ _ (hNaa a)
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → R, w = fun a => (((hNu a).unit⁻¹ : Rˣ) : R) := ⟨_, rfl⟩
  have hw1 : ∀ a, w a * N a a = 1 := fun a => by
    rw [hw]
    exact (hNu a).val_inv_mul
  have hwu : ∀ a, IsUnit (w a) := fun a => by
    rw [hw]
    exact Units.isUnit _
  have hwπ : ∀ a, π (w a) = 1 := fun a => by
    have e := congrArg π (hw1 a)
    rw [map_mul, map_one, hNaa, mul_one] at e
    exact e
  obtain ⟨d, hd'⟩ : ∃ d : Fin 4 → R, d = fun a : Fin 4 => if (a : ℕ) < 2 then w a else 1 := ⟨_, rfl⟩
  have hdu : ∀ a, IsUnit (d a) := fun a => by
    rw [hd']
    dsimp only
    split_ifs
    · exact hwu a
    · exact isUnit_one
  have hdπ : ∀ a, π (d a) = 1 := fun a => by
    rw [hd']
    dsimp only
    split_ifs
    · exact hwπ a
    · exact map_one π
  have hkey : ∀ a, d a.rev * N a a * d a = 1 := by
    intro a
    rw [hd']
    dsimp only
    by_cases ha : (a : ℕ) < 2
    · have hr : ¬ ((a.rev : ℕ) < 2) := by
        rw [Fin.val_rev]
        omega
      rw [if_neg hr, if_pos ha, one_mul, mul_comm, hw1]
    · have hr : (a.rev : ℕ) < 2 := by
        rw [Fin.val_rev]
        have := a.isLt
        omega
      rw [if_pos hr, if_neg ha, mul_one, ← hdiag a, hw1]
  have hHu : IsUnit ((k : M4 R) * Matrix.diagonal d) :=
    k.isUnit.mul (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr hdu))
  refine ⟨hHu.unit, ?_, ?_, ?_⟩
  · rw [IsUnit.unit_spec, ← mul_assoc, hk, mul_assoc, mul_assoc, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    exact mul_comm _ _
  · rw [IsUnit.unit_spec]
    change π.mapMatrix ((k : M4 R) * Matrix.diagonal d) = 1
    rw [map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hk1, one_mul,
      Matrix.diagonal_map (map_zero π)]
    simp only [hdπ]
    exact Matrix.diagonal_one
  · rw [IsUnit.unit_spec, IsGSp, adj_mul, adj_diagonal, one_smul]
    have e : Matrix.diagonal (fun i : Fin 4 => d i.rev) * adj (k : M4 R) * ((k : M4 R) * Matrix.diagonal d) =
        Matrix.diagonal (fun i : Fin 4 => d i.rev) * N * Matrix.diagonal d := by
      rw [hN]
      simp only [mul_assoc]
    rw [e]
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.one_apply]
    split_ifs with hab
    · subst hab
      exact hkey a
    · rw [hoff a b hab, mul_zero, zero_mul]

/- English proof (translation)
Establish `conj_mul : ∀ (u : (M4 R)ˣ) (A B : M4 R), ((u⁻¹ : (M4 R)ˣ) : M4 R) * (A * B) * (u : M4 R) = (((u⁻¹ : (M4 R)ˣ) : M4 R) * A * (u : M4 R)) * (((u⁻¹ : (M4 R)ˣ) : M4 R) * B * (u : M4 R))`. Introduce `u A B`. Simplify using `only [mul_assoc, Units.mul_inv_cancel_left]`. Establish `conj_sub : ∀ (u : (M4 R)ˣ) (A : M4 R) (a : R), ((u⁻¹ : (M4 R)ˣ) : M4 R) * (A - a • 1) * (u : M4 R) = ((u⁻¹ : (M4 R)ˣ) : M4 R) * A * (u : M4 R) - a • 1`. Introduce `u A a`.

Rewrite using `[mul_sub, sub_mul, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.inv_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `hO`. Take `⟨k, hk, hk1, -⟩` from `exists_diag π hπ hd hO.charpoly hred`. Take `⟨h, hh, hh1, hhS⟩` from `exists_symp π hπ hd hu hν hX hk hk1`.

Establish `htri : ∀ g, (((h⁻¹ : (M4 R)ˣ) : M4 R) * r g * (h : M4 R)).BlockTriangular id` using `fun g a b hab => (sandwich hd hh (r g) b a).mp (hO.stable g b a hab)`. Establish `hdm : ∀ g g' i, (((h⁻¹ : (M4 R)ˣ) : M4 R) * r (g * g') * (h : M4 R)) i i = (((h⁻¹ : (M4 R)ˣ) : M4 R) * r g * (h : M4 R)) i i * (((h⁻¹ : (M4 R)ˣ) : M4 R) * r g' * (h : M4 R)) i i`. Introduce `g g' i`. Rewrite using `[map_mul, conj_mul]`. Conclude with `tri_mul_diag (htri g) (htri g') i`.

Establish `hd1 : ∀ i, (((h⁻¹ : (M4 R)ˣ) : M4 R) * r 1 * (h : M4 R)) i i = 1`. Introduce `i`. Rewrite using `[map_one, mul_one, Units.inv_mul, Matrix.one_apply_eq]`. Set `κ : Fin 4 → H →* Rˣ` to `fun i => { toFun := fun g => ⟨(((h⁻¹ : (M4 R)ˣ) : M4 R) * r g * (h : M4 R)) i i, (((h⁻¹ : (M4 R)ˣ) : M4 R) * r g⁻¹ * (h : M4 R)) i i, by rw [← hdm, mul_inv_cancel, hd1], by rw [← hdm, inv_mul_cancel, hd1]⟩ map_one' := Units.ext (hd1 i) map_mul' := fun g g' => Units.ext (hdm g g' …`. Use `⟨h, κ, hhS, hh1, fun g => ⟨fun a b hab => htri g hab, fun i => rfl⟩, fun i s hs' => ?_⟩` and prove the remaining obligations.

Establish `e` using `(sandwich hd hh (r s - ps i s • 1) i i).mp (hO.inert s hs' i)`. Rewrite `e` using `[conj_sub, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, sub_eq_zero]`. Conclude with `e`. Introduce and unpack `⟨h, κ, -, hh1, hF, hκ⟩`. Establish `hG : ∀ g, (((h⁻¹ : (M4 R)ˣ) : M4 R) * r g * (h : M4 R)).BlockTriangular id` using `fun g a b hab => (hF g).1 a b hab`.

Establish `hTd : ∀ i, (((h⁻¹ : (M4 R)ˣ) : M4 R) * r s₀ * (h : M4 R)) i i = ps i s₀` using `fun i => by`. Rewrite using `[(hF s₀).2 i, hκ i s₀ hs]`. Establish `hcT : (((h⁻¹ : (M4 R)ˣ) : M4 R) * r s₀ * (h : M4 R)).charpoly = ∏ j, (Polynomial.X - C (ps j s₀))`. Rewrite using `[Matrix.charpoly_of_isUpperTriangular _ (hG s₀)]`. Simplify using `only [hTd]`.

Establish `hc : (r s₀).charpoly = ∏ j, (Polynomial.X - C (ps j s₀))`. Rewrite using `[← hcT, Matrix.coe_units_inv, Matrix.charpoly_units_conj']`. Establish `hinv1 : ((h⁻¹ : (M4 R)ˣ) : M4 R).map π = 1`. Establish `e : π.mapMatrix (((h⁻¹ : (M4 R)ˣ) : M4 R) * (h : M4 R)) = 1`. Rewrite using `[Units.inv_mul, map_one]`.

Rewrite `e` using `[map_mul]`. Express the relevant statement in the definitionally equal form `((h⁻¹ : (M4 R)ˣ) : M4 R).map π * (h : M4 R).map π = 1 at e`. Rewrite `e` using `[hh1, mul_one]`. Conclude with `e`. Establish `hTred : (((h⁻¹ : (M4 R)ˣ) : M4 R) * r s₀ * (h : M4 R)).map π = Matrix.diagonal fun a => π (ps a s₀)`.

Express the relevant statement in the definitionally equal form `π.mapMatrix _ = _`. Rewrite using `[map_mul, map_mul]`. Express the relevant statement in the definitionally equal form `((h⁻¹ : (M4 R)ˣ) : M4 R).map π * (r s₀).map π * (h : M4 R).map π = _`. Rewrite using `[hinv1, hh1, hred, one_mul, mul_one]`. Take `⟨k, hk, -, hktri⟩` from `exists_diag π hπ hd hcT hTred`.

Establish `hkt` using `hktri (hG s₀)`. Establish `hkinv : ((k⁻¹ : (M4 R)ˣ) : M4 R).BlockTriangular id`. Rewrite using `[Matrix.coe_units_inv]`. Use `letI := k.invertible`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hkt`.

Establish `hh' : r s₀ * ((h * k : (M4 R)ˣ) : M4 R) = ((h * k : (M4 R)ˣ) : M4 R) * Matrix.diagonal fun a => ps a s₀`. Rewrite using `[Units.val_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc, Units.mul_inv_cancel_left]`. Use `_ = (h : M4 R) * ((k : M4 R) * Matrix.diagonal fun a => ps a s₀) := by rw [hk]`.

Use `_ = _ := by rw [mul_assoc]`. Establish `hconj : ∀ M : M4 R, (((h * k)⁻¹ : (M4 R)ˣ) : M4 R) * M * ((h * k : (M4 R)ˣ) : M4 R) = ((k⁻¹ : (M4 R)ˣ) : M4 R) * (((h⁻¹ : (M4 R)ˣ) : M4 R) * M * (h : M4 R)) * (k : M4 R)`. Introduce `M`. Rewrite using `[mul_inv_rev, Units.val_mul, Units.val_mul]`. Simplify using `only [mul_assoc]`.

Use `⟨hc, fun g i j hij => ?_, fun s hs' i => ?_⟩` and prove the remaining obligations. Rewrite using `[sandwich hd hh' (r g) i j, hconj]`. Conclude with `((hkinv.mul (hG g)).mul hkt) hij`. Rewrite using `[sandwich hd hh' _ i i, hconj, conj_sub h, conj_sub k, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, sub_eq_zero, tri_mul_diag (hkinv.mul (hG s)) hkt, tri_mul_diag hkinv (hG s), (hF s).2 i, hκ i s hs']`. Establish `e1 : ((k⁻¹ : (M4 R)ˣ) : M4 R) i i * (k : M4 R) i i = 1`.

Rewrite using `[← tri_mul_diag hkinv hkt, Units.inv_mul, Matrix.one_apply_eq]`. Take the linear combination `(ps i s) * e1`.
-/
theorem ord_iff {H : Type} [Group H] (π : R →+* E) (hπ : ∀ a, π a = 1 → IsUnit a) (I : Subgroup H) (ps : Fin 4 → H → R)
    {s₀ : H} (hs : s₀ ∈ I) (r : H →* M4 R) {ν : R}
    (hd : ∀ i j, i ≠ j → IsUnit (ps i s₀ - ps j s₀)) (hu : ∀ i, IsUnit (ps i s₀)) (hν : ∀ i, ps i.rev s₀ * ps i s₀ = ν)
    (hX : IsGSp ν (r s₀)) (hred : (r s₀).map π = Matrix.diagonal fun a => π (ps a s₀)) :
    Ord I ps s₀ r ↔ ∃ (h : (M4 R)ˣ) (κ : Fin 4 → H →* Rˣ), IsGSp 1 (h : M4 R) ∧ (h : M4 R).map π = 1 ∧ FlagIn r h κ ∧
      ∀ i, ∀ s ∈ I, (κ i s : R) = ps i s := by
  classical
  have conj_mul : ∀ (u : (M4 R)ˣ) (A B : M4 R),
      ((u⁻¹ : (M4 R)ˣ) : M4 R) * (A * B) * (u : M4 R) =
        (((u⁻¹ : (M4 R)ˣ) : M4 R) * A * (u : M4 R)) * (((u⁻¹ : (M4 R)ˣ) : M4 R) * B * (u : M4 R)) := by
    intro u A B
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  have conj_sub : ∀ (u : (M4 R)ˣ) (A : M4 R) (a : R),
      ((u⁻¹ : (M4 R)ˣ) : M4 R) * (A - a • 1) * (u : M4 R) =
        ((u⁻¹ : (M4 R)ˣ) : M4 R) * A * (u : M4 R) - a • 1 := by
    intro u A a
    rw [mul_sub, sub_mul, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.inv_mul]
  constructor
  · intro hO
    obtain ⟨k, hk, hk1, -⟩ := exists_diag π hπ hd hO.charpoly hred
    obtain ⟨h, hh, hh1, hhS⟩ := exists_symp π hπ hd hu hν hX hk hk1
    have htri : ∀ g, (((h⁻¹ : (M4 R)ˣ) : M4 R) * r g * (h : M4 R)).BlockTriangular id :=
      fun g a b hab => (sandwich hd hh (r g) b a).mp (hO.stable g b a hab)
    have hdm : ∀ g g' i, (((h⁻¹ : (M4 R)ˣ) : M4 R) * r (g * g') * (h : M4 R)) i i =
        (((h⁻¹ : (M4 R)ˣ) : M4 R) * r g * (h : M4 R)) i i *
          (((h⁻¹ : (M4 R)ˣ) : M4 R) * r g' * (h : M4 R)) i i := by
      intro g g' i
      rw [map_mul, conj_mul]
      exact tri_mul_diag (htri g) (htri g') i
    have hd1 : ∀ i, (((h⁻¹ : (M4 R)ˣ) : M4 R) * r 1 * (h : M4 R)) i i = 1 := by
      intro i
      rw [map_one, mul_one, Units.inv_mul, Matrix.one_apply_eq]
    let κ : Fin 4 → H →* Rˣ := fun i =>
      { toFun := fun g => ⟨(((h⁻¹ : (M4 R)ˣ) : M4 R) * r g * (h : M4 R)) i i,
          (((h⁻¹ : (M4 R)ˣ) : M4 R) * r g⁻¹ * (h : M4 R)) i i,
          by rw [← hdm, mul_inv_cancel, hd1], by rw [← hdm, inv_mul_cancel, hd1]⟩
        map_one' := Units.ext (hd1 i)
        map_mul' := fun g g' => Units.ext (hdm g g' i) }
    refine ⟨h, κ, hhS, hh1, fun g => ⟨fun a b hab => htri g hab, fun i => rfl⟩, fun i s hs' => ?_⟩
    have e := (sandwich hd hh (r s - ps i s • 1) i i).mp (hO.inert s hs' i)
    rw [conj_sub, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      sub_eq_zero] at e
    exact e
  · rintro ⟨h, κ, -, hh1, hF, hκ⟩
    have hG : ∀ g, (((h⁻¹ : (M4 R)ˣ) : M4 R) * r g * (h : M4 R)).BlockTriangular id :=
      fun g a b hab => (hF g).1 a b hab
    have hTd : ∀ i, (((h⁻¹ : (M4 R)ˣ) : M4 R) * r s₀ * (h : M4 R)) i i = ps i s₀ := fun i => by
      rw [(hF s₀).2 i, hκ i s₀ hs]
    have hcT : (((h⁻¹ : (M4 R)ˣ) : M4 R) * r s₀ * (h : M4 R)).charpoly =
        ∏ j, (Polynomial.X - C (ps j s₀)) := by
      rw [Matrix.charpoly_of_isUpperTriangular _ (hG s₀)]
      simp only [hTd]
    have hc : (r s₀).charpoly = ∏ j, (Polynomial.X - C (ps j s₀)) := by
      rw [← hcT, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
    have hinv1 : ((h⁻¹ : (M4 R)ˣ) : M4 R).map π = 1 := by
      have e : π.mapMatrix (((h⁻¹ : (M4 R)ˣ) : M4 R) * (h : M4 R)) = 1 := by
        rw [Units.inv_mul, map_one]
      rw [map_mul] at e
      change ((h⁻¹ : (M4 R)ˣ) : M4 R).map π * (h : M4 R).map π = 1 at e
      rw [hh1, mul_one] at e
      exact e
    have hTred : (((h⁻¹ : (M4 R)ˣ) : M4 R) * r s₀ * (h : M4 R)).map π =
        Matrix.diagonal fun a => π (ps a s₀) := by
      change π.mapMatrix _ = _
      rw [map_mul, map_mul]
      change ((h⁻¹ : (M4 R)ˣ) : M4 R).map π * (r s₀).map π * (h : M4 R).map π = _
      rw [hinv1, hh1, hred, one_mul, mul_one]
    obtain ⟨k, hk, -, hktri⟩ := exists_diag π hπ hd hcT hTred
    have hkt := hktri (hG s₀)
    have hkinv : ((k⁻¹ : (M4 R)ˣ) : M4 R).BlockTriangular id := by
      rw [Matrix.coe_units_inv]
      letI := k.invertible
      exact Matrix.blockTriangular_inv_of_blockTriangular hkt
    have hh' : r s₀ * ((h * k : (M4 R)ˣ) : M4 R) =
        ((h * k : (M4 R)ˣ) : M4 R) * Matrix.diagonal fun a => ps a s₀ := by
      rw [Units.val_mul]
      calc r s₀ * ((h : M4 R) * (k : M4 R))
          = (h : M4 R) * ((((h⁻¹ : (M4 R)ˣ) : M4 R) * r s₀ * (h : M4 R)) * (k : M4 R)) := by
            simp only [mul_assoc, Units.mul_inv_cancel_left]
        _ = (h : M4 R) * ((k : M4 R) * Matrix.diagonal fun a => ps a s₀) := by rw [hk]
        _ = _ := by rw [mul_assoc]
    have hconj : ∀ M : M4 R, (((h * k)⁻¹ : (M4 R)ˣ) : M4 R) * M * ((h * k : (M4 R)ˣ) : M4 R) =
        ((k⁻¹ : (M4 R)ˣ) : M4 R) * (((h⁻¹ : (M4 R)ˣ) : M4 R) * M * (h : M4 R)) * (k : M4 R) := by
      intro M
      rw [mul_inv_rev, Units.val_mul, Units.val_mul]
      simp only [mul_assoc]
    refine ⟨hc, fun g i j hij => ?_, fun s hs' i => ?_⟩
    · rw [sandwich hd hh' (r g) i j, hconj]
      exact ((hkinv.mul (hG g)).mul hkt) hij
    · rw [sandwich hd hh' _ i i, hconj, conj_sub h, conj_sub k, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one, sub_eq_zero, tri_mul_diag (hkinv.mul (hG s)) hkt,
        tri_mul_diag hkinv (hG s), (hF s).2 i, hκ i s hs']
      have e1 : ((k⁻¹ : (M4 R)ˣ) : M4 R) i i * (k : M4 R) i i = 1 := by
        rw [← tri_mul_diag hkinv hkt, Units.inv_mul, Matrix.one_apply_eq]
      linear_combination (ps i s) * e1

end UpperTheory.V.Loc.SpFlag

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ r hL`. Establish `hs0 : (D.s0 : G ℚ Ω) ∈ D.Ip l` using `hD.decompSigma_mem.1.1`. Establish `hψ : D.ψ (D.s0 : G ℚ Ω) = 1` using `hD.decompSigma_mem.1.2`. Establish `hom : D.om (D.s0 : G ℚ Ω) = 1` using `hD.decompSigma_mem.2`. Establish `hξ : D.ξ (D.s0 : G ℚ Ω) = 1` using `hD.xi_unrT l (by simp [Raw.T]) hs0`.

Establish `hc : ((chiO ℚ Ω l c.O (D.s0 : G ℚ Ω) : (c.O)ˣ) : c.O) = algebraMap ℤ_[l] c.O (cycZ ℚ Ω l (D.s0 : G ℚ Ω) : ℤ_[l])` using `rfl`. Establish `hal : (D.al (D.s0 : G ℚ Ω) : c.O) = algebraMap ℤ_[l] c.O (cycZ ℚ Ω l (D.s0 : G ℚ Ω) : ℤ_[l])`. Rewrite using `[← hc]`. Simplify using `[Raw.al, hom, hξ]`. Establish `hPsi : (D.Psi (D.s0 : G ℚ Ω) : c.O) = algebraMap ℤ_[l] c.O ((cycZ ℚ Ω l (D.s0 : G ℚ Ω) : ℤ_[l]) ^ D.e)`.

Rewrite using `[map_pow, ← hc]`. Simplify using `[Raw.Psi, Chr.Psi, hψ]`. Establish `hx : ∀ i, (D.ps i (D.s0 : G ℚ Ω) : c.O) = algebraMap ℤ_[l] c.O ((cycZ ℚ Ω l (D.s0 : G ℚ Ω) : ℤ_[l]) ^ D.wts4 i)`. Introduce `i`. Apply the tactic sequence `fin_cases i <;> simp [Raw.ps, Raw.th, Raw.wts4, hal, hPsi, pow_succ, mul_comm]`.

Establish `hw : ∀ i j : Fin 4, D.wts4 i = D.wts4 j → i = j`. Establish `h2` using `hD.two_le`. Introduce `i j hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Raw.wts4] at hij ⊢ <;> omega`. Establish `hwr : ∀ i : Fin 4, D.wts4 i.rev + D.wts4 i = D.e + 1`.

Introduce `i`. Apply the tactic sequence `fin_cases i <;> simp [Raw.wts4, Fin.rev] <;> omega`. Establish `hB : ∀ z : ℤ_[l], algebraMap c.O B (algebraMap ℤ_[l] c.O z) = algebraMap ℚ_[l] B (algebraMap ℤ_[l] ℚ_[l] z)`. Introduce `z`. Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`.

Establish `hd : ∀ i j, i ≠ j → IsUnit (algebraMap c.O B (D.ps i (D.s0 : G ℚ Ω)) - algebraMap c.O B (D.ps j (D.s0 : G ℚ Ω)))`. Introduce `i j hij`. Rewrite using `[hx i, hx j, hB, hB, ← map_sub]`. Apply `IsUnit.map` to reduce the goal to its premises. Rewrite using `[isUnit_iff_ne_zero]`.

Introduce `h0`. Rewrite `h0` using `[sub_eq_zero]`. Establish `h1` using `IsFractionRing.injective ℤ_[l] ℚ_[l] h0`. Establish `h2 : cycZ ℚ Ω l (D.s0 : G ℚ Ω) ^ D.wts4 i = cycZ ℚ Ω l (D.s0 : G ℚ Ω) ^ D.wts4 j`. Use `ext`.

Simplify using `using h1`. Conclude with `hij (hw i j ((pow_inj_iff_of_orderOf_eq_zero (orderOf_eq_zero_iff.mpr hD.decompSigma_ord)).mp h2))`. Establish `hu : ∀ i, IsUnit (algebraMap c.O B (D.ps i (D.s0 : G ℚ Ω)))` using `fun i => (Units.isUnit _).map _`. Establish `hth : (D.th (D.s0 : G ℚ Ω) : c.O) = algebraMap ℤ_[l] c.O ((cycZ ℚ Ω l (D.s0 : G ℚ Ω) : ℤ_[l]) ^ (D.e + 1))`. Simplify `hx 0` using `[Raw.ps, Raw.wts4]`.

Establish `hν : ∀ i : Fin 4, algebraMap c.O B (D.ps i.rev (D.s0 : G ℚ Ω)) * algebraMap c.O B (D.ps i (D.s0 : G ℚ Ω)) = algebraMap c.O B (D.th (D.s0 : G ℚ Ω))`. Introduce `i`. Rewrite using `[← map_mul, hx, hx, hth, ← map_mul, ← pow_add, hwr]`. Establish `hπ' : ∀ a : B, (π : B →+* E) a = 1 → IsUnit a`. Introduce `a ha`.

Establish `hn : IsNilpotent (a - 1)` using `hπ _ (by simpa [sub_eq_zero] using ha)`. Simplify using `using hn.isUnit_add_one`. Establish `hred : (r D.s0).map (π : B →+* E) = Matrix.diagonal fun a => (π : B →+* E) (algebraMap c.O B (D.ps a (D.s0 : G ℚ Ω)))`. Use extensionality with `a b`. Establish `e` using `congrArg (fun f => f D.s0 a b) hL.red`.

Simplify using `only [mapRep_apply] at e`. Rewrite using `[Matrix.map_apply, e]`. Simplify using `[Raw.r0At, Raw.r0, diagRep, Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp [IsScalarTower.algebraMap_apply c.O E B]`. Establish `key` using `fun hX => SpFlag.ord_iff (π : B →+* E) hπ' ((D.Ip l).subgroupOf (D.Gp l)) (fun i g => algebraMap c.O B (D.ps i g)) (s₀ := D.s0) (Subgroup.mem_subgroupOf.mpr hs0) r hd hu hν hX hred`.

Unfold `EqL`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hG, hO⟩`. Take `⟨h, κ, h1, h2, h3, h4⟩` from `(key (hG D.s0)).mp hO`. Conclude with `⟨hG, h, κ, h1, h2, h3, fun i s hs => h4 i s (Subgroup.mem_subgroupOf.mpr hs)⟩`.

Introduce and unpack `⟨hG, h, κ, h1, h2, h3, h4⟩`. Conclude with `⟨hG, (key (hG D.s0)).mpr ⟨h, κ, h1, h2, h3, fun i s hs => h4 i s (Subgroup.mem_subgroupOf.mp hs)⟩⟩`.
-/
theorem UpperTheory.V.Loc.spFlag :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra ↥c.O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ↥c.O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing ↥c.O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra ↥c.O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ↥c.O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ↥c.O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : D.Gp l →* M4 B), IsContinuousLiftOfRZero D (π : B →+* E) l r → (EqL D r ↔ (∀ g : D.Gp l, IsGSp (algebraMap c.O B (D.th g)) (r g)) ∧ ∃ (h : (M4 B)ˣ) (κ : Fin 4 → D.Gp l →* Bˣ), IsGSp 1 (h : M4 B) ∧ (h : M4 B).map π = 1 ∧ FlagIn r h κ ∧ ∀ i (s : D.Gp l), (s : G ℚ Ω) ∈ D.Ip l → (κ i s : B) = algebraMap c.O B (D.ps i s)) := by
  intro Ω _ _ _ l _ c D hD E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ r hL
  have hs0 : (D.s0 : G ℚ Ω) ∈ D.Ip l := hD.decompSigma_mem.1.1
  have hψ : D.ψ (D.s0 : G ℚ Ω) = 1 := hD.decompSigma_mem.1.2
  have hom : D.om (D.s0 : G ℚ Ω) = 1 := hD.decompSigma_mem.2
  have hξ : D.ξ (D.s0 : G ℚ Ω) = 1 := hD.xi_unrT l (by simp [Raw.T]) hs0
  have hc : ((chiO ℚ Ω l c.O (D.s0 : G ℚ Ω) : (c.O)ˣ) : c.O) =
      algebraMap ℤ_[l] c.O (cycZ ℚ Ω l (D.s0 : G ℚ Ω) : ℤ_[l]) := rfl
  have hal : (D.al (D.s0 : G ℚ Ω) : c.O) = algebraMap ℤ_[l] c.O (cycZ ℚ Ω l (D.s0 : G ℚ Ω) : ℤ_[l]) := by
    rw [← hc]
    simp [Raw.al, hom, hξ]
  have hPsi : (D.Psi (D.s0 : G ℚ Ω) : c.O) =
      algebraMap ℤ_[l] c.O ((cycZ ℚ Ω l (D.s0 : G ℚ Ω) : ℤ_[l]) ^ D.e) := by
    rw [map_pow, ← hc]
    simp [Raw.Psi, Chr.Psi, hψ]
  have hx : ∀ i, (D.ps i (D.s0 : G ℚ Ω) : c.O) =
      algebraMap ℤ_[l] c.O ((cycZ ℚ Ω l (D.s0 : G ℚ Ω) : ℤ_[l]) ^ D.wts4 i) := by
    intro i
    fin_cases i <;> simp [Raw.ps, Raw.th, Raw.wts4, hal, hPsi, pow_succ, mul_comm]
  have hw : ∀ i j : Fin 4, D.wts4 i = D.wts4 j → i = j := by
    have h2 := hD.two_le
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [Raw.wts4] at hij ⊢ <;> omega
  have hwr : ∀ i : Fin 4, D.wts4 i.rev + D.wts4 i = D.e + 1 := by
    intro i
    fin_cases i <;> simp [Raw.wts4, Fin.rev] <;> omega
  have hB : ∀ z : ℤ_[l], algebraMap c.O B (algebraMap ℤ_[l] c.O z) =
      algebraMap ℚ_[l] B (algebraMap ℤ_[l] ℚ_[l] z) := by
    intro z
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hd : ∀ i j, i ≠ j → IsUnit (algebraMap c.O B (D.ps i (D.s0 : G ℚ Ω)) -
      algebraMap c.O B (D.ps j (D.s0 : G ℚ Ω))) := by
    intro i j hij
    rw [hx i, hx j, hB, hB, ← map_sub]
    apply IsUnit.map
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [sub_eq_zero] at h0
    have h1 := IsFractionRing.injective ℤ_[l] ℚ_[l] h0
    have h2 : cycZ ℚ Ω l (D.s0 : G ℚ Ω) ^ D.wts4 i = cycZ ℚ Ω l (D.s0 : G ℚ Ω) ^ D.wts4 j := by
      ext
      simpa using h1
    exact hij (hw i j ((pow_inj_iff_of_orderOf_eq_zero (orderOf_eq_zero_iff.mpr hD.decompSigma_ord)).mp h2))
  have hu : ∀ i, IsUnit (algebraMap c.O B (D.ps i (D.s0 : G ℚ Ω))) := fun i =>
    (Units.isUnit _).map _
  have hth : (D.th (D.s0 : G ℚ Ω) : c.O) =
      algebraMap ℤ_[l] c.O ((cycZ ℚ Ω l (D.s0 : G ℚ Ω) : ℤ_[l]) ^ (D.e + 1)) := by
    simpa [Raw.ps, Raw.wts4] using hx 0
  have hν : ∀ i : Fin 4, algebraMap c.O B (D.ps i.rev (D.s0 : G ℚ Ω)) *
      algebraMap c.O B (D.ps i (D.s0 : G ℚ Ω)) = algebraMap c.O B (D.th (D.s0 : G ℚ Ω)) := by
    intro i
    rw [← map_mul, hx, hx, hth, ← map_mul, ← pow_add, hwr]
  have hπ' : ∀ a : B, (π : B →+* E) a = 1 → IsUnit a := by
    intro a ha
    have hn : IsNilpotent (a - 1) := hπ _ (by simpa [sub_eq_zero] using ha)
    simpa using hn.isUnit_add_one
  have hred : (r D.s0).map (π : B →+* E) =
      Matrix.diagonal fun a => (π : B →+* E) (algebraMap c.O B (D.ps a (D.s0 : G ℚ Ω))) := by
    ext a b
    have e := congrArg (fun f => f D.s0 a b) hL.red
    simp only [mapRep_apply] at e
    rw [Matrix.map_apply, e]
    simp [Raw.r0At, Raw.r0, diagRep, Matrix.diagonal_apply]
    split_ifs <;> simp [IsScalarTower.algebraMap_apply c.O E B]
  have key := fun hX => SpFlag.ord_iff (π : B →+* E) hπ' ((D.Ip l).subgroupOf (D.Gp l))
    (fun i g => algebraMap c.O B (D.ps i g)) (s₀ := D.s0) (Subgroup.mem_subgroupOf.mpr hs0) r
    hd hu hν hX hred
  unfold EqL
  constructor
  · rintro ⟨hG, hO⟩
    obtain ⟨h, κ, h1, h2, h3, h4⟩ := (key (hG D.s0)).mp hO
    exact ⟨hG, h, κ, h1, h2, h3, fun i s hs => h4 i s (Subgroup.mem_subgroupOf.mpr hs)⟩
  · rintro ⟨hG, h, κ, h1, h2, h3, h4⟩
    exact ⟨hG, (key (hG D.s0)).mpr ⟨h, κ, h1, h2, h3, fun i s hs => h4 i s (Subgroup.mem_subgroupOf.mp hs)⟩⟩
