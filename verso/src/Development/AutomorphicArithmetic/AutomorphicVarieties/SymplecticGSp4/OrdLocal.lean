import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement.OrdinaryLocal

open Polynomial

variable {B : Type} [CommRing B]

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq, mul_add, add_mul]`. Consider the case `monomial n a`. Rewrite using `[aeval_monomial, aeval_monomial, Units.conj_pow, ← Algebra.smul_def, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]`.
-/
private theorem aeval_conj (u : (M4 B)ˣ) (X : M4 B) (p : B[X]) :
    aeval ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) p = (u : M4 B) * aeval X p * (u⁻¹ : (M4 B)ˣ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, mul_add, add_mul]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, Units.conj_pow, ← Algebra.smul_def, ← Algebra.smul_def, mul_smul_comm,
      smul_mul_assoc]

/- English proof (translation)
The claim follows from `aeval_conj u X _`.
-/
private theorem prj_conj (c : Fin 4 → B) (u : (M4 B)ˣ) (X : M4 B) (i : Fin 4) :
    prj c ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) i = (u : M4 B) * prj c X i * (u⁻¹ : (M4 B)ˣ) :=
  aeval_conj u X _

/- English proof (translation)
Establish `h1` using `Matrix.aeval_self_charpoly X`. Rewrite `h1` using `[h, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]`. Conclude with `h1`.
-/
private theorem eig_left (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) :
    (X - c i • (1 : M4 B)) * prj c X i = 0 := by
  have h1 := Matrix.aeval_self_charpoly X
  rw [h, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one] at h1
  exact h1

/- English proof (translation)
Establish `h1` using `Matrix.aeval_self_charpoly X`. Rewrite `h1` using `[h, ← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i), map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]`. Conclude with `h1`.
-/
private theorem eig_right (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) :
    prj c X i * (X - c i • (1 : M4 B)) = 0 := by
  have h1 := Matrix.aeval_self_charpoly X
  rw [h, ← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i), map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one] at h1
  exact h1

/- English proof (translation)
Take `⟨s, hs⟩ : Polynomial.X - C a ∣ p - C (p.eval a)` from `X_sub_C_dvd_sub_C_eval`. Use `⟨aeval X s, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (aeval X) hs`. Rewrite `h` using `[mul_comm, map_mul, map_sub, map_sub, aeval_X, aeval_C, aeval_C, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]`. Conclude with `h`.
-/
private theorem aeval_sub (X : M4 B) (a : B) (p : B[X]) :
    ∃ Y : M4 B, aeval X p - p.eval a • (1 : M4 B) = Y * (X - a • (1 : M4 B)) := by
  obtain ⟨s, hs⟩ : Polynomial.X - C a ∣ p - C (p.eval a) := X_sub_C_dvd_sub_C_eval
  refine ⟨aeval X s, ?_⟩
  have h := congrArg (aeval X) hs
  rw [mul_comm, map_mul, map_sub, map_sub, aeval_X, aeval_C, aeval_C, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one] at h
  exact h

/- English proof (translation)
Take `⟨Y, hY⟩` from `aeval_sub X (c j) (∏ a ∈ Finset.univ.erase i, (Polynomial.X - C (c a)))`. Use `⟨Y, ?_⟩` and prove the remaining obligations. Rewrite using `[← hY, eval_prod]`. Simplify using `only [eval_sub, eval_X, eval_C]`. Both sides reduce to the same expression.
-/
private theorem prj_sub (c : Fin 4 → B) (X : M4 B) (i j : Fin 4) :
    ∃ Y : M4 B, prj c X i - (∏ a ∈ Finset.univ.erase i, (c j - c a)) • (1 : M4 B) = Y * (X - c j • (1 : M4 B)) := by
  obtain ⟨Y, hY⟩ := aeval_sub X (c j) (∏ a ∈ Finset.univ.erase i, (Polynomial.X - C (c a)))
  refine ⟨Y, ?_⟩
  rw [← hY, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rfl

/- English proof (translation)
Take `⟨Y, hY⟩` from `prj_sub c X i j`. Establish `h1` using `congrArg (· * prj c X j) hY`. Simplify using `only [mul_assoc, eig_left c X h j, mul_zero, sub_mul, smul_mul_assoc, one_mul] at h1`. Conclude with `sub_eq_zero.mp h1`.
-/
private theorem prj_mul (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i j : Fin 4) :
    prj c X i * prj c X j = (∏ a ∈ Finset.univ.erase i, (c j - c a)) • prj c X j := by
  obtain ⟨Y, hY⟩ := prj_sub c X i j
  have h1 := congrArg (· * prj c X j) hY
  simp only [mul_assoc, eig_left c X h j, mul_zero, sub_mul, smul_mul_assoc, one_mul] at h1
  exact sub_eq_zero.mp h1

/- English proof (translation)
The claim follows from `IsUnit.prod_iff.mpr fun a ha => hc i a (Finset.ne_of_mem_erase ha).symm`.
-/
private theorem unit_d (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (i : Fin 4) :
    IsUnit (∏ a ∈ Finset.univ.erase i, (c i - c a)) :=
  IsUnit.prod_iff.mpr fun a ha => hc i a (Finset.ne_of_mem_erase ha).symm

/- English proof (translation)
The claim follows from `Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩) (sub_self _)`.
-/
private theorem zero_d (c : Fin 4 → B) {i j : Fin 4} (hij : j ≠ i) :
    (∏ a ∈ Finset.univ.erase i, (c j - c a)) = 0 :=
  Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩) (sub_self _)

/- English proof (translation)
Establish `h1` using `Matrix.eval_charpoly X (c i)`. Rewrite `h1` using `[h, eval_prod, Finset.prod_eq_zero (Finset.mem_univ i) (by simp)]`. Establish `h2 : X - c i • (1 : M4 B) = -(Matrix.scalar (Fin 4) (c i) - X)`. Rewrite using `[neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]`. Rewrite using `[h2, Matrix.det_neg, ← h1, mul_zero]`.
-/
private theorem det_eig (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) :
    (X - c i • (1 : M4 B)).det = 0 := by
  have h1 := Matrix.eval_charpoly X (c i)
  rw [h, eval_prod, Finset.prod_eq_zero (Finset.mem_univ i) (by simp)] at h1
  have h2 : X - c i • (1 : M4 B) = -(Matrix.scalar (Fin 4) (c i) - X) := by
    rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [h2, Matrix.det_neg, ← h1, mul_zero]

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Take `⟨Y, hY⟩` from `prj_sub c X i i`. Establish `h1` using `congrArg Matrix.det hY`. Rewrite `h1` using `[Matrix.det_mul, det_eig c X h i, mul_zero]`.

Establish `h2` using `congrArg (residue B) h1`. Use `set d := ∏ a ∈ Finset.univ.erase i, (c i - c a) with hd`. Establish `h3 : (residue B).mapMatrix (prj c X i - d • (1 : M4 B)) = Matrix.diagonal fun _ => -residue B d`. Use extensionality with `a b`. Establish `h0 : residue B (prj c X i a b) = 0` using `(residue_eq_zero_iff _).mpr (hn (a, b))`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[h0]`. Simplify using `[h0, hab]`. Rewrite `h2` using `[RingHom.map_det, h3, Matrix.det_diagonal, map_zero, Finset.prod_eq_zero_iff]`.

Take `⟨_, -, h4⟩` from `h2`. Conclude with `((unit_d c hc i).map (residue B)).ne_zero (neg_eq_zero.mp h4)`.
-/
private theorem exists_unit [IsLocalRing B] (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (X : M4 B)
    (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) : ∃ ab : Fin 4 × Fin 4, IsUnit (prj c X i ab.1 ab.2) := by
  by_contra hn
  push Not at hn
  obtain ⟨Y, hY⟩ := prj_sub c X i i
  have h1 := congrArg Matrix.det hY
  rw [Matrix.det_mul, det_eig c X h i, mul_zero] at h1
  have h2 := congrArg (residue B) h1
  set d := ∏ a ∈ Finset.univ.erase i, (c i - c a) with hd
  have h3 : (residue B).mapMatrix (prj c X i - d • (1 : M4 B)) = Matrix.diagonal fun _ => -residue B d := by
    ext a b
    have h0 : residue B (prj c X i a b) = 0 := (residue_eq_zero_iff _).mpr (hn (a, b))
    by_cases hab : a = b
    · subst hab; simp [h0]
    · simp [h0, hab]
  rw [RingHom.map_det, h3, Matrix.det_diagonal, map_zero, Finset.prod_eq_zero_iff] at h2
  obtain ⟨_, -, h4⟩ := h2
  exact ((unit_d c hc i).map (residue B)).ne_zero (neg_eq_zero.mp h4)

/- English proof (translation)
Use `choose ab hab using exists_unit c hc X h`. Set `P : M4 B` to `Matrix.of fun x j => prj c X j x (ab j).2`. Set `Q : M4 B` to `Matrix.of fun i x => prj c X i (ab i).1 x`. Establish `hQP : Q * P = Matrix.diagonal fun i => (∏ a ∈ Finset.univ.erase i, (c i - c a)) * prj c X i (ab i).1 (ab i).2`. Use extensionality with `i j`.

Establish `h1 : (Q * P) i j = (prj c X i * prj c X j) (ab i).1 (ab j).2` using `rfl`. Rewrite using `[h1, prj_mul c X h]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[zero_d c (Ne.symm hij), Matrix.diagonal_apply_ne _ hij]`. Simplify using the standard rewrite rules. Establish `hdet : IsUnit (Q * P).det`. Rewrite using `[hQP, Matrix.det_diagonal]`. Conclude with `IsUnit.prod_iff.mpr fun a _ => (unit_d c hc a).mul (hab a)`.

Rewrite `hdet` using `[Matrix.det_mul]`. Take `⟨v, hv⟩` from `(Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_of_mul_isUnit_right hdet)`. Establish `hXP : X * P = P * Matrix.diagonal c`. Use extensionality with `x j`. Establish `h1 : (X * P) x j = (X * prj c X j) x (ab j).2` using `rfl`.

Establish `h2` using `eig_left c X h j`. Rewrite `h2` using `[sub_mul, sub_eq_zero, smul_mul_assoc, one_mul]`. Rewrite using `[h1, h2, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression. Use `⟨v⁻¹, ?_⟩` and prove the remaining obligations.

Rewrite using `[inv_inv, mul_assoc, hv, hXP, ← hv, Units.inv_mul_cancel_left]`.
-/
private theorem diagonalize [IsLocalRing B] (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (X : M4 B)
    (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) :
    ∃ u : (M4 B)ˣ, (u : M4 B) * X * (u⁻¹ : (M4 B)ˣ) = Matrix.diagonal c := by
  choose ab hab using exists_unit c hc X h
  let P : M4 B := Matrix.of fun x j => prj c X j x (ab j).2
  let Q : M4 B := Matrix.of fun i x => prj c X i (ab i).1 x
  have hQP : Q * P = Matrix.diagonal fun i => (∏ a ∈ Finset.univ.erase i, (c i - c a)) * prj c X i (ab i).1 (ab i).2 := by
    ext i j
    have h1 : (Q * P) i j = (prj c X i * prj c X j) (ab i).1 (ab j).2 := rfl
    rw [h1, prj_mul c X h]
    by_cases hij : i = j
    · subst hij; simp
    · rw [zero_d c (Ne.symm hij), Matrix.diagonal_apply_ne _ hij]; simp
  have hdet : IsUnit (Q * P).det := by
    rw [hQP, Matrix.det_diagonal]
    exact IsUnit.prod_iff.mpr fun a _ => (unit_d c hc a).mul (hab a)
  rw [Matrix.det_mul] at hdet
  obtain ⟨v, hv⟩ := (Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_of_mul_isUnit_right hdet)
  have hXP : X * P = P * Matrix.diagonal c := by
    ext x j
    have h1 : (X * P) x j = (X * prj c X j) x (ab j).2 := rfl
    have h2 := eig_left c X h j
    rw [sub_mul, sub_eq_zero, smul_mul_assoc, one_mul] at h2
    rw [h1, h2, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]
    rfl
  refine ⟨v⁻¹, ?_⟩
  rw [inv_inv, mul_assoc, hv, hXP, ← hv, Units.inv_mul_cancel_left]

/- English proof (translation)
Establish `h1 : Matrix.diagonal c = Matrix.diagonalAlgHom B c` using `rfl`. Unfold `prj`. Rewrite using `[h1, aeval_algHom_apply]`. Use `show Matrix.diagonal _ = _`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Rewrite using `[map_prod, Finset.prod_apply]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
private theorem prj_diag (c : Fin 4 → B) (i : Fin 4) :
    prj c (Matrix.diagonal c) i = Matrix.diagonal fun x => ∏ a ∈ Finset.univ.erase i, (c x - c a) := by
  have h1 : Matrix.diagonal c = Matrix.diagonalAlgHom B c := rfl
  unfold prj
  rw [h1, aeval_algHom_apply]
  show Matrix.diagonal _ = _
  congr 1
  funext x
  rw [map_prod, Finset.prod_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp

/- English proof (translation)
Rewrite using `[prj_conj, prj_conj]`. Simplify using `only [mul_assoc, Units.inv_mul_cancel_left]`.
-/
private theorem sandwich (c : Fin 4 → B) (u : (M4 B)ˣ) (X Y : M4 B) (i j : Fin 4) :
    prj c ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) j * ((u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ)) *
      prj c ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) i = (u : M4 B) * (prj c X j * Y * prj c X i) * (u⁻¹ : (M4 B)ˣ) := by
  rw [prj_conj, prj_conj]
  simp only [mul_assoc, Units.inv_mul_cancel_left]

/- English proof (translation)
Establish `h1` using `sandwich c u X Y i j`. Rewrite `h1` using `[h, mul_zero, zero_mul, hu, prj_diag, prj_diag]`. Establish `h2` using `congrFun (congrFun h1 j) i`. Rewrite `h2` using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.zero_apply, (unit_d c hc i).mul_left_eq_zero, (unit_d c hc j).mul_right_eq_zero]`. Conclude with `h2`.
-/
private theorem entry_zero (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (u : (M4 B)ˣ) (X Y : M4 B)
    (hu : (u : M4 B) * X * (u⁻¹ : (M4 B)ˣ) = Matrix.diagonal c) (i j : Fin 4) (h : prj c X j * Y * prj c X i = 0) :
    ((u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ)) j i = 0 := by
  have h1 := sandwich c u X Y i j
  rw [h, mul_zero, zero_mul, hu, prj_diag, prj_diag] at h1
  have h2 := congrFun (congrFun h1 j) i
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.zero_apply, (unit_d c hc i).mul_left_eq_zero,
    (unit_d c hc j).mul_right_eq_zero] at h2
  exact h2

/- English proof (translation)
Proceed by induction on `a using WellFoundedGT.induction with`. Consider the case `ind a ih`. Introduce `ha`. Establish `h1` using `congrFun (congrFun hP a) b`. Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_single a, Matrix.zero_apply, (hu a ha).mul_right_eq_zero]`.

Conclude with `h1`. Introduce `x _ hx`. Break down `lt_or_gt_of_ne hx with h | h` into its components or cases. Rewrite using `[hT a x h, zero_mul]`. Rewrite using `[ih x h (ha.trans h), mul_zero]`.

Simplify using the standard rewrite rules.
-/
private theorem row_zero (T P : M4 B) (hT : ∀ i j, j < i → T i j = 0) (hP : T * P = 0) (i : Fin 4)
    (hu : ∀ a, i < a → IsUnit (T a a)) (b a : Fin 4) : i < a → P a b = 0 := by
  induction a using WellFoundedGT.induction with
  | ind a ih =>
    intro ha
    have h1 := congrFun (congrFun hP a) b
    rw [Matrix.mul_apply, Finset.sum_eq_single a, Matrix.zero_apply, (hu a ha).mul_right_eq_zero] at h1
    · exact h1
    · intro x _ hx
      rcases lt_or_gt_of_ne hx with h | h
      · rw [hT a x h, zero_mul]
      · rw [ih x h (ha.trans h), mul_zero]
    · simp

/- English proof (translation)
Proceed by induction on `a using WellFoundedLT.induction with`. Consider the case `ind a ih`. Introduce `ha`. Establish `h1` using `congrFun (congrFun hP b) a`. Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_single a, Matrix.zero_apply, (hu a ha).mul_left_eq_zero]`.

Conclude with `h1`. Introduce `x _ hx`. Break down `lt_or_gt_of_ne hx with h | h` into its components or cases. Rewrite using `[ih x h (h.trans ha), zero_mul]`. Rewrite using `[hT x a h, mul_zero]`.

Simplify using the standard rewrite rules.
-/
private theorem col_zero (T P : M4 B) (hT : ∀ i j, j < i → T i j = 0) (hP : P * T = 0) (i : Fin 4)
    (hu : ∀ a, a < i → IsUnit (T a a)) (b a : Fin 4) : a < i → P b a = 0 := by
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro ha
    have h1 := congrFun (congrFun hP b) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, Matrix.zero_apply, (hu a ha).mul_left_eq_zero] at h1
    · exact h1
    · intro x _ hx
      rcases lt_or_gt_of_ne hx with h | h
      · rw [ih x h (h.trans ha), zero_mul]
      · rw [hT x a h, mul_zero]
    · simp

/- English proof (translation)
Rewrite using `[Matrix.charpoly_of_upperTriangular T (fun i j h => hT i j h)]`. Simplify using `only [hd]`.
-/
private theorem charpoly_tri (c : Fin 4 → B) (T : M4 B) (hT : ∀ i j, j < i → T i j = 0) (hd : ∀ i, T i i = c i) :
    T.charpoly = ∏ j, (Polynomial.X - C (c j)) := by
  rw [Matrix.charpoly_of_upperTriangular T (fun i j h => hT i j h)]
  simp only [hd]

/- English proof (translation)
Establish `hch` using `charpoly_tri c T hT hd`. Establish `hT' : ∀ k i j, j < i → (T - c k • (1 : M4 B)) i j = 0` using `fun k i j h => by`. Simplify using `[hT i j h, Matrix.one_apply_ne h.ne']`. Establish `hu : ∀ k a, a ≠ k → IsUnit ((T - c k • (1 : M4 B)) a a)` using `fun k a h => by`. Simplify `hc a k h` using `[hd]`.

Establish `hrow` using `row_zero _ _ (hT' i) (eig_left c T hch i) i fun a h => hu i a h.ne'`. Establish `hcol` using `col_zero _ _ (hT' j) (eig_right c T hch j) j fun a h => hu j a h.ne`. Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun y _ => ?_` and prove the remaining obligations.

Break down `lt_or_ge i y with hy | hy` into its components or cases. Rewrite using `[hrow b y hy, mul_zero]`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]`. Introduce `x _`. Break down `lt_or_ge x j with hx | hx` into its components or cases.

Rewrite using `[hcol a x hx, zero_mul]`. Break down `lt_or_ge y x with hxy | hxy` into its components or cases. Rewrite using `[hR x y hxy, mul_zero]`. Establish `e1 : x = j` using `le_antisymm (hxy.trans (hy.trans hij)) hx`. Establish `e2 : y = i` using `le_antisymm hy (hij.trans (hx.trans hxy))`.

Rewrite using `[e1, e2, h0, mul_zero]`.
-/
private theorem tri_zero (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (T R : M4 B)
    (hT : ∀ i j, j < i → T i j = 0) (hd : ∀ i, T i i = c i) (hR : ∀ i j, j < i → R i j = 0) (i j : Fin 4) (hij : i ≤ j)
    (h0 : R j i = 0) : prj c T j * R * prj c T i = 0 := by
  have hch := charpoly_tri c T hT hd
  have hT' : ∀ k i j, j < i → (T - c k • (1 : M4 B)) i j = 0 := fun k i j h => by
    simp [hT i j h, Matrix.one_apply_ne h.ne']
  have hu : ∀ k a, a ≠ k → IsUnit ((T - c k • (1 : M4 B)) a a) := fun k a h => by
    simpa [hd] using hc a k h
  have hrow := row_zero _ _ (hT' i) (eig_left c T hch i) i fun a h => hu i a h.ne'
  have hcol := col_zero _ _ (hT' j) (eig_right c T hch j) j fun a h => hu j a h.ne
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  rcases lt_or_ge i y with hy | hy
  · rw [hrow b y hy, mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro x _
    rcases lt_or_ge x j with hx | hx
    · rw [hcol a x hx, zero_mul]
    · rcases lt_or_ge y x with hxy | hxy
      · rw [hR x y hxy, mul_zero]
      · have e1 : x = j := le_antisymm (hxy.trans (hy.trans hij)) hx
        have e2 : y = i := le_antisymm hy (hij.trans (hx.trans hxy))
        rw [e1, e2, h0, mul_zero]

/- English proof (translation)
Rewrite using `[mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, Units.mul_inv]`.
-/
private theorem conj_sub (u : (M4 B)ˣ) (Y : M4 B) (a : B) :
    (u : M4 B) * (Y - a • (1 : M4 B)) * (u⁻¹ : (M4 B)ˣ) = (u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ) - a • (1 : M4 B) := by
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, Units.mul_inv]

/- English proof (translation)
Rewrite `h` using `[Units.mul_left_eq_zero, Units.mul_right_eq_zero]`. Then use the resulting hypothesis.
-/
private theorem conj_zero (u : (M4 B)ˣ) (Y : M4 B) (h : (u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ) = 0) : Y = 0 := by
  rwa [Units.mul_left_eq_zero, Units.mul_right_eq_zero] at h

end UpperTheory.V.GradeZeroInterpolatingElement.OrdinaryLocal

open UpperTheory.V.GradeZeroInterpolatingElement.OrdinaryLocal in
/- English proof (translation)
Introduce `H _ I B _ _ ps s₀ r hs₀ hc`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨u, hu⟩` from `diagonalize (fun a => ps a s₀) hc (r s₀) h.charpoly`. Use `⟨u, fun g i j hij => entry_zero _ hc u _ _ hu j i (h.stable g j i hij), fun s hs i => ?_⟩` and prove the remaining obligations.

Establish `h1` using `entry_zero _ hc u _ _ hu i i (h.inert s hs i)`. Rewrite `h1` using `[conj_sub, Matrix.sub_apply, sub_eq_zero]`. Simplify using `using h1`. Introduce and unpack `⟨u, h1, h2⟩`. Use `⟨?_, fun g i j hij => ?_, fun s hs i => ?_⟩` and prove the remaining obligations.

Establish `h3` using `charpoly_tri (fun a => ps a s₀) _ (h1 s₀) (h2 s₀ hs₀)`. Rewrite using `[← h3, Matrix.coe_units_inv]`. Conclude with `(Matrix.charpoly_units_conj u (r s₀)).symm`. Apply `conj_zero u` to reduce the goal to its premises. Rewrite using `[← sandwich]`.

Conclude with `tri_zero _ hc _ _ (h1 s₀) (h2 s₀ hs₀) (h1 g) i j hij.le (h1 g j i hij)`. Apply `conj_zero u` to reduce the goal to its premises. Rewrite using `[← sandwich, conj_sub]`. Use `tri_zero _ hc _ _ (h1 s₀) (h2 s₀ hs₀) (fun a b hab => ?_) i i le_rfl ?_` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, h1 s a b hab]`.

Simplify using `[Matrix.one_apply_ne hab.ne']`. Rewrite using `[Matrix.sub_apply, h2 s hs i]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.ordLocal :
    ∀ {H : Type} [Group H] (I : Subgroup H) (B : Type) [CommRing B] [IsLocalRing B] (ps : Fin 4 → H → B) (s₀ : H) (r : H →* M4 B), s₀ ∈ I → (∀ i j, i ≠ j → IsUnit (ps i s₀ - ps j s₀)) → (Ord I ps s₀ r ↔ ∃ u : (M4 B)ˣ, (∀ g i j, j < i → ((u : M4 B) * r g * (u⁻¹ : (M4 B)ˣ)) i j = 0) ∧ ∀ s ∈ I, ∀ i, ((u : M4 B) * r s * (u⁻¹ : (M4 B)ˣ)) i i = ps i s) := by
  intro H _ I B _ _ ps s₀ r hs₀ hc
  constructor
  · intro h
    obtain ⟨u, hu⟩ := diagonalize (fun a => ps a s₀) hc (r s₀) h.charpoly
    refine ⟨u, fun g i j hij => entry_zero _ hc u _ _ hu j i (h.stable g j i hij), fun s hs i => ?_⟩
    have h1 := entry_zero _ hc u _ _ hu i i (h.inert s hs i)
    rw [conj_sub, Matrix.sub_apply, sub_eq_zero] at h1
    simpa using h1
  · rintro ⟨u, h1, h2⟩
    refine ⟨?_, fun g i j hij => ?_, fun s hs i => ?_⟩
    · have h3 := charpoly_tri (fun a => ps a s₀) _ (h1 s₀) (h2 s₀ hs₀)
      rw [← h3, Matrix.coe_units_inv]
      exact (Matrix.charpoly_units_conj u (r s₀)).symm
    · apply conj_zero u
      rw [← sandwich]
      exact tri_zero _ hc _ _ (h1 s₀) (h2 s₀ hs₀) (h1 g) i j hij.le (h1 g j i hij)
    · apply conj_zero u
      rw [← sandwich, conj_sub]
      refine tri_zero _ hc _ _ (h1 s₀) (h2 s₀ hs₀) (fun a b hab => ?_) i i le_rfl ?_
      · rw [Matrix.sub_apply, h1 s a b hab]
        simp [Matrix.one_apply_ne hab.ne']
      · rw [Matrix.sub_apply, h2 s hs i]
        simp
