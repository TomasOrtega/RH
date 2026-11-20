import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CharpolyPow

variable {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}

/- English proof (translation)
Rewrite using `[IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`.
-/
lemma card_roots_charpoly (M : Matrix (Fin n) (Fin n) k) : Multiset.card M.charpoly.roots = n := by
  rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/- English proof (translation)
Establish `hroots : Multiset.card M.charpoly.roots = M.charpoly.natDegree`. Rewrite using `[card_roots_charpoly, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Rewrite using `[← Matrix.eval_charpoly, ← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic M) hroots, eval_multiset_prod, Multiset.map_map]`. Simplify using the standard rewrite rules.
-/
lemma det_scalar_sub (M : Matrix (Fin n) (Fin n) k) (t : k) :
    (Matrix.scalar (Fin n) t - M).det = (M.charpoly.roots.map (fun z => t - z)).prod := by
  have hroots : Multiset.card M.charpoly.roots = M.charpoly.natDegree := by
    rw [card_roots_charpoly, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [← Matrix.eval_charpoly,
    ← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic M) hroots,
    eval_multiset_prod, Multiset.map_map]
  simp

/- English proof (translation)
Establish `key : ∀ a : k, (aeval M (C a - X)).det = (M.charpoly.roots.map (fun z => a - z)).prod`. Introduce `a`. Rewrite using `[← det_scalar_sub]`. Use `congr 1`. Simplify using `[Matrix.scalar, Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal]`.

Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, map_mul, Matrix.det_mul, key, ih, ← Multiset.prod_map_mul]`. Use `congr 1`.

Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `z _`. Simplify using the standard rewrite rules.
-/
lemma det_aeval_prod (M : Matrix (Fin n) (Fin n) k) (s : Multiset k) :
    (aeval M (s.map (fun a => C a - X)).prod).det
      = (M.charpoly.roots.map (fun z => eval z (s.map (fun a => C a - X)).prod)).prod := by
  have key : ∀ a : k, (aeval M (C a - X)).det = (M.charpoly.roots.map (fun z => a - z)).prod := by
    intro a
    rw [← det_scalar_sub]
    congr 1
    simp [Matrix.scalar, Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal]
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Matrix.det_mul, key, ih,
      ← Multiset.prod_map_mul]
    congr 1
    apply Multiset.map_congr rfl
    intro z _
    simp

/- English proof (translation)
Use `set m := Multiset.card q.roots`. Use `set c := q.leadingCoeff * (-1) ^ m`. Establish `hq : q = C c * (q.roots.map (fun a => C a - X)).prod`. Establish `hsplit` using `C_leadingCoeff_mul_prod_multiset_X_sub_C (p := q) IsAlgClosed.card_roots_eq_natDegree`. Establish `hneg : (q.roots.map (fun a => C a - X)).prod = (-1) ^ m * (q.roots.map (fun a => X - C a)).prod`.

Establish `: (fun a : k => C a - X) = fun a => (-1) * (X - C a)`. Use function extensionality and compare the values at `a`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]`. Rewrite using `[hneg, C_mul, C_pow, C_neg, C_1]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, mul_assoc (C q.leadingCoeff), ← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules. Establish `hcard : Multiset.card M.charpoly.roots = n` using `card_roots_charpoly M`. Use `conv_lhs => rw [hq]`.

Use `conv_rhs => rw [hq]`. Rewrite using `[map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.det_smul, Fintype.card_fin, det_aeval_prod]`. Simplify using `only [eval_mul, eval_C]`. Rewrite using `[Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]`.
-/
lemma det_aeval (M : Matrix (Fin n) (Fin n) k) (q : k[X]) :
    (aeval M q).det = (M.charpoly.roots.map (fun z => eval z q)).prod := by
  set m := Multiset.card q.roots
  set c := q.leadingCoeff * (-1) ^ m
  have hq : q = C c * (q.roots.map (fun a => C a - X)).prod := by
    have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := q) IsAlgClosed.card_roots_eq_natDegree
    have hneg : (q.roots.map (fun a => C a - X)).prod
        = (-1) ^ m * (q.roots.map (fun a => X - C a)).prod := by
      have : (fun a : k => C a - X) = fun a => (-1) * (X - C a) := by
        funext a; ring
      rw [this, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]
    rw [hneg, C_mul, C_pow, C_neg, C_1]
    calc q = C q.leadingCoeff * (q.roots.map (fun a => X - C a)).prod := hsplit.symm
      _ = C q.leadingCoeff * (-1) ^ m * ((-1) ^ m * (q.roots.map (fun a => X - C a)).prod) := by
        rw [← mul_assoc, mul_assoc (C q.leadingCoeff), ← pow_add, ← two_mul, pow_mul]
        simp
  have hcard : Multiset.card M.charpoly.roots = n := card_roots_charpoly M
  conv_lhs => rw [hq]
  conv_rhs => rw [hq]
  rw [map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.det_smul,
    Fintype.card_fin, det_aeval_prod]
  simp only [eval_mul, eval_C]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]

/- English proof (translation)
Establish `hinf : Infinite k` using `IsAlgClosed.instInfinite`. Establish `hcard : Multiset.card (Matrix.charpoly (M ^ r)).roots = (Matrix.charpoly (M ^ r)).natDegree`. Conclude with `IsAlgClosed.card_roots_eq_natDegree`. Establish `hfac` using `prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic (M ^ r)) hcard`. It suffices to establish `h : Matrix.charpoly (M ^ r) = (((Matrix.charpoly M).roots.map (· ^ r)).map fun a => X - C a).prod by`.

Rewrite using `[h, roots_multiset_prod_X_sub_C]`. Apply `Polynomial.funext` to reduce the goal to its premises. Introduce `t`. Rewrite using `[Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map, Multiset.map_map]`. Establish `h1 : Matrix.scalar (Fin n) t - M ^ r = aeval M (C t - X ^ r)`.

Simplify using `[Matrix.scalar, Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal]`. Rewrite using `[h1, GlobalTheory.CharpolyPow.det_aeval]`. Simplify using `[Function.comp_def]`.
-/
theorem roots_charpoly_pow (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ)
    (M : Matrix (Fin n) (Fin n) k) :
    (Matrix.charpoly (M ^ r)).roots = (Matrix.charpoly M).roots.map (· ^ r) := by
  have hinf : Infinite k := IsAlgClosed.instInfinite
  have hcard : Multiset.card (Matrix.charpoly (M ^ r)).roots = (Matrix.charpoly (M ^ r)).natDegree := by
    exact IsAlgClosed.card_roots_eq_natDegree
  have hfac := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic (M ^ r)) hcard
  suffices h : Matrix.charpoly (M ^ r) = (((Matrix.charpoly M).roots.map (· ^ r)).map fun a => X - C a).prod by
    rw [h, roots_multiset_prod_X_sub_C]
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  have h1 : Matrix.scalar (Fin n) t - M ^ r = aeval M (C t - X ^ r) := by
    simp [Matrix.scalar, Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal]
  rw [h1, GlobalTheory.CharpolyPow.det_aeval]
  simp [Function.comp_def]

end GlobalTheory.CharpolyPow
