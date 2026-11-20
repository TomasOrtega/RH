import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `M hM`. Use `⟨Fin.elim0, ?_⟩` and prove the remaining obligations.

Rewrite `hM` using `[Multiset.card_eq_zero]`. Substitute `hM` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `M hM`.

Take `⟨a, ha⟩` from `Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card M)`. Take `⟨u, hu⟩` from `ih (M.erase a) (by rw [Multiset.card_erase_of_mem ha, hM]; rfl)`. Use `⟨Fin.cons a u, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.univ_val_map, List.ofFn_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`.

Rewrite using `[← Multiset.cons_coe, ← Fin.univ_val_map, hu, Multiset.cons_erase ha]`.
-/
theorem exists_fin_enum_multiset {α : Type} : ∀ (n : ℕ) (M : Multiset α), Multiset.card M = n →
    ∃ u : Fin n → α, Multiset.map u Finset.univ.val = M := by
  classical
  intro n
  induction n with
  | zero =>
    intro M hM
    refine ⟨Fin.elim0, ?_⟩
    rw [Multiset.card_eq_zero] at hM
    subst hM; simp
  | succ n ih =>
    intro M hM
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card M)
    obtain ⟨u, hu⟩ := ih (M.erase a) (by rw [Multiset.card_erase_of_mem ha, hM]; rfl)
    refine ⟨Fin.cons a u, ?_⟩
    rw [Fin.univ_val_map, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← Multiset.cons_coe, ← Fin.univ_val_map, hu, Multiset.cons_erase ha]

/- English proof (translation)
Proceed by induction on `R using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a R ih`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm, Polynomial.homogenize_mul _ _ (m := 1) (n := Multiset.card R) ?_ ?_, ih]`. Simplify using `[Multiset.map_cons]`.

Conclude with `Polynomial.natDegree_X_sub_C_le a`. Rewrite using `[Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]`.
-/
theorem homogenize_multiset_prod_X_sub_C {E : Type} [Field E] (R : Multiset E) :
    Polynomial.homogenize (R.map fun a => Polynomial.X - Polynomial.C a).prod (Multiset.card R)
      = (R.map fun a => MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1).prod := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons a R ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm,
      Polynomial.homogenize_mul _ _ (m := 1) (n := Multiset.card R) ?_ ?_, ih]
    · simp [Multiset.map_cons]
    · exact Polynomial.natDegree_X_sub_C_le a
    · rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]

/- English proof (translation)
Introduce `F _ m p hp`. Use `set q : F[X] := ∑ i : Fin (m + 1), Polynomial.C (p i) * Polynomial.X ^ (i : ℕ) with hq_def`. Establish `hcoeff : ∀ i : Fin (m + 1), q.coeff i = p i`. Introduce `i`. Simplify using `only [hq_def, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]`.

Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Rewrite using `[if_neg]`. Conclude with `fun h => hj (Fin.ext h.symm)`.

Simplify using the standard rewrite rules. Establish `hq0 : q ≠ 0`. Introduce `h`. Apply `hp` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Rewrite using `[← hcoeff i, h]`. Simplify using the standard rewrite rules. Establish `hdeg : q.natDegree ≤ m`. Rewrite using `[hq_def]`. Use `Polynomial.natDegree_sum_le_of_forall_le _ _ ?_` and prove the remaining obligations.

Introduce `i _`. Conclude with `(Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.2)`. Set `E` to `q.SplittingField`. Use `set Q : E[X] := q.map (algebraMap F E) with hQ_def`. Establish `hsplit : Q.Splits` using `Polynomial.SplittingField.splits q`.

Establish `hQ0 : Q ≠ 0` using `Polynomial.map_ne_zero hq0`. Establish `hQdeg : Q.natDegree = q.natDegree` using `Polynomial.natDegree_map _`. Use `set d := Q.natDegree with hd`. Establish `hdm : d ≤ m` using `hQdeg ▸ hdeg`. Establish `hcard : Multiset.card Q.roots = d` using `hsplit.natDegree_eq_card_roots.symm`.

Set `M : Multiset (E × E)` to `Q.roots.map (fun r => (-r, 1)) + Multiset.replicate (m - d) (1, 0)`. Establish `hM : Multiset.card M = m` using `by simp [M, hcard]; omega`. Take `⟨u, hu⟩` from `exists_fin_enum_multiset m M hM`. Use `⟨E, inferInstance, inferInstance, inferInstance, Q.leadingCoeff, fun j => (u j).1, fun j => (u j).2, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Polynomial.leadingCoeff_ne_zero.mpr hQ0`.

Introduce `j`. Establish `hj : u j ∈ M` using `by rw [← hu]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)`. Simplify using `only [M, Multiset.mem_add, Multiset.mem_map, Multiset.mem_replicate] at hj`. Introduce `h`. Establish `h0` using `congrFun h 0`.

Establish `h1` using `congrFun h 1`. Simplify using `at h0 h1`. Break down `hj with ⟨r, _, hr⟩ | ⟨_, hr⟩` into its components or cases. Rewrite `h1` using `[← hr]`. Simplify using `at h1`.

Rewrite `h0` using `[hr]`. Simplify using `at h0`. Introduce `A _ _ x y`. Establish `hform : Polynomial.homogenize Q m = ∑ i : Fin (m + 1), MvPolynomial.C (algebraMap F E (p i)) * (MvPolynomial.X 0 ^ (i : ℕ) * MvPolynomial.X 1 ^ (m - i))`. Rewrite using `[hQ_def, congrArg (Polynomial.map (algebraMap F E)) hq_def, Polynomial.map_sum, Polynomial.homogenize_finsetSum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, Polynomial.homogenize_C_mul, Polynomial.homogenize_X_pow (Nat.lt_succ_iff.mp i.2)]`. Establish `hfac` using `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (hcard.trans hd)`. Establish `hP` using `homogenize_multiset_prod_X_sub_C Q.roots`. Rewrite `hP` using `[hcard]`.

Establish `key : Polynomial.homogenize Q m = MvPolynomial.C Q.leadingCoeff * ((Q.roots.map fun a => MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1).prod * MvPolynomial.X 1 ^ (m - d))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_one, hfac, Nat.add_sub_cancel' hdm]`. Use `_ = _ := by`. Rewrite using `[Polynomial.homogenize_C_mul, Polynomial.homogenize_mul _ _ ?_ ?_, hP, Polynomial.homogenize_one]`.

Rewrite using `[Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hcard]`. Simplify using the standard rewrite rules. Establish `h1` using `congrArg (MvPolynomial.aeval (R := E) (σ := Fin 2) ![y, x]) (hform.symm.trans key)`. Simplify using `only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_multiset_prod, Multiset.map_map, Function.comp_def, map_sub, Matrix.cons_val_zero, Matrix.cons_val_one] at h1`. Establish `hprod : ∏ j, (algebraMap E A (u j).1 * x + algebraMap E A (u j).2 * y) = (M.map fun st => algebraMap E A st.1 * x + algebraMap E A st.2 * y).prod`.

Rewrite using `[← hu, Multiset.map_map]`. Both sides reduce to the same expression. Simplify using `only [mul_assoc] at h1 ⊢`. Rewrite using `[h1, hprod]`. Simplify using `only [M, Multiset.map_add, Multiset.prod_add, Multiset.map_map, Function.comp_def, Multiset.map_replicate, Multiset.prod_replicate]`.

Use `congr 2`. Use `congr 1`. Use `Multiset.map_congr rfl fun r _ => ?_` and prove the remaining obligations. Simplify using `only [map_neg, map_one]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules.
-/
theorem binary_form_splits : ∀ (F : Type) [Field F] (m : ℕ) (p : Fin (m + 1) → F), p ≠ 0 →
    ∃ (E : Type) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (c : E)
      (s t : Fin m → E), c ≠ 0 ∧ (∀ j, ![s j, t j] ≠ 0) ∧
      ∀ (A : Type) [CommRing A] [Algebra E A] (x y : A),
        ∑ i : Fin (m + 1), algebraMap E A (algebraMap F E (p i)) * y ^ (i : ℕ) * x ^ (m - i) =
          algebraMap E A c * ∏ j, (algebraMap E A (s j) * x + algebraMap E A (t j) * y) := by
  intro F _ m p hp
  classical
  set q : F[X] := ∑ i : Fin (m + 1), Polynomial.C (p i) * Polynomial.X ^ (i : ℕ) with hq_def
  have hcoeff : ∀ i : Fin (m + 1), q.coeff i = p i := by
    intro i
    simp only [hq_def, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg]
      exact fun h => hj (Fin.ext h.symm)
    · simp
  have hq0 : q ≠ 0 := by
    intro h; apply hp; funext i; rw [← hcoeff i, h]; simp
  have hdeg : q.natDegree ≤ m := by
    rw [hq_def]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro i _
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.2)
  let E := q.SplittingField
  set Q : E[X] := q.map (algebraMap F E) with hQ_def
  have hsplit : Q.Splits := Polynomial.SplittingField.splits q
  have hQ0 : Q ≠ 0 := Polynomial.map_ne_zero hq0
  have hQdeg : Q.natDegree = q.natDegree := Polynomial.natDegree_map _
  set d := Q.natDegree with hd
  have hdm : d ≤ m := hQdeg ▸ hdeg
  have hcard : Multiset.card Q.roots = d := hsplit.natDegree_eq_card_roots.symm
  let M : Multiset (E × E) := Q.roots.map (fun r => (-r, 1)) + Multiset.replicate (m - d) (1, 0)
  have hM : Multiset.card M = m := by simp [M, hcard]; omega
  obtain ⟨u, hu⟩ := exists_fin_enum_multiset m M hM
  refine ⟨E, inferInstance, inferInstance, inferInstance, Q.leadingCoeff, fun j => (u j).1,
    fun j => (u j).2, ?_, ?_, ?_⟩
  · exact Polynomial.leadingCoeff_ne_zero.mpr hQ0
  · intro j
    have hj : u j ∈ M := by rw [← hu]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)
    simp only [M, Multiset.mem_add, Multiset.mem_map, Multiset.mem_replicate] at hj
    intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    rcases hj with ⟨r, _, hr⟩ | ⟨_, hr⟩
    · rw [← hr] at h1; simp at h1
    · rw [hr] at h0; simp at h0
  · intro A _ _ x y
    have hform : Polynomial.homogenize Q m = ∑ i : Fin (m + 1),
        MvPolynomial.C (algebraMap F E (p i)) * (MvPolynomial.X 0 ^ (i : ℕ) *
          MvPolynomial.X 1 ^ (m - i)) := by
      rw [hQ_def, congrArg (Polynomial.map (algebraMap F E)) hq_def, Polynomial.map_sum, Polynomial.homogenize_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.homogenize_C_mul, Polynomial.homogenize_X_pow (Nat.lt_succ_iff.mp i.2)]
    have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (hcard.trans hd)
    have hP := homogenize_multiset_prod_X_sub_C Q.roots
    rw [hcard] at hP
    have key : Polynomial.homogenize Q m = MvPolynomial.C Q.leadingCoeff *
        ((Q.roots.map fun a => MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1).prod *
          MvPolynomial.X 1 ^ (m - d)) := by
      calc Polynomial.homogenize Q m
          = Polynomial.homogenize (Polynomial.C Q.leadingCoeff *
              ((Q.roots.map fun a => Polynomial.X - Polynomial.C a).prod * 1)) (d + (m - d)) := by
            rw [mul_one, hfac, Nat.add_sub_cancel' hdm]
        _ = _ := by
            rw [Polynomial.homogenize_C_mul, Polynomial.homogenize_mul _ _ ?_ ?_, hP,
              Polynomial.homogenize_one]
            · rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hcard]
            · simp
    have h1 := congrArg (MvPolynomial.aeval (R := E) (σ := Fin 2) ![y, x]) (hform.symm.trans key)
    simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      map_multiset_prod, Multiset.map_map, Function.comp_def, map_sub, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h1
    have hprod : ∏ j, (algebraMap E A (u j).1 * x + algebraMap E A (u j).2 * y) =
        (M.map fun st => algebraMap E A st.1 * x + algebraMap E A st.2 * y).prod := by
      rw [← hu, Multiset.map_map]; rfl
    simp only [mul_assoc] at h1 ⊢
    rw [h1, hprod]
    simp only [M, Multiset.map_add, Multiset.prod_add, Multiset.map_map, Function.comp_def,
      Multiset.map_replicate, Multiset.prod_replicate]
    congr 2
    · congr 1
      refine Multiset.map_congr rfl fun r _ => ?_
      simp only [map_neg, map_one]
      ring
    · simp

end GlobalTheory.Nef
