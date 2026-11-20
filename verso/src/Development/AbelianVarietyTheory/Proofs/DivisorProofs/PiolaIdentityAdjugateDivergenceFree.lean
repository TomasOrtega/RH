import Mathlib

namespace GlobalTheory.PiolaAlg

open Finset Matrix

variable {K R : Type} [CommRing K] [CommRing R] [Algebra K R]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[prod_insert ha, Derivation.leibniz, ih, sum_insert ha, prod_insert ha, Function.update_self, prod_congr rfl (fun i hi => Function.update_of_ne (ne_of_mem_of_not_mem hi ha) _ _)]`. Simplify using `only [smul_eq_mul, mul_sum]`.

Rewrite using `[add_comm, mul_comm (∏ i ∈ s, f i)]`. Use `congr 1`. Use `sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Rewrite using `[prod_insert ha, Function.update_of_ne (ne_of_mem_of_not_mem hk ha).symm]`.
-/
theorem derivation_prod {ι : Type} [DecidableEq ι] (D : Derivation K R R) (f : ι → R) (s : Finset ι) :
    D (∏ i ∈ s, f i) = ∑ k ∈ s, ∏ i ∈ s, Function.update f k (D (f k)) i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, Derivation.leibniz, ih, sum_insert ha, prod_insert ha, Function.update_self,
      prod_congr rfl (fun i hi => Function.update_of_ne (ne_of_mem_of_not_mem hi ha) _ _)]
    simp only [smul_eq_mul, mul_sum]
    rw [add_comm, mul_comm (∏ i ∈ s, f i)]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    rw [prod_insert ha, Function.update_of_ne (ne_of_mem_of_not_mem hk ha).symm]

/- English proof (translation)
Simplify using `only [det_apply, map_sum]`. Rewrite using `[sum_comm]`. Use `sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>`. Simplify using `only [h, one_smul, Units.neg_smul, map_neg, sum_neg_distrib, neg_inj]`.

Rewrite using `[derivation_prod]`. Use `conv_rhs => rw [← Equiv.sum_comp σ]`. Use `sum_congr rfl fun k _ => prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality.

Simplify using `[updateRow_apply]`. Rewrite using `[Function.update_of_ne hik, updateRow_apply, if_neg (σ.injective.ne hik)]`.
-/
theorem derivation_det {ι : Type} [Fintype ι] [DecidableEq ι] (D : Derivation K R R)
    (A : Matrix ι ι R) :
    D A.det = ∑ k, (A.updateRow k fun l => D (A k l)).det := by
  simp only [det_apply, map_sum]
  rw [sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
  · simp only [h, one_smul, Units.neg_smul, map_neg, sum_neg_distrib, neg_inj]
    rw [derivation_prod]
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine sum_congr rfl fun k _ => prod_congr rfl fun i _ => ?_
    by_cases hik : i = k
    · subst hik; simp [updateRow_apply]
    · rw [Function.update_of_ne hik, updateRow_apply, if_neg (σ.injective.ne hik)]

/- English proof (translation)
Use `set f : ι × ι → R := fun p => ((M.updateRow p.1 (Pi.single j 1)).updateRow p.2 fun l => δ p.1 ((M.updateRow p.1 (Pi.single j 1)) p.2 l)).det with hf`. Establish `hS : ∑ i, δ i (M.adjugate j i) = ∑ p ∈ univ ×ˢ univ, f p`. Rewrite using `[sum_product]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[adjugate_apply, derivation_det]`.

Establish `hdiag : ∀ i, f (i, i) = 0`. Introduce `i`. Use `det_eq_zero_of_row_eq_zero i fun l => ?_` and prove the remaining obligations. Simplify using `only [updateRow_self]`. Distinguish the cases in `hl : l = j`.

Substitute `hl` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hl]`. Establish `hpair : ∀ i k, i ≠ k → f (i, k) + f (k, i) = 0`. Introduce `i k hik`.

Use `set D : ι → R := fun l => δ i (M k l) with hD`. Establish `h1 : f (i, k) = ((M.updateRow i (Pi.single j 1)).updateRow k D).det`. Simplify using `only [hf]`. Use `congr 2`. Use function extensionality and compare the values at `l`.

Rewrite using `[updateRow_ne (Ne.symm hik)]`. Establish `h2 : f (k, i) = (((M.updateRow i (Pi.single j 1)).updateRow k D).submatrix (Equiv.swap i k) id).det`. Simplify using `only [hf]`. Use `congr 1`. Use extensionality with `a b`.

Simplify using `only [submatrix_apply, id, updateRow_apply, updateRow_ne hik, hD]`. Distinguish the cases in `hai : a = i`. Substitute `hai` using the available equality. Simplify using `[Equiv.swap_apply_left, hik, Ne.symm hik, hM]`. Distinguish the cases in `hak : a = k`.

Substitute `hak` using the available equality. Simplify using `[Equiv.swap_apply_right, hik, Ne.symm hik]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne hai hak]`. Simplify using `[hai, hak]`. Rewrite using `[h1, h2, det_permute, Equiv.Perm.sign_swap hik]`.

Simplify using the standard rewrite rules. Rewrite using `[hS]`. Use `sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨i, k⟩ _`. Distinguish the cases in `hik : i = k`.

Substitute `hik` using the available equality. Simplify using `[hdiag]`. Conclude with `hpair i k hik`. Introduce and unpack `⟨i, k⟩ _ hne heq`. Simplify using `only [Prod.swap_prod_mk, Prod.mk.injEq] at heq`.

Rewrite `hne` using `[heq.1]`. Conclude with `hne (hdiag i)`. Introduce `p _`. Simplify using the standard rewrite rules. Introduce `p _`.

Simplify using the standard rewrite rules.
-/
theorem piola {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ι → Derivation K R R)
    (M : Matrix ι ι R) (hM : ∀ h i j, δ h (M i j) = δ i (M h j)) (j : ι) :
    ∑ i, δ i (M.adjugate j i) = 0 := by
  set f : ι × ι → R := fun p =>
    ((M.updateRow p.1 (Pi.single j 1)).updateRow p.2
      fun l => δ p.1 ((M.updateRow p.1 (Pi.single j 1)) p.2 l)).det with hf
  have hS : ∑ i, δ i (M.adjugate j i) = ∑ p ∈ univ ×ˢ univ, f p := by
    rw [sum_product]
    refine sum_congr rfl fun i _ => ?_
    rw [adjugate_apply, derivation_det]
  have hdiag : ∀ i, f (i, i) = 0 := by
    intro i
    refine det_eq_zero_of_row_eq_zero i fun l => ?_
    simp only [updateRow_self]
    by_cases hl : l = j
    · subst hl; simp
    · simp [Pi.single_apply, hl]
  have hpair : ∀ i k, i ≠ k → f (i, k) + f (k, i) = 0 := by
    intro i k hik
    set D : ι → R := fun l => δ i (M k l) with hD
    have h1 : f (i, k) = ((M.updateRow i (Pi.single j 1)).updateRow k D).det := by
      simp only [hf]
      congr 2
      funext l
      rw [updateRow_ne (Ne.symm hik)]
    have h2 : f (k, i) = (((M.updateRow i (Pi.single j 1)).updateRow k D).submatrix
        (Equiv.swap i k) id).det := by
      simp only [hf]
      congr 1
      ext a b
      simp only [submatrix_apply, id, updateRow_apply, updateRow_ne hik, hD]
      by_cases hai : a = i
      · subst hai; simp [Equiv.swap_apply_left, hik, Ne.symm hik, hM]
      · by_cases hak : a = k
        · subst hak; simp [Equiv.swap_apply_right, hik, Ne.symm hik]
        · rw [Equiv.swap_apply_of_ne_of_ne hai hak]; simp [hai, hak]
    rw [h1, h2, det_permute, Equiv.Perm.sign_swap hik]
    simp
  rw [hS]
  refine sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
  · rintro ⟨i, k⟩ _
    by_cases hik : i = k
    · subst hik; simp [hdiag]
    · exact hpair i k hik
  · rintro ⟨i, k⟩ _ hne heq
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
    rw [heq.1] at hne
    exact hne (hdiag i)
  · intro p _; simp
  · intro p _; simp

/- English proof (translation)
Introduce `δ M hM j` and use `piola δ M hM j`.
-/
theorem piola_identity : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] {ι : Type} [Fintype ι]
    [DecidableEq ι] (δ : ι → Derivation K R R) (M : Matrix ι ι R),
    (∀ h i j, δ h (M i j) = δ i (M h j)) → ∀ j, ∑ i, δ i (M.adjugate j i) = 0 :=
  fun δ M hM j => piola δ M hM j

end GlobalTheory.PiolaAlg
