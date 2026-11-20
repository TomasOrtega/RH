import Mathlib
import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.RotationOfDiagonalGenerator
set_option maxSynthPendingDepth 1

open Polynomial Formalism.REAL

namespace GroundTheory.BlockD.FourierDecayAlt.GaugeExists

noncomputable section

section Capelli

variable {A : Type} [Ring A] [Algebra ℂ A]

def tmPoly {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) : A[X] :=
  (if a = b then X - C (algebraMap ℂ A (k : ℂ)) else 0) + C (E a b)

def qdetPoly {n : ℕ} (E : Fin n → Fin n → A) : A[X] :=
  ∑ σ : Equiv.Perm (Fin n), C ((Equiv.Perm.sign σ : ℤ) : A) *
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod

def evU (u : ℂ) : A[X] →+* A :=
  eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u) (fun a => (Algebra.commutes u a).symm)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evU_apply (u : ℂ) (p : A[X]) : evU u p = eval₂ (RingHom.id A) (algebraMap ℂ A u) p := rfl

/- English proof (translation)
Unfold `tmPoly Tm`. Apply the tactic sequence `split_ifs <;> simp [evU_apply, map_sub]`.
-/
theorem evU_tmPoly {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (k : ℕ) (a b : Fin n) :
    evU u (tmPoly E k a b) = Tm E (u - (k : ℂ)) a b := by
  unfold tmPoly Tm
  split_ifs <;> simp [evU_apply, map_sub]

/- English proof (translation)
Unfold `qdetPoly qdet qminor`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_list_prod, List.map_ofFn]`. Use `congr 1`.

Simplify using the standard rewrite rules. Use `congr 1`. Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `[Function.comp, evU_tmPoly]`.
-/
theorem evU_qdetPoly {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : evU u (qdetPoly E) = qdet E u := by
  unfold qdetPoly qdet qminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_list_prod, List.map_ofFn]
  congr 1
  · simp
  · congr 1
    congr 1
    funext k
    simp [Function.comp, evU_tmPoly]

/- English proof (translation)
Unfold `tmPoly`. Use `split_ifs with h`. Use `(natDegree_add_le _ _).trans ?_` and prove the remaining obligations. Apply the tactic sequence `refine max_le ((natDegree_sub_le _ _).trans (max_le natDegree_X_le ?_)) ?_ <;> simp`. Simplify using the standard rewrite rules.
-/
theorem natDegree_tmPoly_le {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    (tmPoly E k a b).natDegree ≤ if a = b then 1 else 0 := by
  unfold tmPoly
  split_ifs with h
  · refine (natDegree_add_le _ _).trans ?_
    refine max_le ((natDegree_sub_le _ _).trans (max_le natDegree_X_le ?_)) ?_ <;> simp
  · simp

/- English proof (translation)
Use `(natDegree_list_prod_le _).trans ?_` and prove the remaining obligations. Rewrite using `[List.map_ofFn, List.sum_ofFn]`. Conclude with `Finset.sum_le_sum fun k _ => natDegree_tmPoly_le E k (σ k) k`.
-/
theorem natDegree_prod_le {n : ℕ} (E : Fin n → Fin n → A) (σ : Equiv.Perm (Fin n)) :
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod.natDegree ≤
      ∑ k : Fin n, if σ k = k then 1 else 0 := by
  refine (natDegree_list_prod_le _).trans ?_
  rw [List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_le_sum fun k _ => natDegree_tmPoly_le E k (σ k) k

/- English proof (translation)
Establish `h : σ.support.card = ∑ k : Fin n, if σ k = k then 0 else 1`. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one]`. Use `congr 1`. Rewrite using `[h, ← Finset.sum_add_distrib]`. Simplify using `only [apply_ite₂]`.

Simplify using the standard rewrite rules.
-/
theorem fixed_add_support {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (∑ k : Fin n, if σ k = k then 1 else 0) + σ.support.card = n := by
  have h : σ.support.card = ∑ k : Fin n, if σ k = k then 0 else 1 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one]
    congr 1
  rw [h, ← Finset.sum_add_distrib]
  simp only [apply_ite₂]
  simp

/- English proof (translation)
Establish `h1` using `natDegree_prod_le E σ`. Establish `h2` using `fixed_add_support σ`. Establish `h3` using `Equiv.Perm.two_le_card_support_of_ne_one hσ`. Use linear arithmetic over natural numbers and integers.
-/
theorem natDegree_prod_ne_one {n : ℕ} (E : Fin n → Fin n → A) {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ 1) :
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod.natDegree + 2 ≤ n := by
  have h1 := natDegree_prod_le E σ
  have h2 := fixed_add_support σ
  have h3 := Equiv.Perm.two_le_card_support_of_ne_one hσ
  omega

omit [Algebra ℂ A] in

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Take `⟨h1, h2, h3⟩` from `ih (fun k => c k.castSucc)`. Rewrite using `[List.ofFn_succ', List.prod_concat]`.

Use `set P := (List.ofFn fun k : Fin m => X + C (c k.castSucc)).prod`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `(natDegree_mul_le).trans ?_` and prove the remaining obligations. Establish `: (X + C (c (Fin.last m))).natDegree ≤ 1` using `(natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp))`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[mul_add, coeff_add, coeff_mul_X, coeff_mul_C, h2, coeff_eq_zero_of_natDegree_lt (show P.natDegree < m + 1 by omega)]`. Simplify using the standard rewrite rules. Introduce `j hj`. Establish `hj' : j = m` using `by omega`. Substitute `hj'` using the available equality.

Rewrite using `[Fin.sum_univ_castSucc, mul_add, coeff_add, coeff_mul_C, h2, one_mul]`. Use `congr 1`. Consider the cases of `j with`. Consider the case `zero => simp [P]`. Consider the case `succ i => rw [coeff_mul_X, h3 i rfl]`.
-/
theorem prod_linear (m : ℕ) (c : Fin m → A) :
    (List.ofFn fun k : Fin m => X + C (c k)).prod.natDegree ≤ m ∧
      (List.ofFn fun k : Fin m => X + C (c k)).prod.coeff m = 1 ∧
      ∀ j, j + 1 = m → (List.ofFn fun k : Fin m => X + C (c k)).prod.coeff j = ∑ k, c k := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun k => c k.castSucc)
    rw [List.ofFn_succ', List.prod_concat]
    set P := (List.ofFn fun k : Fin m => X + C (c k.castSucc)).prod
    refine ⟨?_, ?_, ?_⟩
    · refine (natDegree_mul_le).trans ?_
      have : (X + C (c (Fin.last m))).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp))
      omega
    · rw [mul_add, coeff_add, coeff_mul_X, coeff_mul_C, h2,
        coeff_eq_zero_of_natDegree_lt (show P.natDegree < m + 1 by omega)]
      simp
    · intro j hj
      have hj' : j = m := by omega
      subst hj'
      rw [Fin.sum_univ_castSucc, mul_add, coeff_add, coeff_mul_C, h2, one_mul]
      congr 1
      cases j with
      | zero => simp [P]
      | succ i => rw [coeff_mul_X, h3 i rfl]

/- English proof (translation)
Unfold `tmPoly`. Simplify using `only [if_true, map_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem tmPoly_diag {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a : Fin n) :
    tmPoly E k a a = X + C (E a a - algebraMap ℂ A (k : ℂ)) := by
  unfold tmPoly
  simp only [if_true, map_sub]
  abel

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [Fin.val_castSucc, Fin.val_last]`.

Rewrite using `[ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_fin_cast (n : ℕ) : ∑ k : Fin n, ((k : ℕ) : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

/- English proof (translation)
Unfold `qdetPoly`. Use `natDegree_sum_le_of_forall_le _ _ fun σ _ => (natDegree_C_mul_le _ _).trans ?_` and prove the remaining obligations. Use `(natDegree_prod_le E σ).trans ?_` and prove the remaining obligations. Use `fixed_add_support σ` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem natDegree_qdetPoly_le {n : ℕ} (E : Fin n → Fin n → A) : (qdetPoly E).natDegree ≤ n := by
  unfold qdetPoly
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_prod_le E σ).trans ?_
  have := fixed_add_support σ
  omega

/- English proof (translation)
Unfold `qdetPoly`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n))), coeff_add, finsetSum_coeff]`. Rewrite using `[Finset.sum_eq_zero]`. Simplify using `[tmPoly_diag]`. Introduce `σ hσ`.

Establish `hσ1 : σ ≠ 1` using `Finset.ne_of_mem_erase hσ`. Use `natDegree_prod_ne_one E hσ1` as an intermediate fact. Rewrite using `[coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]`.
-/
theorem coeff_qdetPoly_top {n : ℕ} (E : Fin n → Fin n → A) (j : ℕ) (hj : n ≤ j + 1) :
    (qdetPoly E).coeff j = (List.ofFn fun k : Fin n => X + C (E k k - algebraMap ℂ A ((k : ℕ) : ℂ))).prod.coeff j := by
  unfold qdetPoly
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n))), coeff_add, finsetSum_coeff]
  rw [Finset.sum_eq_zero]
  · simp [tmPoly_diag]
  · intro σ hσ
    have hσ1 : σ ≠ 1 := Finset.ne_of_mem_erase hσ
    have := natDegree_prod_ne_one E hσ1
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]

end Capelli

/- English proof (translation)
Introduce `A _ _ n Eo hn`. Take `⟨-, htop, hsub⟩` from `prod_linear n fun k => Eo k k - algebraMap ℂ A ((k : ℕ) : ℂ)`. Establish `hN : (qdetPoly Eo).coeff n = 1` using `by rw [coeff_qdetPoly_top Eo n (by omega), htop]`. Establish `hN1 : (qdetPoly Eo).coeff (n - 1) = ∑ i, Eo i i - algebraMap ℂ A (((n : ℂ) * ((n : ℂ) - 1)) / 2)`. Rewrite using `[coeff_qdetPoly_top Eo (n - 1) (by omega), hsub (n - 1) (by omega), Finset.sum_sub_distrib, ← map_sum, sum_fin_cast]`.

Use `⟨fun j => (qdetPoly Eo).coeff j, fun u => ?_⟩` and prove the remaining obligations. Establish `hdeg : (qdetPoly Eo).natDegree < n - 1 + 1 + 1`. Use `natDegree_qdetPoly_le Eo` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[← evU_qdetPoly Eo u, evU_apply, eval₂_eq_sum_range' _ hdeg, Finset.sum_range_succ, Finset.sum_range_succ, show n - 1 + 1 = n by omega, hN, hN1]`.

Simplify using `only [RingHom.id_apply, one_mul, ← map_pow]`. Rewrite using `[Finset.sum_congr rfl fun j _ => (Algebra.commutes (u ^ j) ((qdetPoly Eo).coeff j)).symm, ← Algebra.commutes (u ^ (n - 1))]`. Normalize the expressions using the abelian group laws.
-/
theorem quantum_determinant_leading_terms : QdetSub := by
  intro A _ _ n Eo hn
  obtain ⟨-, htop, hsub⟩ := prod_linear n fun k => Eo k k - algebraMap ℂ A ((k : ℕ) : ℂ)
  have hN : (qdetPoly Eo).coeff n = 1 := by rw [coeff_qdetPoly_top Eo n (by omega), htop]
  have hN1 : (qdetPoly Eo).coeff (n - 1) = ∑ i, Eo i i - algebraMap ℂ A (((n : ℂ) * ((n : ℂ) - 1)) / 2) := by
    rw [coeff_qdetPoly_top Eo (n - 1) (by omega), hsub (n - 1) (by omega), Finset.sum_sub_distrib,
      ← map_sum, sum_fin_cast]
  refine ⟨fun j => (qdetPoly Eo).coeff j, fun u => ?_⟩
  have hdeg : (qdetPoly Eo).natDegree < n - 1 + 1 + 1 := by
    have := natDegree_qdetPoly_le Eo
    omega
  rw [← evU_qdetPoly Eo u, evU_apply, eval₂_eq_sum_range' _ hdeg, Finset.sum_range_succ,
    Finset.sum_range_succ, show n - 1 + 1 = n by omega, hN, hN1]
  simp only [RingHom.id_apply, one_mul, ← map_pow]
  rw [Finset.sum_congr rfl fun j _ => (Algebra.commutes (u ^ j) ((qdetPoly Eo).coeff j)).symm,
    ← Algebra.commutes (u ^ (n - 1))]
  abel

end

end GroundTheory.BlockD.FourierDecayAlt.GaugeExists
