import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KRest

open MvPolynomial

noncomputable section

/- English proof (translation)
Use `conv_lhs => rw [← sum_homogeneousComponent G, Finset.mul_sum]`. Rewrite using `[map_sum]`. Establish `hterm : ∀ i, homogeneousComponent d (P * homogeneousComponent i G) = if d = l + i then P * homogeneousComponent i G else 0` using `fun i => homogeneousComponent_of_mem ((hP.mul (homogeneousComponent_isHomogeneous i G)))`. Repeatedly rewrite using `[hterm]`. Distinguish the cases in `h : l ≤ d`.

Rewrite using `[if_pos h]`. Apply the tactic sequence `have h2 : ∀ i, (if d = l + i then P * homogeneousComponent i G else 0) = if d - l = i then P * homogeneousComponent i G else 0 := fun i => by split_ifs <;> first | rfl | (exfalso; omega)`. Repeatedly rewrite using `[h2]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with hm`.

Both sides reduce to the same expression. Rewrite using `[homogeneousComponent_eq_zero, mul_zero]`. Simplify using `only [Finset.mem_range] at hm`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h]`.

Conclude with `Finset.sum_eq_zero fun i _ => if_neg (by omega)`.
-/
theorem homogeneousComponent_mul_left {σ R : Type*} [CommRing R] {P : MvPolynomial σ R} {l : ℕ}
    (hP : P.IsHomogeneous l) (G : MvPolynomial σ R) (d : ℕ) :
    homogeneousComponent d (P * G) =
      if l ≤ d then P * homogeneousComponent (d - l) G else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent G, Finset.mul_sum]
  rw [map_sum]
  have hterm : ∀ i, homogeneousComponent d (P * homogeneousComponent i G) =
      if d = l + i then P * homogeneousComponent i G else 0 := fun i =>
    homogeneousComponent_of_mem ((hP.mul (homogeneousComponent_isHomogeneous i G)))
  simp_rw [hterm]
  by_cases h : l ≤ d
  · rw [if_pos h]
    have h2 : ∀ i, (if d = l + i then P * homogeneousComponent i G else 0) =
        if d - l = i then P * homogeneousComponent i G else 0 := fun i => by
      split_ifs <;> first | rfl | (exfalso; omega)
    simp_rw [h2]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · rw [homogeneousComponent_eq_zero, mul_zero]
      simp only [Finset.mem_range] at hm
      omega
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun i _ => if_neg (by omega)

/- English proof (translation)
Rewrite using `[Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_filter]`. Use `congr 1`. Use extensionality with `j`.

Simplify using the standard rewrite rules.
-/
theorem prod_Ioi_eq_prod_ite {R : Type*} [CommMonoid R] {m : ℕ} (g : Fin m → Fin m → R) :
    ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, g i j =
      ∏ x : Fin m × Fin m, if x.1 < x.2 then g x.1 x.2 else 1 := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

/- English proof (translation)
Establish `h1 : (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))).det = (Matrix.vandermonde (v ∘ Fin.rev)).det`. Rewrite using `[← Matrix.det_submatrix_equiv_self Fin.revPerm (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ)))]`. Use `congr 1`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply, Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]`.

Use `congr 1`. Use `b.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[h1, Matrix.det_vandermonde, RestTerms.vandermondeOf, prod_Ioi_eq_prod_ite, prod_Ioi_eq_prod_ite]`. Use `Fintype.prod_equiv ((Equiv.prodComm _ _).trans (Fin.revPerm.prodCongr Fin.revPerm)) _ _ ?_` and prove the remaining obligations.

Introduce `x`. Simplify using `only [Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, Equiv.prodCongr_apply, Prod.map, Fin.revPerm_apply, Fin.rev_lt_rev, Function.comp_apply]`.
-/
theorem det_rev_pow_eq_vandermondeOf {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) :
    (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))).det = RestTerms.vandermondeOf v := by
  have h1 : (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))).det =
      (Matrix.vandermonde (v ∘ Fin.rev)).det := by
    rw [← Matrix.det_submatrix_equiv_self Fin.revPerm
      (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ)))]
    congr 1
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply,
      Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 1
    have := b.isLt
    omega
  rw [h1, Matrix.det_vandermonde, RestTerms.vandermondeOf, prod_Ioi_eq_prod_ite,
    prod_Ioi_eq_prod_ite]
  refine Fintype.prod_equiv ((Equiv.prodComm _ _).trans (Fin.revPerm.prodCongr Fin.revPerm)) _ _ ?_
  intro x
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
    Equiv.prodCongr_apply, Prod.map, Fin.revPerm_apply, Fin.rev_lt_rev, Function.comp_apply]

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id_mul_two]`.
-/
theorem sum_fin_val_mul_two (N : ℕ) : (∑ i : Fin N, (i : ℕ)) * 2 = N * (N - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id_mul_two]

/- English proof (translation)
Rewrite using `[← sum_fin_val_mul_two N]`. Use `congr 1`. Use `Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_` and prove the remaining obligations. Simplify using `only [Fin.card_Ioi, Fin.revPerm_apply, Fin.val_rev]`. Use `i.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem sum_card_Ioi_mul_two (N : ℕ) :
    (∑ i : Fin N, (Finset.Ioi i).card) * 2 = N * (N - 1) := by
  rw [← sum_fin_val_mul_two N]
  congr 1
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.card_Ioi, Fin.revPerm_apply, Fin.val_rev]
  have := i.isLt
  omega

def psiPolyFun {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) (P : MvPolynomial σ ℝ) : MvPolynomial σ ℚ :=
  ∑ β ∈ P.support, monomial β (ψ (coeff β P))

/- English proof (translation)
Rewrite using `[psiPolyFun, coeff_sum]`. Simplify using `only [coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with h`. Both sides reduce to the same expression.

Simplify using `only [mem_support_iff, not_not] at h`. Rewrite using `[h, map_zero]`.
-/
theorem coeff_psiPolyFun {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) (P : MvPolynomial σ ℝ) (β : σ →₀ ℕ) :
    coeff β (psiPolyFun ψ P) = ψ (coeff β P) := by
  classical
  rw [psiPolyFun, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [mem_support_iff, not_not] at h
    rw [h, map_zero]

def psiPoly {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) : MvPolynomial σ ℝ →+ MvPolynomial σ ℚ :=
  AddMonoidHom.mk' (psiPolyFun ψ) fun P Q => by
    ext β
    simp only [coeff_psiPolyFun, coeff_add, map_add]

/- English proof (translation)
The claim follows from `coeff_psiPolyFun ψ P β`.
-/
theorem coeff_psiPoly {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) (P : MvPolynomial σ ℝ) (β : σ →₀ ℕ) :
    coeff β (psiPoly ψ P) = ψ (coeff β P) :=
  coeff_psiPolyFun ψ P β

/- English proof (translation)
Use extensionality with `β`. Rewrite using `[coeff_psiPoly, coeff_mul, coeff_mul, map_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_map, coeff_psiPoly, ← Algebra.smul_def, ψ.map_smul, smul_eq_mul]`.
-/
theorem psiPoly_map_mul {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) (A : MvPolynomial σ ℚ)
    (P : MvPolynomial σ ℝ) : psiPoly ψ (map (algebraMap ℚ ℝ) A * P) = A * psiPoly ψ P := by
  classical
  ext β
  rw [coeff_psiPoly, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_psiPoly, ← Algebra.smul_def, ψ.map_smul, smul_eq_mul]

/- English proof (translation)
The claim follows from `(Module.forall_dual_apply_eq_zero_iff ℚ t).mp h`.
-/
theorem eq_zero_of_forall_psi {t : ℝ} (h : ∀ ψ : ℝ →ₗ[ℚ] ℚ, ψ t = 0) : t = 0 :=
  (Module.forall_dual_apply_eq_zero_iff ℚ t).mp h

end

end KRest

end GroundTheory.Heights₂.Heights
