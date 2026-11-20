import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace FlagEq

variable {f N : ℕ}

def permSign (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) : ℤ :=
  ∏ τ, ((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ)

def stairExp (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) : Fin f × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => N - 1 - ((w v.1).symm v.2 : ℕ)

def rho (f N : ℕ) : Fin f × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => N - 1 - (v.2 : ℕ)

def stairConst (f N : ℕ) : ℝ := (∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ)) ^ f

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem stairExp_one : stairExp f N 1 = rho f N := by
  ext v; simp [stairExp, rho, Equiv.Perm.one_def]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem permSign_one : permSign f N 1 = 1 := by simp [permSign]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem permSign_inv (w : Fin f → Equiv.Perm (Fin N)) : permSign f N w⁻¹ = permSign f N w := by
  simp [permSign, Equiv.Perm.sign_inv]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem permSign_mul (u w : Fin f → Equiv.Perm (Fin N)) :
    permSign f N (u * w) = permSign f N u * permSign f N w := by
  simp [permSign, Equiv.Perm.sign_mul, prod_mul_distrib]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem permSign_mul_self (u : Fin f → Equiv.Perm (Fin N)) :
    permSign f N u * permSign f N u = 1 := by
  rw [permSign, ← prod_mul_distrib]
  exact prod_eq_one fun τ _ => by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stairConst_pos : 0 < stairConst f N :=
  pow_pos (prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _) _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem coeff_rename_prodCongrRight {R : Type*} [CommSemiring R] (w : Fin f → Equiv.Perm (Fin N))
    (P : MvPolynomial (Fin f × Fin N) R) (d : Fin f × Fin N →₀ ℕ) :
    coeff d (rename (Equiv.prodCongrRight w) P) =
      coeff (Finsupp.equivFunOnFinite.symm fun v => d (Equiv.prodCongrRight w v)) P := by
  rw [← coeff_rename_mapDomain (Equiv.prodCongrRight w) (Equiv.injective _) P]
  congr 1
  ext v
  obtain ⟨u, rfl⟩ := (Equiv.prodCongrRight w).surjective v
  rw [Finsupp.mapDomain_apply (Equiv.injective _)]
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.
-/
theorem coeff_rho_antisym {R : Type*} [CommRing R] (P : MvPolynomial (Fin f × Fin N) R) :
    coeff (rho f N) (∑ w : Fin f → Equiv.Perm (Fin N),
        ((permSign f N w : ℤ) : R) • rename (Equiv.prodCongrRight w) P) =
      ∑ w, ((permSign f N w : ℤ) : R) * coeff (stairExp f N w) P := by
  rw [coeff_sum]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ (fun w => ?_)
  rw [coeff_smul, smul_eq_mul, coeff_rename_prodCongrRight, Equiv.inv_apply, permSign_inv]
  congr 2

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Use symmetry to reverse the relation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem blockVandermonde_eq_sum (f N : ℕ) :
    blockVandermonde f N = ∑ w : Fin f → Equiv.Perm (Fin N),
      ((permSign f N w : ℤ) : ℚ) • monomial (stairExp f N w) (1 : ℚ) := by
  simp only [blockVandermonde, Comb.vandermondeOf_eq_det, Matrix.det_apply', Matrix.of_apply]
  rw [prod_univ_sum, Fintype.piFinset_univ]
  refine sum_congr rfl fun w _ => ?_
  rw [prod_mul_distrib, smul_eq_C_mul, monomial_eq, C_1, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  congr 1
  · simp [permSign]
  · refine prod_congr rfl fun τ _ => ?_
    symm
    rw [← Equiv.prod_comp (w τ)]
    simp [stairExp]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem coeff_blockVandermonde (α : Fin f × Fin N →₀ ℕ) :
    coeff α (blockVandermonde f N) =
      ∑ w, ((permSign f N w : ℤ) : ℚ) * if stairExp f N w = α then 1 else 0 := by
  rw [blockVandermonde_eq_sum, coeff_sum]
  simp only [coeff_smul, coeff_monomial, smul_eq_mul]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_one_of_stairExp_eq (w : Fin f → Equiv.Perm (Fin N)) (h : stairExp f N w = rho f N) :
    w = 1 := by
  funext τ
  ext i
  have h1 := DFunLike.congr_fun h (τ, w τ i)
  simp [stairExp, rho] at h1
  have := (w τ i).isLt
  have := i.isLt
  simp only [Pi.one_apply, Equiv.Perm.coe_one, id_eq]
  omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem prod_factorial_stairExp (w : Fin f → Equiv.Perm (Fin N)) :
    (stairExp f N w).prod (fun _ e => (e.factorial : ℝ)) = stairConst f N := by
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Fintype.prod_prod_type]
  have h : ∀ τ, ∏ i : Fin N, ((stairExp f N w (τ, i)).factorial : ℝ) =
      ∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ) := by
    intro τ
    simp only [stairExp, Finsupp.coe_equivFunOnFinite_symm]
    exact Equiv.prod_comp (w τ).symm (fun i : Fin N => ((N - 1 - (i : ℕ)).factorial : ℝ))
  rw [prod_congr rfl (fun τ _ => h τ), prod_const, card_univ, Fintype.card_fin, stairConst]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem rho_degree (f N : ℕ) : (rho f N).degree = f * (N * (N - 1) / 2) := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  simp only [rho, Finsupp.coe_equivFunOnFinite_symm, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N]
  have h := sum_range_reflect (fun i => i) N
  rw [h, sum_range_id]

end FlagEq

end

end GroundTheory.Heights₂.Heights.RestTerms
