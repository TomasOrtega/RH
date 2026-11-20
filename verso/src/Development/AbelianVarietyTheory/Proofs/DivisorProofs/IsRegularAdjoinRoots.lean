import Mathlib
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
open IsLocalRing

open MvPolynomial

namespace GlobalTheory.RootAdjoin

variable {R : Type} [CommRing R] {r : ℕ} (n : ℕ) (x : Fin r → R)

noncomputable abbrev rel : Ideal (MvPolynomial (Fin r) R) :=
  Ideal.span (Set.range fun i => X i ^ n - C (x i))

noncomputable def wt (a : Fin r →₀ ℕ) : R := by
  classical exact if ∀ i, n ∣ a i then ∏ i, x i ^ (a i / n) else 0

/- English proof (translation)
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Use the resulting assumption.

Rewrite the conclusion using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma wt_add_single (hn : 0 < n) (b : Fin r →₀ ℕ) (i : Fin r) :
    wt n x (b + Finsupp.single i n) = x i * wt n x b := by
  classical
  unfold wt
  by_cases h : ∀ j, n ∣ b j
  · have h' : ∀ j, n ∣ (b + Finsupp.single i n) j := by
      intro j
      rw [Finsupp.add_apply, Finsupp.single_apply]
      split_ifs
      · exact (Nat.dvd_add_self_right).mpr (h j)
      · simpa using h j
    rw [if_pos h', if_pos h, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ (fun j => x j ^ (b j / n)) (Finset.mem_univ i)]
    have h1 : (b + Finsupp.single i n) i / n = b i / n + 1 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same, Nat.add_div_right _ hn]
    have h2 : ∏ j ∈ Finset.univ.erase i, x j ^ ((b + Finsupp.single i n) j / n) =
        ∏ j ∈ Finset.univ.erase i, x j ^ (b j / n) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hj).symm, add_zero]
    rw [h1, h2, pow_succ]
    ring
  · have h' : ¬ ∀ j, n ∣ (b + Finsupp.single i n) j := by
      push_neg at h ⊢
      obtain ⟨j, hj⟩ := h
      refine ⟨j, ?_⟩
      rw [Finsupp.add_apply, Finsupp.single_apply]
      split_ifs with hij
      · subst hij; rwa [Nat.dvd_add_self_right]
      · rwa [add_zero]
    rw [if_neg h', if_neg h, mul_zero]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma wt_zero : wt n x 0 = 1 := by simp [wt]

noncomputable def lin : MvPolynomial (Fin r) R →ₗ[R] R :=
  (basisMonomials (Fin r) R).constr R (wt n x)

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
lemma lin_monomial (a : Fin r →₀ ℕ) (c : R) : lin n x (monomial a c) = c * wt n x a := by
  have : monomial a c = c • (basisMonomials (Fin r) R a) := by
    simp [coe_basisMonomials, smul_monomial]
  rw [this, map_smul, lin, Module.Basis.constr_basis, smul_eq_mul]

/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Treat this case separately.
-/
lemma lin_mul_rel (hn : 0 < n) (p : MvPolynomial (Fin r) R) (i : Fin r) :
    lin n x (p * (X i ^ n - C (x i))) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial b c =>
    rw [mul_sub, X_pow_eq_monomial, monomial_mul, mul_one, mul_comm (monomial b c) (C (x i)),
      C_mul_monomial, map_sub, lin_monomial, lin_monomial, wt_add_single n x hn]
    ring
  | add p q hp hq => rw [add_mul, map_add, hp, hq, add_zero]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma lin_rel (hn : 0 < n) {f : MvPolynomial (Fin r) R} (hf : f ∈ rel n x) : lin n x f = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
  rw [map_sum]
  exact Finset.sum_eq_zero fun i _ => lin_mul_rel n x hn _ i

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma algebraMap_eq_mk (z : R) :
    algebraMap R (MvPolynomial (Fin r) R ⧸ rel n x) z = Ideal.Quotient.mk (rel n x) (C z) := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem injective (hn : 0 < n) :
    Function.Injective (algebraMap R (MvPolynomial (Fin r) R ⧸ rel n x)) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  rw [algebraMap_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hc
  have := lin_rel n x hn hc
  rwa [C_apply, lin_monomial, wt_zero, mul_one] at this

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma mk_X_pow (j : Fin r) :
    Ideal.Quotient.mk (rel n x) (X j) ^ n = Ideal.Quotient.mk (rel n x) (C (x j)) := by
  rw [← map_pow, Ideal.Quotient.eq]
  exact Ideal.subset_span ⟨j, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isIntegral (hn : 0 < n) : Algebra.IsIntegral R (MvPolynomial (Fin r) R ⧸ rel n x) := by
  constructor
  intro a
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction f using MvPolynomial.induction_on with
  | C c => rw [← algebraMap_eq_mk]; exact isIntegral_algebraMap
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp =>
    rw [map_mul]
    refine hp.mul ⟨Polynomial.X ^ n - Polynomial.C (x i), Polynomial.monic_X_pow_sub_C _ hn.ne', ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, mk_X_pow,
      algebraMap_eq_mk, sub_self]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
lemma eval₂_residue_zero {R : Type} [CommRing R] [IsLocalRing R] {r : ℕ}
    (f : MvPolynomial (Fin r) R) : eval₂ (residue R) 0 f = residue R (constantCoeff f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp

end GlobalTheory.RootAdjoin
