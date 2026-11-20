import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.MonExp

noncomputable def ex (w : ℕ) (i : Fin (w + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ))

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ex_zero (w : ℕ) (i : Fin (w + 1)) : ex w i 0 = i := by
  simp [ex]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ex_one (w : ℕ) (i : Fin (w + 1)) : ex w i 1 = w - i := by
  simp [ex]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem ex_inj (w : ℕ) {i j : Fin (w + 1)} (h : ex w i = ex w j) : i = j := by
  apply Fin.ext
  have := congrArg (fun d => d 0) h
  simpa [ex_zero] using this

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mon_eq (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) :
    mon R w i = MvPolynomial.monomial (ex w i) 1 := by
  rw [mon, ex, MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem C_mul_mon (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) (c : R) :
    MvPolynomial.C c * mon R w i = MvPolynomial.monomial (ex w i) c := by
  rw [mon_eq, MvPolynomial.C_mul_monomial, mul_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem coeff_sum_mon (R : Type) [CommRing R] (w : ℕ) (c : Fin (w + 1) → R) (j : Fin (w + 1)) :
    MvPolynomial.coeff (ex w j) (∑ i, MvPolynomial.C (c i) * mon R w i) = c j := by
  rw [MvPolynomial.coeff_sum]
  simp_rw [C_mul_mon, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [if_neg]
    intro h; exact hij (ex_inj w h)
  · simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem mon_hom (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) : (mon R w i).IsHomogeneous w := by
  have h := (MvPolynomial.isHomogeneous_X_pow (R := R) (0 : Fin 2) (i : ℕ)).mul
    (MvPolynomial.isHomogeneous_X_pow (R := R) (1 : Fin 2) (w - (i : ℕ)))
  have hi : (i : ℕ) + (w - (i : ℕ)) = w := Nat.add_sub_cancel' (Nat.lt_succ_iff.mp i.isLt)
  rw [hi] at h
  exact h

/- English proof (translation)
By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.

Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem hom_expand (R : Type) [CommRing R] (w : ℕ) (p : MvPolynomial (Fin 2) R) (hp : p.IsHomogeneous w) :
    p = ∑ i : Fin (w + 1), MvPolynomial.C (MvPolynomial.coeff (ex w i) p) * mon R w i := by
  ext d
  by_cases hd : ∃ j : Fin (w + 1), ex w j = d
  · obtain ⟨j, rfl⟩ := hd
    rw [coeff_sum_mon]
  · have h0 : MvPolynomial.coeff d p = 0 := by
      apply hp.coeff_eq_zero
      intro hdeg
      apply hd
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
      refine ⟨⟨d 0, by omega⟩, ?_⟩
      ext k
      fin_cases k
      · simp [ex_zero]
      · simp [ex_one]; omega
    rw [h0, MvPolynomial.coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [C_mul_mon, MvPolynomial.coeff_monomial, if_neg]
    intro h; exact hd ⟨i, h⟩

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem polySlash_monomial_isHomogeneous (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (k : Fin (w + 1)) :
    (slP m (mon ℤ w k)).IsHomogeneous w := by
  have hl : ∀ j : Fin 2, ((m j 0 : ℤ) • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) +
      (m j 1 : ℤ) • MvPolynomial.X 1).IsHomogeneous 1 := by
    intro j
    have hs : ∀ (a : ℤ) (v : Fin 2), (a • (MvPolynomial.X v : MvPolynomial (Fin 2) ℤ)).IsHomogeneous 1 := by
      intro a v
      rw [MvPolynomial.smul_eq_C_mul]
      simpa using (MvPolynomial.isHomogeneous_C (Fin 2) a).mul (MvPolynomial.isHomogeneous_X ℤ v)
    exact (hs _ 0).add (hs _ 1)
  have h := ((hl 0).pow (k : ℕ)).mul ((hl 1).pow (w - (k : ℕ)))
  have hi : 1 * (k : ℕ) + 1 * (w - (k : ℕ)) = w := by
    have := Nat.lt_succ_iff.mp k.isLt; omega
  rw [hi] at h
  simpa [slP, mon, map_mul, map_pow, MvPolynomial.aeval_X] using h

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem map₃ (R : Type) [CommRing R] (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (k : Fin (w + 1)) :
    MvPolynomial.map (Int.castRingHom R) (slP m (mon ℤ w k)) = slP m (mon R w k) := by
  simp [slP, mon, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.smul_eq_C_mul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem map_mon (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) :
    MvPolynomial.map (Int.castRingHom R) (mon ℤ w i) = mon R w i := by
  simp [mon]

end GlobalTheory.KZ.MonExp

open GlobalTheory.KZ.MonExp in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.KZ.H3.mon_expand : ∀ (R : Type) [CommRing R] (w : ℕ), (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (k : Fin (w + 1)), slP m (mon R w k) = ∑ i, MvPolynomial.C ((cf w m i k : ℤ) : R) * mon R w i) ∧ (∀ p : MvPolynomial (Fin 2) R, p.IsHomogeneous w → p = ∑ i : Fin (w + 1), MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ))) p) * mon R w i) ∧ (∀ i, (mon R w i).IsHomogeneous w) ∧ (∀ (u : Fin 2 → R) (i : Fin (w + 1)), MvPolynomial.eval u (mon R w i) = u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) ∧ (∀ c : Fin (w + 1) → R, ∑ i, MvPolynomial.C (c i) * mon R w i = 0 → c = 0) := by
  intro R _ w
  refine ⟨?_, fun p hp => hom_expand R w p hp, mon_hom R w, ?_, ?_⟩
  · intro m k
    have hz := hom_expand ℤ w _ (polySlash_monomial_isHomogeneous w m k)
    rw [← map₃, hz, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.map_C, map_mon]
    rfl
  · intro u i
    simp [mon]
  · intro c hc
    funext j
    have := coeff_sum_mon R w c j
    rw [hc, MvPolynomial.coeff_zero] at this
    exact this.symm
