import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsRootSubsetProductEquationOfHenselianReduct
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsMonicFactorOfRootSubsetProductEquation

noncomputable section
open Polynomial

/- English proof (translation)
Introduce `A _ I _ g hg n m hgm`. Distinguish the cases in `hR : Nontrivial (A ⧸ I)`. Use `swap`. Rewrite `hR` using `[not_nontrivial_iff_subsingleton]`. Conclude with `⟨g, 1, hg, monic_one, (mul_one g).symm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩`.

Use `haveI := hR`. Use `haveI hA : Nontrivial A := (Ideal.Quotient.mk I).domain_nontrivial`. Establish `h1 : ((X : (A ⧸ I)[X]) - 1) = X - C 1` using `by simp`. Establish `hdeg : g.natDegree = n + m`. Establish `h` using `congrArg natDegree hgm`.

Rewrite `h` using `[hg.natDegree_map, h1, (monic_X_pow n).natDegree_mul ((monic_X_sub_C 1).pow m), natDegree_X_pow, (monic_X_sub_C (1 : A ⧸ I)).natDegree_pow, natDegree_X_sub_C, mul_one]`. Conclude with `h`. Take `⟨α, c, hα, hc⟩` from `UpperTheory.exists_root_subset_product_equation_of_henselian_reduction A I g n m (n + m) rfl hg hdeg hgm`. Take `⟨P, Q, hP, hQ, hPQ, hQd, hQm, hQ0⟩` from `UpperTheory.exists_monic_factor_of_root_subset_product_equation A g n m (n + m) rfl hg hdeg α c hc`. Establish `hQdeg : Q.natDegree = m` using `natDegree_eq_of_le_of_coeff_ne_zero hQd (by rw [hQm]; exact one_ne_zero)`.

Establish `hPdeg : P.natDegree = n`. Establish `h` using `hP.natDegree_mul hQ`. Rewrite `h` using `[← hPQ, hdeg, hQdeg]`. Use linear arithmetic over natural numbers and integers. Use `set φ := Ideal.Quotient.mk I`.

Establish `hPb : (P.map φ).Monic` using `hP.map φ`. Establish `hprod : P.map φ * Q.map φ = X ^ n * (X - 1) ^ m`. Rewrite using `[← Polynomial.map_mul, ← hPQ, hgm]`. Establish `hQ0b : (Q.map φ).eval 0 = (-1) ^ m`. Rewrite using `[eval_zero_map, hQ0, map_mul, map_pow, map_neg, map_one, Ideal.Quotient.eq.mpr hα, map_one, mul_one]`.

Establish `hcop : IsCoprime (X : (A ⧸ I)[X]) (Q.map φ)`. Establish `hd : X ∣ Q.map φ - C ((Q.map φ).coeff 0)` using `X_dvd_sub_C`. Take `⟨r, hr⟩` from `hd`. Rewrite `hr` using `[coeff_zero_eq_eval_zero, hQ0b]`. Use `⟨-(C ((-1) ^ m) * r), C ((-1) ^ m), ?_⟩` and prove the remaining obligations.

Establish `hu : ((-1 : A ⧸ I) ^ m) * (-1) ^ m = 1`. Rewrite using `[← mul_pow, neg_one_mul, neg_neg, one_pow]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨s, hs⟩` from `hcop.pow_left.dvd_of_dvd_mul_right ⟨(X - 1) ^ m, hprod⟩`. Establish `hsm : s.Monic` using `(monic_X_pow n).of_mul_monic_left (by rw [← hs]; exact hPb)`.

Establish `hsdeg : s.natDegree = 0`. Establish `h` using `congrArg natDegree hs`. Rewrite `h` using `[hP.natDegree_map φ, (monic_X_pow n).natDegree_mul hsm, natDegree_X_pow, hPdeg]`. Use linear arithmetic over natural numbers and integers. Establish `hs1 : s = 1` using `eq_one_of_monic_natDegree_zero hsm hsdeg`.

Establish `hPmap : P.map φ = X ^ n` using `by rw [hs, hs1, mul_one]`. Establish `hQmap : Q.map φ = (X - 1) ^ m`. Rewrite `hprod` using `[hPmap]`. Establish `h : X ^ n * (Q.map φ - (X - 1) ^ m) = 0` using `by rw [mul_sub, hprod, sub_self]`. Conclude with `sub_eq_zero.mp ((monic_X_pow n).mul_right_eq_zero_iff.mp h)`.

Conclude with `⟨P, Q, hP, hQ, hPQ, hPmap, hQmap⟩`.
-/
theorem UpperTheory.exists_monic_factor_lift_of_pow_mul_sub_one_pow :
    ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (g : A[X]), g.Monic → ∀ n m : ℕ, g.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) ^ m →
      ∃ P Q : A[X], P.Monic ∧ Q.Monic ∧ g = P * Q ∧ P.map (Ideal.Quotient.mk I) = X ^ n ∧ Q.map (Ideal.Quotient.mk I) = (X - 1) ^ m := by
  intro A _ I _ g hg n m hgm
  by_cases hR : Nontrivial (A ⧸ I)
  swap
  · rw [not_nontrivial_iff_subsingleton] at hR
    exact ⟨g, 1, hg, monic_one, (mul_one g).symm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  haveI := hR
  haveI hA : Nontrivial A := (Ideal.Quotient.mk I).domain_nontrivial
  have h1 : ((X : (A ⧸ I)[X]) - 1) = X - C 1 := by simp
  have hdeg : g.natDegree = n + m := by
    have h := congrArg natDegree hgm
    rw [hg.natDegree_map, h1, (monic_X_pow n).natDegree_mul ((monic_X_sub_C 1).pow m),
      natDegree_X_pow, (monic_X_sub_C (1 : A ⧸ I)).natDegree_pow, natDegree_X_sub_C, mul_one] at h
    exact h
  obtain ⟨α, c, hα, hc⟩ := UpperTheory.exists_root_subset_product_equation_of_henselian_reduction A I g n m (n + m) rfl hg hdeg hgm
  obtain ⟨P, Q, hP, hQ, hPQ, hQd, hQm, hQ0⟩ := UpperTheory.exists_monic_factor_of_root_subset_product_equation A g n m (n + m) rfl hg hdeg α c hc
  have hQdeg : Q.natDegree = m :=
    natDegree_eq_of_le_of_coeff_ne_zero hQd (by rw [hQm]; exact one_ne_zero)
  have hPdeg : P.natDegree = n := by
    have h := hP.natDegree_mul hQ
    rw [← hPQ, hdeg, hQdeg] at h
    omega
  set φ := Ideal.Quotient.mk I
  have hPb : (P.map φ).Monic := hP.map φ
  have hprod : P.map φ * Q.map φ = X ^ n * (X - 1) ^ m := by
    rw [← Polynomial.map_mul, ← hPQ, hgm]
  have hQ0b : (Q.map φ).eval 0 = (-1) ^ m := by
    rw [eval_zero_map, hQ0, map_mul, map_pow, map_neg, map_one, Ideal.Quotient.eq.mpr hα, map_one, mul_one]
  have hcop : IsCoprime (X : (A ⧸ I)[X]) (Q.map φ) := by
    have hd : X ∣ Q.map φ - C ((Q.map φ).coeff 0) := X_dvd_sub_C
    obtain ⟨r, hr⟩ := hd
    rw [coeff_zero_eq_eval_zero, hQ0b] at hr
    refine ⟨-(C ((-1) ^ m) * r), C ((-1) ^ m), ?_⟩
    have hu : ((-1 : A ⧸ I) ^ m) * (-1) ^ m = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    calc -(C ((-1) ^ m) * r) * X + C ((-1) ^ m) * Q.map φ
        = C ((-1) ^ m) * (Q.map φ - X * r) := by ring
      _ = 1 := by rw [← hr, sub_sub_cancel, ← C_mul, hu, C_1]
  obtain ⟨s, hs⟩ := hcop.pow_left.dvd_of_dvd_mul_right ⟨(X - 1) ^ m, hprod⟩
  have hsm : s.Monic := (monic_X_pow n).of_mul_monic_left (by rw [← hs]; exact hPb)
  have hsdeg : s.natDegree = 0 := by
    have h := congrArg natDegree hs
    rw [hP.natDegree_map φ, (monic_X_pow n).natDegree_mul hsm, natDegree_X_pow, hPdeg] at h
    omega
  have hs1 : s = 1 := eq_one_of_monic_natDegree_zero hsm hsdeg
  have hPmap : P.map φ = X ^ n := by rw [hs, hs1, mul_one]
  have hQmap : Q.map φ = (X - 1) ^ m := by
    rw [hPmap] at hprod
    have h : X ^ n * (Q.map φ - (X - 1) ^ m) = 0 := by rw [mul_sub, hprod, sub_self]
    exact sub_eq_zero.mp ((monic_X_pow n).mul_right_eq_zero_iff.mp h)
  exact ⟨P, Q, hP, hQ, hPQ, hPmap, hQmap⟩

end
