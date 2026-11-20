import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne

open IsLocalRing Polynomial Matrix UpperTheory.V

/- English proof (translation)
Introduce `K _ n M a hM ha d hd`. Establish `hinj : Function.Injective (fun i => (a i : K) ^ d)`. Introduce `i j hij`. Assume the negation of the conclusion as `hne`. Apply `ha i j hne` to reduce the goal to its premises.

Rewrite using `[isOfFinOrder_iff_pow_eq_one]`. Use `⟨d, hd, ?_⟩` and prove the remaining obligations. Rewrite using `[div_pow, div_eq_one]`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `using hij`.

Establish `hroot : ∀ i, (M ^ d).charpoly.IsRoot ((a i : K) ^ d)`. Introduce `i`. Rewrite using `[← Matrix.mem_spectrum_iff_isRoot_charpoly]`. Apply `spectrum.pow_mem_pow` to reduce the goal to its premises. Rewrite using `[Matrix.mem_spectrum_iff_isRoot_charpoly, hM, Polynomial.IsRoot, Polynomial.eval_prod]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp)`. Establish `hdvd : (∏ i, (X - C ((a i : K) ^ d))) ∣ (M ^ d).charpoly`. Apply `Finset.prod_dvd_of_coprime` to reduce the goal to its premises. Introduce `i _ j _ hij`. Conclude with `Polynomial.pairwise_coprime_X_sub_C hinj hij`.

Introduce `i _`. Conclude with `Polynomial.dvd_iff_isRoot.2 (hroot i)`. Establish `hmon : (∏ i, (X - C ((a i : K) ^ d))).Monic` using `Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)`. Establish `heq : (M ^ d).charpoly = ∏ i, (X - C ((a i : K) ^ d))`. Apply `Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic _) hdvd` to reduce the goal to its premises.

Rewrite using `[Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ]`. Rewrite using `[heq]`. Conclude with `Polynomial.separable_prod_X_sub_C_iff.2 hinj`.
-/
theorem UpperTheory.V.Ws.charpoly_pow_separable_of_eigenvalue_ratios_not_finOrder :
    ∀ (K : Type) [Field K] (n : ℕ) (M : Matrix (Fin n) (Fin n) K) (a : Fin n → Kˣ), M.charpoly = ∏ i, (X - C (a i : K)) →
      (∀ i j, i ≠ j → ¬ IsOfFinOrder (a i / a j)) → ∀ d : ℕ, 0 < d → (M ^ d).charpoly.Separable := by
  intro K _ n M a hM ha d hd
  have hinj : Function.Injective (fun i => (a i : K) ^ d) := by
    intro i j hij
    by_contra hne
    apply ha i j hne
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨d, hd, ?_⟩
    rw [div_pow, div_eq_one]
    apply Units.ext
    simpa using hij
  have hroot : ∀ i, (M ^ d).charpoly.IsRoot ((a i : K) ^ d) := by
    intro i
    rw [← Matrix.mem_spectrum_iff_isRoot_charpoly]
    apply spectrum.pow_mem_pow
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hM, Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hdvd : (∏ i, (X - C ((a i : K) ^ d))) ∣ (M ^ d).charpoly := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact Polynomial.pairwise_coprime_X_sub_C hinj hij
    · intro i _
      exact Polynomial.dvd_iff_isRoot.2 (hroot i)
  have hmon : (∏ i, (X - C ((a i : K) ^ d))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)
  have heq : (M ^ d).charpoly = ∏ i, (X - C ((a i : K) ^ d)) := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic _) hdvd
    rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ]
  rw [heq]
  exact Polynomial.separable_prod_X_sub_C_iff.2 hinj
