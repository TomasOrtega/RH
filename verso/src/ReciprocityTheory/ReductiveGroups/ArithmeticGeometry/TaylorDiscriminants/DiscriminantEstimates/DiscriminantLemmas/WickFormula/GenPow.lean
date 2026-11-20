import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.GenDefs

open MvPolynomial

namespace PI.WickFormula.Gen

section
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]

/- English proof (translation)
Establish `h : ⁅(pderiv a : Derivation K (MvPolynomial (I ⊕ J) K) (MvPolynomial (I ⊕ J) K)), (pderiv b : Derivation K (MvPolynomial (I ⊕ J) K) (MvPolynomial (I ⊕ J) K))⁆ = 0`. Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce `c`. Rewrite using `[Derivation.commutator_apply, pderiv_X, pderiv_X]`. Simplify using `only [Pi.single_apply, Derivation.zero_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `h2` using `congrArg (fun D : Derivation K (MvPolynomial (I ⊕ J) K) (MvPolynomial (I ⊕ J) K) => D p) h`. Simplify using `only [Derivation.commutator_apply, Derivation.zero_apply] at h2`. Conclude with `sub_eq_zero.mp h2`.
-/
theorem pderiv_comm (a b : I ⊕ J) (p : MvPolynomial (I ⊕ J) K) :
    pderiv a (pderiv b p) = pderiv b (pderiv a p) := by
  classical
  have h : ⁅(pderiv a : Derivation K (MvPolynomial (I ⊕ J) K) (MvPolynomial (I ⊕ J) K)),
      (pderiv b : Derivation K (MvPolynomial (I ⊕ J) K) (MvPolynomial (I ⊕ J) K))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro c
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply, Derivation.zero_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation K (MvPolynomial (I ⊕ J) K) (MvPolynomial (I ⊕ J) K) =>
    D p) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h2
  exact sub_eq_zero.mp h2

noncomputable abbrev pd (a : I ⊕ J) : Module.End K (MvPolynomial (I ⊕ J) K) :=
  (pderiv a).toLinearMap

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `p`. Conclude with `pderiv_comm a b p`.
-/
theorem commute_pd (a b : I ⊕ J) : Commute (pd (K := K) a) (pd b) := by
  apply LinearMap.ext
  intro p
  exact pderiv_comm a b p

/- English proof (translation)
Unfold `gdelta`. Use `Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ => ?_` and prove the remaining obligations. Use `Commute.smul_left ?_ _` and prove the remaining obligations. Conclude with `(commute_pd (Sum.inl i) c).mul_left (commute_pd (Sum.inr j) c)`.
-/
theorem commute_gdelta_pd (κ : I → J → K) (c : I ⊕ J) : Commute (gdelta κ) (pd c) := by
  unfold gdelta
  refine Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ => ?_
  refine Commute.smul_left ?_ _
  exact (commute_pd (Sum.inl i) c).mul_left (commute_pd (Sum.inr j) c)

/- English proof (translation)
Unfold `dL`. Use `Commute.sum_right _ _ _ fun j _ => ?_` and prove the remaining obligations. Conclude with `Commute.smul_right (commute_gdelta_pd κ (Sum.inr j)) _`.
-/
theorem commute_gdelta_dL (κ : I → J → K) (i : I) : Commute (gdelta κ) (dL κ i) := by
  unfold dL
  refine Commute.sum_right _ _ _ fun j _ => ?_
  exact Commute.smul_right (commute_gdelta_pd κ (Sum.inr j)) _

/- English proof (translation)
The claim follows from `LinearMap.congr_fun (commute_gdelta_dL κ i).eq S`.
-/
theorem gdelta_dL_apply (κ : I → J → K) (i : I) (S : MvPolynomial (I ⊕ J) K) :
    gdelta κ (dL κ i S) = dL κ i (gdelta κ S) :=
  LinearMap.congr_fun (commute_gdelta_dL κ i).eq S

/- English proof (translation)
Rewrite using `[pow_succ']`. Both sides reduce to the same expression.
-/
theorem gdelta_pow_succ_apply (κ : I → J → K) (m : ℕ) (S : MvPolynomial (I ⊕ J) K) :
    (gdelta κ ^ (m + 1)) S = gdelta κ ((gdelta κ ^ m) S) := by
  rw [pow_succ']
  rfl

/- English proof (translation)
Simplify using `[gdelta, LinearMap.sum_apply]`.
-/
theorem gdelta_apply (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ R = ∑ i, ∑ j, κ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) R) := by
  simp [gdelta, LinearMap.sum_apply]

/- English proof (translation)
Simplify using `[dL, LinearMap.sum_apply]`.
-/
theorem dL_apply (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    dL κ i R = ∑ j, κ i j • pderiv (Sum.inr j) R := by
  simp [dL, LinearMap.sum_apply]

/- English proof (translation)
Establish `h1 : ∀ i' j, pderiv (Sum.inl i') (pderiv (Sum.inr j) (X (Sum.inl i) * R)) = X (Sum.inl i) * pderiv (Sum.inl i') (pderiv (Sum.inr j) R) + (if i' = i then pderiv (Sum.inr j) R else 0)`. Introduce `i' j`. Rewrite using `[pderiv_mul, pderiv_X_of_ne (by simp), zero_mul, zero_add, pderiv_mul, pderiv_X]`. Distinguish the cases in `h : i' = i`. Substitute `h` using the available equality.

Simplify using `[add_comm]`. Simplify using `[h, Ne.symm h]`. Rewrite using `[gdelta_apply, gdelta_apply, dL_apply]`. Simplify using `only [h1, smul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_smul_comm, smul_ite, smul_zero]`. Use `congr 1`.

Rewrite using `[Finset.sum_comm]`. Simplify using the standard rewrite rules.
-/
theorem gdelta_X_inl (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ (X (Sum.inl i) * R) = X (Sum.inl i) * gdelta κ R + dL κ i R := by
  classical
  have h1 : ∀ i' j, pderiv (Sum.inl i') (pderiv (Sum.inr j) (X (Sum.inl i) * R)) =
      X (Sum.inl i) * pderiv (Sum.inl i') (pderiv (Sum.inr j) R) +
        (if i' = i then pderiv (Sum.inr j) R else 0) := by
    intro i' j
    rw [pderiv_mul, pderiv_X_of_ne (by simp), zero_mul, zero_add, pderiv_mul, pderiv_X]
    by_cases h : i' = i
    · subst h
      simp [add_comm]
    · simp [h, Ne.symm h]
  rw [gdelta_apply, gdelta_apply, dL_apply]
  simp only [h1, smul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_smul_comm, smul_ite,
    smul_zero]
  congr 1
  rw [Finset.sum_comm]
  simp

end

/- English proof (translation)
Introduce `K I J _ _ _ κ i R n`. Establish `h` using `((commute_gdelta_dL κ i).pow_left n).eq`. Conclude with `LinearMap.congr_fun h R`.
-/
theorem commL_holds : CommL := by
  intro K I J _ _ _ κ i R n
  have h := ((commute_gdelta_dL κ i).pow_left n).eq
  exact LinearMap.congr_fun h R

/- English proof (translation)
Introduce `K I J _ _ _ κ i R n`. Proceed by induction on `n with`. Consider the case `zero => simp [gdelta_X_inl]`. Consider the case `succ n ih`. Rewrite using `[gdelta_pow_succ_apply, ih, map_add, gdelta_X_inl, map_nsmul, ← gdelta_pow_succ_apply, gdelta_dL_apply, ← gdelta_pow_succ_apply, succ_nsmul _ (n + 1)]`.

Normalize the expressions using the abelian group laws.
-/
theorem powXL_holds : PowXL := by
  intro K I J _ _ _ κ i R n
  induction n with
  | zero => simp [gdelta_X_inl]
  | succ n ih =>
    rw [gdelta_pow_succ_apply, ih, map_add, gdelta_X_inl, map_nsmul,
      ← gdelta_pow_succ_apply, gdelta_dL_apply,
      ← gdelta_pow_succ_apply, succ_nsmul _ (n + 1)]
    abel

section
variable {K I J : Type} [CommRing K] [Algebra ℚ K] [Fintype I] [Fintype J]

end

end PI.WickFormula.Gen
