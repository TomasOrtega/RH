import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.DividedPowerIntegrals.GenDefs

open MvPolynomial

namespace PI.DivPowInteg.Gen

section
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]

/- English proof (translation)
Establish `hc : ∀ (c d : I ⊕ J) (n : I ⊕ J), pderiv c (Pi.single (M` using `fun _ => MvPolynomial (I ⊕ J) K) d 1 n) = 0 := by`. Introduce `c d n`. Rewrite using `[Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Proceed by induction on `p using MvPolynomial.induction_on with`.

Consider the case `C x => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p n hp`. Simplify using `only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, hc, hp, mul_zero, zero_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pderiv_comm (a b : I ⊕ J) (p : MvPolynomial (I ⊕ J) K) :
    pderiv a (pderiv b p) = pderiv b (pderiv a p) := by
  classical
  have hc : ∀ (c d : I ⊕ J) (n : I ⊕ J),
      pderiv c (Pi.single (M := fun _ => MvPolynomial (I ⊕ J) K) d 1 n) = 0 := by
    intro c d n
    rw [Pi.single_apply]
    split_ifs <;> simp
  induction p using MvPolynomial.induction_on with
  | C x => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, hc, hp, mul_zero, zero_add]
    ring

noncomputable abbrev pd (a : I ⊕ J) : Module.End K (MvPolynomial (I ⊕ J) K) :=
  (pderiv a).toLinearMap

/- English proof (translation)
Simplify using `[gdelta]`.
-/
private theorem gdelta_apply' (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ R = ∑ i, ∑ j, κ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) R) := by
  simp [gdelta]

/- English proof (translation)
Use `LinearMap.ext fun R => ?_` and prove the remaining obligations. Use `show gdelta κ (pderiv c R) = pderiv c (gdelta κ R)`. Simplify using `only [gdelta_apply', map_sum, map_smul, Derivation.map_smul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[pderiv_comm c (Sum.inl i), pderiv_comm c (Sum.inr j)]`.
-/
theorem commute_gdelta_pd (κ : I → J → K) (c : I ⊕ J) : Commute (gdelta κ) (pd c) := by
  refine LinearMap.ext fun R => ?_
  show gdelta κ (pderiv c R) = pderiv c (gdelta κ R)
  simp only [gdelta_apply', map_sum, map_smul, Derivation.map_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pderiv_comm c (Sum.inl i), pderiv_comm c (Sum.inr j)]

/- English proof (translation)
Simplify using `[dL]`.
-/
private theorem dL_apply' (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    dL κ i R = ∑ j, κ i j • pderiv (Sum.inr j) R := by
  simp [dL]

/- English proof (translation)
Simplify using `[dR]`.
-/
private theorem dR_apply' (κ : I → J → K) (j : J) (R : MvPolynomial (I ⊕ J) K) :
    dR κ j R = ∑ i, κ i j • pderiv (Sum.inl i) R := by
  simp [dR]

/- English proof (translation)
The claim follows from `LinearMap.congr_fun (commute_gdelta_pd κ c).eq S`.
-/
private theorem gdelta_pderiv_comm (κ : I → J → K) (c : I ⊕ J) (S : MvPolynomial (I ⊕ J) K) :
    gdelta κ (pderiv c S) = pderiv c (gdelta κ S) :=
  LinearMap.congr_fun (commute_gdelta_pd κ c).eq S

/- English proof (translation)
Use `LinearMap.ext fun S => ?_` and prove the remaining obligations. Use `show gdelta κ (dL κ i S) = dL κ i (gdelta κ S)`. Rewrite using `[dL_apply', dL_apply', map_sum]`. Simplify using `only [map_smul, gdelta_pderiv_comm]`.
-/
theorem commute_gdelta_dL (κ : I → J → K) (i : I) : Commute (gdelta κ) (dL κ i) := by
  refine LinearMap.ext fun S => ?_
  show gdelta κ (dL κ i S) = dL κ i (gdelta κ S)
  rw [dL_apply', dL_apply', map_sum]
  simp only [map_smul, gdelta_pderiv_comm]

/- English proof (translation)
Use `LinearMap.ext fun S => ?_` and prove the remaining obligations. Use `show gdelta κ (dR κ j S) = dR κ j (gdelta κ S)`. Rewrite using `[dR_apply', dR_apply', map_sum]`. Simplify using `only [map_smul, gdelta_pderiv_comm]`.
-/
theorem commute_gdelta_dR (κ : I → J → K) (j : J) : Commute (gdelta κ) (dR κ j) := by
  refine LinearMap.ext fun S => ?_
  show gdelta κ (dR κ j S) = dR κ j (gdelta κ S)
  rw [dR_apply', dR_apply', map_sum]
  simp only [map_smul, gdelta_pderiv_comm]

/- English proof (translation)
The claim follows from `LinearMap.congr_fun (commute_gdelta_dL κ i).eq S`.
-/
theorem gdelta_dL_apply (κ : I → J → K) (i : I) (S : MvPolynomial (I ⊕ J) K) :
    gdelta κ (dL κ i S) = dL κ i (gdelta κ S) := LinearMap.congr_fun (commute_gdelta_dL κ i).eq S

/- English proof (translation)
The claim follows from `LinearMap.congr_fun (commute_gdelta_dR κ j).eq S`.
-/
theorem gdelta_dR_apply (κ : I → J → K) (j : J) (S : MvPolynomial (I ⊕ J) K) :
    gdelta κ (dR κ j S) = dR κ j (gdelta κ S) := LinearMap.congr_fun (commute_gdelta_dR κ j).eq S

/- English proof (translation)
Rewrite using `[pow_succ']`. Both sides reduce to the same expression.
-/
theorem gdelta_pow_succ_apply (κ : I → J → K) (m : ℕ) (S : MvPolynomial (I ⊕ J) K) :
    (gdelta κ ^ (m + 1)) S = gdelta κ ((gdelta κ ^ m) S) := by
  rw [pow_succ']
  rfl

/- English proof (translation)
Conclude with `gdelta_apply' κ R`.
-/
theorem gdelta_apply (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ R = ∑ i, ∑ j, κ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) R) := by
  exact gdelta_apply' κ R

/- English proof (translation)
Conclude with `dL_apply' κ i R`.
-/
theorem dL_apply (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    dL κ i R = ∑ j, κ i j • pderiv (Sum.inr j) R := by
  exact dL_apply' κ i R

/- English proof (translation)
Conclude with `dR_apply' κ j R`.
-/
theorem dR_apply (κ : I → J → K) (j : J) (R : MvPolynomial (I ⊕ J) K) :
    dR κ j R = ∑ i, κ i j • pderiv (Sum.inl i) R := by
  exact dR_apply' κ j R

/- English proof (translation)
Establish `h1 : ∀ j, pderiv (Sum.inr j) (X (Sum.inl i) * R) = X (Sum.inl i) * pderiv (Sum.inr j) R`. Introduce `j`. Rewrite using `[Derivation.leibniz, pderiv_X_of_ne Sum.inl_ne_inr, smul_zero, add_zero, smul_eq_mul]`. Establish `h2 : ∀ (i' : I) (S : MvPolynomial (I ⊕ J) K), pderiv (Sum.inl i') (X (Sum.inl i) * S) = X (Sum.inl i) * pderiv (Sum.inl i') S + if i' = i then S else 0`. Introduce `i' S`.

Rewrite using `[Derivation.leibniz]`. Simplify using `only [smul_eq_mul]`. Distinguish the cases in `h : i' = i`. Substitute `h` using the available equality. Rewrite using `[pderiv_X_self, mul_one, if_pos rfl]`.

Rewrite using `[pderiv_X_of_ne (fun e => h (Sum.inl_injective e).symm), mul_zero, add_zero, if_neg h, add_zero]`. Establish `hΔ : ∀ S : MvPolynomial (I ⊕ J) K, gdelta κ S = ∑ j, ∑ i', κ i' j • pderiv (Sum.inl i') (pderiv (Sum.inr j) S)`. Introduce `S`. Rewrite using `[gdelta_apply, Finset.sum_comm]`. Rewrite using `[hΔ, hΔ, dL_apply, Finset.mul_sum, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[h1, Finset.mul_sum]`. Simplify using `only [h2, smul_add, Finset.sum_add_distrib, mul_smul_comm, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem gdelta_X_inl (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ (X (Sum.inl i) * R) = X (Sum.inl i) * gdelta κ R + dL κ i R := by
  classical
  have h1 : ∀ j, pderiv (Sum.inr j) (X (Sum.inl i) * R) = X (Sum.inl i) * pderiv (Sum.inr j) R := by
    intro j
    rw [Derivation.leibniz, pderiv_X_of_ne Sum.inl_ne_inr, smul_zero, add_zero, smul_eq_mul]
  have h2 : ∀ (i' : I) (S : MvPolynomial (I ⊕ J) K), pderiv (Sum.inl i') (X (Sum.inl i) * S) =
      X (Sum.inl i) * pderiv (Sum.inl i') S + if i' = i then S else 0 := by
    intro i' S
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    by_cases h : i' = i
    · subst h
      rw [pderiv_X_self, mul_one, if_pos rfl]
    · rw [pderiv_X_of_ne (fun e => h (Sum.inl_injective e).symm), mul_zero, add_zero, if_neg h, add_zero]
  have hΔ : ∀ S : MvPolynomial (I ⊕ J) K,
      gdelta κ S = ∑ j, ∑ i', κ i' j • pderiv (Sum.inl i') (pderiv (Sum.inr j) S) := by
    intro S
    rw [gdelta_apply, Finset.sum_comm]
  rw [hΔ, hΔ, dL_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h1, Finset.mul_sum]
  simp only [h2, smul_add, Finset.sum_add_distrib, mul_smul_comm, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Establish `h1 : ∀ (i' : I) (S : MvPolynomial (I ⊕ J) K), pderiv (Sum.inl i') (X (Sum.inr j) * S) = X (Sum.inr j) * pderiv (Sum.inl i') S`. Introduce `i' S`. Rewrite using `[Derivation.leibniz, pderiv_X_of_ne Sum.inr_ne_inl, smul_zero, add_zero, smul_eq_mul]`. Establish `h2 : ∀ (j' : J) (S : MvPolynomial (I ⊕ J) K), pderiv (Sum.inr j') (X (Sum.inr j) * S) = X (Sum.inr j) * pderiv (Sum.inr j') S + if j' = j then S else 0`. Introduce `j' S`.

Rewrite using `[Derivation.leibniz]`. Simplify using `only [smul_eq_mul]`. Distinguish the cases in `h : j' = j`. Substitute `h` using the available equality. Rewrite using `[pderiv_X_self, mul_one, if_pos rfl]`.

Rewrite using `[pderiv_X_of_ne (fun e => h (Sum.inr_injective e).symm), mul_zero, add_zero, if_neg h, add_zero]`. Establish `h3 : ∀ (i' : I) (j' : J), pderiv (Sum.inl i') (pderiv (Sum.inr j') (X (Sum.inr j) * R)) = X (Sum.inr j) * pderiv (Sum.inl i') (pderiv (Sum.inr j') R) + if j' = j then pderiv (Sum.inl i') R else 0`. Introduce `i' j'`. Rewrite using `[h2, map_add, h1]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[gdelta_apply, gdelta_apply, dR_apply, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i' _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Simplify using `only [h3, smul_add, Finset.sum_add_distrib, mul_smul_comm, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem gdelta_X_inr (κ : I → J → K) (j : J) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ (X (Sum.inr j) * R) = X (Sum.inr j) * gdelta κ R + dR κ j R := by
  classical
  have h1 : ∀ (i' : I) (S : MvPolynomial (I ⊕ J) K),
      pderiv (Sum.inl i') (X (Sum.inr j) * S) = X (Sum.inr j) * pderiv (Sum.inl i') S := by
    intro i' S
    rw [Derivation.leibniz, pderiv_X_of_ne Sum.inr_ne_inl, smul_zero, add_zero, smul_eq_mul]
  have h2 : ∀ (j' : J) (S : MvPolynomial (I ⊕ J) K), pderiv (Sum.inr j') (X (Sum.inr j) * S) =
      X (Sum.inr j) * pderiv (Sum.inr j') S + if j' = j then S else 0 := by
    intro j' S
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    by_cases h : j' = j
    · subst h
      rw [pderiv_X_self, mul_one, if_pos rfl]
    · rw [pderiv_X_of_ne (fun e => h (Sum.inr_injective e).symm), mul_zero, add_zero, if_neg h, add_zero]
  have h3 : ∀ (i' : I) (j' : J), pderiv (Sum.inl i') (pderiv (Sum.inr j') (X (Sum.inr j) * R)) =
      X (Sum.inr j) * pderiv (Sum.inl i') (pderiv (Sum.inr j') R) +
        if j' = j then pderiv (Sum.inl i') R else 0 := by
    intro i' j'
    rw [h2, map_add, h1]
    split_ifs <;> simp
  rw [gdelta_apply, gdelta_apply, dR_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.mul_sum]
  simp only [h3, smul_add, Finset.sum_add_distrib, mul_smul_comm, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end

/- English proof (translation)
Unfold `PowXL`. Introduce `K I J _ _ _ κ i R n`. Proceed by induction on `n with`. Consider the case `zero => simp [gdelta_X_inl]`. Consider the case `succ n ih`.

Rewrite using `[gdelta_pow_succ_apply κ (n + 1), ih, map_add, map_nsmul, gdelta_X_inl, gdelta_dL_apply, ← gdelta_pow_succ_apply, ← gdelta_pow_succ_apply, add_assoc, ← succ_nsmul']`.
-/
theorem powXL_holds : PowXL := by
  unfold PowXL
  intro K I J _ _ _ κ i R n
  induction n with
  | zero => simp [gdelta_X_inl]
  | succ n ih =>
    rw [gdelta_pow_succ_apply κ (n + 1), ih, map_add, map_nsmul, gdelta_X_inl, gdelta_dL_apply,
      ← gdelta_pow_succ_apply, ← gdelta_pow_succ_apply, add_assoc, ← succ_nsmul']

/- English proof (translation)
Unfold `PowXR`. Introduce `K I J _ _ _ κ j R n`. Proceed by induction on `n with`. Consider the case `zero => simp [gdelta_X_inr]`. Consider the case `succ n ih`.

Rewrite using `[gdelta_pow_succ_apply κ (n + 1), ih, map_add, map_nsmul, gdelta_X_inr, gdelta_dR_apply, ← gdelta_pow_succ_apply, ← gdelta_pow_succ_apply, add_assoc, ← succ_nsmul']`.
-/
theorem powXR_holds : PowXR := by
  unfold PowXR
  intro K I J _ _ _ κ j R n
  induction n with
  | zero => simp [gdelta_X_inr]
  | succ n ih =>
    rw [gdelta_pow_succ_apply κ (n + 1), ih, map_add, map_nsmul, gdelta_X_inr, gdelta_dR_apply,
      ← gdelta_pow_succ_apply, ← gdelta_pow_succ_apply, add_assoc, ← succ_nsmul']

section
variable {K I J : Type} [CommRing K] [Algebra ℚ K] [Fintype I] [Fintype J]

end

end PI.DivPowInteg.Gen
