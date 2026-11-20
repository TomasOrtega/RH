import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Establish `h : Matrix.vandermonde (v ∘ σ) = (Matrix.vandermonde v).submatrix σ id`. Use extensionality with `i j`. Simplify using `[Matrix.vandermonde_apply]`. Rewrite using `[h, Matrix.det_permute]`.
-/
private lemma det_vand_comp {n : ℕ} (v : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    (Matrix.vandermonde (v ∘ σ)).det =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (Matrix.vandermonde v).det := by
  have h : Matrix.vandermonde (v ∘ σ) = (Matrix.vandermonde v).submatrix σ id := by
    ext i j; simp [Matrix.vandermonde_apply]
  rw [h, Matrix.det_permute]

/- English proof (translation)
Rewrite using `[Finset.prod_filter, Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_filter]`. Use `Finset.prod_congr ?_ fun _ _ => rfl` and prove the remaining obligations. Use extensionality with `j`.

Simplify using the standard rewrite rules.
-/
private lemma prod_prs {n : ℕ} (f : Fin n → Fin n → ℂ) :
    ∏ p ∈ prs n, f p.1 p.2 = ∏ i, ∏ j ∈ Finset.Ioi i, f i j := by
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext j; simp

/- English proof (translation)
Rewrite using `[Matrix.det_vandermonde, ← prod_prs (fun i j => (v ∘ Fin.revPerm) j - (v ∘ Fin.revPerm) i)]`. Use `Finset.prod_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1)) (fun p => (Fin.rev p.2, Fin.rev p.1)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Simplify `hp` using `[Fin.rev_lt_rev]`. Introduce `p hp`.

Simplify `hp` using `[Fin.rev_lt_rev]`. Introduce `p _`. Simplify using the standard rewrite rules. Introduce `p _`. Simplify using the standard rewrite rules.

Introduce `p _`. Simplify using the standard rewrite rules.
-/
private lemma det_rev {n : ℕ} (v : Fin n → ℂ) :
    (Matrix.vandermonde (v ∘ Fin.revPerm)).det = ∏ p ∈ prs n, (v p.1 - v p.2) := by
  rw [Matrix.det_vandermonde, ← prod_prs (fun i j => (v ∘ Fin.revPerm) j - (v ∘ Fin.revPerm) i)]
  refine Finset.prod_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1))
    (fun p => (Fin.rev p.2, Fin.rev p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa [Fin.rev_lt_rev] using hp
  · intro p hp
    simpa [Fin.rev_lt_rev] using hp
  · intro p _; simp
  · intro p _; simp
  · intro p _; simp

/- English proof (translation)
Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`.
-/
private lemma sign_sq_one {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/- English proof (translation)
Establish `h1` using `det_rev (v ∘ σ)`. Establish `h2` using `det_rev v`. Rewrite `h1`, `h2` using `[det_vand_comp]`. Establish `h3` using `det_vand_comp v σ`. Simplify using `only [Function.comp_apply] at h1`.

Rewrite using `[← h1, ← h2, h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma prod_comp {n : ℕ} (v : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    ∏ p ∈ prs n, (v (σ p.1) - v (σ p.2)) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ p ∈ prs n, (v p.1 - v p.2) := by
  have h1 := det_rev (v ∘ σ)
  have h2 := det_rev v
  rw [det_vand_comp] at h1 h2
  have h3 := det_vand_comp v σ
  simp only [Function.comp_apply] at h1
  rw [← h1, ← h2, h3]
  ring

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `[alternant_eq_det]`. Conclude with `(Finset.prod_of_isEmpty _).symm`. Establish `h` using `det_rev (fun i => (z i : ℂ))`. Rewrite `h` using `[det_vand_comp]`.

Rewrite using `[alternant_staircase_eq_vdm hn, map_mul, evalAt_vdm_det, ← h, mul_comm]`. Simplify using the standard rewrite rules.
-/
private lemma evalAt_alternant {n : ℕ} (z : Fin n → ℂˣ) :
    evalAt z (alternant (staircase n)) = ∏ p ∈ prs n, ((z p.1 : ℂ) - (z p.2 : ℂ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [alternant_eq_det]
    exact (Finset.prod_of_isEmpty _).symm
  · have h := det_rev (fun i => (z i : ℂ))
    rw [det_vand_comp] at h
    rw [alternant_staircase_eq_vdm hn, map_mul, evalAt_vdm_det, ← h, mul_comm]
    simp

/- English proof (translation)
Introduce `n t l z hz`. Establish `hD : ∏ p ∈ prs n, ((z p.1 : ℂ) - (z p.2 : ℂ)) ≠ 0`. Use `Finset.prod_ne_zero_iff.mpr fun p hp h => ?_` and prove the remaining obligations. Establish `hlt : p.1 < p.2` using `(Finset.mem_filter.mp hp).2`. Conclude with `hlt.ne (hz (Units.ext (sub_eq_zero.mp h)))`.

Establish `key` using `congrArg (evalAt z) (alternant_mul_altQuot (monomial l * hlFactor n t))`. Rewrite `key` using `[map_mul, evalAt_antisymm, evalAt_alternant]`. Use `mul_left_cancel₀ hD ?_` and prove the remaining obligations. Establish `hR : hlR t l = altQuot (monomial l * hlFactor n t)` using `rfl`. Rewrite using `[hR, key, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Establish `hs` using `sign_sq_one σ`. Establish `hc : ∏ p ∈ prs n, ((z (σ p.1) : ℂ) - (z (σ p.2) : ℂ)) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ p ∈ prs n, ((z p.1 : ℂ) - (z p.2 : ℂ))` using `prod_comp (fun i => (z i : ℂ)) σ`. Rewrite using `[map_mul, monomial, evalAt_single, one_mul, evalAt_hlFactor, Finset.prod_div_distrib, hc]`. Simplify using `only [Function.comp_apply]`.

Establish `hs0 : ((Equiv.Perm.sign σ : ℤ) : ℂ) ≠ 0` using `left_ne_zero_of_mul_eq_one hs`. Clear the denominators using the available nonvanishing facts. Take the linear combination `((monomialChar l (z ∘ σ)) * ∏ p ∈ prs n, ((z (σ p.1) : ℂ) - t * (z (σ p.2) : ℂ))) * hs`.
-/
theorem UpperTheory.Gal.Gen.rFormula_pf :
    UpperTheory.Gal.Gen.RFormula := by
  intro n t l z hz
  have hD : ∏ p ∈ prs n, ((z p.1 : ℂ) - (z p.2 : ℂ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p hp h => ?_
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    exact hlt.ne (hz (Units.ext (sub_eq_zero.mp h)))
  have key := congrArg (evalAt z) (alternant_mul_altQuot (monomial l * hlFactor n t))
  rw [map_mul, evalAt_antisymm, evalAt_alternant] at key
  refine mul_left_cancel₀ hD ?_
  have hR : hlR t l = altQuot (monomial l * hlFactor n t) := rfl
  rw [hR, key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hs := sign_sq_one σ
  have hc : ∏ p ∈ prs n, ((z (σ p.1) : ℂ) - (z (σ p.2) : ℂ)) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ p ∈ prs n, ((z p.1 : ℂ) - (z p.2 : ℂ)) :=
    prod_comp (fun i => (z i : ℂ)) σ
  rw [map_mul, monomial, evalAt_single, one_mul, evalAt_hlFactor, Finset.prod_div_distrib, hc]
  simp only [Function.comp_apply]
  have hs0 : ((Equiv.Perm.sign σ : ℤ) : ℂ) ≠ 0 := left_ne_zero_of_mul_eq_one hs
  field_simp
  linear_combination ((monomialChar l (z ∘ σ)) * ∏ p ∈ prs n, ((z (σ p.1) : ℂ) - t * (z (σ p.2) : ℂ))) * hs
