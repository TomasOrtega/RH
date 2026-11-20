import Mathlib
open MvPolynomial

namespace GlobalTheory

/- English proof (translation)
Establish `hr : ∀ q : MvPolynomial σ ℂ, sumAlgEquiv ℂ (Fin L) σ (rename Sum.inr q) = C q`. Introduce `q`. Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C r => simp [sumAlgEquiv_C_inl]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.

Consider the case `mul_X p c hp => rw [map_mul, map_mul, hp, rename_X, sumAlgEquiv_X_inr, map_mul]`. Establish `hx : ∀ i : Fin L, sumAlgEquiv ℂ (Fin L) σ (X (Sum.inl i)) = X i` using `fun i => sumAlgEquiv_X_inl ℂ (Fin L) σ i`. Establish `cmC : ∀ {τ : Type} (n : τ →₀ ℕ) (p : MvPolynomial τ (MvPolynomial σ ℂ)) (c : MvPolynomial σ ℂ), coeff n (p * C c) = coeff n p * c`. Introduce `τ n p c`. Rewrite using `[mul_comm, coeff_C_mul, mul_comm]`.

Use `set e : Fin L →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ) with he`. Establish `hmono : ∀ t : Finset (Fin L), coeff e (∏ i ∈ t, (X i * C (m i) : MvPolynomial (Fin L) (MvPolynomial σ ℂ))) = if t = Finset.univ then ∏ i, m i else 0`. Introduce `t`. Rewrite using `[Finset.prod_mul_distrib, ← map_prod, cmC]`. Establish `hX : (∏ i ∈ t, (X i : MvPolynomial (Fin L) (MvPolynomial σ ℂ))) = monomial (∑ i ∈ t, Finsupp.single i 1) 1`.

Rewrite using `[monomial_sum_one]`. Both sides reduce to the same expression. Rewrite using `[hX, coeff_monomial]`. Distinguish the cases in `ht : t = Finset.univ`. Substitute `ht` using the available equality.

Establish `: (∑ i ∈ (Finset.univ : Finset (Fin L)), Finsupp.single i 1) = e`. Use extensionality with `j`. Simplify using `[he, Finsupp.finset_sum_apply, Finsupp.single_apply]`. Simplify using `[this]`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, j ∉ t := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `ht (Finset.eq_univ_iff_forall.mpr h)`. Establish `: (∑ i ∈ t, Finsupp.single i 1) ≠ e`. Introduce `h`.

Use `congrArg (fun f => f j) h` as an intermediate fact. Simplify using `[he, Finsupp.finset_sum_apply, Finsupp.single_apply, hj] at this`. Simplify using `[this, ht]`. Rewrite using `[map_mul, hr, cmC, map_prod]`. Repeatedly rewrite using `[map_add, map_one, map_mul, hr, hx]`.

Rewrite using `[Finset.prod_one_add, coeff_sum, Finset.sum_eq_single Finset.univ]`. Rewrite using `[hmono]`. Simplify using the standard rewrite rules. Introduce `t _ ht`. Rewrite using `[hmono, if_neg ht]`.

Introduce `h`. Conclude with `absurd (Finset.mem_powerset.mpr (Finset.Subset.refl _)) h`.
-/
theorem coeff_allOnes_prod_one_add_mul {σ : Type} {L : ℕ} (m : Fin L → MvPolynomial σ ℂ)
    (a : MvPolynomial σ ℂ) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ))
      (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ ((∏ i, (1 + MvPolynomial.X (Sum.inl i) *
        MvPolynomial.rename Sum.inr (m i))) * MvPolynomial.rename Sum.inr a)) = (∏ i, m i) * a := by
  have hr : ∀ q : MvPolynomial σ ℂ, sumAlgEquiv ℂ (Fin L) σ (rename Sum.inr q) = C q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r => simp [sumAlgEquiv_C_inl]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p c hp => rw [map_mul, map_mul, hp, rename_X, sumAlgEquiv_X_inr, map_mul]
  have hx : ∀ i : Fin L, sumAlgEquiv ℂ (Fin L) σ (X (Sum.inl i)) = X i := fun i =>
    sumAlgEquiv_X_inl ℂ (Fin L) σ i
  have cmC : ∀ {τ : Type} (n : τ →₀ ℕ) (p : MvPolynomial τ (MvPolynomial σ ℂ)) (c : MvPolynomial σ ℂ),
      coeff n (p * C c) = coeff n p * c := by
    intro τ n p c; rw [mul_comm, coeff_C_mul, mul_comm]
  set e : Fin L →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ) with he
  have hmono : ∀ t : Finset (Fin L),
      coeff e (∏ i ∈ t, (X i * C (m i) : MvPolynomial (Fin L) (MvPolynomial σ ℂ))) =
        if t = Finset.univ then ∏ i, m i else 0 := by
    intro t
    rw [Finset.prod_mul_distrib, ← map_prod, cmC]
    have hX : (∏ i ∈ t, (X i : MvPolynomial (Fin L) (MvPolynomial σ ℂ))) =
        monomial (∑ i ∈ t, Finsupp.single i 1) 1 := by
      rw [monomial_sum_one]; rfl
    rw [hX, coeff_monomial]
    by_cases ht : t = Finset.univ
    · subst ht
      have : (∑ i ∈ (Finset.univ : Finset (Fin L)), Finsupp.single i 1) = e := by
        ext j; simp [he, Finsupp.finset_sum_apply, Finsupp.single_apply]
      simp [this]
    · obtain ⟨j, hj⟩ : ∃ j, j ∉ t := by
        by_contra h; push_neg at h; exact ht (Finset.eq_univ_iff_forall.mpr h)
      have : (∑ i ∈ t, Finsupp.single i 1) ≠ e := by
        intro h
        have := congrArg (fun f => f j) h
        simp [he, Finsupp.finset_sum_apply, Finsupp.single_apply, hj] at this
      simp [this, ht]
  rw [map_mul, hr, cmC, map_prod]
  simp_rw [map_add, map_one, map_mul, hr, hx]
  rw [Finset.prod_one_add, coeff_sum, Finset.sum_eq_single Finset.univ]
  · rw [hmono]; simp
  · intro t _ ht; rw [hmono, if_neg ht]
  · intro h; exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl _)) h

end GlobalTheory
