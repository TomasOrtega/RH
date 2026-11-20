import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Substitute using the available equality. Supply the required witnesses or components.
-/
private theorem exists_fin_map {α : Type} (s : Multiset α) (n : ℕ) (h : Multiset.card s = n) :
    ∃ x : Fin n → α, Finset.univ.val.map x = s := by
  induction s using Quotient.inductionOn with
  | h l =>
    have h' : l.length = n := by simpa using h
    subst h'
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
private theorem esymm_surj (n : ℕ) (y : Fin n → ℂ) :
    ∃ x : Fin n → ℂ, ∀ i : Fin n, aeval x (esymm (Fin n) ℂ (i + 1)) = y i := by
  set q : Polynomial ℂ :=
    ∑ j : Fin n, Polynomial.C ((-1) ^ (n - j) * y j.rev) * Polynomial.X ^ (j : ℕ) with hq
  have hqd : q.degree < n := Polynomial.degree_sum_fin_lt _
  set p : Polynomial ℂ := Polynomial.X ^ n + q with hp
  have hm : p.Monic := Polynomial.monic_X_pow_add hqd
  have hd : p.natDegree = n := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    rw [hp, Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
    rwa [Polynomial.degree_X_pow]
  have hc : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  obtain ⟨x, hx⟩ := exists_fin_map p.roots n (hc.trans hd)
  refine ⟨x, fun i => ?_⟩
  rw [aeval_esymm_eq_multiset_esymm, hx]
  have hi := i.2
  have h1 := Polynomial.coeff_eq_esymm_roots_of_card hc (k := (i.rev : ℕ)) (by rw [hd]; exact i.rev.2.le)
  have e : n - (i.rev : ℕ) = i + 1 := by rw [Fin.val_rev]; omega
  have h2 : p.coeff (i.rev : ℕ) = (-1) ^ ((i : ℕ) + 1) * y i := by
    rw [hp, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg i.rev.2.ne, zero_add, hq,
      Polynomial.finsetSum_coeff, Finset.sum_eq_single i.rev]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl, e, Fin.rev_rev]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul_X_pow, if_neg (fun h => hb (Fin.ext h.symm))]
    · simp
  rw [hd, e, hm.leadingCoeff, one_mul, h2] at h1
  exact (mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h1).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.FX.blockE_inj :
    ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ), Function.Injective (aeval (blockE (τ := τ) (n := n)) : MvPolynomial (τ × Fin n) ℂ →ₐ[ℂ] MvPolynomial (τ × Fin n) ℂ) := by
  intro τ _ _ n G H hGH
  apply MvPolynomial.funext
  intro y
  choose x hx using fun t : τ => esymm_surj n (fun i => y (t, i))
  have key : ∀ P : MvPolynomial (τ × Fin n) ℂ,
      aeval (fun ti : τ × Fin n => x ti.1 ti.2) (aeval (blockE (τ := τ) (n := n)) P) = eval y P := by
    intro P
    have hf : (fun ti : τ × Fin n => aeval (fun ti : τ × Fin n => x ti.1 ti.2) (blockE ti)) = y := by
      funext ⟨t, i⟩
      rw [blockE, aeval_rename]
      exact hx t i
    rw [← AlgHom.comp_apply, comp_aeval, hf]
    rfl
  rw [← key, ← key, hGH]
