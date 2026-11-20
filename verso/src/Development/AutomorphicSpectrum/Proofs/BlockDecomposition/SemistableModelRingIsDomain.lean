import Mathlib

namespace GlobalTheory.CompanionTheory.SemistableLocal

open MvPolynomial in

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem irreducible_prod_X_sub_C (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (m' r : ℕ) (hr : 1 ≤ r) :
    Irreducible ((∏ i ∈ Finset.univ.filter (fun i : Fin (m' + 1) => (i : ℕ) < r), X i) - C ϖ :
      MvPolynomial (Fin (m' + 1)) O) := by
  set g : MvPolynomial (Fin m') O :=
    ∏ j ∈ Finset.univ.filter (fun j : Fin m' => (j : ℕ) + 1 < r), MvPolynomial.X j with hgdef
  have hprod : (∏ i ∈ Finset.univ.filter (fun i : Fin (m' + 1) => (i : ℕ) < r),
      (MvPolynomial.X i : MvPolynomial (Fin (m' + 1)) O))
      = MvPolynomial.X 0 * ∏ j ∈ Finset.univ.filter (fun j : Fin m' => (j : ℕ) + 1 < r),
          (MvPolynomial.X (Fin.succ j) : MvPolynomial (Fin (m' + 1)) O) := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_succ]
    have h0 : 0 < r := by omega
    simp [Fin.val_succ, h0]
  have hC : MvPolynomial.finSuccEquiv O m' (MvPolynomial.C ϖ) =
      Polynomial.C (MvPolynomial.C ϖ) := by
    have h := (MvPolynomial.finSuccEquiv O m').commutes ϖ
    rw [MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq] at h
    exact h
  have hϖ0 : (MvPolynomial.C ϖ : MvPolynomial (Fin m') O) ≠ 0 := by
    rw [Ne, MvPolynomial.C_eq_zero]; exact hϖ.ne_zero
  have hg0 : g ≠ 0 := by
    intro h
    have h1 := congrArg (MvPolynomial.eval (fun _ : Fin m' => (1 : O))) h
    simp [hgdef] at h1
  have hcop : ∀ a : MvPolynomial (Fin m') O, a ∣ g → a ∣ MvPolynomial.C ϖ → IsUnit a := by
    intro a hag hac
    obtain ⟨s, hs⟩ := hac
    have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul] at hs; exact hϖ0 hs
    have hs0 : s ≠ 0 := by rintro rfl; rw [mul_zero] at hs; exact hϖ0 hs
    have hdeg := MvPolynomial.totalDegree_mul_of_isDomain ha0 hs0
    rw [← hs, MvPolynomial.totalDegree_C] at hdeg
    have hda : a.totalDegree = 0 := by omega
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hda
    rw [hda] at hag ⊢
    refine IsUnit.map MvPolynomial.C (isUnit_of_dvd_one ?_)
    have h1 := map_dvd (MvPolynomial.eval (fun _ : Fin m' => (1 : O))) hag
    simpa [hgdef] using h1
  have hirr : Irreducible (Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) :
      Polynomial (MvPolynomial (Fin m') O)) := by
    have hdeg : (Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) :
        Polynomial (MvPolynomial (Fin m') O)).natDegree = 1 := Polynomial.natDegree_linear hg0
    have key2 : ∀ c d : Polynomial (MvPolynomial (Fin m') O),
        Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) = c * d →
          c.natDegree = 0 → IsUnit c := by
      intro c d hcd hc
      have hc' := Polynomial.eq_C_of_natDegree_eq_zero hc
      have hdvd : Polynomial.C (c.coeff 0) ∣
          Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) := by
        rw [← hc']; exact ⟨d, hcd⟩
      rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvd
      rw [hc']
      refine IsUnit.map Polynomial.C (hcop _ ?_ ?_)
      · simpa [Polynomial.coeff_C_mul_X, Polynomial.coeff_C] using hdvd 1
      · simpa [Polynomial.coeff_C_mul_X, Polynomial.coeff_C] using hdvd 0
    refine irreducible_iff.mpr ⟨?_, ?_⟩
    · intro hu
      have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · intro a b hab
      have ha0 : a ≠ 0 := by
        rintro rfl; rw [zero_mul] at hab; rw [hab] at hdeg; simp at hdeg
      have hb0 : b ≠ 0 := by
        rintro rfl; rw [mul_zero] at hab; rw [hab] at hdeg; simp at hdeg
      have hsum := Polynomial.natDegree_mul ha0 hb0
      rw [← hab, hdeg] at hsum
      rcases Nat.eq_zero_or_pos a.natDegree with h | h
      · exact Or.inl (key2 a b hab h)
      · exact Or.inr (key2 b a (by rw [hab, mul_comm]) (by omega))
  refine (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv O m')).mp ?_
  rw [hprod, map_sub, map_mul, map_prod, MvPolynomial.finSuccEquiv_X_zero, hC]
  simp only [MvPolynomial.finSuccEquiv_X_succ]
  convert hirr using 1
  rw [hgdef, map_prod, map_neg]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isDomain_quotient_prod_X_sub_C :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
      ∀ (m r : ℕ), 1 ≤ r → r ≤ m →
        IsDomain (MvPolynomial (Fin m) O ⧸ Ideal.span
          {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
            MvPolynomial.C ϖ}) := by
  intro O _ _ _ ϖ hϖ m r hr hrm
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hirr := irreducible_prod_X_sub_C O ϖ hϖ m' r hr
  haveI : UniqueFactorizationMonoid (MvPolynomial (Fin (m' + 1)) O) :=
    MvPolynomial.uniqueFactorizationMonoid _
  have hp := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  haveI := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  exact Ideal.Quotient.isDomain _

end GlobalTheory.CompanionTheory.SemistableLocal
