import Mathlib

namespace GlobalTheory.CompanionTheory.SemistableLocal

open MvPolynomial in

/- English proof (translation)
Use `set g : MvPolynomial (Fin m') O := ∏ j ∈ Finset.univ.filter (fun j : Fin m' => (j : ℕ) + 1 < r), MvPolynomial.X j with hgdef`. Establish `hprod : (∏ i ∈ Finset.univ.filter (fun i : Fin (m' + 1) => (i : ℕ) < r), (MvPolynomial.X i : MvPolynomial (Fin (m' + 1)) O)) = MvPolynomial.X 0 * ∏ j ∈ Finset.univ.filter (fun j : Fin m' => (j : ℕ) + 1 < r), (MvPolynomial.X (Fin.succ j) : MvPolynomial (Fin (m' + 1)) O)`. Rewrite using `[Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_succ]`. Establish `h0 : 0 < r` using `by omega`. Simplify using `[Fin.val_succ, h0]`.

Establish `hC : MvPolynomial.finSuccEquiv O m' (MvPolynomial.C ϖ) = Polynomial.C (MvPolynomial.C ϖ)`. Establish `h` using `(MvPolynomial.finSuccEquiv O m').commutes ϖ`. Rewrite `h` using `[MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]`. Conclude with `h`. Establish `hϖ0 : (MvPolynomial.C ϖ : MvPolynomial (Fin m') O) ≠ 0`.

Rewrite using `[Ne, MvPolynomial.C_eq_zero]`. Conclude with `hϖ.ne_zero`. Establish `hg0 : g ≠ 0`. Introduce `h`. Establish `h1` using `congrArg (MvPolynomial.eval (fun _ : Fin m' => (1 : O))) h`.

Simplify using `[hgdef] at h1`. Establish `hcop : ∀ a : MvPolynomial (Fin m') O, a ∣ g → a ∣ MvPolynomial.C ϖ → IsUnit a`. Introduce `a hag hac`. Take `⟨s, hs⟩` from `hac`. Establish `ha0 : a ≠ 0` using `by rintro rfl; rw [zero_mul] at hs; exact hϖ0 hs`.

Establish `hs0 : s ≠ 0` using `by rintro rfl; rw [mul_zero] at hs; exact hϖ0 hs`. Establish `hdeg` using `MvPolynomial.totalDegree_mul_of_isDomain ha0 hs0`. Rewrite `hdeg` using `[← hs, MvPolynomial.totalDegree_C]`. Establish `hda : a.totalDegree = 0` using `by omega`. Rewrite `hda` using `[MvPolynomial.totalDegree_eq_zero_iff_eq_C]`.

Rewrite `hag`, the goal using `[hda]`. Use `IsUnit.map MvPolynomial.C (isUnit_of_dvd_one ?_)` and prove the remaining obligations. Establish `h1` using `map_dvd (MvPolynomial.eval (fun _ : Fin m' => (1 : O))) hag`. Simplify `h1` using `[hgdef]`. Establish `hirr : Irreducible (Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) : Polynomial (MvPolynomial (Fin m') O))`.

Establish `hdeg : (Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) : Polynomial (MvPolynomial (Fin m') O)).natDegree = 1` using `Polynomial.natDegree_linear hg0`. Establish `key2 : ∀ c d : Polynomial (MvPolynomial (Fin m') O), Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) = c * d → c.natDegree = 0 → IsUnit c`. Introduce `c d hcd hc`. Establish `hc'` using `Polynomial.eq_C_of_natDegree_eq_zero hc`. Establish `hdvd : Polynomial.C (c.coeff 0) ∣ Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ)`.

Rewrite using `[← hc']`. Conclude with `⟨d, hcd⟩`. Rewrite `hdvd` using `[Polynomial.C_dvd_iff_dvd_coeff]`. Rewrite using `[hc']`. Use `IsUnit.map Polynomial.C (hcop _ ?_ ?_)` and prove the remaining obligations.

Simplify `hdvd 1` using `[Polynomial.coeff_C_mul_X, Polynomial.coeff_C]`. Simplify `hdvd 0` using `[Polynomial.coeff_C_mul_X, Polynomial.coeff_C]`. Use `irreducible_iff.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `hu`. Establish `h0` using `Polynomial.natDegree_eq_zero_of_isUnit hu`.

Use linear arithmetic over natural numbers and integers. Introduce `a b hab`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `hab` using `[zero_mul]`.

Rewrite `hdeg` using `[hab]`. Simplify using `at hdeg`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Rewrite `hab` using `[mul_zero]`.

Rewrite `hdeg` using `[hab]`. Simplify using `at hdeg`. Establish `hsum` using `Polynomial.natDegree_mul ha0 hb0`. Rewrite `hsum` using `[← hab, hdeg]`. Break down `Nat.eq_zero_or_pos a.natDegree with h | h` into its components or cases.

Conclude with `Or.inl (key2 a b hab h)`. Conclude with `Or.inr (key2 b a (by rw [hab, mul_comm]) (by omega))`. Use `(MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv O m')).mp ?_` and prove the remaining obligations. Rewrite using `[hprod, map_sub, map_mul, map_prod, MvPolynomial.finSuccEquiv_X_zero, hC]`. Simplify using `only [MvPolynomial.finSuccEquiv_X_succ]`.

Use `hirr using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hgdef, map_prod, map_neg]`. Expand and normalize the polynomial expressions, which then agree.
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
Introduce `O _ _ _ ϖ hϖ m r hr hrm`. Take `⟨m', rfl⟩ : ∃ m', m = m' + 1` from `⟨m - 1, by omega⟩`. Establish `hirr` using `irreducible_prod_X_sub_C O ϖ hϖ m' r hr`. Use `haveI : UniqueFactorizationMonoid (MvPolynomial (Fin (m' + 1)) O) := MvPolynomial.uniqueFactorizationMonoid _`. Establish `hp` using `UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr`.

Use `haveI := (Ideal.span_singleton_prime hp.ne_zero).mpr hp`. Conclude with `Ideal.Quotient.isDomain _`.
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
