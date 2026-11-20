import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SplittingFieldIsoQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.KstarRam
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Cases
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.BchiFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.primesex

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Introduce `hB`. Establish `hcop : IsCoprime (p : ℤ) (q : ℤ)`. Rewrite using `[Nat.isCoprime_iff_coprime]`. Conclude with `(Nat.coprime_primes hp hq).2 hpq`. Take `⟨a, b, hab⟩` from `hcop`.

Establish `h1 : ((a : Ω) * (p : Ω) + (b : Ω) * (q : Ω)) = 1`. Use `congrArg (fun z : ℤ => (z : Ω)) hab` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `ha : A.valuation (a : Ω) ≤ 1` using `(A.valuation_le_one_iff _).2 (intCast_mem A a)`.

Establish `hb : A.valuation (b : Ω) ≤ 1` using `(A.valuation_le_one_iff _).2 (intCast_mem A b)`. Establish `hx : A.valuation ((a : Ω) * (p : Ω)) < 1`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hy : A.valuation ((b : Ω) * (q : Ω)) < 1`.

Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hs` using `Valuation.map_add_lt A.valuation hx hy`. Rewrite `hs` using `[h1, map_one]`. Conclude with `lt_irrefl _ hs`.
-/
private theorem not_valuation_lt_one_of_ne_of_valuation_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) (hA : A.valuation (p : Ω) < 1) : ¬ A.valuation (q : Ω) < 1 := by
  intro hB
  have hcop : IsCoprime (p : ℤ) (q : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes hp hq).2 hpq
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : ((a : Ω) * (p : Ω) + (b : Ω) * (q : Ω)) = 1 := by
    have := congrArg (fun z : ℤ => (z : Ω)) hab
    push_cast at this
    exact this
  have ha : A.valuation (a : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A a)
  have hb : A.valuation (b : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A b)
  have hx : A.valuation ((a : Ω) * (p : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (a : Ω) * A.valuation (p : Ω) ≤ 1 * A.valuation (p : Ω) := by gcongr
      _ < 1 := by rw [one_mul]; exact hA
  have hy : A.valuation ((b : Ω) * (q : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (b : Ω) * A.valuation (q : Ω) ≤ 1 * A.valuation (q : Ω) := by gcongr
      _ < 1 := by rw [one_mul]; exact hB
  have hs := Valuation.map_add_lt A.valuation hx hy
  rw [h1, map_one] at hs
  exact lt_irrefl _ hs

/- English proof (translation)
Introduce `h t hBig Ω _ _ _ _ l _ e hl2 he0 het hI O _ _ ψ hψ hpar`. Establish `hB` using `UpperTheory.V.HV.bchiFacts h t hBig`. Establish `hpB : pK h.chi ∈ Bchi h.chi` using `hB.2.1`. Establish `hpPrime : Nat.Prime (pK h.chi)` using `(prime_of_mem_Bchi hpB).1`. Establish `hp4 : pK h.chi % 4 = 3`.

Establish `hne : {p : ℕ | Nat.Prime p ∧ p % 4 = 3 ∧ 7 ≤ p ∧ p.Coprime h.chi.N}.Nonempty`. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[Set.not_nonempty_iff_eq_empty]`. Establish `h0 : pK h.chi = 0`. Unfold `pK`.

Rewrite using `[hc, Nat.sInf_empty]`. Conclude with `hpPrime.ne_zero h0`. Conclude with `(Nat.sInf_mem hne).2.1`. Establish `hK` using `UpperTheory.V.HV.kstar (pK h.chi) hpPrime hp4`. Establish `hlB : l ∉ Bchi h.chi` using `hI.1`.

Establish `hl` using `hB.2.2.2.2 l (Fact.out) hl2 hlB`. Establish `hC` using `(UpperTheory.V.HV.cases h t hBig O ψ hψ l e (Fact.out) hl2 he0 het).1 hlB`. Establish `hlp : l ≠ pK h.chi` using `hl.2.2.2.1`. Establish `hpN : ¬ pK h.chi ∣ h.N` using `hB.2.2.1`. Use `⟨hl2, he0, ?_, hC.1, hC.2.1, hpar, hK.2.2.1, hK.2.1, ?_, ?_, ?_, hI.2⟩` and prove the remaining obligations.

Rewrite using `[even_iff_two_dvd]`. Conclude with `(dvd_pow_self 2 (by omega : h.ex + 2 ≠ 0)).trans h.two_pow_dvd`. Rewrite using `[hK.1]`. Establish `habs : (-(pK h.chi : ℤ)).natAbs = pK h.chi` using `by simp`. Rewrite using `[habs]`.

Introduce `hdvd`. Break down `(Nat.Prime.dvd_mul (Fact.out : Nat.Prime l)).1 hdvd with h1 | h1` into its components or cases. Conclude with `hlp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hpPrime).1 h1)`. Conclude with `hl.2.2.2.2.1 h1`. Rewrite using `[hK.1]`.

Establish `habs : (-(pK h.chi : ℤ)).natAbs = pK h.chi` using `by simp`. Rewrite using `[habs]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hpPrime).2 hpN`. Introduce `hle`. Take `⟨A, hA⟩` from `(UpperTheory.V.Chr.placesQ Ω).1 (pK h.chi) hpPrime`.

Apply `UpperTheory.V.HV.kstarRam (pK h.chi) hpPrime hp4 Ω A hA` to reduce the goal to its premises. Introduce `x hx`. Apply `hle` to reduce the goal to its premises. Rewrite using `[Subgroup.mem_inf]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `hlA : ¬ A.valuation (l : Ω) < 1` using `not_valuation_lt_one_of_ne_of_valuation_lt_one A (pK h.chi) l hpPrime Fact.out (Ne.symm hlp) hA`. Use `((UpperTheory.V.Base.places ℚ Ω l A).2.2.2 hlA) hx` as an intermediate fact. Rewrite `this`, the goal using `[MonoidHom.mem_ker]`. Simplify using `[cycMod, this]`. Establish `hNA : ¬ A.valuation (h.N : Ω) < 1`.

Rewrite using `[(UpperTheory.V.Chr.placesQ Ω).2.1 A h.N (NeZero.ne _)]`. Introduce and unpack `⟨q, hqN, hq⟩`. Establish `hqP : Nat.Prime q` using `Nat.prime_of_mem_primeFactors hqN`. Establish `hne : pK h.chi ≠ q`. Introduce and unpack `rfl`.

Conclude with `hpN (Nat.dvd_of_mem_primeFactors hqN)`. Conclude with `not_valuation_lt_one_of_ne_of_valuation_lt_one A (pK h.chi) q hpPrime hqP hne hA hq`. Use `((UpperTheory.V.Chr.clsFacts ℚ Ω h.N).2.2.2.2 A hNA) hx` as an intermediate fact. Rewrite `this`, the goal using `[MonoidHom.mem_ker]`. Simplify using `[UpperTheory.V.Chr.dirG, this]`.
-/
theorem UpperTheory.V.HV.gdOfHost :
    ∀ (h : Host) (t : ℕ), h.Big t → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra (Kstar (pK h.chi)) Ω] (l : ℕ) [Fact l.Prime] (e : ℕ), l ≠ 2 → 0 < e → e < t → h.CaseI l e →
      ∀ (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ → PsiEven e ψ → GD Ω (Kstar (pK h.chi)) l e ψ := by
  intro h t hBig Ω _ _ _ _ l _ e hl2 he0 het hI O _ _ ψ hψ hpar
  have hB := UpperTheory.V.HV.bchiFacts h t hBig
  have hpB : pK h.chi ∈ Bchi h.chi := hB.2.1
  have hpPrime : Nat.Prime (pK h.chi) := (prime_of_mem_Bchi hpB).1
  have hp4 : pK h.chi % 4 = 3 := by
    have hne : {p : ℕ | Nat.Prime p ∧ p % 4 = 3 ∧ 7 ≤ p ∧ p.Coprime h.chi.N}.Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      have h0 : pK h.chi = 0 := by
        unfold pK
        rw [hc, Nat.sInf_empty]
      exact hpPrime.ne_zero h0
    exact (Nat.sInf_mem hne).2.1
  have hK := UpperTheory.V.HV.kstar (pK h.chi) hpPrime hp4
  have hlB : l ∉ Bchi h.chi := hI.1
  have hl := hB.2.2.2.2 l (Fact.out) hl2 hlB
  have hC := (UpperTheory.V.HV.cases h t hBig O ψ hψ l e (Fact.out) hl2 he0 het).1 hlB
  have hlp : l ≠ pK h.chi := hl.2.2.2.1
  have hpN : ¬ pK h.chi ∣ h.N := hB.2.2.1
  refine ⟨hl2, he0, ?_, hC.1, hC.2.1, hpar, hK.2.2.1, hK.2.1, ?_, ?_, ?_, hI.2⟩
  · rw [even_iff_two_dvd]
    exact (dvd_pow_self 2 (by omega : h.ex + 2 ≠ 0)).trans h.two_pow_dvd
  · rw [hK.1]
    have habs : (-(pK h.chi : ℤ)).natAbs = pK h.chi := by simp
    rw [habs]
    intro hdvd
    rcases (Nat.Prime.dvd_mul (Fact.out : Nat.Prime l)).1 hdvd with h1 | h1
    · exact hlp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hpPrime).1 h1)
    · exact hl.2.2.2.2.1 h1
  · rw [hK.1]
    have habs : (-(pK h.chi : ℤ)).natAbs = pK h.chi := by simp
    rw [habs]
    exact (Nat.Prime.coprime_iff_not_dvd hpPrime).2 hpN
  · intro hle
    obtain ⟨A, hA⟩ := (UpperTheory.V.Chr.placesQ Ω).1 (pK h.chi) hpPrime
    apply UpperTheory.V.HV.kstarRam (pK h.chi) hpPrime hp4 Ω A hA
    intro x hx
    apply hle
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · have hlA : ¬ A.valuation (l : Ω) < 1 := not_valuation_lt_one_of_ne_of_valuation_lt_one A (pK h.chi) l hpPrime Fact.out (Ne.symm hlp) hA
      have := ((UpperTheory.V.Base.places ℚ Ω l A).2.2.2 hlA) hx
      rw [MonoidHom.mem_ker] at this ⊢
      simp [cycMod, this]
    · have hNA : ¬ A.valuation (h.N : Ω) < 1 := by
        rw [(UpperTheory.V.Chr.placesQ Ω).2.1 A h.N (NeZero.ne _)]
        rintro ⟨q, hqN, hq⟩
        have hqP : Nat.Prime q := Nat.prime_of_mem_primeFactors hqN
        have hne : pK h.chi ≠ q := by
          rintro rfl
          exact hpN (Nat.dvd_of_mem_primeFactors hqN)
        exact not_valuation_lt_one_of_ne_of_valuation_lt_one A (pK h.chi) q hpPrime hqP hne hA hq
      have := ((UpperTheory.V.Chr.clsFacts ℚ Ω h.N).2.2.2.2 A hNA) hx
      rw [MonoidHom.mem_ker] at this ⊢
      simp [UpperTheory.V.Chr.dirG, this]
