import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Use `haveI := c.dvr`. Use `haveI := c.fin`. Take `⟨-, hfin, hlm, -, -, -⟩` from `UpperTheory.V.abelian₂.dvr_finite l c.O`. Establish `hchar : CharP (ResidueField c.O) l`. Take `⟨p, hp⟩` from `CharP.exists (ResidueField c.O)`.

Establish `hp0` using `CharP.char_ne_zero_of_finite (ResidueField c.O) p`. Use `haveI : NeZero p := ⟨hp0⟩`. Establish `hpp` using `(CharP.char_is_prime_of_pos (ResidueField c.O) p).out`. Establish `hl0 : ((l : ℕ) : ResidueField c.O) = 0`. Rewrite using `[← map_natCast (residue c.O)]`.

Conclude with `(IsLocalRing.residue_eq_zero_iff _).2 hlm`. Establish `hdvd : p ∣ l` using `(CharP.cast_eq_zero_iff (ResidueField c.O) p l).1 hl0`. Establish `hpl : p = l` using `(Nat.prime_dvd_prime_iff_eq hpp hl.out).1 hdvd`. Substitute `hpl` using the available equality. Conclude with `hp`.

Use `⟨hfin, hchar, ?_, ?_⟩` and prove the remaining obligations. Introduce `c' h haveI := c'.fin`. Establish `hint : (inc h).IsIntegral`. Introduce `y`. Take `⟨p, hp, hpy⟩` from `Algebra.IsIntegral.isIntegral (R := ℤ_[l]) y`.

Use `⟨p.map (algebraMap ℤ_[l] c.O), hp.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`. Establish `hcomp : (inc h).comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c'.O` using `RingHom.ext fun a => (Subalgebra.inclusion h).commutes a`. Rewrite using `[hcomp]`. Conclude with `hpy`.

Conclude with `hint.isLocalHom (Subalgebra.inclusion_injective h)`. Introduce `m x hcop hxm hres`. Establish `hnd : ¬ l ∣ m` using `(Nat.Prime.coprime_iff_not_dvd hl.out).1 hcop`. Establish `hsum : IsUnit (∑ i ∈ Finset.range m, x ^ i)`. Assume the negation of the conclusion as `hnu`.

Establish `hmem : (∑ i ∈ Finset.range m, x ^ i) ∈ maximalIdeal c.O` using `(IsLocalRing.mem_maximalIdeal _).2 hnu`. Establish `h0` using `(IsLocalRing.residue_eq_zero_iff _).2 hmem`. Rewrite `h0` using `[map_sum]`. Simplify using `only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h0`. Conclude with `hnd ((CharP.cast_eq_zero_iff (ResidueField c.O) l m).1 h0)`.

Establish `hg` using `geom_sum_mul x m`. Rewrite `hg` using `[hxm, sub_self]`. Establish `hx1 : x - 1 = 0`. Break down `mul_eq_zero.1 hg with h | h` into its components or cases. Conclude with `absurd (h ▸ hsum) not_isUnit_zero`.

Conclude with `h`. Conclude with `sub_eq_zero.1 hx1`.
-/
theorem UpperTheory.V.Ws.P1.coefRes {l : ℕ} [hl : Fact l.Prime] (c : Coef l) :
    Finite (ResidueField c.O) ∧ CharP (ResidueField c.O) l ∧
      (∀ (c' : Coef l) (h : c.O ≤ c'.O), IsLocalHom (inc h)) ∧
      ∀ (m : ℕ) (x : c.O), l.Coprime m → x ^ m = 1 → residue c.O x = 1 → x = 1 := by
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, hfin, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  have hchar : CharP (ResidueField c.O) l := by
    obtain ⟨p, hp⟩ := CharP.exists (ResidueField c.O)
    have hp0 := CharP.char_ne_zero_of_finite (ResidueField c.O) p
    haveI : NeZero p := ⟨hp0⟩
    have hpp := (CharP.char_is_prime_of_pos (ResidueField c.O) p).out
    have hl0 : ((l : ℕ) : ResidueField c.O) = 0 := by
      rw [← map_natCast (residue c.O)]
      exact (IsLocalRing.residue_eq_zero_iff _).2 hlm
    have hdvd : p ∣ l := (CharP.cast_eq_zero_iff (ResidueField c.O) p l).1 hl0
    have hpl : p = l := (Nat.prime_dvd_prime_iff_eq hpp hl.out).1 hdvd
    subst hpl
    exact hp
  refine ⟨hfin, hchar, ?_, ?_⟩
  · intro c' h
    haveI := c'.fin
    have hint : (inc h).IsIntegral := by
      intro y
      obtain ⟨p, hp, hpy⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[l]) y
      refine ⟨p.map (algebraMap ℤ_[l] c.O), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : (inc h).comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c'.O :=
        RingHom.ext fun a => (Subalgebra.inclusion h).commutes a
      rw [hcomp]
      exact hpy
    exact hint.isLocalHom (Subalgebra.inclusion_injective h)
  · intro m x hcop hxm hres
    have hnd : ¬ l ∣ m := (Nat.Prime.coprime_iff_not_dvd hl.out).1 hcop
    have hsum : IsUnit (∑ i ∈ Finset.range m, x ^ i) := by
      by_contra hnu
      have hmem : (∑ i ∈ Finset.range m, x ^ i) ∈ maximalIdeal c.O :=
        (IsLocalRing.mem_maximalIdeal _).2 hnu
      have h0 := (IsLocalRing.residue_eq_zero_iff _).2 hmem
      rw [map_sum] at h0
      simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one] at h0
      exact hnd ((CharP.cast_eq_zero_iff (ResidueField c.O) l m).1 h0)
    have hg := geom_sum_mul x m
    rw [hxm, sub_self] at hg
    have hx1 : x - 1 = 0 := by
      rcases mul_eq_zero.1 hg with h | h
      · exact absurd (h ▸ hsum) not_isUnit_zero
      · exact h
    exact sub_eq_zero.1 hx1
