import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.IntDvdAdele

/- English proof (translation)
Establish `e : ((r : v.adicCompletion ℚ)) = algebraMap ℤ (v.adicCompletion ℚ) r` using `(eq_intCast _ r).symm`. Rewrite using `[e, valuedAdicCompletion_eq_valuation, valuation_of_algebraMap, intValuation_le_pow_iff_mem]`.
-/
theorem valued_intCast_le_iff (v : HeightOneSpectrum ℤ) (r : ℤ) (k : ℕ) :
    Valued.v ((r : v.adicCompletion ℚ)) ≤ WithZero.exp (-(k : ℤ)) ↔ r ∈ v.asIdeal ^ k := by
  have e : ((r : v.adicCompletion ℚ)) = algebraMap ℤ (v.adicCompletion ℚ) r := (eq_intCast _ r).symm
  rw [e, valuedAdicCompletion_eq_valuation, valuation_of_algebraMap, intValuation_le_pow_iff_mem]

def placeAt {p : ℕ} (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) : AwayP p :=
  ⟨⟨Ideal.span {(l : ℤ)},
    (Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.mp hl),
    by simp [hl.ne_zero]⟩, by
    intro h
    have h' := Ideal.span_singleton_eq_span_singleton.1 h
    rw [Int.associated_iff_natAbs] at h'
    simp at h'
    exact hlp h'⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem placeAt_asIdeal {p : ℕ} (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) :
    (placeAt (p := p) l hl hlp).1.asIdeal = Ideal.span {(l : ℤ)} := rfl

/- English proof (translation)
Introduce `p _ n hn hcop z w hw hz`. Rewrite using `[Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]`. Introduce `l k hl hlk`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Simplify using the standard rewrite rules.

Establish `hl' : l.Prime` using `hl`. Establish `hln : l ∣ n` using `(dvd_pow_self l hk.ne').trans hlk`. Establish `hlp : l ≠ p`. Introduce and unpack `rfl`. Establish `h1 : Nat.Coprime l l` using `Nat.Coprime.coprime_dvd_left hln hcop`.

Conclude with `hl'.one_lt.ne' ((Nat.coprime_self l).1 h1)`. Use `set v := placeAt (p := p) l hl' hlp`. Establish `hzv` using `congrArg (AfP.eval v) hz`. Rewrite `hzv` using `[map_intCast, map_mul, map_natCast]`. Establish `hwv : Valued.v (AfP.eval v w) ≤ 1` using `hw v`.

Establish `hnv : Valued.v (((n : ℤ) : v.1.adicCompletion ℚ)) ≤ WithZero.exp (-(k : ℤ))`. Rewrite using `[valued_intCast_le_iff, placeAt_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `hlk` after adjusting the coercions. Establish `hzle : Valued.v ((z : v.1.adicCompletion ℚ)) ≤ WithZero.exp (-(k : ℤ))`. Rewrite using `[hzv, map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `hzle` using `[valued_intCast_le_iff, placeAt_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Establish `: ((l ^ k : ℕ) : ℤ) ∣ z` using `by exact_mod_cast hzle`. Conclude with `Int.natCast_dvd.1 this`.
-/
theorem dvd_of_eq_mul_int : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → n.Coprime p → ∀ (z : ℤ) (w : AfP p),
    IsIntAf w → (z : AfP p) = (n : AfP p) * w → (n : ℤ) ∣ z := by
  intro p _ n hn hcop z w hw hz
  rw [Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro l k hl hlk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hl' : l.Prime := hl
  have hln : l ∣ n := (dvd_pow_self l hk.ne').trans hlk
  have hlp : l ≠ p := by
    rintro rfl
    have h1 : Nat.Coprime l l := Nat.Coprime.coprime_dvd_left hln hcop
    exact hl'.one_lt.ne' ((Nat.coprime_self l).1 h1)
  set v := placeAt (p := p) l hl' hlp
  have hzv := congrArg (AfP.eval v) hz
  rw [map_intCast, map_mul, map_natCast] at hzv
  have hwv : Valued.v (AfP.eval v w) ≤ 1 := hw v
  have hnv : Valued.v (((n : ℤ) : v.1.adicCompletion ℚ)) ≤ WithZero.exp (-(k : ℤ)) := by
    rw [valued_intCast_le_iff, placeAt_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact_mod_cast hlk
  have hzle : Valued.v ((z : v.1.adicCompletion ℚ)) ≤ WithZero.exp (-(k : ℤ)) := by
    rw [hzv, map_mul]
    calc Valued.v ((n : v.1.adicCompletion ℚ)) * Valued.v (AfP.eval v w)
        ≤ Valued.v ((n : v.1.adicCompletion ℚ)) * 1 := by gcongr
      _ = Valued.v (((n : ℤ) : v.1.adicCompletion ℚ)) := by rw [_root_.mul_one, Int.cast_natCast]
      _ ≤ _ := hnv
  rw [valued_intCast_le_iff, placeAt_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hzle
  have : ((l ^ k : ℕ) : ℤ) ∣ z := by exact_mod_cast hzle
  exact Int.natCast_dvd.1 this

end GlobalTheory.IntDvdAdele
