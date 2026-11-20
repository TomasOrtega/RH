import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.RatioUnit

/- English proof (translation)
Introduce `m`. Proceed by induction on `m using Nat.recOnMul with`. Consider the case `zero => intro h`. Conclude with `absurd rfl h`. Consider the case `one => intro _ _`.

Rewrite using `[Nat.cast_one]`. Conclude with `fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)`. Consider the case `prime p hp => intro _ h`. Conclude with `h p hp dvd_rfl`. Consider the case `mul a b ha hb`.

Introduce `hab h hmem`. Rewrite `hmem` using `[Nat.cast_mul]`. Break down `hP.mem_or_mem hmem with h1 | h1` into its components or cases. Conclude with `ha (left_ne_zero_of_mul hab) (fun p hp hd => h p hp (dvd_mul_of_dvd_left hd b)) h1`. Conclude with `hb (right_ne_zero_of_mul hab) (fun p hp hd => h p hp (dvd_mul_of_dvd_right hd a)) h1`.
-/
theorem natCast_notMem_of_primes {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ m : ℕ, m ≠ 0 → (∀ p : ℕ, p.Prime → p ∣ m → (p : R) ∉ P) → (m : R) ∉ P := by
  intro m
  induction m using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; rw [Nat.cast_one]; exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)
  | prime p hp => intro _ h; exact h p hp dvd_rfl
  | mul a b ha hb =>
    intro hab h hmem
    rw [Nat.cast_mul] at hmem
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact ha (left_ne_zero_of_mul hab) (fun p hp hd => h p hp (dvd_mul_of_dvd_left hd b)) h1
    · exact hb (right_ne_zero_of_mul hab) (fun p hp hd => h p hp (dvd_mul_of_dvd_right hd a)) h1

/- English proof (translation)
The claim follows from `hp.not_dvd_one (by simpa [Nat.Coprime.gcd_eq_one r.reduced] using Nat.dvd_gcd h1 h2)`.
-/
theorem not_dvd_both {r : ℚ} {p : ℕ} (hp : p.Prime) (h1 : p ∣ r.num.natAbs) (h2 : p ∣ r.den) : False :=
  hp.not_dvd_one (by simpa [Nat.Coprime.gcd_eq_one r.reduced] using Nat.dvd_gcd h1 h2)

/- English proof (translation)
Use `haveI := Fact.mk hp`. Establish `hnd : ¬ p ∣ r.den` using `fun hd' => not_dvd_both hp hd hd'`. Establish `h0 : r.num.natAbs ≠ 0` using `by simpa using hr`. Establish `h1` using `one_le_padicValNat_of_dvd h0 hd`. Simplify using `only [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hnd]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem padicValRat_ne_zero_of_dvd_num {r : ℚ} (hr : r ≠ 0) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ r.num.natAbs) : padicValRat p r ≠ 0 := by
  haveI := Fact.mk hp
  have hnd : ¬ p ∣ r.den := fun hd' => not_dvd_both hp hd hd'
  have h0 : r.num.natAbs ≠ 0 := by simpa using hr
  have h1 := one_le_padicValNat_of_dvd h0 hd
  simp only [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hnd]
  omega

/- English proof (translation)
Use `haveI := Fact.mk hp`. Establish `hnd : ¬ p ∣ r.num.natAbs` using `fun hd' => not_dvd_both hp hd' hd`. Establish `h1` using `one_le_padicValNat_of_dvd r.den_nz hd`. Simplify using `only [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hnd]`. Use linear arithmetic over natural numbers and integers.
-/
theorem padicValRat_ne_zero_of_dvd_den {r : ℚ} {p : ℕ} (hp : p.Prime)
    (hd : p ∣ r.den) : padicValRat p r ≠ 0 := by
  haveI := Fact.mk hp
  have hnd : ¬ p ∣ r.num.natAbs := fun hd' => not_dvd_both hp hd' hd
  have h1 := one_le_padicValNat_of_dvd r.den_nz hd
  simp only [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hnd]
  omega

end GlobalTheory.Fam.RatioUnit

namespace GlobalTheory.Fam
open Formalism.DivisionValues GlobalTheory.Fam.RatioUnit

/- English proof (translation)
Break down `Int.natAbs_eq z with e | e` into its components or cases. Rewrite using `[e]`. Simplify using `using h`. Rewrite using `[e]`. Simplify `h` using `[Ideal.neg_mem_iff]`.
-/
theorem RatioUnit.intCast_notMem_of_natAbs {R : Type} [CommRing R] (P : Ideal R) (z : ℤ)
    (h : ((z.natAbs : ℕ) : R) ∉ P) : ((z : ℤ) : R) ∉ P := by
  rcases Int.natAbs_eq z with e | e
  · rw [e]; simpa using h
  · rw [e]; simpa [Ideal.neg_mem_iff] using h

/- English proof (translation)
Introduce `K _ _ σ w S x y hU hS a ha`. Use `letI : StarRing K := starRingOfComm`. Take `⟨_, n, hn, r, hr0, hpow, hrS⟩` from `hU`. Establish `hpow' : a ^ n = (r : K)`. Apply `σ.injective` to reduce the goal to its premises.

Rewrite using `[map_pow, ha, hpow, map_ratCast]`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `hpow'` using `[zero_pow hn.ne']`. Conclude with `hr0 (by exact_mod_cast hpow'.symm)`.

Establish `hnum : ((r.num : ℤ) : 𝓞 K) ∉ w.asIdeal`. Use `intCast_notMem_of_natAbs _ _ (natCast_notMem_of_primes w.asIdeal _ (by simpa using hr0) ?_)` and prove the remaining obligations. Introduce `p hp hd`. Conclude with `hS p hp (hrS p hp (padicValRat_ne_zero_of_dvd_num hr0 hp hd))`. Establish `hden : ((r.den : ℕ) : 𝓞 K) ∉ w.asIdeal`.

Use `natCast_notMem_of_primes w.asIdeal _ r.den_nz ?_` and prove the remaining obligations. Introduce `p hp hd`. Conclude with `hS p hp (hrS p hp (padicValRat_ne_zero_of_dvd_den hp hd))`. Establish `vnum` using `ReductionFirst.vw_unit w _ hnum`. Establish `vden` using `ReductionFirst.vw_unit w _ hden`.

Rewrite `vnum` using `[show (((r.num : ℤ) : 𝓞 K) : K) = (r.num : K) from map_intCast (algebraMap (𝓞 K) K) _]`. Rewrite `vden` using `[show (((r.den : ℕ) : 𝓞 K) : K) = (r.den : K) from map_natCast (algebraMap (𝓞 K) K) _]`. Establish `hd0 : (r.den : K) ≠ 0` using `by exact_mod_cast r.den_nz`. Establish `hrK0 : (r : K) ≠ 0` using `by exact_mod_cast hr0`. Establish `key : (r : K) * (r.den : K) = (r.num : K)`.

Rewrite using `[Rat.cast_def]`. Clear the denominators using the available nonvanishing facts. Establish `h1` using `ReductionFirst.vw_mul w hrK0 hd0`. Rewrite `h1` using `[key, vnum, vden]`. Establish `h2` using `ReductionFirst.vw_pow w a n`.

Rewrite `h2` using `[hpow']`. Establish `h3 : (n : ℤ) * vw w a = 0` using `by rw [← h2]; omega`. Break down `mul_eq_zero.1 h3 with h | h` into its components or cases. Conclude with `absurd (by exact_mod_cast h) hn.ne'`. Conclude with `h`.
-/
theorem vw_eq_zero_of_unitRatio : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (w : HeightOneSpectrum (𝓞 K)) (S : ℕ → Prop) (x y : ℂ), GlobalTheory.Fam.UnitRatio S x y → (∀ p : ℕ, p.Prime → S p → (p : 𝓞 K) ∉ w.asIdeal) → ∀ a : K, σ a = x / y → Formalism.DivisionValues.vw w a = 0 := by
  intro K _ _ σ w S x y hU hS a ha

  letI : StarRing K := starRingOfComm
  obtain ⟨_, n, hn, r, hr0, hpow, hrS⟩ := hU
  have hpow' : a ^ n = (r : K) := by
    apply σ.injective
    rw [map_pow, ha, hpow, map_ratCast]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hpow'
    exact hr0 (by exact_mod_cast hpow'.symm)
  have hnum : ((r.num : ℤ) : 𝓞 K) ∉ w.asIdeal := by
    refine intCast_notMem_of_natAbs _ _ (natCast_notMem_of_primes w.asIdeal _ (by simpa using hr0) ?_)
    intro p hp hd
    exact hS p hp (hrS p hp (padicValRat_ne_zero_of_dvd_num hr0 hp hd))
  have hden : ((r.den : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    refine natCast_notMem_of_primes w.asIdeal _ r.den_nz ?_
    intro p hp hd
    exact hS p hp (hrS p hp (padicValRat_ne_zero_of_dvd_den hp hd))
  have vnum := ReductionFirst.vw_unit w _ hnum
  have vden := ReductionFirst.vw_unit w _ hden
  rw [show (((r.num : ℤ) : 𝓞 K) : K) = (r.num : K) from map_intCast (algebraMap (𝓞 K) K) _] at vnum
  rw [show (((r.den : ℕ) : 𝓞 K) : K) = (r.den : K) from map_natCast (algebraMap (𝓞 K) K) _] at vden
  have hd0 : (r.den : K) ≠ 0 := by exact_mod_cast r.den_nz
  have hrK0 : (r : K) ≠ 0 := by exact_mod_cast hr0
  have key : (r : K) * (r.den : K) = (r.num : K) := by
    rw [Rat.cast_def]; field_simp
  have h1 := ReductionFirst.vw_mul w hrK0 hd0
  rw [key, vnum, vden] at h1
  have h2 := ReductionFirst.vw_pow w a n
  rw [hpow'] at h2
  have h3 : (n : ℤ) * vw w a = 0 := by rw [← h2]; omega
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (by exact_mod_cast h) hn.ne'
  · exact h

end GlobalTheory.Fam
