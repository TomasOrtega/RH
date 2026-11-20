import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSFamPrimePowSq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSiegelFamilyOverNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyDeeperLevelOfDvdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelFamilyOfDivisorLevelSamePrimesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelTor

/- English proof (translation)
Introduce `g n hg hn hodd`. Establish `hn1 : n ≠ 1` using `by omega`. Establish `hlp : n.minFac.Prime` using `Nat.minFac_prime hn1`. Establish `hln : n.minFac ∣ n` using `Nat.minFac_dvd n`. Establish `hlodd : Odd n.minFac` using `Odd.of_dvd_nat hodd hln`.

Take `⟨j, hj, ⟨F⟩⟩` from `GlobalTheory.SiegelTor.exists_sFam_primePow_sq g n.minFac hg hlp hlodd`. Use `set l := n.minFac with hl`. Use `set k := (l ^ j) ^ 2 with hk`. Establish `hl3 : 3 ≤ l`. Break down `hlodd with ⟨m, hm⟩` into its components or cases.

Use `hlp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hk3 : 3 ≤ k`. Establish `h1 : l ≤ l ^ j` using `Nat.le_self_pow (by omega) l`. Establish `h2 : l ^ j ≤ (l ^ j) ^ 2` using `Nat.le_self_pow (by norm_num) _`.

Use linear arithmetic over natural numbers and integers. Establish `hkodd : Odd k` using `(hlodd.pow).pow`. Establish `hN0 : n * k ≠ 0` using `by positivity`. Establish `hNodd : Odd (n * k)` using `hodd.mul hkodd`. Take `⟨i, hi, hz, -⟩` from `GlobalTheory.T.exists_inclusion_cyclotomicAwayRing_finite_etale k (n * k) hN0 (dvd_mul_left k n)`.

Take `⟨F₂⟩` from `GlobalTheory.SiegelFamilyNumberField.nonempty_baseChange F i hi`. Rewrite `F₂` using `[hz]`. Use `haveI : IsDedekindDomain (cycAway (n * k)) := (arBase_cycAway (n * k) hN0).1`. Establish `hup : Nonempty (SFam g (n * k) ((cycBase hN0).ζ : cycAway (n * k)))` using `GlobalTheory.T.siegelFamily_deeper_level_of_dvd g k (n * k) (cycAway (n * k)) (cycBase hN0) hk3 hNodd (dvd_mul_left k n) (by rw [cycBase_ζ]; exact ⟨F₂⟩)`. Rewrite `hup` using `[cycBase_ζ]`.

Use `GlobalTheory.T.nonempty_siegelFamily_of_divisor_level_same_primes g n (n * k) hn hNodd (dvd_mul_right n k) ⟨2 * j + 1, ?_⟩ hup` and prove the remaining obligations. Rewrite using `[pow_succ', hk, ← pow_mul, mul_comm j 2]`. Conclude with `mul_dvd_mul_left n (pow_dvd_pow_of_dvd hln _)`.
-/
theorem exists_sFam_cycAway : ∀ g n : ℕ, 1 ≤ g → 3 ≤ n → Odd n → Nonempty (SFam g n (zetaAway n)) := by
  intro g n hg hn hodd
  have hn1 : n ≠ 1 := by omega
  have hlp : n.minFac.Prime := Nat.minFac_prime hn1
  have hln : n.minFac ∣ n := Nat.minFac_dvd n
  have hlodd : Odd n.minFac := Odd.of_dvd_nat hodd hln
  obtain ⟨j, hj, ⟨F⟩⟩ := GlobalTheory.SiegelTor.exists_sFam_primePow_sq g n.minFac hg hlp hlodd
  set l := n.minFac with hl
  set k := (l ^ j) ^ 2 with hk
  have hl3 : 3 ≤ l := by
    rcases hlodd with ⟨m, hm⟩
    have := hlp.two_le
    omega
  have hk3 : 3 ≤ k := by
    have h1 : l ≤ l ^ j := Nat.le_self_pow (by omega) l
    have h2 : l ^ j ≤ (l ^ j) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hkodd : Odd k := (hlodd.pow).pow
  have hN0 : n * k ≠ 0 := by positivity
  have hNodd : Odd (n * k) := hodd.mul hkodd
  obtain ⟨i, hi, hz, -⟩ := GlobalTheory.T.exists_inclusion_cyclotomicAwayRing_finite_etale k (n * k) hN0 (dvd_mul_left k n)
  obtain ⟨F₂⟩ := GlobalTheory.SiegelFamilyNumberField.nonempty_baseChange F i hi
  rw [hz] at F₂
  haveI : IsDedekindDomain (cycAway (n * k)) := (arBase_cycAway (n * k) hN0).1
  have hup : Nonempty (SFam g (n * k) ((cycBase hN0).ζ : cycAway (n * k))) :=
    GlobalTheory.T.siegelFamily_deeper_level_of_dvd g k (n * k) (cycAway (n * k)) (cycBase hN0) hk3 hNodd (dvd_mul_left k n)
      (by rw [cycBase_ζ]; exact ⟨F₂⟩)
  rw [cycBase_ζ] at hup
  refine GlobalTheory.T.nonempty_siegelFamily_of_divisor_level_same_primes g n (n * k) hn hNodd (dvd_mul_right n k) ⟨2 * j + 1, ?_⟩ hup
  rw [pow_succ', hk, ← pow_mul, mul_comm j 2]
  exact mul_dvd_mul_left n (pow_dvd_pow_of_dvd hln _)

end GlobalTheory.SiegelTor
