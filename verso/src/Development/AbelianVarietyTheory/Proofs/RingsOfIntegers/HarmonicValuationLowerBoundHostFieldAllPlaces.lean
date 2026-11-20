import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueBoundIntegralChartRamifiedStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueIntegralOfUnitDiscriminantStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HostFieldGaloisDegreeDiscrConjMovesPrimesStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open Formalism.BasicNotions Formalism.MainNotions IsDedekindDomain

namespace GlobalTheory.PlaceInt.HostChart

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap T.V T.Fr)]`. Unfold `vV`. Distinguish the cases in `ha : valV T.V (algebraMap T.V T.Fr p) = 0`. Rewrite using `[ha]`. Simplify using the standard rewrite rules.

Establish `h1 : valV T.V (algebraMap T.V T.Fr p) ≤ 1` using `IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _`. Use `(WithZero.log_le_log ha one_ne_zero).2 h1` as an intermediate fact. Simplify using `only [WithZero.log_one] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem vV_nat_nonneg (T : CDVR) (p : ℕ) : 0 ≤ vV T.V (p : T.Fr) := by
  rw [← map_natCast (algebraMap T.V T.Fr)]
  unfold vV
  by_cases ha : valV T.V (algebraMap T.V T.Fr p) = 0
  · rw [ha]; simp
  have h1 : valV T.V (algebraMap T.V T.Fr p) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
  have := (WithZero.log_le_log ha one_ne_zero).2 h1
  simp only [WithZero.log_one] at this
  omega

/- English proof (translation)
Introduce `k` and use `le_trans (EReal.coe_le_coe_iff.2 (neg_le_neg hle)) (h k)`.
-/
theorem chBound_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr}
    {y : IntFr Xo c T io} {C : IntegralChartA3 Xo c T io y} {e : ℕ} {ρ ρ' : ℝ} {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (h : ChBound C e ρ w n) (hle : ρ ≤ ρ') : ChBound C e ρ' w n :=
  fun k => le_trans (EReal.coe_le_coe_iff.2 (neg_le_neg hle)) (h k)

/- English proof (translation)
Introduce `D H Dw l Xo c _ hstar T io y C e he w n DFw hDF`. Take `⟨hG, -, hD, hP⟩` from `GlobalTheory.T.hostField_galois_degree_discr_conj_moves_primes D H`. Establish `hd0 : (NumberField.discr D.host.E).natAbs ≠ 0` using `Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)`. Establish `hnn : ∀ p ∈ D.host.condN.primeFactors, (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) / e * D.host.vdH p * (DFw : ℝ) / 2`. Introduce `p _`.

Establish `h1 : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ)` using `by exact_mod_cast vV_nat_nonneg T p`. Establish `h2` using `D.host.vdH_nonneg p`. Check the signs of the components of the expression. Distinguish the cases in `hu : ∀ p ∈ D.host.condN.primeFactors, IsUnit (p : T.V)`. Use `chBound_mono (GlobalTheory.T.harmonic_value_integral_of_unit_discriminant D.host.E H Dw l Xo c hstar T io y C ?_ e w n) (Finset.sum_nonneg hnn)` and prove the remaining obligations.

Establish `h1 : IsUnit (((NumberField.discr D.host.E).natAbs : ℕ) : T.V)`. Rewrite using `[← Nat.factorization_prod_pow_eq_self hd0, Finsupp.prod, Nat.cast_prod]`. Use `IsUnit.prod_iff.2 fun p hp => ?_` and prove the remaining obligations. Establish `hp'` using `Nat.mem_primeFactors.1 (Nat.support_factorization _ ▸ hp)`. Rewrite using `[Nat.cast_pow]`.

Conclude with `(hu p (Nat.mem_primeFactors.2 ⟨hp'.1, hD p hp'.1 (Int.natCast_dvd.2 hp'.2.1), D.host.condN_ne_zero⟩)).pow _`. Break down `Int.natAbs_eq (NumberField.discr D.host.E) with h | h` into its components or cases. Rewrite using `[h, Int.cast_natCast]`. Conclude with `h1`. Rewrite using `[h, Int.cast_neg, Int.cast_natCast]`.

Conclude with `h1.neg`. Use `push Not at hu`. Take `⟨p, hp, hpu⟩` from `hu`. Establish `hpp` using `(hP p hp).1`. Use `haveI : Fact p.Prime := ⟨hpp⟩`.

Establish `hm : ¬ p ∣ ordCompl[p] (NumberField.discr D.host.E).natAbs` using `Nat.not_dvd_ordCompl hpp hd0`. Establish `hDa` using `(Nat.ordProj_mul_ordCompl_eq_self (NumberField.discr D.host.E).natAbs p).symm`. Use `chBound_mono (GlobalTheory.T.harmonicValue_bound_integralChart_ramified D.host.E H Dw l Xo c hstar T io y C hG p _ _ hpp hpu hm hDa (hP p hp).2 e he w n) (le_trans ?_ (Finset.single_le_sum hnn hp))` and prove the remaining obligations. Rewrite using `[Nat.factorization_def _ hpp]`. Establish `h1 : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ)` using `by exact_mod_cast vV_nat_nonneg T p`.

Establish `h2` using `D.host.vdH_nonneg p`. Establish `h3 : (Formalism.L2.Pj.DF Dw w : ℝ) ≤ DFw` using `by exact_mod_cast hDF`. Use `show (vV T.V (p : T.Fr) : ℝ) / e * D.host.vdH p * _ / 2 ≤ _`. Use `gcongr`.
-/
theorem chBound_host : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 D.host.E)], (∀ a : 𝓞 D.host.E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (e : ℕ), 0 < e → ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (n DFw : ℕ), Formalism.L2.Pj.DF Dw w ≤ DFw → ChBound C e (∑ p ∈ D.host.condN.primeFactors, (vV T.V (p : T.Fr) : ℝ) / e * D.host.vdH p * (DFw : ℝ) / 2) w n := by
  intro D H Dw l Xo c _ hstar T io y C e he w n DFw hDF
  obtain ⟨hG, -, hD, hP⟩ := GlobalTheory.T.hostField_galois_degree_discr_conj_moves_primes D H
  have hd0 : (NumberField.discr D.host.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
  have hnn : ∀ p ∈ D.host.condN.primeFactors, (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) / e * D.host.vdH p * (DFw : ℝ) / 2 := by
    intro p _
    have h1 : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast vV_nat_nonneg T p
    have h2 := D.host.vdH_nonneg p
    positivity
  by_cases hu : ∀ p ∈ D.host.condN.primeFactors, IsUnit (p : T.V)
  · refine chBound_mono (GlobalTheory.T.harmonic_value_integral_of_unit_discriminant D.host.E H Dw l Xo c hstar T io y C ?_ e w n) (Finset.sum_nonneg hnn)
    have h1 : IsUnit (((NumberField.discr D.host.E).natAbs : ℕ) : T.V) := by
      rw [← Nat.factorization_prod_pow_eq_self hd0, Finsupp.prod, Nat.cast_prod]
      refine IsUnit.prod_iff.2 fun p hp => ?_
      have hp' := Nat.mem_primeFactors.1 (Nat.support_factorization _ ▸ hp)
      rw [Nat.cast_pow]
      exact (hu p (Nat.mem_primeFactors.2 ⟨hp'.1, hD p hp'.1 (Int.natCast_dvd.2 hp'.2.1), D.host.condN_ne_zero⟩)).pow _
    rcases Int.natAbs_eq (NumberField.discr D.host.E) with h | h
    · rw [h, Int.cast_natCast]; exact h1
    · rw [h, Int.cast_neg, Int.cast_natCast]; exact h1.neg
  · push Not at hu
    obtain ⟨p, hp, hpu⟩ := hu
    have hpp := (hP p hp).1
    haveI : Fact p.Prime := ⟨hpp⟩
    have hm : ¬ p ∣ ordCompl[p] (NumberField.discr D.host.E).natAbs := Nat.not_dvd_ordCompl hpp hd0
    have hDa := (Nat.ordProj_mul_ordCompl_eq_self (NumberField.discr D.host.E).natAbs p).symm
    refine chBound_mono (GlobalTheory.T.harmonicValue_bound_integralChart_ramified D.host.E H Dw l Xo c hstar T io y C hG p _ _ hpp hpu hm hDa
      (hP p hp).2 e he w n) (le_trans ?_ (Finset.single_le_sum hnn hp))
    rw [Nat.factorization_def _ hpp]
    have h1 : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast vV_nat_nonneg T p
    have h2 := D.host.vdH_nonneg p
    have h3 : (Formalism.L2.Pj.DF Dw w : ℝ) ≤ DFw := by exact_mod_cast hDF
    show (vV T.V (p : T.Fr) : ℝ) / e * D.host.vdH p * _ / 2 ≤ _
    gcongr

end GlobalTheory.PlaceInt.HostChart
