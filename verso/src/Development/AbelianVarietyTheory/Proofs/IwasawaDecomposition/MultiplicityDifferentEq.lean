import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.Pad

/- English proof (translation)
Use `haveI := Fact.mk hp`. Establish `hd : (discr E).natAbs ≠ 0` using `Int.natAbs_ne_zero.mpr (discr_ne_zero E)`. Take `⟨a, m, hm, hdisc⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hd p hp.ne_one`. Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hm (dvd_zero _)`. Establish `h` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E p a m hp hm hdisc w.asIdeal w.isPrime hw`.

Use `haveI := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.liesOver_span E p hp w.isPrime hw`. Establish `hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)}`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `he : eWL E w = (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count w.asIdeal`. Rewrite using `[eWL, Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (Ideal.span {(p : ℤ)}) w.asIdeal (by rw [hmap]; exact ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.span_nat_ne_bot p), hmap]`.

Establish `hv : padicValNat p (discr E).natAbs = a`. Rewrite using `[hdisc, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]`. Establish `hE : (Module.finrank ℚ E : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr Module.finrank_pos.ne'`. Establish `hD0 : differentIdeal ℤ (𝓞 E) ≠ ⊥` using `differentIdeal_ne_bot`. Rewrite using `[multiplicity_eq_count_normalizedFactors w.irreducible hD0, normalize_eq, he, vDiff, hv, ← mul_div_assoc, eq_div_iff hE, mul_comm _ (a : ℝ)]`.

Conclude with `h` after adjusting the coercions.
-/
theorem multiplicity_different_eq (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (p : 𝓞 E) ∈ w.asIdeal) :
    (multiplicity w.asIdeal (differentIdeal ℤ (𝓞 E)) : ℝ) = (eWL E w : ℝ) * vDiff E p := by
  classical
  haveI := Fact.mk hp
  have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  obtain ⟨a, m, hm, hdisc⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd p hp.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E p a m hp hm hdisc w.asIdeal w.isPrime hw
  haveI := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.liesOver_span E p hp w.isPrime hw
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have he : eWL E w = (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count w.asIdeal := by
    rw [eWL, Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (Ideal.span {(p : ℤ)}) w.asIdeal
      (by rw [hmap]; exact ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.span_nat_ne_bot p), hmap]
  have hv : padicValNat p (discr E).natAbs = a := by
    rw [hdisc, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hD0 : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  rw [multiplicity_eq_count_normalizedFactors w.irreducible hD0, normalize_eq, he, vDiff, hv, ← mul_div_assoc,
    eq_div_iff hE, mul_comm _ (a : ℝ)]
  exact_mod_cast h

/- English proof (translation)
Use `⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), fun h => ?_, fun hp w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[vDiff, padicValNat.eq_zero_of_not_dvd h, Nat.cast_zero, zero_div]`. Use `haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois`. Conclude with `multiplicity_different_eq _ hp w hw`.
-/
theorem vDiff_spec (D : D7) (p : ℕ) : 0 ≤ vDiff D.host.E p ∧ (DV.UnramE D p → vDiff D.host.E p = 0) ∧
    (p.Prime → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
      (multiplicity w.asIdeal (differentIdeal ℤ (𝓞 D.host.E)) : ℝ) = (eWL D.host.E w : ℝ) * vDiff D.host.E p) := by
  refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), fun h => ?_, fun hp w hw => ?_⟩
  · rw [vDiff, padicValNat.eq_zero_of_not_dvd h, Nat.cast_zero, zero_div]
  · haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
    exact multiplicity_different_eq _ hp w hw

end GlobalTheory.ShFam.Pad
