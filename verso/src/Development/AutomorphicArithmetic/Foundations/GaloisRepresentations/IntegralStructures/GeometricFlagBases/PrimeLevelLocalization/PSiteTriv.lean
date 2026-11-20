import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormPerfSt

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Int.Geo.Pl

/- English proof (translation)
Assemble the required witnesses or components as `⟨hq, hp, hg.1.1, hr, W2.Seed.pFormPerfSt E A n q hg.2, w.isMaximal, by refine Ideal.span_le.2 ?_ rintro y (rfl | rfl) exacts [hw, hω]⟩`.
-/
theorem atPrime_of {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] (S : Setup A n p)
    {q : ℕ} (hq : q.Prime) (hp : q ≠ p) (hg : A.Good q) {r : ℤ} (hr : (q : ℤ) ∣ r ^ 2 - A.tr * r + A.nm) {w : Plc E}
    (hw : (q : 𝓞 E) ∈ w.asIdeal) (hω : A.ω - (r : 𝓞 E) ∈ w.asIdeal) : AtPrime S.D q r w.asIdeal :=
  ⟨hq, hp, hg.1.1, hr, W2.Seed.pFormPerfSt E A n q hg.2, w.isMaximal, by
    refine Ideal.span_le.2 ?_
    rintro y (rfl | rfl)
    exacts [hw, hω]⟩

/- English proof (translation)
Introduce `E _ _ _ A n p _ S x hx N q hq hp hg hN w hw`. Take `⟨r, hr, hω⟩` from `(hS E A x hx q hq hg.1 w hw).2.2.2.2.2.1`. Establish `h1 : ordCompl[q] N.1 = N.1`. Rewrite using `[Nat.factorization_eq_zero_of_not_dvd hN]`. Simplify using the standard rewrite rules.

Use `⟨⟨q, r, ⊤, S.L.KN N.1, hg, atPrime_of S hq hp hg hr hw hω, ?_, ?_, ?_⟩, rfl, rfl⟩` and prove the remaining obligations. Rewrite using `[h1]`. Conclude with `⟨N.2.1, ((Nat.Prime.coprime_iff_not_dvd hq).2 hN).symm, N.2.2, top_sup_eq _, 0, le_top⟩`. Rewrite using `[h1, Ideal.mul_top]`. Conclude with `(hL p S.D S.G S.L).2.2.1 N.1`.

Rewrite using `[h1, Ideal.mul_top]`. Conclude with `Ideal.mem_span_singleton_self _`.
-/
theorem siteTriv_of (hS : Sides) (hL : LevBasic) : SiteTriv := by
  intro E _ _ _ A n p _ S x hx N q hq hp hg hN w hw
  obtain ⟨r, hr, hω⟩ := (hS E A x hx q hq hg.1 w hw).2.2.2.2.2.1
  have h1 : ordCompl[q] N.1 = N.1 := by
    rw [Nat.factorization_eq_zero_of_not_dvd hN]; simp
  refine ⟨⟨q, r, ⊤, S.L.KN N.1, hg, atPrime_of S hq hp hg hr hw hω, ?_, ?_, ?_⟩, rfl, rfl⟩
  · rw [h1]
    exact ⟨N.2.1, ((Nat.Prime.coprime_iff_not_dvd hq).2 hN).symm, N.2.2, top_sup_eq _, 0, le_top⟩
  · rw [h1, Ideal.mul_top]
    exact (hL p S.D S.G S.L).2.2.1 N.1
  · rw [h1, Ideal.mul_top]
    exact Ideal.mem_span_singleton_self _

end UpperTheory.Gal.Int.Geo.Pl
