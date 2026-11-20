import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HcfjHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNatCastMemPowOfRingHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatPrimeNotMemPrimeCubeOfIsUnramifiedAtStatement

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

/- English proof (translation)
Introduce `hw`. Use `isTotallyComplex_of_sq_eq_neg hp.pos hx` as an intermediate fact. Take `⟨⟨⟨hfin, -, hun⟩, -⟩, -⟩` from `GlobalTheory.Laid.hcfj_holds K h2 L₀ ((isIntegersLattice_iff hp.pos h2 hx L₀).mp hL)`. Establish `: NumberField K⟮(latticeCurve L₀).j⟯` using `NumberField.of_module_finite K _`. Establish `hle : ℚ⟮(latticeCurve L₀).j⟯ ≤ (K⟮(latticeCurve L₀).j⟯.toSubfield.toIntermediateField fun q => SubfieldClass.ratCast_mem _ q)` using `IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self K _)`.

Set `f : ℚ⟮(latticeCurve L₀).j⟯ →+* K⟮(latticeCurve L₀).j⟯` to `RingHom.codRestrict (algebraMap ℚ⟮(latticeCurve L₀).j⟯ ℂ) K⟮(latticeCurve L₀).j⟯ fun z => hle z.2`. Take `⟨P, hP, hP0, hPp⟩` from `GlobalTheory.T.exists_prime_natCast_mem_pow_of_ringHom' _ _ f w p 3 hw`. Conclude with `GlobalTheory.T.natPrime_not_mem_prime_cube_of_isUnramifiedAt p K K⟮(latticeCurve L₀).j⟯ x P hp h2 hx hP0 (hun P hP0) hPp`.
-/
theorem natCast_notMem_pow_three_of_quadratic (p : ℕ) (K : Type) [Field K] [NumberField K]
    [Algebra K ℂ] (h2 : Module.finrank ℚ K = 2) (x : K) (hx : x ^ 2 = -(p : K))
    (L₀ : PeriodPair) [NumberField ℚ⟮(latticeCurve L₀).j⟯]
    (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)) (hp : p.Prime)
    (hL : IsIntegersLattice p L₀) : (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  intro hw
  have := isTotallyComplex_of_sq_eq_neg hp.pos hx
  obtain ⟨⟨⟨hfin, -, hun⟩, -⟩, -⟩ :=
    GlobalTheory.Laid.hcfj_holds K h2 L₀ ((isIntegersLattice_iff hp.pos h2 hx L₀).mp hL)
  have : NumberField K⟮(latticeCurve L₀).j⟯ := NumberField.of_module_finite K _
  have hle : ℚ⟮(latticeCurve L₀).j⟯ ≤
      (K⟮(latticeCurve L₀).j⟯.toSubfield.toIntermediateField fun q =>
        SubfieldClass.ratCast_mem _ q) :=
    IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self K _)
  let f : ℚ⟮(latticeCurve L₀).j⟯ →+* K⟮(latticeCurve L₀).j⟯ :=
    RingHom.codRestrict (algebraMap ℚ⟮(latticeCurve L₀).j⟯ ℂ) K⟮(latticeCurve L₀).j⟯
      fun z => hle z.2
  obtain ⟨P, hP, hP0, hPp⟩ := GlobalTheory.T.exists_prime_natCast_mem_pow_of_ringHom' _ _ f w p 3 hw
  exact GlobalTheory.T.natPrime_not_mem_prime_cube_of_isUnramifiedAt p K K⟮(latticeCurve L₀).j⟯ x P hp h2 hx hP0 (hun P hP0) hPp

/- English proof (translation)
Introduce `p L₀ _ w hp hL`. Establish `hint : IsIntegral ℚ (sqrtNegNat p)` using `IsIntegral.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isIntegral_natCast p).neg)`. Establish `: FiniteDimensional ℚ ℚ⟮sqrtNegNat p⟯` using `IntermediateField.adjoin.finiteDimensional hint`. Establish `: NumberField ℚ⟮sqrtNegNat p⟯` using `NumberField.of_module_finite ℚ _`. Establish `hx : (IntermediateField.AdjoinSimple.gen ℚ (sqrtNegNat p)) ^ 2 = -(p : ℚ⟮sqrtNegNat p⟯)` using `Subtype.ext (by simpa using sqrtNegNat_sq p)`.

Use `isTotallyComplex_of_sq_eq_neg hp.pos hx` as an intermediate fact. Establish `h2 : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ = 2`. Establish `hle : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ ≤ 2`. Rewrite using `[IntermediateField.adjoin.finrank hint]`. Establish `hm : (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)).Monic` using `Polynomial.monic_X_pow_add_C _ two_ne_zero`.

Use `Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ (sqrtNegNat p) (p := Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) (by simp [sqrtNegNat_sq])) hm.ne_zero` as an intermediate fact. Rewrite `this` using `[Polynomial.natDegree_X_pow_add_C]`. Then use the resulting hypothesis. Establish `h1` using `IsTotallyComplex.finrank ℚ⟮sqrtNegNat p⟯`. Establish `h3 : 0 < Module.finrank ℚ ℚ⟮sqrtNegNat p⟯` using `Module.finrank_pos`. Use linear arithmetic over natural numbers and integers.

Conclude with `natCast_notMem_pow_three_of_quadratic p _ h2 _ hx L₀ w hp hL`.
-/
theorem natCast_notMem_pow_three_adjoin_j : ∀ (p : ℕ) (L₀ : PeriodPair)
    [NumberField ℚ⟮(latticeCurve L₀).j⟯] (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)),
    p.Prime → IsIntegersLattice p L₀ → (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  intro p L₀ _ w hp hL
  have hint : IsIntegral ℚ (sqrtNegNat p) :=
    IsIntegral.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isIntegral_natCast p).neg)
  have : FiniteDimensional ℚ ℚ⟮sqrtNegNat p⟯ := IntermediateField.adjoin.finiteDimensional hint
  have : NumberField ℚ⟮sqrtNegNat p⟯ := NumberField.of_module_finite ℚ _
  have hx : (IntermediateField.AdjoinSimple.gen ℚ (sqrtNegNat p)) ^ 2 =
      -(p : ℚ⟮sqrtNegNat p⟯) := Subtype.ext (by simpa using sqrtNegNat_sq p)
  have := isTotallyComplex_of_sq_eq_neg hp.pos hx
  have h2 : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ = 2 := by
    have hle : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ ≤ 2 := by
      rw [IntermediateField.adjoin.finrank hint]
      have hm : (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)).Monic :=
        Polynomial.monic_X_pow_add_C _ two_ne_zero
      have := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ (sqrtNegNat p)
        (p := Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) (by simp [sqrtNegNat_sq])) hm.ne_zero
      rwa [Polynomial.natDegree_X_pow_add_C] at this
    have h1 := IsTotallyComplex.finrank ℚ⟮sqrtNegNat p⟯
    have h3 : 0 < Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ := Module.finrank_pos
    omega
  exact natCast_notMem_pow_three_of_quadratic p _ h2 _ hx L₀ w hp hL

end GlobalTheory.CMModel
