import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.WeilBound.CoreStatements.HodgeTatePoints.DvrOfHeightOne

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Gc

/- English proof (translation)
Introduce `A _ _ _ _ _ p hp q hq h1 hpq`. Take `⟨R, _, _, _, _, _⟩ : ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra A R), IsLocalization.AtPrime R q ∧ IsDiscreteValuationRing R` from `⟨Localization.AtPrime q, inferInstance, inferInstance, inferInstance, inferInstance, dvr_of_height_one q h1⟩`. Set `K` to `FractionRing R`. Establish `hAR : Function.Injective (algebraMap A R)` using `IsLocalization.injective R q.primeCompl_le_nonZeroDivisors`. Use `haveI : CharZero R := charZero_of_injective_algebraMap hAR`.

Use `haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)`. Establish `hpR : (p : R) ∈ IsLocalRing.maximalIdeal R`. Use `(IsLocalization.AtPrime.to_map_mem_maximal_iff R q (p : A)).2 hpq` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Take `⟨C, _, _, _, _, _, _, hC⟩` from `GlobalTheory.exists_complete_isAlgClosed_padic_of_isDiscreteValuationRing R K p hpR`.

Take `⟨φ, hφ, hφ'⟩` from `GlobalTheory.exists_isLocalHom_normIntegers hC`. Use `haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective`. Establish `hO` using `GlobalTheory.normIntegers_integers C`. Establish `key : ∀ a : A, a ∈ q ↔ NormedField.valuation (K` using `C) (algebraMap (GlobalTheory.normIntegers C) C (φ (algebraMap A R a))) < 1 := by`. Introduce `a`.

Rewrite using `[← IsLocalization.AtPrime.to_map_mem_maximal_iff R q a, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff φ, hO.isUnit_iff_valuation_eq_one]`. Conclude with `(hO.map_le_one _).lt_iff_ne.symm`. Establish `hv : NormedField.valuation (K` using `C) (p : C) < 1 := by`. Simplify `(key p).1 hpq` using `only [map_natCast]`. Use `⟨C, GlobalTheory.normIntegers C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, NormedField.valuation, φ.comp (algebraMap A R), hO, hv, ?_, ?_, key⟩` and prove the remaining obligations.

Apply `GlobalTheory.NormIntegers.isAdicComplete_span_singleton hO` to reduce the goal to its premises. Rewrite using `[map_natCast]`. Conclude with `hv` after adjusting the coercions. Introduce `a b hab`. Establish `: (φ (algebraMap A R a) : C) = (φ (algebraMap A R b) : C)` using `congrArg Subtype.val hab`.

Rewrite `this` using `[hφ', hφ']`. Conclude with `hAR (IsFractionRing.injective R K ((algebraMap K C).injective this))`.
-/
theorem test_field : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (p : ℕ) [Fact p.Prime] (𝔮 : Ideal A), 𝔮.IsPrime → 𝔮.height = 1 → (p : A) ∈ 𝔮 → ∃ (C O : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : CommRing O) (_ : IsDomain O) (_ : Algebra O C) (v : Valuation C NNReal) (φ : A →+* O), v.Integers O ∧ v (p : C) < 1 ∧ IsAdicComplete (Ideal.span {(p : O)}) O ∧ Function.Injective φ ∧ ∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (φ a)) < 1 := by
  intro A _ _ _ _ _ p hp q hq h1 hpq
  obtain ⟨R, _, _, _, _, _⟩ : ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra A R),
      IsLocalization.AtPrime R q ∧ IsDiscreteValuationRing R :=
    ⟨Localization.AtPrime q, inferInstance, inferInstance, inferInstance, inferInstance,
      dvr_of_height_one q h1⟩
  let K := FractionRing R
  have hAR : Function.Injective (algebraMap A R) :=
    IsLocalization.injective R q.primeCompl_le_nonZeroDivisors
  haveI : CharZero R := charZero_of_injective_algebraMap hAR
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  have hpR : (p : R) ∈ IsLocalRing.maximalIdeal R := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff R q (p : A)).2 hpq
    rwa [map_natCast] at this
  obtain ⟨C, _, _, _, _, _, _, hC⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_padic_of_isDiscreteValuationRing R K p hpR
  obtain ⟨φ, hφ, hφ'⟩ := GlobalTheory.exists_isLocalHom_normIntegers hC
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  have hO := GlobalTheory.normIntegers_integers C
  have key : ∀ a : A, a ∈ q ↔
      NormedField.valuation (K := C) (algebraMap (GlobalTheory.normIntegers C) C (φ (algebraMap A R a))) < 1 := by
    intro a
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff R q a, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, ← isUnit_map_iff φ, hO.isUnit_iff_valuation_eq_one]
    exact (hO.map_le_one _).lt_iff_ne.symm
  have hv : NormedField.valuation (K := C) (p : C) < 1 := by
    simpa only [map_natCast] using (key p).1 hpq
  refine ⟨C, GlobalTheory.normIntegers C, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, NormedField.valuation, φ.comp (algebraMap A R), hO, hv, ?_, ?_, key⟩
  · apply GlobalTheory.NormIntegers.isAdicComplete_span_singleton hO
    rw [map_natCast]
    exact_mod_cast hv
  · intro a b hab
    have : (φ (algebraMap A R a) : C) = (φ (algebraMap A R b) : C) := congrArg Subtype.val hab
    rw [hφ', hφ'] at this
    exact hAR (IsFractionRing.injective R K ((algebraMap K C).injective this))

end PositivityTheory.HtPt.Gc
