import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

/- English proof (translation)
Set `_ : Algebra (Localization.Away r) (Localization.Away (r * g))` to `(IsLocalization.Away.awayToAwayRight (S := Localization.Away r) r g).toAlgebra`. Establish `_ : IsScalarTower C (Localization.Away r) (Localization.Away (r * g))` using `IsScalarTower.of_algebraMap_eq fun c => (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away r) r g c).symm`. Set `_ : Module (Localization.Away r) (LocalizedModule (Submonoid.powers (r * g)) M)` to `Module.compHom _ (algebraMap (Localization.Away r) (Localization.Away (r * g)))`. Establish `_ : IsScalarTower (Localization.Away r) (Localization.Away (r * g)) (LocalizedModule (Submonoid.powers (r * g)) M)` using `⟨fun a b x => by show (a • b) • x = algebraMap _ (Localization.Away (r * g)) a • b • x`. Rewrite using `[Algebra.smul_def, mul_smul]⟩`.

Establish `_ : IsScalarTower C (Localization.Away r) (LocalizedModule (Submonoid.powers (r * g)) M)` using `⟨fun c a x => by show algebraMap _ (Localization.Away (r * g)) (c • a) • x = c • algebraMap _ (Localization.Away (r * g)) a • x`. Rewrite using `[Algebra.smul_def, map_mul, mul_smul, ← IsScalarTower.algebraMap_apply C (Localization.Away r) (Localization.Away (r * g)), algebraMap_smul]⟩`. Establish `hr` using `LocalizedModule.isBaseChange (Submonoid.powers r) M`. Establish `hrg` using `LocalizedModule.isBaseChange (Submonoid.powers (r * g)) M`. Rewrite `hrg` using `[← hr.lift_comp (LocalizedModule.mkLinearMap (Submonoid.powers (r * g)) M)]`.

Conclude with `Module.Free.of_equiv (hr.of_comp hrg).equiv`.
-/
theorem free_localizedModule_mul {C : Type} [CommRing C] (M : Type) [AddCommGroup M] [Module C M]
    (r g : C) (h : Module.Free (Localization.Away r) (LocalizedModule (Submonoid.powers r) M)) :
    Module.Free (Localization.Away (r * g)) (LocalizedModule (Submonoid.powers (r * g)) M) := by
  let _ : Algebra (Localization.Away r) (Localization.Away (r * g)) :=
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away r) r g).toAlgebra
  have _ : IsScalarTower C (Localization.Away r) (Localization.Away (r * g)) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away r) r g c).symm
  let _ : Module (Localization.Away r) (LocalizedModule (Submonoid.powers (r * g)) M) :=
    Module.compHom _ (algebraMap (Localization.Away r) (Localization.Away (r * g)))
  have _ : IsScalarTower (Localization.Away r) (Localization.Away (r * g))
      (LocalizedModule (Submonoid.powers (r * g)) M) :=
    ⟨fun a b x => by
      show (a • b) • x = algebraMap _ (Localization.Away (r * g)) a • b • x
      rw [Algebra.smul_def, mul_smul]⟩
  have _ : IsScalarTower C (Localization.Away r) (LocalizedModule (Submonoid.powers (r * g)) M) :=
    ⟨fun c a x => by
      show algebraMap _ (Localization.Away (r * g)) (c • a) • x =
        c • algebraMap _ (Localization.Away (r * g)) a • x
      rw [Algebra.smul_def, map_mul, mul_smul,
        ← IsScalarTower.algebraMap_apply C (Localization.Away r) (Localization.Away (r * g)),
        algebraMap_smul]⟩
  have hr := LocalizedModule.isBaseChange (Submonoid.powers r) M
  have hrg := LocalizedModule.isBaseChange (Submonoid.powers (r * g)) M
  rw [← hr.lift_comp (LocalizedModule.mkLinearMap (Submonoid.powers (r * g)) M)] at hrg
  exact Module.Free.of_equiv (hr.of_comp hrg).equiv

/- English proof (translation)
Introduce `k C _ _ _ _ _ _ _ M _ _ _`. Establish `_ : IsNoetherianRing C` using `Algebra.FiniteType.isNoetherianRing k C`. Establish `_ : Algebra.FinitePresentation k C` using `Algebra.FinitePresentation.of_finiteType.mp inferInstance`. Establish `_ : Module.FinitePresentation C M` using `Module.finitePresentation_of_finite C M`. Take `⟨m, hm⟩` from `Ideal.exists_maximal C`.

Use `hm.isPrime` as an intermediate fact. Take `⟨p, hp, -⟩` from `Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal C)) (J := m) bot_le`. Establish `_ : p.IsPrime` using `hp.1.1`. Establish `_ : Ring.KrullDimLE 0 (Localization.AtPrime p)` using `Ring.KrullDimLE.of_isLocalization p hp _`. Set `_ : Field (Localization.AtPrime p)` to `(Ring.KrullDimLE.isField_of_isReduced).toField`.

Establish `_ : Algebra.IsSmoothAt k p` using `Algebra.FormallySmooth.of_perfectField`. Establish `_ : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M)` using `Module.Free.of_divisionRing _ _`. Take `⟨f₁, hf₁p, hf₁⟩` from `Algebra.IsSmoothAt.exists_notMem_smooth k p`. Take `⟨r, hrp, hr, -⟩` from `Module.FinitePresentation.exists_free_localizedModule_powers p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)`. Use `⟨r * f₁, ?_, ?_, free_localizedModule_mul M r f₁ hr⟩` and prove the remaining obligations.

Introduce `h0`. Establish `: r * f₁ ∈ p` using `by rw [h0]; exact p.zero_mem`. Conclude with `(Ideal.IsPrime.mem_or_mem ‹_› this).elim hrp hf₁p`. Rewrite `hf₁`, the goal using `[← Algebra.basicOpen_subset_smoothLocus_iff_smooth]`. Conclude with `fun x hx => hf₁ (PrimeSpectrum.basicOpen_mul_le_right r f₁ hx)`.
-/
theorem exists_smooth_free_away : ∀ (k C : Type) [Field k] [PerfectField k] [CommRing C] [Nontrivial C] [IsReduced C] [Algebra k C] [Algebra.FiniteType k C] (M : Type) [AddCommGroup M] [Module C M] [Module.Finite C M], ∃ f : C, f ≠ 0 ∧ Algebra.Smooth k (Localization.Away f) ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  intro k C _ _ _ _ _ _ _ M _ _ _
  have _ : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  have _ : Algebra.FinitePresentation k C := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have _ : Module.FinitePresentation C M := Module.finitePresentation_of_finite C M
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  have := hm.isPrime
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal C)) (J := m) bot_le
  have _ : p.IsPrime := hp.1.1
  have _ : Ring.KrullDimLE 0 (Localization.AtPrime p) := Ring.KrullDimLE.of_isLocalization p hp _
  let _ : Field (Localization.AtPrime p) := (Ring.KrullDimLE.isField_of_isReduced).toField
  have _ : Algebra.IsSmoothAt k p := Algebra.FormallySmooth.of_perfectField
  have _ : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.Free.of_divisionRing _ _
  obtain ⟨f₁, hf₁p, hf₁⟩ := Algebra.IsSmoothAt.exists_notMem_smooth k p
  obtain ⟨r, hrp, hr, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  refine ⟨r * f₁, ?_, ?_, free_localizedModule_mul M r f₁ hr⟩
  · intro h0
    have : r * f₁ ∈ p := by rw [h0]; exact p.zero_mem
    exact (Ideal.IsPrime.mem_or_mem ‹_› this).elim hrp hf₁p
  · rw [← Algebra.basicOpen_subset_smoothLocus_iff_smooth] at hf₁ ⊢
    exact fun x hx => hf₁ (PrimeSpectrum.basicOpen_mul_le_right r f₁ hx)

end GlobalTheory.SS
