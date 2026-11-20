import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSpreadsOutFromLocalizationAtPrimeStatement

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Take `⟨f₀, hp, hf₀⟩` from `GlobalTheory.T.finite_spreads_out_from_localization_at_prime R q B hfin`. Establish `hq : q ∈ Module.freeLocus R B` using `(Module.mem_freeLocus_iff_tensor q (Localization.AtPrime q.asIdeal)).mpr hfree`. Use `clear hfin hfree`. Use `set A := Localization.Away f₀`. Use `Module.FinitePresentation.of_finite_of_finitePresentation A (A ⊗[R] B)` as an intermediate fact.

Choose the witnesses or unpack the hypotheses as in `⟨p, rfl⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R A)) := by`. Rewrite using `[PrimeSpectrum.localization_away_comap_range A f₀]`. Conclude with `hp`. Establish `: Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl (A ⊗[R] B))` using `Module.mem_freeLocus.mp (Module.comap_freeLocus_le (A := A) hq)`. Take `⟨r, hr, hf, -⟩` from `Module.FinitePresentation.exists_free_localizedModule_powers p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (A ⊗[R] B)) (Localization.AtPrime p.asIdeal)`.

Take `⟨⟨r', u⟩, hu⟩` from `IsLocalization.surj (Submonoid.powers f₀) r`. Establish `hu' : IsUnit (algebraMap R A u)` using `IsLocalization.map_units A u`. Establish `hass : Associated r (algebraMap R A r')` using `⟨hu'.unit, hu⟩`. Establish `hr' : r' ∉ (PrimeSpectrum.comap (algebraMap R A) p).asIdeal` using `fun h => by`. Establish `h' : algebraMap R A r' ∈ p.asIdeal` using `h`.

Rewrite `h'` using `[← show r * algebraMap R A u = algebraMap R A r' from hu]`. Conclude with `(p.isPrime.mem_or_mem h').elim hr fun h'' => p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem h'' hu')`. Set `T` to `Localization.Away r`. Establish `: IsLocalization.Away (algebraMap R A r') T` using `IsLocalization.Away.of_associated hass`. Establish `: IsLocalization.Away (f₀ * r') T` using `IsLocalization.Away.mul' A T f₀ r'`.

Set `e : T ≃ₐ[R] Localization.Away (f₀ * r')` to `IsLocalization.algEquiv (Submonoid.powers (f₀ * r')) _ _`. Use `letI : Algebra T (Localization.Away (f₀ * r')) := e.toRingHom.toAlgebra`. Use `letI : Algebra A (Localization.Away (f₀ * r')) := (e.toRingHom.comp (algebraMap A T)).toAlgebra`. Establish `: IsScalarTower A T (Localization.Away (f₀ * r'))` using `IsScalarTower.of_algebraMap_eq' rfl`. Establish `: IsScalarTower R A (Localization.Away (f₀ * r'))` using `IsScalarTower.of_algebraMap_eq fun x => by`.

Express the relevant statement in the definitionally equal form `_ = e (algebraMap A T (algebraMap R A x))`. Rewrite using `[← IsScalarTower.algebraMap_apply, e.commutes]`. Establish `: Module.Free T (T ⊗[A] (A ⊗[R] B))` using `Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) (A ⊗[R] B))`. Establish `: Module.Free (Localization.Away (f₀ * r')) (Localization.Away (f₀ * r') ⊗[A] (A ⊗[R] B))` using `Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange A T (Localization.Away (f₀ * r')) (Localization.Away (f₀ * r')) (A ⊗[R] B))`. Set `c` to `TensorProduct.AlgebraTensorModule.cancelBaseChange R A (Localization.Away (f₀ * r')) (Localization.Away (f₀ * r')) B`.

Conclude with `⟨f₀ * r', fun h => ((PrimeSpectrum.comap (algebraMap R A) p).isPrime.mem_or_mem h).elim hp hr', Module.Finite.equiv c, Module.Free.of_equiv c⟩`.
-/
theorem exists_finite_free_away_of_atPrime (R : Type) [CommRing R] (q : PrimeSpectrum R) (B : Type) [CommRing B]
    [Algebra R B] [Algebra.FinitePresentation R B]
    (hfin : Module.Finite (Localization.AtPrime q.asIdeal) ((Localization.AtPrime q.asIdeal) ⊗[R] B))
    (hfree : Module.Free (Localization.AtPrime q.asIdeal) ((Localization.AtPrime q.asIdeal) ⊗[R] B)) :
    ∃ r : R, r ∉ q.asIdeal ∧ Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] B) ∧
      Module.Free (Localization.Away r) (Localization.Away r ⊗[R] B) := by
  obtain ⟨f₀, hp, hf₀⟩ := GlobalTheory.T.finite_spreads_out_from_localization_at_prime R q B hfin
  have hq : q ∈ Module.freeLocus R B :=
    (Module.mem_freeLocus_iff_tensor q (Localization.AtPrime q.asIdeal)).mpr hfree
  clear hfin hfree
  set A := Localization.Away f₀
  have := Module.FinitePresentation.of_finite_of_finitePresentation A (A ⊗[R] B)
  obtain ⟨p, rfl⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R A)) := by
    rw [PrimeSpectrum.localization_away_comap_range A f₀]; exact hp
  have : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl (A ⊗[R] B)) :=
    Module.mem_freeLocus.mp (Module.comap_freeLocus_le (A := A) hq)
  obtain ⟨r, hr, hf, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (A ⊗[R] B))
    (Localization.AtPrime p.asIdeal)
  obtain ⟨⟨r', u⟩, hu⟩ := IsLocalization.surj (Submonoid.powers f₀) r
  have hu' : IsUnit (algebraMap R A u) := IsLocalization.map_units A u
  have hass : Associated r (algebraMap R A r') := ⟨hu'.unit, hu⟩
  have hr' : r' ∉ (PrimeSpectrum.comap (algebraMap R A) p).asIdeal := fun h => by
    have h' : algebraMap R A r' ∈ p.asIdeal := h
    rw [← show r * algebraMap R A u = algebraMap R A r' from hu] at h'
    exact (p.isPrime.mem_or_mem h').elim hr fun h'' => p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem h'' hu')
  let T := Localization.Away r
  have : IsLocalization.Away (algebraMap R A r') T := IsLocalization.Away.of_associated hass
  have : IsLocalization.Away (f₀ * r') T := IsLocalization.Away.mul' A T f₀ r'
  let e : T ≃ₐ[R] Localization.Away (f₀ * r') := IsLocalization.algEquiv (Submonoid.powers (f₀ * r')) _ _
  letI : Algebra T (Localization.Away (f₀ * r')) := e.toRingHom.toAlgebra
  letI : Algebra A (Localization.Away (f₀ * r')) := (e.toRingHom.comp (algebraMap A T)).toAlgebra
  have : IsScalarTower A T (Localization.Away (f₀ * r')) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R A (Localization.Away (f₀ * r')) := IsScalarTower.of_algebraMap_eq fun x => by
    change _ = e (algebraMap A T (algebraMap R A x))
    rw [← IsScalarTower.algebraMap_apply, e.commutes]
  have : Module.Free T (T ⊗[A] (A ⊗[R] B)) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) (A ⊗[R] B))
  have : Module.Free (Localization.Away (f₀ * r')) (Localization.Away (f₀ * r') ⊗[A] (A ⊗[R] B)) :=
    Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange A T
      (Localization.Away (f₀ * r')) (Localization.Away (f₀ * r')) (A ⊗[R] B))
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange R A
      (Localization.Away (f₀ * r')) (Localization.Away (f₀ * r')) B
  exact ⟨f₀ * r', fun h => ((PrimeSpectrum.comap (algebraMap R A) p).isPrime.mem_or_mem h).elim hp hr',
    Module.Finite.equiv c, Module.Free.of_equiv c⟩

end GlobalTheory
