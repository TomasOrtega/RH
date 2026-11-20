import Mathlib

namespace GlobalTheory

open IsLocalRing Module nonZeroDivisors IsLocalization.AtPrime

attribute [local instance] Ideal.Quotient.field

/- English proof (translation)
Set `Rₚ` to `Localization.AtPrime p`. Set `Sₚ` to `Localization (Algebra.algebraMapSubmonoid S p.primeCompl)`. Set `: Algebra Rₚ Sₚ` to `localizationAlgebra p.primeCompl S`. Establish `hp0 : p.primeCompl ≤ R⁰` using `p.primeCompl_le_nonZeroDivisors`. Establish `: IsDomain Rₚ` using `IsLocalization.isDomain_of_le_nonZeroDivisors _ hp0`.

Establish `: IsIntegrallyClosed Rₚ` using `isIntegrallyClosed_of_isLocalization _ _ hp0`. Establish `: IsScalarTower R Rₚ Sₚ` using `IsScalarTower.of_algebraMap_eq' (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq])`. Establish `: IsLocalization (Submonoid.map (algebraMap R S) (Ideal.primeCompl p)) Sₚ` using `inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ)`. Establish `e : Algebra.algebraMapSubmonoid S p.primeCompl ≤ S⁰` using `Submonoid.map_le_of_le_comap _ <| p.primeCompl_le_nonZeroDivisors.trans (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _))`. Establish `: IsDomain Sₚ` using `IsLocalization.isDomain_of_le_nonZeroDivisors _ e`.

Establish `: IsTorsionFree Rₚ Sₚ`. Rewrite using `[isTorsionFree_iff_algebraMap_injective]`. Conclude with `IsLocalization.map_injective_of_injective p.primeCompl Rₚ Sₚ (FaithfulSMul.algebraMap_injective R S)`. Establish `: Module.Finite Rₚ Sₚ` using `.of_isLocalization R S p.primeCompl`. Establish `: IsIntegrallyClosed Sₚ` using `isIntegrallyClosed_of_isLocalization _ _ e`.

Establish `: Module.Flat Rₚ Sₚ` using `Module.Flat.of_isLocalizedModule Rₚ p.primeCompl (IsScalarTower.toAlgHom R S Sₚ).toLinearMap`. Establish `: Module.Free Rₚ Sₚ` using `Module.free_of_flat_of_isLocalRing`. Apply `(equivQuotMaximalIdeal p Rₚ).injective` to reduce the goal to its premises. Rewrite using `[trace_quotient_eq_trace_localization_quotient S p Rₚ Sₚ, IsScalarTower.algebraMap_eq S Sₚ, RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, Algebra.trace_quotient_mk, RingEquiv.apply_symm_apply, ← Algebra.intTrace_eq_trace, ← Algebra.intTrace_eq_of_isLocalization R S p.primeCom …`. Simplify using `only [equivQuotMaximalIdeal, RingHom.quotientKerEquivOfSurjective, RingEquiv.coe_trans, Function.comp_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfRightInverse.apply, RingHom.kerLift_mk]`.
-/
theorem trace_quotient_eq_of_projective (R S : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S]
    [Module.IsTorsionFree R S] [Module.Finite R S] [Module.Projective R S] (p : Ideal R)
    [p.IsMaximal] (x : S) :
    Algebra.trace (R ⧸ p) (S ⧸ p.map (algebraMap R S)) (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk p (Algebra.intTrace R S x) := by
  let Rₚ := Localization.AtPrime p
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let : Algebra Rₚ Sₚ := localizationAlgebra p.primeCompl S
  have hp0 : p.primeCompl ≤ R⁰ := p.primeCompl_le_nonZeroDivisors
  have : IsDomain Rₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hp0
  have : IsIntegrallyClosed Rₚ := isIntegrallyClosed_of_isLocalization _ _ hp0
  have : IsScalarTower R Rₚ Sₚ := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq])
  have : IsLocalization (Submonoid.map (algebraMap R S) (Ideal.primeCompl p)) Sₚ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ)
  have e : Algebra.algebraMapSubmonoid S p.primeCompl ≤ S⁰ :=
    Submonoid.map_le_of_le_comap _ <| p.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _))
  have : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ e
  have : IsTorsionFree Rₚ Sₚ := by
    rw [isTorsionFree_iff_algebraMap_injective]
    exact IsLocalization.map_injective_of_injective p.primeCompl Rₚ Sₚ
      (FaithfulSMul.algebraMap_injective R S)
  have : Module.Finite Rₚ Sₚ := .of_isLocalization R S p.primeCompl
  have : IsIntegrallyClosed Sₚ := isIntegrallyClosed_of_isLocalization _ _ e
  have : Module.Flat Rₚ Sₚ :=
    Module.Flat.of_isLocalizedModule Rₚ p.primeCompl (IsScalarTower.toAlgHom R S Sₚ).toLinearMap
  have : Module.Free Rₚ Sₚ := Module.free_of_flat_of_isLocalRing
  apply (equivQuotMaximalIdeal p Rₚ).injective
  rw [trace_quotient_eq_trace_localization_quotient S p Rₚ Sₚ, IsScalarTower.algebraMap_eq S Sₚ,
    RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, Algebra.trace_quotient_mk,
    RingEquiv.apply_symm_apply, ← Algebra.intTrace_eq_trace,
    ← Algebra.intTrace_eq_of_isLocalization R S p.primeCompl (Aₘ := Rₚ) (Bₘ := Sₚ) x,
    ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simp only [equivQuotMaximalIdeal, RingHom.quotientKerEquivOfSurjective, RingEquiv.coe_trans,
    Function.comp_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfRightInverse.apply,
    RingHom.kerLift_mk]

end GlobalTheory
