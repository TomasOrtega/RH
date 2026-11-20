import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

/- English proof (translation)
Introduce `R _ _ _ _ q x p _ hq hp hx`. Establish `: IsDiscreteValuationRing (Localization.AtPrime p)` using `h₁ R q p hq hp`. Use `set O := Localization.AtPrime p`. Establish `hfin : FiniteMultiplicity q x` using `FiniteMultiplicity.of_prime_left hq hx`. Take `⟨y, hxy, hy⟩` from `hfin.exists_eq_pow_mul_and_not_dvd`.

Rewrite using `[hfin.emultiplicity_eq_multiplicity]`. Establish `hyu : IsUnit (algebraMap R O y)`. Rewrite using `[IsLocalization.AtPrime.isUnit_to_map_iff O p y]`. Express the relevant statement in the definitionally equal form `y ∉ p`. Rewrite using `[hp, Ideal.mem_span_singleton]`.

Conclude with `hy`. Establish `hmax : maximalIdeal O = Ideal.span {algebraMap R O q}`. Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal p O, congrArg (Ideal.map (algebraMap R O)) hp, Ideal.map_span, Set.image_singleton]`. Establish `hirr : Irreducible (algebraMap R O q)` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax`. Establish `hnz : algebraMap R O q ∈ nonZeroDivisors O` using `mem_nonZeroDivisors_of_ne_zero hirr.ne_zero`.

Use `conv_rhs => rw [hxy, map_mul, map_pow, Ring.ord_mul_of_isUnit_right hyu, Ring.ord_pow hnz, Ring.ord_of_irreducible hirr]`. Simplify using the standard rewrite rules.
-/
theorem EmultiplicityOrd.proof (h₁ : LocalizationPrimeDVR.Statement) : EmultiplicityOrd.Statement := by
  intro R _ _ _ _ q x p _ hq hp hx
  have : IsDiscreteValuationRing (Localization.AtPrime p) := h₁ R q p hq hp
  set O := Localization.AtPrime p
  have hfin : FiniteMultiplicity q x := FiniteMultiplicity.of_prime_left hq hx
  obtain ⟨y, hxy, hy⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  rw [hfin.emultiplicity_eq_multiplicity]

  have hyu : IsUnit (algebraMap R O y) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff O p y]
    change y ∉ p
    rw [hp, Ideal.mem_span_singleton]
    exact hy

  have hmax : maximalIdeal O = Ideal.span {algebraMap R O q} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p O, congrArg (Ideal.map (algebraMap R O)) hp,
      Ideal.map_span, Set.image_singleton]
  have hirr : Irreducible (algebraMap R O q) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have hnz : algebraMap R O q ∈ nonZeroDivisors O :=
    mem_nonZeroDivisors_of_ne_zero hirr.ne_zero
  conv_rhs => rw [hxy, map_mul, map_pow, Ring.ord_mul_of_isUnit_right hyu, Ring.ord_pow hnz,
    Ring.ord_of_irreducible hirr]
  simp

end GroundTheory.Heights₂.Heights
