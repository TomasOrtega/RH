import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsKrullAkizuki
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

namespace KrullAkizuki

/- English proof (translation)
Establish `hmeet : ∀ I : Ideal S, I ≠ ⊥ → ∃ b : R, b ≠ 0 ∧ algebraMap R S b ∈ I`. Introduce `I hI`. Take `⟨x, hxI, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Establish `halg : Algebra.IsAlgebraic R L` using `(IsFractionRing.comap_isAlgebraic_iff (K := K)).mpr inferInstance`. Establish `hx : IsAlgebraic R x` using `Subalgebra.isAlgebraic_iff_isAlgebraic_val.mpr (halg.isAlgebraic _)`.

Take `⟨b, hb, hb0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (Ideal.comap_ne_bot_of_algebraic_mem hx0 hxI hx)`. Conclude with `⟨b, hb0, hb⟩`. Use `⟨(isNoetherianRing_iff_ideal_fg S).mpr fun I => ?_, ⟨fun {P} hP0 hP => ?_⟩⟩` and prove the remaining obligations. Break down `eq_or_ne I ⊥ with rfl | hI` into its components or cases. Conclude with `Submodule.fg_bot`.

Take `⟨b, hb0, hbI⟩` from `hmeet I hI`. Establish `: IsNoetherian R (S ⧸ Ideal.span {algebraMap R S b})` using `(isFiniteLength_iff_isNoetherian_isArtinian.mp (h b hb0)).1`. Establish `: IsNoetherian S (S ⧸ Ideal.span {algebraMap R S b})` using `isNoetherian_of_tower R inferInstance`. Use `Submodule.fg_of_fg_map_of_fg_inf_ker (Ideal.span {algebraMap R S b}).mkQ (IsNoetherian.noetherian _) ?_` and prove the remaining obligations. Rewrite using `[Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem I).mpr hbI)]`.

Conclude with `Submodule.fg_span_singleton _`. Take `⟨b, hb0, hbP⟩` from `hmeet P hP0`. Establish `hle : Ideal.span {algebraMap R S b} ≤ P` using `(Ideal.span_singleton_le_iff_mem P).mpr hbP`. Establish `hfl : IsFiniteLength R (S ⧸ P)` using `(h b hb0).of_surjective (f := (Ideal.Quotient.factorₐ R hle).toLinearMap) (Ideal.Quotient.factor_surjective hle)`. Establish `: IsArtinian R (S ⧸ P)` using `(isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2`.

Establish `: IsArtinianRing (S ⧸ P)` using `isArtinian_of_tower R inferInstance`. Establish `: IsDomain (S ⧸ P)` using `Ideal.Quotient.isDomain P`. Conclude with `Ideal.Quotient.maximal_of_isField P (IsArtinianRing.isField_of_isDomain _)`.
-/
theorem noetherian_and_dimensionLEOne
    {R : Type} [CommRing R] [IsDomain R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L]
    [IsScalarTower R K L] (S : Subalgebra R L)
    (h : ∀ b : R, b ≠ 0 → IsFiniteLength R (S ⧸ Ideal.span {algebraMap R S b})) :
    IsNoetherianRing S ∧ Ring.DimensionLEOne S := by

  have hmeet : ∀ I : Ideal S, I ≠ ⊥ → ∃ b : R, b ≠ 0 ∧ algebraMap R S b ∈ I := by
    intro I hI
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have halg : Algebra.IsAlgebraic R L :=
      (IsFractionRing.comap_isAlgebraic_iff (K := K)).mpr inferInstance
    have hx : IsAlgebraic R x :=
      Subalgebra.isAlgebraic_iff_isAlgebraic_val.mpr (halg.isAlgebraic _)
    obtain ⟨b, hb, hb0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (Ideal.comap_ne_bot_of_algebraic_mem hx0 hxI hx)
    exact ⟨b, hb0, hb⟩
  refine ⟨(isNoetherianRing_iff_ideal_fg S).mpr fun I => ?_, ⟨fun {P} hP0 hP => ?_⟩⟩
  · rcases eq_or_ne I ⊥ with rfl | hI
    · exact Submodule.fg_bot
    obtain ⟨b, hb0, hbI⟩ := hmeet I hI
    have : IsNoetherian R (S ⧸ Ideal.span {algebraMap R S b}) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp (h b hb0)).1
    have : IsNoetherian S (S ⧸ Ideal.span {algebraMap R S b}) :=
      isNoetherian_of_tower R inferInstance
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (Ideal.span {algebraMap R S b}).mkQ
      (IsNoetherian.noetherian _) ?_
    rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem I).mpr hbI)]
    exact Submodule.fg_span_singleton _
  · obtain ⟨b, hb0, hbP⟩ := hmeet P hP0
    have hle : Ideal.span {algebraMap R S b} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hbP
    have hfl : IsFiniteLength R (S ⧸ P) :=
      (h b hb0).of_surjective (f := (Ideal.Quotient.factorₐ R hle).toLinearMap)
        (Ideal.Quotient.factor_surjective hle)
    have : IsArtinian R (S ⧸ P) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
    have : IsArtinianRing (S ⧸ P) := isArtinian_of_tower R inferInstance
    have : IsDomain (S ⧸ P) := Ideal.Quotient.isDomain P
    exact Ideal.Quotient.maximal_of_isField P (IsArtinianRing.isField_of_isDomain _)

/- English proof (translation)
Use `⟨fun R _ _ _ hR K _ _ _ L _ _ _ _ _ S => ?_, fun R _ _ _ hR K _ _ _ => ?_⟩` and prove the remaining obligations. Take `⟨h₁, h₂⟩` from `noetherian_and_dimensionLEOne (K := K) S (h R hR K L S)`. Use `⟨h₁, ?_⟩` and prove the remaining obligations. Use `(Ring.krullDimLE_iff (R := S) (n := 1)).mp inferInstance` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Take `⟨h₁, h₂⟩` from `noetherian_and_dimensionLEOne (K := K) (L := K) (integralClosure R K) (h R hR K K _)`. Establish `: IsIntegrallyClosed (integralClosure R K)` using `integralClosure.isIntegrallyClosedOfFiniteExtension (R := R) K (L := K)`. Conclude with `{ }`.
-/
theorem proof (h : KrullAkizukiQuotientLength.Statement) : KrullAkizuki.Statement := by
  refine ⟨fun R _ _ _ hR K _ _ _ L _ _ _ _ _ S => ?_, fun R _ _ _ hR K _ _ _ => ?_⟩
  · obtain ⟨h₁, h₂⟩ := noetherian_and_dimensionLEOne (K := K) S (h R hR K L S)
    refine ⟨h₁, ?_⟩
    have := (Ring.krullDimLE_iff (R := S) (n := 1)).mp inferInstance
    exact_mod_cast this
  · obtain ⟨h₁, h₂⟩ :=
      noetherian_and_dimensionLEOne (K := K) (L := K) (integralClosure R K) (h R hR K K _)
    have : IsIntegrallyClosed (integralClosure R K) :=
      integralClosure.isIntegrallyClosedOfFiniteExtension (R := R) K (L := K)
    exact { }

end KrullAkizuki

end GroundTheory.Heights₂.Heights.Model
