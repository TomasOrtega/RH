import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.NefGenericLocalizeSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.NefExtendIsoSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocalizeBundleSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocalizeNefAboveSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExtendTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isUnit_algebraMap_primeCompl {S : Type} [CommRing S] (𝔪 : Ideal S) [𝔪.IsPrime] {K : Type} [Field K]
    [Algebra S K] (h : Function.Injective (algebraMap S K)) (y : 𝔪.primeCompl) : IsUnit (algebraMap S K y) :=
  IsUnit.mk0 _ fun h' => y.2 (by rw [(map_eq_zero_iff _ h).mp h']; exact 𝔪.zero_mem)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem NefGenericLocalize.proof (hI : NefExtendIso.Statement) (hB : LocalizeBundle.Statement)
    (hN : LocalizeNefAbove.Statement) : NefGenericLocalize.Statement := by
  intro hD S _ _ F _ _ _ Ω _ _ _ _ N x M 𝔪 h𝔪 hM
  by_cases h0 : 𝔪 = ⊥
  · subst h0
    refine hI S F Ω N x M.toSubSystem
      ⟨IsFractionRing.injective S F, IsFractionRing.surjective_iff_isField.mpr (Ring.isField_iff_maximal_bot.mpr h𝔪)⟩ ?_
    rw [Ideal.map_bot] at hM
    exact hM
  · have hinj : Function.Injective (algebraMap S Ω) := by
      rw [IsScalarTower.algebraMap_eq S F Ω]
      exact (algebraMap F Ω).injective.comp (IsFractionRing.injective S F)
    let O := Localization.AtPrime 𝔪
    let _ : Algebra O Ω :=
      (IsLocalization.lift (M := 𝔪.primeCompl) (S := O) (isUnit_algebraMap_primeCompl 𝔪 hinj)).toAlgebra
    let _ : Algebra O F := (IsLocalization.lift (M := 𝔪.primeCompl) (S := O)
      (isUnit_algebraMap_primeCompl 𝔪 (IsFractionRing.injective S F))).toAlgebra
    have : IsScalarTower S O Ω := IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
    have : IsScalarTower S O F := IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
    have : IsScalarTower O F Ω := IsScalarTower.of_algebraMap_eq' <|
      IsLocalization.ringHom_ext 𝔪.primeCompl <| by
        rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq,
          ← IsScalarTower.algebraMap_eq]
    have : IsFractionRing O F := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔪.primeCompl O F
    have : IsDiscreteValuationRing O := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S h0 O
    obtain ⟨M', hM'⟩ := hB S 𝔪 O Ω N x M
    have hN' := hN S 𝔪 O Ω N x M.toSubSystem hM
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal 𝔪 O, ← hM'] at hN'
    convert hD O F Ω N x M' hN' using 1
    refine Kleiman.SubSystem.ext_sub fun I => ?_
    change Submodule.span (Kleiman.chartRing F x I) (M.sub I : Set Ω) =
      Submodule.span (Kleiman.chartRing F x I) (M'.sub I : Set Ω)
    rw [show M'.sub I = (M.toSubSystem.baseChange O).sub I by rw [← hM']]
    exact (Kleiman.span_extend_span I _).symm

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
