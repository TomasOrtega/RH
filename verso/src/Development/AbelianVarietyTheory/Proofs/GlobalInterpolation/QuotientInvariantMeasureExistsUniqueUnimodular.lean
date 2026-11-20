import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilCriterionInvariantMeasureHomogeneousSpaceStatement

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular

/- English proof (translation)
Use `haveI := hG Measure.haar inferInstance`. Express the relevant statement in the definitionally equal form `Measure.modularCharacterFun g = 1`. Rewrite using `[Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure G) g]`. Establish `key : ∀ (μ' : Measure G) [IsFiniteMeasureOnCompacts μ'] [μ'.IsMulLeftInvariant], μ' = Measure.haar → Measure.haarScalarFactor μ' (Measure.haar : Measure G) = 1`. Introduce `μ' _ _ h`.

Substitute `h` using the available equality. Conclude with `Measure.haarScalarFactor_self _`. Conclude with `key _ (map_mul_right_eq_self _ g)`.
-/
theorem modularCharacter_eq_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (hG : IsUnimodular G) (g : G) :
    Measure.modularCharacter g = 1 := by
  haveI := hG Measure.haar inferInstance
  change Measure.modularCharacterFun g = 1
  rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure G) g]
  have key : ∀ (μ' : Measure G) [IsFiniteMeasureOnCompacts μ'] [μ'.IsMulLeftInvariant],
      μ' = Measure.haar → Measure.haarScalarFactor μ' (Measure.haar : Measure G) = 1 := by
    intro μ' _ _ h
    subst h
    exact Measure.haarScalarFactor_self _
  exact key _ (map_mul_right_eq_self _ g)

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ H _ _ hH uG uH`. Use `haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space G H hH fun h => ?_` and prove the remaining obligations. Rewrite using `[modularCharacter_eq_one uG, modularCharacter_eq_one uH]`.
-/
theorem invariantMeasureClause : InvariantMeasureClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH uG uH
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  refine GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space G H hH fun h => ?_
  rw [modularCharacter_eq_one uG, modularCharacter_eq_one uH]

end GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular
