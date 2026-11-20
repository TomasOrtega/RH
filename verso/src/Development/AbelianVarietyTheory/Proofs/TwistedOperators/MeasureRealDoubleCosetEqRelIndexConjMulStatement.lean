import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasureRealDoubleCosetEqRelIndexConjMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FMeasureRealDoubleCosetEqRelIndexConjMul.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.measureReal_doubleCoset_eq_relIndex_conj_mul : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ g : G,
    μ.real (DoubleCoset.doubleCoset g (J : Set G) (J : Set G)) =
      ((J.map (MulAut.conj g).toMonoidHom).relIndex J : ℝ) * μ.real (J : Set G) := by
  first | exact @GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul | exact GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul | (intros; apply GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul <;> assumption)
