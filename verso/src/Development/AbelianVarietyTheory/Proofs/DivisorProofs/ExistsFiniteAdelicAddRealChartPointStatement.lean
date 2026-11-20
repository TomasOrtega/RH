import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicAddRealChartPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealWeilF.exists_realZero_add_iotaVF` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFiniteAdelicAddRealChartPoint.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_finiteAdelic_add_realChartPoint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ)
    (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (ι : (InfinitePlace F → ℂ) →+ AEF F E), IsChartF θ ι →
      ∀ w : WOF F E nS nT, ∃ (u : WOF F E nS nT) (v : IxF F nS nT → ℂ), u.map (infPartF F E) = 0 ∧ w = u + iotaVF ι v := by
  first | exact @GlobalTheory.RealWeilF.exists_realZero_add_iotaVF | exact GlobalTheory.RealWeilF.exists_realZero_add_iotaVF | (intros; apply GlobalTheory.RealWeilF.exists_realZero_add_iotaVF <;> assumption)
