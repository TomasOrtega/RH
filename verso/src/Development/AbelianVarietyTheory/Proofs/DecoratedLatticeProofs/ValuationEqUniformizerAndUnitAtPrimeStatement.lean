import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrime
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FValuationEqUniformizerAndUnitAtPrime.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.valuation_eq_uniformizer_and_unit_at_prime : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∀ t t' : 𝓞 D.host.E, t ∈ PP.asIdeal → t ∉ PP.asIdeal ^ 2 → t' ∉ PP.asIdeal →
    (∃ q : Unif k, valuation k (p.pr (incA D (t : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k)) ∧
      valuation k (p.pr (incA D (t' : D.host.E))) = 1 := by
  first | exact @GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit | exact GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit | (intros; apply GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit <;> assumption)
