import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndefiniteUnitaryLieAlgAddISmulEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HoweD.upq_span` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIndefiniteUnitaryLieAlgAddISmulEq.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.exists_indefiniteUnitaryLieAlg_add_I_smul_eq : ∀ (p q : ℕ) (Z : Mat p q), ∃ X ∈ upq p q, ∃ Y ∈ upq p q, Z = X + Complex.I • Y := by
  first | exact @GlobalTheory.HoweD.upq_span | exact GlobalTheory.HoweD.upq_span | (intros; apply GlobalTheory.HoweD.upq_span <;> assumption)
