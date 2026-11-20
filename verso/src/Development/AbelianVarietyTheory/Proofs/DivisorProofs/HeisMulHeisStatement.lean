import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisMulHeis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeisMulHeis.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.heis_mul_heis : ∀ (R : Type) [CommRing R] (m : ℕ) (a w a' w' : Fin m → R) (α α' : R),
    Heisenberg₂ a w α * Heisenberg₂ a' w' α' = Heisenberg₂ (a + a') (w + w') (α + α' + ∑ k, a k * w' k) := by
  first | exact @GlobalTheory.QhtUnip.heis_mul | exact GlobalTheory.QhtUnip.heis_mul | (intros; apply GlobalTheory.QhtUnip.heis_mul <;> assumption)
