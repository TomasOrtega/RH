import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnimodularHermitianCongrOneAtTamePlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FUnimodularHermitianCongrOneAtTamePlace.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.unimodular_hermitian_congr_one_at_tamePlace : ∀ (D : D7) (v : Pl D) (ε : AE D) (n : ℕ) (H : Matrix (Fin n) (Fin n) (AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → (∀ i j, H i j ∈ intAt D (· = v)) → (∀ i j, cA D (H i j) = H j i) → (∃ H' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ H * H' = ε • (1 : Matrix (Fin n) (Fin n) (AE D))) → ∃ P P' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, P i j ∈ intAt D (· = v)) ∧ (∀ i j, P' i j ∈ intAt D (· = v)) ∧ P * P' = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ P' * P = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ adj P * (H * P) = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) := by
  first | exact @GlobalTheory.IwaPlace.UnimodNF.unimodular_congr_one | exact GlobalTheory.IwaPlace.UnimodNF.unimodular_congr_one | (intros; apply GlobalTheory.IwaPlace.UnimodNF.unimodular_congr_one <;> assumption)
