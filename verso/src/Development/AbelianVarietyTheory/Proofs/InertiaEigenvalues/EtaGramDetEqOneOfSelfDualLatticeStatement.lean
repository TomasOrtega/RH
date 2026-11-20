import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaGramDetEqOneOfSelfDualLattice
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FEtaGramDetEqOneOfSelfDualLattice.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.eta_gramDet_eq_one_of_selfDual_lattice : ∀ (K : UQ) (B : InvAlg K) (x : B.A), B.σ x = x → (B.X x).Nonempty → K.eta (B.gramDet x) = 1 := by
  first | exact @GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one | exact GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one | (intros; apply GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one <;> assumption)
