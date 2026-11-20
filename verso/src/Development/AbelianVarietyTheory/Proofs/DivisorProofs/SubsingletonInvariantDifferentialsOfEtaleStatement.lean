import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonInvariantDifferentialsOfEtale
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSubsingletonInvariantDifferentialsOfEtale.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.subsingleton_invariantDifferentials_of_etale : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt → Subsingleton G.omega ∧ Subsingleton G.dual.dual.omega := by
  first | exact @GlobalTheory.PDivGroup.subsingleton_omega_of_isEt | exact GlobalTheory.PDivGroup.subsingleton_omega_of_isEt | (intros; apply GlobalTheory.PDivGroup.subsingleton_omega_of_isEt <;> assumption)
