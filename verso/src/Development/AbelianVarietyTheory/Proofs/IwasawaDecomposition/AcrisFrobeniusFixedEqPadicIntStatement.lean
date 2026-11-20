import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFixedEqPadicInt
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.phi_fixed_eq_padicInt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAcrisFrobeniusFixedEqPadicInt.lean&line=273#L273)
-/
theorem _root_.GlobalTheory.T.acris_frobenius_fixed_eq_padicInt : ∀ (l : ℕ) [Fact l.Prime], ∀ x : Per.Acris l, phiA l x = x → ∃ z : ℤ_[l], x = algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z) := by
  first | exact @GlobalTheory.MemLoc.phi_fixed_eq_padicInt | exact GlobalTheory.MemLoc.phi_fixed_eq_padicInt | (intros; apply GlobalTheory.MemLoc.phi_fixed_eq_padicInt <;> assumption)
