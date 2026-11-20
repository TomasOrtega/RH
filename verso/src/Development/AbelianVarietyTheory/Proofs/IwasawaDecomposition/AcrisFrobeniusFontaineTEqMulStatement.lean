import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFontaineTEqMul
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAcrisFrobeniusFontaineTEqMul.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, phiA l C.t = (l : Per.Acris l) * C.t := by
  first | exact @GlobalTheory.MemLoc.TPhi.t_phi | exact GlobalTheory.MemLoc.TPhi.t_phi | (intros; apply GlobalTheory.MemLoc.TPhi.t_phi <;> assumption)
