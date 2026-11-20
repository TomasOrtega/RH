import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneReOpenNearOfIsUnit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuaternionNormOneReOpenNearOfIsUnit.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.quaternion_normOne_re_open_near_of_isUnit : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), SqOpen R → ∀ g : ℍ[R, a, b], nrm g = 1 → IsUnit (1 - g.re ^ 2) → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g → ∃ O : Set R, IsOpen O ∧ g.re ∈ O ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  first | exact @GlobalTheory.traceOpen_near_of_isUnit | exact GlobalTheory.traceOpen_near_of_isUnit | (intros; apply GlobalTheory.traceOpen_near_of_isUnit <;> assumption)
