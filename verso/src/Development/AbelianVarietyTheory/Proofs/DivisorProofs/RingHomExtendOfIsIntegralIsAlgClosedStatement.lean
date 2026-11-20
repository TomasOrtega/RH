import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendOfIsIntegralIsAlgClosed
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRingHomExtendOfIsIntegralIsAlgClosed.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_ringHom_extend_of_isIntegral_of_isAlgClosed : ∀ (A C K : Type) [CommRing A] [CommRing C] [Algebra A C] [Algebra.IsIntegral A C] [Field K] [IsAlgClosed K] (h : A →+* K), RingHom.ker (algebraMap A C) ≤ RingHom.ker h → ∃ ψ : C →+* K, ψ.comp (algebraMap A C) = h := by
  first | exact @GlobalTheory.ringHom_extend_of_isIntegral_isAlgClosed | exact GlobalTheory.ringHom_extend_of_isIntegral_isAlgClosed | (intros; apply GlobalTheory.ringHom_extend_of_isIntegral_isAlgClosed <;> assumption)
