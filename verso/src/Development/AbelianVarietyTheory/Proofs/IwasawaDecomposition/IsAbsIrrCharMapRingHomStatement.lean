import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAbsIrrCharMapRingHom
import Mathlib
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsAbsIrrCharMapRingHom.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.isAbsIrrChar_map_ringHom : ∀ {K K' G : Type} [Field K] [Field K'] [CharZero K] [CharZero K'] [Group G] [Fintype G] (φ : K →+* K') (χ : G → K), IsAbsIrrChar χ → IsAbsIrrChar (fun g => φ (χ g)) := by
  first | exact @GlobalTheory.AbsIrrMap.isAbsIrrChar_map | exact GlobalTheory.AbsIrrMap.isAbsIrrChar_map | (intros; apply GlobalTheory.AbsIrrMap.isAbsIrrChar_map <;> assumption)
