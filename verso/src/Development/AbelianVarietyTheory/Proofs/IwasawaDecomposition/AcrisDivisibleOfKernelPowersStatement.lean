import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisDivisibleOfKernelPowers
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.dvd_of_forall_fil_add` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAcrisDivisibleOfKernelPowers.lean&line=160#L160)
-/
theorem _root_.GlobalTheory.T.acris_divisible_of_kernel_powers : ∀ (l : ℕ) [Fact l.Prime], ∀ s : Per.Acris0 l, (∀ n : ℕ, ∃ (u w : Per.Acris0 l), s = u + (l : Per.Acris0 l) * w ∧ (u : Per.AinfP l) ∈ Per.kerP l ^ n) → (l : Per.Acris0 l) ∣ s := by
  first | exact @GlobalTheory.MemLoc.dvd_of_forall_fil_add | exact GlobalTheory.MemLoc.dvd_of_forall_fil_add | (intros; apply GlobalTheory.MemLoc.dvd_of_forall_fil_add <;> assumption)
