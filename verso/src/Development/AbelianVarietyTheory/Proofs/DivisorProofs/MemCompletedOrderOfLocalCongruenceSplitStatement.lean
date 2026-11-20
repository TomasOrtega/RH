import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderOfLocalCongruenceSplit
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemCompletedOrderOfLocalCongruenceSplit.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.mem_completedOrder_of_local_congruence_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ c → Splits v) → ∀ z : Af E, (∀ v, LocIn (expIn c v) v z) → z ∈ hatO c := by
  first | exact @GlobalTheory.CMVal.Euler.HatLoc.mem_hatO_of_locIn | exact GlobalTheory.CMVal.Euler.HatLoc.mem_hatO_of_locIn | (intros; apply GlobalTheory.CMVal.Euler.HatLoc.mem_hatO_of_locIn <;> assumption)
