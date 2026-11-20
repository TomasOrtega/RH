import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicRingClassLatticeOneEqOrder
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIdelicRingClassLatticeOneEqOrder.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.idelicRingClassLattice_one_eq_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → lattice c 1 = (orderC c : Set E) := by
  first | exact @GlobalTheory.CMVal.HatCap.lattice_one | exact GlobalTheory.CMVal.HatCap.lattice_one | (intros; apply GlobalTheory.CMVal.HatCap.lattice_one <;> assumption)
