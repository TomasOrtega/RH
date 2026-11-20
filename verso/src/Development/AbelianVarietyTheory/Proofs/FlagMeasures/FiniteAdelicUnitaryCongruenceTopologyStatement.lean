import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CongTop.adelic_topology | exact GlobalTheory.CongTop.adelic_topology | (intros; apply GlobalTheory.CongTop.adelic_topology <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.finiteAdelicUnitary_congruenceTopology : ∀ I : AutInst, T2Space I.Gf ∧ LocallyCompactSpace I.Gf ∧ SecondCountableTopology I.Gf ∧ IsCompact I.Kset ∧ IsOpen I.Kset ∧ (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kset) ∧ ∀ g : ℕ, 1 ≤ g → IsOpen (I.Kg g) ∧ (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kg g) ∧ ∀ k ∈ I.Kset, ∀ x ∈ I.Kg g, k * x * k⁻¹ ∈ I.Kg g := by
  first | exact @GlobalTheory.CongTop.adelic_topology | exact GlobalTheory.CongTop.adelic_topology | (intros; apply GlobalTheory.CongTop.adelic_topology <;> assumption)
