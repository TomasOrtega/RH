import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FFiniteAdelicUnitaryCongruenceTopology.lean&line=335#L335)
-/
theorem _root_.GlobalTheory.T.finiteAdelicUnitary_congruenceTopology : ∀ I : AutInst, T2Space I.Gf ∧ LocallyCompactSpace I.Gf ∧ SecondCountableTopology I.Gf ∧ IsCompact I.Kset ∧ IsOpen I.Kset ∧ (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kset) ∧ ∀ g : ℕ, 1 ≤ g → IsOpen (I.Kg g) ∧ (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kg g) ∧ ∀ k ∈ I.Kset, ∀ x ∈ I.Kg g, k * x * k⁻¹ ∈ I.Kg g := by
  first | exact @GlobalTheory.CongTop.adelic_topology | exact GlobalTheory.CongTop.adelic_topology | (intros; apply GlobalTheory.CongTop.adelic_topology <;> assumption)
