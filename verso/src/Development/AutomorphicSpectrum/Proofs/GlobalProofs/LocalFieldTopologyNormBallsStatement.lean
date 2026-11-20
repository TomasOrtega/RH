import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldTopologyNormBalls
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.QLTop.localField_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FLocalFieldTopologyNormBalls.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.localField_topology_norm_balls : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → IsOpen (O : Set F) ∧ IsCompact (O : Set F) ∧ SecondCountableTopology F ∧ Continuous (fun x : F => nrm x) ∧ (∀ e : ℤ, IsOpen {x : F | nrm x ≤ (q : ℝ) ^ e}) ∧ (∀ s ∈ nhds (0 : F), ∃ e : ℤ, {x : F | nrm x ≤ (q : ℝ) ^ e} ⊆ s) := by
  first | exact @GlobalTheory.CompanionTheory.QLTop.localField_top | exact GlobalTheory.CompanionTheory.QLTop.localField_top | (intros; apply GlobalTheory.CompanionTheory.QLTop.localField_top <;> assumption)
