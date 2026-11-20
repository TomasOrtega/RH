import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodLiftsLatticeMapMemSetupGoodLifts
import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MomGood.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FGoodLiftsLatticeMapMemSetupGoodLifts.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.goodLiftsLattice_map_mem_setup_goodLifts : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D (tor0 D cc δ) L L') → ∀ y ∈ GlobalTheory.MomT.goodLifts D (tor0 D cc δ) lam N₀ n L L', e y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d, ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x} := by
  first | exact @GlobalTheory.MomGood.main | exact GlobalTheory.MomGood.main | (intros; apply GlobalTheory.MomGood.main <;> assumption)
