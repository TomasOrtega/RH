import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

/- English proof (translation)
Introduce `D ψ V W L f`. Use `⟨fun hf γ w => ?_, fun u hu hf => ?_⟩` and prove the remaining obligations. Unfold `dRho`. Rewrite using `[← deriv_const_mul_field]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Conclude with `GlobalTheory.DualPairCheck.heis_quasi ψ V W (L t) f hf γ w`. Use function extensionality and compare the values at `w`. Establish `key : ∀ t, Heisenberg₂ ψ V W u (Heisenberg₂ ψ V W (L t) f) = Heisenberg₂ ψ V W (L t) f`. Introduce `t`.

Use `conv_rhs => rw [← hf]`. Rewrite using `[GlobalTheory.DualPairCheck.heis_heis, GlobalTheory.DualPairCheck.heis_heis, (hu t).1, (hu t).2, add_comm]`. Establish `: (fun t => Heisenberg₂ ψ V W (L t) f w) = fun t => Heisenberg₂ ψ V W u (Heisenberg₂ ψ V W (L t) f) w`. Use function extensionality and compare the values at `t`. Rewrite using `[key]`.

Use `conv_rhs => unfold dRho`. Rewrite using `[this]`. Unfold `dRho`. Rewrite using `[Heisenberg₂, ← deriv_const_mul_field]`. Both sides reduce to the same expression.
-/
theorem dRho_quasi_and_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : ℝ →+ WA V W) (f : WA V W → ℂ), ((∀ γ w, f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * f w) → ∀ γ w, dRho ψ V W L f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * dRho ψ V W L f w) ∧ ∀ u : WA V W, (∀ t, symplH V W u (L t) = 0 ∧ symplH V W (L t) u = 0) → Heisenberg₂ ψ V W u f = f → Heisenberg₂ ψ V W u (dRho ψ V W L f) = dRho ψ V W L f := by
  intro D ψ V W L f
  refine ⟨fun hf γ w => ?_, fun u hu hf => ?_⟩
  · unfold dRho
    rw [← deriv_const_mul_field]
    congr 1
    funext t
    exact GlobalTheory.DualPairCheck.heis_quasi ψ V W (L t) f hf γ w
  · funext w
    have key : ∀ t, Heisenberg₂ ψ V W u (Heisenberg₂ ψ V W (L t) f) = Heisenberg₂ ψ V W (L t) f := by
      intro t
      conv_rhs => rw [← hf]
      rw [GlobalTheory.DualPairCheck.heis_heis, GlobalTheory.DualPairCheck.heis_heis, (hu t).1, (hu t).2, add_comm]
    have : (fun t => Heisenberg₂ ψ V W (L t) f w) = fun t => Heisenberg₂ ψ V W u (Heisenberg₂ ψ V W (L t) f) w := by
      funext t; rw [key]
    conv_rhs => unfold dRho; rw [this]
    unfold dRho
    rw [Heisenberg₂, ← deriv_const_mul_field]
    rfl

end GlobalTheory.FockCompare
