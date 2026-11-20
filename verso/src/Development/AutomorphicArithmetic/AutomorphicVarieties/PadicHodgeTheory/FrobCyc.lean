import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Introduce `l _`. Take `⟨-, -, -, ⟨σ, hσ⟩, h⟩` from `iqBasic l`. Take `⟨g, hg, hc⟩` from `(cycInertia l).1 (cyc l l σ)⁻¹`. Use `⟨σ * g, (h σ _ hσ).2 ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_mul_cancel_left]` and apply the resulting hypothesis.

Rewrite using `[map_mul, hc, mul_inv_cancel]`.
-/
theorem UpperTheory.V.Loc.frobCyc :
    ∀ (l : ℕ) [Fact l.Prime], ∃ σ : GQ l, IsFrob σ ∧ cyc l l σ = 1 := by
  intro l _
  obtain ⟨-, -, -, ⟨σ, hσ⟩, h⟩ := iqBasic l
  obtain ⟨g, hg, hc⟩ := (cycInertia l).1 (cyc l l σ)⁻¹
  refine ⟨σ * g, (h σ _ hσ).2 ?_, ?_⟩
  · rwa [inv_mul_cancel_left]
  · rw [map_mul, hc, mul_inv_cancel]
