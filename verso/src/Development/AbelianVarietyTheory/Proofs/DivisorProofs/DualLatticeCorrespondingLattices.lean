import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch.Transport

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem dualLat_latCorr {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
    {D D₂ : Type} [Fintype D] [Fintype D₂] (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) : LatCorr j cD (dualLat Λ) (dualLat Λ₂) := by
  have key : ∀ y x : D → k, (fun c => j (y (cD c))) ⬝ᵥ (fun c => j (x (cD c))) = j (y ⬝ᵥ x) := by
    intro y x
    simp only [dotProduct, map_sum, map_mul]
    exact Fintype.sum_equiv cD _ _ fun c => rfl
  intro y
  rw [mem_dualLat, mem_dualLat]
  constructor
  · intro H x hx
    have := H _ ((h x).2 hx)
    rw [key] at this
    exact (hj.2.2 _).1 this
  · intro H x₂ hx₂
    set x : D → k := fun d => j.symm (x₂ (cD.symm d)) with hxdef
    have hx : (fun c => j (x (cD c))) = x₂ := by
      funext c; simp [x]
    rw [← hx] at hx₂ ⊢
    rw [key]
    exact (hj.2.2 _).2 (H x ((h x).1 hx₂))

end GlobalTheory.PureMatch.Transport
