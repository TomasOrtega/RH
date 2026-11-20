import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPowerUnitsTowerClosureProperties
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

/- English proof (translation)
Introduce `Ω _ _ _ ε X hj l n _ a ha`. Take `⟨-, -, hmul, hone, hsmul, -, -⟩` from `GlobalTheory.KZ.H3.cls_props Ω ε X l n`. Take `⟨u1, umul, -, -, -, upow, -⟩` from `GlobalTheory.KZ.UnClosure.un_closure ε X ε.injective hj (l ^ n)`. Unfold `Tower.A at ha`. Proceed by induction on `ha using Submodule.span_induction with`.

Consider the case `mem x hx => exact hx n`. Consider the case `zero => exact ⟨1, u1, by rw [map_zero, hone]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨f, hf, ef⟩` from `hx`. Take `⟨g, hg, eg⟩` from `hy`.

Conclude with `⟨f * g, umul f g hf hg, by rw [map_add, ef, eg, hmul]⟩`. Consider the case `smul c x _ hx`. Take `⟨f, hf, ef⟩` from `hx`. Conclude with `⟨_, upow _ f hf, by rw [map_smul, ef, hsmul]⟩`.
-/
theorem exists_un_eval_eq_cls : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l n : ℕ) [Fact l.Prime], ∀ a ∈ X.A l, ∃ f ∈ X.Un (l ^ n), AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f := by
  intro Ω _ _ _ ε X hj l n _ a ha
  obtain ⟨-, -, hmul, hone, hsmul, -, -⟩ := GlobalTheory.KZ.H3.cls_props Ω ε X l n
  obtain ⟨u1, umul, -, -, -, upow, -⟩ := GlobalTheory.KZ.UnClosure.un_closure ε X ε.injective hj (l ^ n)
  unfold Tower.A at ha
  induction ha using Submodule.span_induction with
  | mem x hx => exact hx n
  | zero => exact ⟨1, u1, by rw [map_zero, hone]⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, ef⟩ := hx
    obtain ⟨g, hg, eg⟩ := hy
    exact ⟨f * g, umul f g hf hg, by rw [map_add, ef, eg, hmul]⟩
  | smul c x _ hx =>
    obtain ⟨f, hf, ef⟩ := hx
    exact ⟨_, upow _ f hf, by rw [map_smul, ef, hsmul]⟩

end GlobalTheory.KZ.ES
