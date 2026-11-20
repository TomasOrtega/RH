import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameOf

/- English proof (translation)
Introduce `l _ Lf _`. Use `⟨fun a b h => Subtype.ext (Subtype.ext h), fun x => ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Use `⟨(a : Lf).2, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le]`. Establish `ha : IsIntegral ℤ_[l] (a : Lf)` using `a.2`. Conclude with `ha.map (Lf.val.restrictScalars ℤ_[l])`. Introduce and unpack `⟨hx, hn⟩`. Rewrite `hn` using `[← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le]`.

Establish `hi : IsIntegral ℤ_[l] (⟨x, hx⟩ : Lf)` using `(isIntegral_algHom_iff (Lf.val.restrictScalars ℤ_[l]) Subtype.val_injective).1 hn`. Conclude with `⟨⟨⟨x, hx⟩, hi⟩, rfl⟩`.
-/
theorem intEmb_range_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] Lf],
    Function.Injective (intEmb Lf) ∧ ∀ x, x ∈ Set.range (intEmb Lf) ↔ x ∈ Lf ∧ ‖x‖ ≤ 1 := by
  intro l _ Lf _
  refine ⟨fun a b h => Subtype.ext (Subtype.ext h), fun x => ?_⟩
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(a : Lf).2, ?_⟩
    rw [← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le]
    have ha : IsIntegral ℤ_[l] (a : Lf) := a.2
    exact ha.map (Lf.val.restrictScalars ℤ_[l])
  · rintro ⟨hx, hn⟩
    rw [← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le] at hn
    have hi : IsIntegral ℤ_[l] (⟨x, hx⟩ : Lf) :=
      (isIntegral_algHom_iff (Lf.val.restrictScalars ℤ_[l]) Subtype.val_injective).1 hn
    exact ⟨⟨⟨x, hx⟩, hi⟩, rfl⟩

end GlobalTheory.FrameOf

end
