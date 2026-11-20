import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TensorRank

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem rank_piTensorProduct_le_one {α : Type} [Fintype α] (M : α → Type)
    [∀ a, AddCommGroup (M a)] [∀ a, Module ℂ (M a)]
    (h : ∀ a, Module.rank ℂ (M a) ≤ 1) : Module.rank ℂ (⨂[ℂ] a, M a) ≤ 1 := by
  choose v₀ hv₀ using fun a => rank_le_one_iff.mp (h a)
  rw [rank_le_one_iff]
  refine ⟨PiTensorProduct.tprod ℂ v₀, fun x => ?_⟩
  refine PiTensorProduct.induction_on x ?_ ?_
  · intro r f
    choose c hc using fun a => hv₀ a (f a)
    refine ⟨r * ∏ a, c a, ?_⟩
    have hf : f = fun a => c a • v₀ a := funext fun a => (hc a).symm
    rw [hf, MultilinearMap.map_smul_univ, mul_smul]
  · rintro x y ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r + s, by rw [add_smul, hr, hs]⟩

end GlobalTheory.CompanionTheory.TensorRank
