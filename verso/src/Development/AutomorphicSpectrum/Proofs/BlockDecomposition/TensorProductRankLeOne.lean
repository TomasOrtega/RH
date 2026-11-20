import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TensorRank

/- English proof (translation)
Use `choose v₀ hv₀ using fun a => rank_le_one_iff.mp (h a)`. Rewrite using `[rank_le_one_iff]`. Use `⟨PiTensorProduct.tprod ℂ v₀, fun x => ?_⟩` and prove the remaining obligations. Use `PiTensorProduct.induction_on x ?_ ?_` and prove the remaining obligations. Introduce `r f choose c hc using fun a => hv₀ a (f a)`.

Use `⟨r * ∏ a, c a, ?_⟩` and prove the remaining obligations. Establish `hf : f = fun a => c a • v₀ a` using `funext fun a => (hc a).symm`. Rewrite using `[hf, MultilinearMap.map_smul_univ, mul_smul]`. Introduce and unpack `x y ⟨r, hr⟩ ⟨s, hs⟩`. Conclude with `⟨r + s, by rw [add_smul, hr, hs]⟩`.
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
