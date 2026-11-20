import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

/- English proof (translation)
Introduce `ι m S _ _ w w' f g hf hg`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨l, hl1, hlw, rfl⟩` from `hx`. Take `⟨l', hl1', hlw', rfl⟩` from `hy`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨l ++ l', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Break down `List.mem_append.1 hx with h | h` into its components or cases. Conclude with `hl1 x h`. Conclude with `hl1' x h`. Simplify using `[List.map_append, List.sum_append, hlw, hlw']`. Use function extensionality and compare the values at `A`.

Simplify using `[trProd, List.map_append, List.prod_append]`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [mul_add]`. Conclude with `add_mem hy hz`. Consider the case `smul a y _ hy => rw [mul_smul_comm]`.

Conclude with `Submodule.smul_mem _ a hy`. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz => rw [add_mul]`. Conclude with `add_mem hx hz`. Consider the case `smul a x _ hx => rw [smul_mul_assoc]`.

Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem trSpan_mul : ∀ {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (w w' : ℕ)
    (f g : Mat m S → S), f ∈ TrSpan m w S → g ∈ TrSpan m w' S → f * g ∈ TrSpan m (w + w') S := by
  intro ι m S _ _ w w' f g hf hg
  induction hf using Submodule.span_induction with
  | mem x hx =>
    induction hg using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl1, hlw, rfl⟩ := hx
      obtain ⟨l', hl1', hlw', rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨l ++ l', ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact hl1 x h
        · exact hl1' x h
      · simp [List.map_append, List.sum_append, hlw, hlw']
      · funext A
        simp [trProd, List.map_append, List.prod_append]
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hy
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hx

end GlobalTheory.GoodMetric.ChernSpan
