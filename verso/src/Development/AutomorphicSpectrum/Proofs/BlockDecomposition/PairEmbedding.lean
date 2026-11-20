import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

/- English proof (translation)
Introduce `hS h₁ h₂ E _ _ _ a b ι _ K₁ K₂ W₁ W₂ X₁ Y₁ X₂ Y₂ G hW₁ hW₂ hX₁ hX₂ hE₁ hE₂ hG hGp hGt`. Take `⟨e₁, he₁Y, he₁i, he₁q⟩` from `hE₁`. Take `⟨e₂, he₂Y, he₂i, he₂q⟩` from `hE₂`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hG`. Take `⟨x, hx⟩` from `Function.ne_iff.mp hi`.

Take `⟨hmem, hval⟩` from `(hS E a b X₁ X₂ (G i) (hGp i)).1 x.2`. Establish `hφ : sl₁ (G i) x.2 ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Establish `h` using `congrFun hval x.1`.

Rewrite `h` using `[h0]`. Simplify using `using h.symm`. Take `⟨n₁, p₁, t₁, c₁⟩` from `h₁ E a b ι K₁ K₂ W₁ W₂ X₁ Y₁ X₂ e₁ G hW₁ hW₂ hX₁ he₁q he₁Y hGp hGt ⟨i, x.2, sl₁ (G i) x.2, hval, fun h0 => hφ (he₁i _ hmem h0)⟩`. Take `⟨j, hj⟩` from `Function.ne_iff.mp n₁`. Take `⟨y, hy⟩` from `Function.ne_iff.mp hj`.

Take `⟨hmem₂, hval₂⟩` from `(hS E a b Y₁ X₂ (ap₁ e₁ (G j)) (p₁ j)).2 y.1`. Establish `hψ : sl₂ (ap₁ e₁ (G j)) y.1 ≠ 0`. Introduce `h0`. Apply `hy` to reduce the goal to its premises. Establish `h` using `congrFun hval₂ y.2`.

Rewrite `h` using `[h0]`. Simplify using `using h.symm`. Take `⟨n₂, p₂, t₂, c₂⟩` from `h₂ E a b ι K₁ K₂ W₁ W₂ Y₁ X₂ Y₂ e₂ (fun i => ap₁ e₁ (G i)) hW₁ hW₂ hX₂ he₂q he₂Y p₁ t₁ ⟨j, y.1, sl₂ (ap₁ e₁ (G j)) y.1, hval₂, fun h0 => hψ (he₂i _ hmem₂ h0)⟩`. Conclude with `⟨fun i => ap₂ e₂ (ap₁ e₁ (G i)), n₂, p₂, t₂, fun h c hc => c₂ h c (c₁ h c hc)⟩`.
-/
theorem pairEmb_of_steps : PairSlices → PairStep₁ → PairStep₂ → PairEmb := by
  intro hS h₁ h₂ E _ _ _ a b ι _ K₁ K₂ W₁ W₂ X₁ Y₁ X₂ Y₂ G hW₁ hW₂ hX₁ hX₂ hE₁ hE₂ hG hGp hGt
  obtain ⟨e₁, he₁Y, he₁i, he₁q⟩ := hE₁
  obtain ⟨e₂, he₂Y, he₂i, he₂q⟩ := hE₂
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hG
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hi
  obtain ⟨hmem, hval⟩ := (hS E a b X₁ X₂ (G i) (hGp i)).1 x.2
  have hφ : sl₁ (G i) x.2 ≠ 0 := by
    intro h0
    apply hx
    have h := congrFun hval x.1
    rw [h0] at h
    simpa using h.symm
  obtain ⟨n₁, p₁, t₁, c₁⟩ := h₁ E a b ι K₁ K₂ W₁ W₂ X₁ Y₁ X₂ e₁ G hW₁ hW₂ hX₁ he₁q he₁Y hGp hGt
    ⟨i, x.2, sl₁ (G i) x.2, hval, fun h0 => hφ (he₁i _ hmem h0)⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp n₁
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hj
  obtain ⟨hmem₂, hval₂⟩ := (hS E a b Y₁ X₂ (ap₁ e₁ (G j)) (p₁ j)).2 y.1
  have hψ : sl₂ (ap₁ e₁ (G j)) y.1 ≠ 0 := by
    intro h0
    apply hy
    have h := congrFun hval₂ y.2
    rw [h0] at h
    simpa using h.symm
  obtain ⟨n₂, p₂, t₂, c₂⟩ := h₂ E a b ι K₁ K₂ W₁ W₂ Y₁ X₂ Y₂ e₂ (fun i => ap₁ e₁ (G i)) hW₁ hW₂ hX₂ he₂q he₂Y p₁ t₁
    ⟨j, y.1, sl₂ (ap₁ e₁ (G j)) y.1, hval₂, fun h0 => hψ (he₂i _ hmem₂ h0)⟩
  exact ⟨fun i => ap₂ e₂ (ap₁ e₁ (G i)), n₂, p₂, t₂, fun h c hc => c₂ h c (c₁ h c hc)⟩

end GlobalTheory.CompanionTheory.EGlue
