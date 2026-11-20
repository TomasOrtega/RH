import Mathlib
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `X U hU F hFU hsp W hW`. Establish `key : ∀ a ∈ F, ∃ g : Γ(X, U), a ∈ X.basicOpen g ∧ X.basicOpen g ≤ W a ∧ ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen g`. Introduce `a ha`. Set `C : Set X` to `⋃ b ∈ F.erase a, closure {b}`. Establish `hC : IsClosed C` using `isClosed_biUnion_finset (fun b _ => isClosed_closure)`.

Set `V : X.Opens` to `W a ⊓ ⟨Cᶜ, hC.isOpen_compl⟩`. Establish `haC : a ∉ C`. Simplify using `only [C, Set.mem_iUnion, not_exists]`. Introduce `b hb hab`. Establish `hb'` using `Finset.mem_erase.mp hb`.

Conclude with `hb'.1 (hsp b hb'.2 a ha (specializes_iff_mem_closure.mpr hab))`. Establish `haV : a ∈ V` using `⟨hW a ha, haC⟩`. Take `⟨g, hgV, hag⟩` from `hU.exists_basicOpen_le ⟨a, haV⟩ (hFU a ha)`. Use `⟨g, hag, le_trans hgV inf_le_left, ?_⟩` and prove the remaining obligations. Introduce `b hb hba hbg`.

Establish `hbV : b ∈ V` using `hgV hbg`. Apply `hbV.2` to reduce the goal to its premises. Simplify using `only [C, Set.mem_iUnion]`. Conclude with `⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, subset_closure rfl⟩`. Use `choose! f hf using key`.

Conclude with `⟨f, hf⟩`.
-/
theorem exists_separating_basicOpen_functions : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (F : Finset X), (∀ a ∈ F, a ∈ U) → (∀ a ∈ F, ∀ b ∈ F, a ⤳ b → a = b) → ∀ W : X → X.Opens, (∀ a ∈ F, a ∈ W a) → ∃ f : X → Γ(X, U), ∀ a ∈ F, a ∈ X.basicOpen (f a) ∧ X.basicOpen (f a) ≤ W a ∧ ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen (f a) := by
  intro X U hU F hFU hsp W hW
  classical
  have key : ∀ a ∈ F, ∃ g : Γ(X, U), a ∈ X.basicOpen g ∧ X.basicOpen g ≤ W a ∧
      ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen g := by
    intro a ha
    let C : Set X := ⋃ b ∈ F.erase a, closure {b}
    have hC : IsClosed C := isClosed_biUnion_finset (fun b _ => isClosed_closure)
    let V : X.Opens := W a ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
    have haC : a ∉ C := by
      simp only [C, Set.mem_iUnion, not_exists]
      intro b hb hab
      have hb' := Finset.mem_erase.mp hb
      exact hb'.1 (hsp b hb'.2 a ha (specializes_iff_mem_closure.mpr hab))
    have haV : a ∈ V := ⟨hW a ha, haC⟩
    obtain ⟨g, hgV, hag⟩ := hU.exists_basicOpen_le ⟨a, haV⟩ (hFU a ha)
    refine ⟨g, hag, le_trans hgV inf_le_left, ?_⟩
    intro b hb hba hbg
    have hbV : b ∈ V := hgV hbg
    apply hbV.2
    simp only [C, Set.mem_iUnion]
    exact ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, subset_closure rfl⟩
  choose! f hf using key
  exact ⟨f, hf⟩

end GlobalTheory
