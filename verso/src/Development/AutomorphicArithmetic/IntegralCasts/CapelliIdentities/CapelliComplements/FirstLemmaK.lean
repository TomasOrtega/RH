import Mathlib

namespace Bl.FirstLemmaK

/- English proof (translation)
Introduce `α S hS f hf`. Break down `S.eq_empty_or_nonempty with h | hne` into its components or cases. Use `⟨1, one_pos, le_rfl, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[h]`.

Conclude with `absurd hx (Set.notMem_empty x)`. Take `⟨a, ha, hmin⟩` from `Set.exists_min_image S f hS hne`. Establish `hfa : 0 < f a` using `hf a ha`. Use `⟨min (f a) 1 / 2, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: 0 < min (f a) 1` using `lt_min hfa one_pos`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `: min (f a) 1 ≤ 1` using `min_le_right _ _`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `x hx`. Establish `h1 : min (f a) 1 ≤ f a` using `min_le_left _ _`.

Establish `h2 : f a ≤ f x` using `hmin x hx`. Establish `: 0 < min (f a) 1` using `lt_min hfa one_pos`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem goal1 :
  ∀ {α : Type} {S : Set.{0} α},
  Set.Finite.{0} S →
    ∀ (f : α → Real),
      (∀ (x : α), Membership.mem.{0, 0} S x → LT.lt.{0} 0 (f x)) →
        Exists.{1} fun (r : Real) ↦
          And (LT.lt.{0} 0 r) (And (LE.le.{0} r 1) (∀ (x : α), Membership.mem.{0, 0} S x → LT.lt.{0} r (f x))) := by
  intro α S hS f hf
  rcases S.eq_empty_or_nonempty with h | hne
  · refine ⟨1, one_pos, le_rfl, ?_⟩
    intro x hx
    rw [h] at hx
    exact absurd hx (Set.notMem_empty x)
  · obtain ⟨a, ha, hmin⟩ := Set.exists_min_image S f hS hne
    have hfa : 0 < f a := hf a ha
    refine ⟨min (f a) 1 / 2, ?_, ?_, ?_⟩
    · have : 0 < min (f a) 1 := lt_min hfa one_pos
      linarith
    · have : min (f a) 1 ≤ 1 := min_le_right _ _
      linarith
    · intro x hx
      have h1 : min (f a) 1 ≤ f a := min_le_left _ _
      have h2 : f a ≤ f x := hmin x hx
      have : 0 < min (f a) 1 := lt_min hfa one_pos
      linarith

end Bl.FirstLemmaK
