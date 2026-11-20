import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave

open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.ShuffleWords

variable {T : Type u}

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil`. Introduce `u' x h'`. Consider the cases of `h'`. Conclude with `⟨[], Interleave.nil, Interleave.nil⟩`.

Consider the case `@left a u v w _ ih`. Introduce `u' x h'`. Take `⟨v', h₁, h₂⟩` from `ih h'`. Conclude with `⟨a :: v', Interleave.right h₁, Interleave.left h₂⟩`. Consider the case `@right a u v w _ ih`.

Introduce `u' x h'`. Consider the cases of `h' with`. Consider the case `left h'`. Take `⟨v', h₁, h₂⟩` from `ih h'`. Conclude with `⟨v', Interleave.left h₁, h₂⟩`.

Consider the case `right h'`. Take `⟨v', h₁, h₂⟩` from `ih h'`. Conclude with `⟨a :: v', Interleave.right h₁, Interleave.right h₂⟩`.
-/
theorem interleave_exchange {u v w : List T} (h : Interleave u v w) :
    ∀ {u' x : List T}, Interleave u' x v →
      ∃ v', Interleave u' v' w ∧ Interleave u x v' := by
  induction h with
  | nil =>
    intro u' x h'
    cases h'
    exact ⟨[], Interleave.nil, Interleave.nil⟩
  | @left a u v w _ ih =>
    intro u' x h'
    obtain ⟨v', h₁, h₂⟩ := ih h'
    exact ⟨a :: v', Interleave.right h₁, Interleave.left h₂⟩
  | @right a u v w _ ih =>
    intro u' x h'
    cases h' with
    | left h' =>
      obtain ⟨v', h₁, h₂⟩ := ih h'
      exact ⟨v', Interleave.left h₁, h₂⟩
    | right h' =>
      obtain ⟨v', h₁, h₂⟩ := ih h'
      exact ⟨a :: v', Interleave.right h₁, Interleave.right h₂⟩

/- English proof (translation)
Consider the cases of `h with`. Consider the case `cons hv hw`. Consider the cases of `hv with`. Consider the case `cons hx hv`. Take `⟨v', h₁, h₂⟩` from `interleave_exchange hw hv`.

Conclude with `Shuffle.cons (Shuffle.cons hx h₂) h₁`.
-/
theorem shuffle_swap {a b : List T} {us : List (List T)} {w : List T}
    (h : Shuffle (a :: b :: us) w) : Shuffle (b :: a :: us) w := by
  cases h with
  | cons hv hw =>
    cases hv with
    | cons hx hv =>
      obtain ⟨v', h₁, h₂⟩ := interleave_exchange hw hv
      exact Shuffle.cons (Shuffle.cons hx h₂) h₁

/- English proof (translation)
Proceed by induction on `hp generalizing w with`. Consider the case `nil => exact h`. Consider the case `cons a _ ih`. Consider the cases of `h with`. Consider the case `cons hv hw => exact Shuffle.cons (ih _ hv) hw`.

Consider the case `swap a b l => exact shuffle_swap h`. Consider the case `trans _ _ ih₁ ih₂ => exact ih₂ _ (ih₁ _ h)`.
-/
theorem shuffle_perm {T : Type u} (us us' : List (List T)) (w : List T)
    (h : Shuffle us w) (hp : us.Perm us') : Shuffle us' w := by
  induction hp generalizing w with
  | nil => exact h
  | cons a _ ih =>
    cases h with
    | cons hv hw => exact Shuffle.cons (ih _ hv) hw
  | swap a b l => exact shuffle_swap h
  | trans _ _ ih₁ ih₂ => exact ih₂ _ (ih₁ _ h)

end GlobalTheory.CompanionTheory.ShuffleWords
