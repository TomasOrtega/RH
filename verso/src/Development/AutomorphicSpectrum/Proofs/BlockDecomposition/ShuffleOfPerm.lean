import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave

open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.ShuffleWords

variable {T : Type u}

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Supply the required witnesses or components.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
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
Split into cases according to the possible forms of the given data. Treat this case separately. Split into cases according to the possible forms of the given data. Treat this case separately. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
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
Proceed by induction. Treat this case separately. Treat this case separately. Split into cases according to the possible forms of the given data. Treat this case separately.

Treat this case separately. Treat this case separately.
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
