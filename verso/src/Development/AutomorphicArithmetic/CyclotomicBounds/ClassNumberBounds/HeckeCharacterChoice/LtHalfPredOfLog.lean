import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.OddRad

namespace KStar.Choice

structure RootData (S L : Finset ℕ) (ν o : ℕ → ℕ) : Prop where
  prime_small : ∀ l ∈ S, l.Prime
  nu_two : 0 < ν 2
  one_lt : ∀ l, l.Prime → ν l = 0 → 1 < o l
  unramified : ∀ l, l.Prime → l ≠ 2 → l ∉ S → l ∉ L → ν l = 0 ∧ o l = l - 1
  large : ∀ l ∈ L, ν l = 0 ∧ (l - 1) / 2 ≤ o l
  small : ∀ l ∈ S, o l ∣ l - 1

/- English proof (translation)
Simplify using `[Nat.prime_two] nu_two := by simp one_lt := fun l hl h => by`. Establish `h2 : l ≠ 2` using `by rintro rfl; simp at h`. Use `hl.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `unramified := fun l _ h _ _ => by simp [h]`.

Use `large := by simp`. Use `small := by simp`.
-/
example : RootData {2} ∅ (fun l => if l = 2 then 1 else 0) (fun l => l - 1) where
  prime_small := by simp [Nat.prime_two]
  nu_two := by simp
  one_lt := fun l hl h => by
    have h2 : l ≠ 2 := by rintro rfl; simp at h
    have := hl.two_le; omega
  unramified := fun l _ h _ _ => by simp [h]
  large := by simp
  small := by simp

end KStar.Choice
