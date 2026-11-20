import Mathlib

namespace Bl.FirstBlockLemmaL

/- English proof (translation)
Introduce `ℓ _ s hs`. Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a t ih`. Establish `ha : a ≠ 0` using `hs a (by simp)`.

Establish `ht' : ∀ x, x ∈ t → x ≠ 0` using `fun x hx => hs x (Multiset.mem_cons_of_mem hx)`. Establish `ht : t.prod ≠ 0`. Rewrite using `[Ne, Multiset.prod_eq_zero_iff]`. Introduce `h`. Conclude with `ht' 0 h rfl`.

Rewrite using `[Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, padicValNat.mul ha ht, ih ht']`.
-/
theorem goal1 :
  ∀ (ℓ : Nat) [Fact (Nat.Prime ℓ)] (s : Multiset.{0} Nat),
  (∀ (x : Nat), Membership.mem.{0, 0} s x → Ne.{1} x 0) →
    Eq.{1} (padicValNat ℓ (Multiset.prod.{0} s)) (Multiset.sum.{0} (Multiset.map.{0, 0} (padicValNat ℓ) s)) := by
  intro ℓ _ s hs
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    have ha : a ≠ 0 := hs a (by simp)
    have ht' : ∀ x, x ∈ t → x ≠ 0 := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have ht : t.prod ≠ 0 := by
      rw [Ne, Multiset.prod_eq_zero_iff]
      intro h
      exact ht' 0 h rfl
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, padicValNat.mul ha ht, ih ht']

end Bl.FirstBlockLemmaL
