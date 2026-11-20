import Mathlib
open Matrix

namespace GlobalTheory.CompanionTheory.Transversal

/- English proof (translation)
Set `f : T → A ⧸ L.addSubgroupOf A` to `fun t => QuotientAddGroup.mk ⟨t.1, hT t.1 t.2⟩`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht⟩ ⟨t', ht'⟩ h`. Establish `h' : -(⟨t, hT t ht⟩ : A) + ⟨t', hT t' ht'⟩ ∈ L.addSubgroupOf A` using `QuotientAddGroup.eq.mp h`.

Rewrite `h'` using `[AddSubgroup.mem_addSubgroupOf]`. Establish `hL : t - t' ∈ L`. Establish `h2` using `L.neg_mem h'`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use `push_cast`.

Normalize the expressions using the abelian group laws. Take `⟨u, _, hu'⟩` from `hu t (hT t ht)`. Establish `e1 : t = u` using `hu' t ⟨ht, by simp⟩`. Establish `e2 : t' = u` using `hu' t' ⟨ht', hL⟩`. Conclude with `Subtype.ext (e1.trans e2.symm)`.

Introduce `q`. Take `⟨a, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Take `⟨t, ⟨ht, hat⟩, _⟩` from `hu a.1 a.2`. Use `⟨⟨t, ht⟩, QuotientAddGroup.eq.mpr ?_⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`.

Establish `e : ((-(⟨t, hT t ht⟩ : A) + a : A) : X) = a.1 - t`. Use `push_cast`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `hat`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_eq_relIndex (X : Type) [AddCommGroup X] (A L : AddSubgroup X) (T : Finset X)
    (_hLA : L ≤ A) (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) :
    T.card = L.relIndex A := by
  classical
  let f : T → A ⧸ L.addSubgroupOf A := fun t => QuotientAddGroup.mk ⟨t.1, hT t.1 t.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨t, ht⟩ ⟨t', ht'⟩ h
      have h' : -(⟨t, hT t ht⟩ : A) + ⟨t', hT t' ht'⟩ ∈ L.addSubgroupOf A := QuotientAddGroup.eq.mp h
      rw [AddSubgroup.mem_addSubgroupOf] at h'
      have hL : t - t' ∈ L := by
        have h2 := L.neg_mem h'
        convert h2 using 1
        push_cast
        abel
      obtain ⟨u, _, hu'⟩ := hu t (hT t ht)
      have e1 : t = u := hu' t ⟨ht, by simp⟩
      have e2 : t' = u := hu' t' ⟨ht', hL⟩
      exact Subtype.ext (e1.trans e2.symm)
    · intro q
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨t, ⟨ht, hat⟩, _⟩ := hu a.1 a.2
      refine ⟨⟨t, ht⟩, QuotientAddGroup.eq.mpr ?_⟩
      rw [AddSubgroup.mem_addSubgroupOf]
      have e : ((-(⟨t, hT t ht⟩ : A) + a : A) : X) = a.1 - t := by
        push_cast
        abel
      rw [e]
      exact hat
  calc T.card = Nat.card T := (Nat.card_eq_finsetCard T).symm
    _ = Nat.card (A ⧸ L.addSubgroupOf A) := Nat.card_congr (Equiv.ofBijective f hf)
    _ = L.relIndex A := by simp only [AddSubgroup.relIndex, AddSubgroup.index]

end GlobalTheory.CompanionTheory.Transversal
