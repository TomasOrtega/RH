import Mathlib

open Matrix

namespace GlobalTheory.CompanionTheory.OpenSubgroupTransversal

/- English proof (translation)
Use `haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA`. Establish `hopen : IsOpen ((H.addSubgroupOf A : AddSubgroup A) : Set A)` using `hH.preimage continuous_subtype_val`. Use `haveI : Finite (A ⧸ H.addSubgroupOf A) := AddSubgroup.quotient_finite_of_isOpen _ hopen`. Use `haveI : Fintype (A ⧸ H.addSubgroupOf A) := Fintype.ofFinite _`. Set `rep : A ⧸ H.addSubgroupOf A → X` to `fun q => ((Quotient.out q : A) : X)`.

Use `⟨Finset.univ.image rep, ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.mp ht`. Conclude with `(Quotient.out q).2`. Introduce `a ha`.

Establish `key : ∀ q : A ⧸ H.addSubgroupOf A, a - rep q ∈ H ↔ q = QuotientAddGroup.mk ⟨a, ha⟩`. Introduce `q`. Use `conv_rhs => rw [← QuotientAddGroup.out_eq' q]`. Rewrite using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, sub_eq_add_neg, add_comm]`. Conclude with `Iff.rfl`.

Use `⟨rep (QuotientAddGroup.mk ⟨a, ha⟩), ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, (key _).mpr rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `t ⟨ht, hat⟩`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.mp ht`. Rewrite using `[(key q).mp hat]`.
-/
theorem finite_transversal {X : Type} [TopologicalSpace X] [AddCommGroup X]
    [IsTopologicalAddGroup X] (A H : AddSubgroup X) (hA : IsCompact (A : Set X))
    (hH : IsOpen (H : Set X)) (_hHA : H ≤ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H := by
  classical
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hopen : IsOpen ((H.addSubgroupOf A : AddSubgroup A) : Set A) :=
    hH.preimage continuous_subtype_val
  haveI : Finite (A ⧸ H.addSubgroupOf A) := AddSubgroup.quotient_finite_of_isOpen _ hopen
  haveI : Fintype (A ⧸ H.addSubgroupOf A) := Fintype.ofFinite _
  let rep : A ⧸ H.addSubgroupOf A → X := fun q => ((Quotient.out q : A) : X)
  refine ⟨Finset.univ.image rep, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    exact (Quotient.out q).2
  · intro a ha
    have key : ∀ q : A ⧸ H.addSubgroupOf A,
        a - rep q ∈ H ↔ q = QuotientAddGroup.mk ⟨a, ha⟩ := by
      intro q
      conv_rhs => rw [← QuotientAddGroup.out_eq' q]
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, sub_eq_add_neg, add_comm]
      exact Iff.rfl
    refine ⟨rep (QuotientAddGroup.mk ⟨a, ha⟩),
      ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, (key _).mpr rfl⟩, ?_⟩
    rintro t ⟨ht, hat⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    rw [(key q).mp hat]

/- English proof (translation)
Introduce `A H hA hH hHA` and use `GlobalTheory.CompanionTheory.OpenSubgroupTransversal.finite_transversal A H hA hH hHA`.
-/
theorem main : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
    (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A →
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H :=
  fun A H hA hH hHA => GlobalTheory.CompanionTheory.OpenSubgroupTransversal.finite_transversal A H hA hH hHA

end GlobalTheory.CompanionTheory.OpenSubgroupTransversal
