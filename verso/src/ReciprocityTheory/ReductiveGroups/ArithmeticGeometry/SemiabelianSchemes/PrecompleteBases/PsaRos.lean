import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusIsCommMonObjSt

open AddMonoidAlgebra

namespace ReciprocityTheory.ChartRestriction.G.Semi

/- English proof (translation)
Establish `hone0 : (1 : AddMonoidAlgebra R A).coeff 0 = 1`. Rewrite using `[AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]`. Establish `hone1 : ∀ x : A, x ≠ 0 → (1 : AddMonoidAlgebra R A).coeff x = 0`. Introduce `x hx`. Rewrite using `[AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single]`.

Simplify using `only [Finsupp.single_apply, hx, Ne.symm hx, if_false]`. Establish `hf : f ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[zero_mul]`. Conclude with `zero_ne_one h`.

Establish `hg : g ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[mul_zero]`. Conclude with `zero_ne_one h`. Establish `hfs : f.coeff.support.Nonempty`.

Rewrite using `[Finsupp.support_nonempty_iff]`. Introduce `h0`. Apply `hf` to reduce the goal to its premises. Apply `AddMonoidAlgebra.ext` to reduce the goal to its premises. Rewrite using `[h0, AddMonoidAlgebra.coeff_zero]`.

Establish `hgs : g.coeff.support.Nonempty`. Rewrite using `[Finsupp.support_nonempty_iff]`. Introduce `h0`. Apply `hg` to reduce the goal to its premises. Apply `AddMonoidAlgebra.ext` to reduce the goal to its premises.

Rewrite using `[h0, AddMonoidAlgebra.coeff_zero]`. Establish `hcard : f.coeff.support.card * g.coeff.support.card ≤ 1`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Take `⟨p1, hp1, p2, hp2, hne, hu1, hu2⟩` from `TwoUniqueSums.uniqueAdd_of_one_lt_card hlt`.

Rewrite `hp1`, `hp2` using `[Finset.mem_product]`. Establish `hc : ∀ p : A × A, p.1 ∈ f.coeff.support → p.2 ∈ g.coeff.support → UniqueAdd f.coeff.support g.coeff.support p.1 p.2 → p.1 + p.2 = 0`. Introduce `p hpa hpb hu`. Establish `e1` using `AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd hu`. Rewrite `e1` using `[h]`.

Assume the negation of the conclusion as `hz`. Rewrite `e1` using `[hone1 _ hz]`. Conclude with `mul_ne_zero (Finsupp.mem_support_iff.mp hpa) (Finsupp.mem_support_iff.mp hpb) e1.symm`. Establish `s1` using `hc p1 hp1.1 hp1.2 hu1`. Establish `s2` using `hc p2 hp2.1 hp2.2 hu2`.

Establish `h12` using `hu1 hp2.1 hp2.2 (s2.trans s1.symm)`. Conclude with `hne (Prod.ext h12.1 h12.2).symm`. Establish `hc1` using `hfs.card_pos`. Establish `hc2` using `hgs.card_pos`. Establish `hcf : f.coeff.support.card = 1` using `by nlinarith`.

Establish `hcg : g.coeff.support.card = 1` using `by nlinarith`. Take `⟨a, ha⟩` from `Finset.card_eq_one.mp hcf`. Take `⟨b, hb⟩` from `Finset.card_eq_one.mp hcg`. Establish `hfa : f = single a (f.coeff a)`. Apply `AddMonoidAlgebra.ext` to reduce the goal to its premises.

Rewrite using `[AddMonoidAlgebra.coeff_single]`. Use extensionality with `x`. Distinguish the cases in `hx : x = a`. Substitute `hx` using the available equality. Rewrite using `[Finsupp.single_eq_same]`.

Simplify using `only [Finsupp.single_apply, hx, Ne.symm hx, if_false]`. Assume the negation of the conclusion as `hne`. Establish `hmem : x ∈ f.coeff.support` using `Finsupp.mem_support_iff.mpr hne`. Rewrite `hmem` using `[ha, Finset.mem_singleton]`. Conclude with `hx hmem`.

Establish `hgb : g = single b (g.coeff b)`. Apply `AddMonoidAlgebra.ext` to reduce the goal to its premises. Rewrite using `[AddMonoidAlgebra.coeff_single]`. Use extensionality with `x`. Distinguish the cases in `hx : x = b`.

Substitute `hx` using the available equality. Rewrite using `[Finsupp.single_eq_same]`. Simplify using `only [Finsupp.single_apply, hx, Ne.symm hx, if_false]`. Assume the negation of the conclusion as `hne`. Establish `hmem : x ∈ g.coeff.support` using `Finsupp.mem_support_iff.mpr hne`.

Rewrite `hmem` using `[hb, Finset.mem_singleton]`. Conclude with `hx hmem`. Establish `hu : UniqueAdd f.coeff.support g.coeff.support a b`. Introduce `a' b' ha' hb' _`. Rewrite `ha'` using `[ha, Finset.mem_singleton]`.

Rewrite `hb'` using `[hb, Finset.mem_singleton]`. Conclude with `⟨ha', hb'⟩`. Establish `e1` using `AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd hu`. Rewrite `e1` using `[h]`. Establish `hfa0 : f.coeff a ≠ 0` using `Finsupp.mem_support_iff.mp (by rw [ha]; exact Finset.mem_singleton_self a)`.

Establish `hgb0 : g.coeff b ≠ 0` using `Finsupp.mem_support_iff.mp (by rw [hb]; exact Finset.mem_singleton_self b)`. Establish `hab : a + b = 0`. Assume the negation of the conclusion as `hz`. Rewrite `e1` using `[hone1 _ hz]`. Conclude with `mul_ne_zero hfa0 hgb0 e1.symm`.

Rewrite `e1` using `[hab, hone0]`. Conclude with `⟨a, b, hab, e1.symm, hfa, hgb⟩`.
-/
theorem eq_single_of_mul_eq_one {R A : Type*} [CommRing R] [IsDomain R] [AddCommMonoid A]
    [TwoUniqueSums A] {f g : AddMonoidAlgebra R A} (h : f * g = 1) :
    ∃ a b : A, a + b = 0 ∧ f.coeff a * g.coeff b = 1 ∧
      f = single a (f.coeff a) ∧ g = single b (g.coeff b) := by
  classical
  have hone0 : (1 : AddMonoidAlgebra R A).coeff 0 = 1 := by
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  have hone1 : ∀ x : A, x ≠ 0 → (1 : AddMonoidAlgebra R A).coeff x = 0 := by
    intro x hx
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single]
    simp only [Finsupp.single_apply, hx, Ne.symm hx, if_false]
  have hf : f ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact zero_ne_one h
  have hg : g ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact zero_ne_one h
  have hfs : f.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h0
    apply hf
    apply AddMonoidAlgebra.ext
    rw [h0, AddMonoidAlgebra.coeff_zero]
  have hgs : g.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h0
    apply hg
    apply AddMonoidAlgebra.ext
    rw [h0, AddMonoidAlgebra.coeff_zero]
  have hcard : f.coeff.support.card * g.coeff.support.card ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨p1, hp1, p2, hp2, hne, hu1, hu2⟩ := TwoUniqueSums.uniqueAdd_of_one_lt_card hlt
    rw [Finset.mem_product] at hp1 hp2
    have hc : ∀ p : A × A, p.1 ∈ f.coeff.support → p.2 ∈ g.coeff.support →
        UniqueAdd f.coeff.support g.coeff.support p.1 p.2 → p.1 + p.2 = 0 := by
      intro p hpa hpb hu
      have e1 := AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd hu
      rw [h] at e1
      by_contra hz
      rw [hone1 _ hz] at e1
      exact mul_ne_zero (Finsupp.mem_support_iff.mp hpa) (Finsupp.mem_support_iff.mp hpb) e1.symm
    have s1 := hc p1 hp1.1 hp1.2 hu1
    have s2 := hc p2 hp2.1 hp2.2 hu2
    have h12 := hu1 hp2.1 hp2.2 (s2.trans s1.symm)
    exact hne (Prod.ext h12.1 h12.2).symm
  have hc1 := hfs.card_pos
  have hc2 := hgs.card_pos
  have hcf : f.coeff.support.card = 1 := by nlinarith
  have hcg : g.coeff.support.card = 1 := by nlinarith
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcf
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcg
  have hfa : f = single a (f.coeff a) := by
    apply AddMonoidAlgebra.ext
    rw [AddMonoidAlgebra.coeff_single]
    ext x
    by_cases hx : x = a
    · subst hx
      rw [Finsupp.single_eq_same]
    · simp only [Finsupp.single_apply, hx, Ne.symm hx, if_false]
      by_contra hne
      have hmem : x ∈ f.coeff.support := Finsupp.mem_support_iff.mpr hne
      rw [ha, Finset.mem_singleton] at hmem
      exact hx hmem
  have hgb : g = single b (g.coeff b) := by
    apply AddMonoidAlgebra.ext
    rw [AddMonoidAlgebra.coeff_single]
    ext x
    by_cases hx : x = b
    · subst hx
      rw [Finsupp.single_eq_same]
    · simp only [Finsupp.single_apply, hx, Ne.symm hx, if_false]
      by_contra hne
      have hmem : x ∈ g.coeff.support := Finsupp.mem_support_iff.mpr hne
      rw [hb, Finset.mem_singleton] at hmem
      exact hx hmem
  have hu : UniqueAdd f.coeff.support g.coeff.support a b := by
    intro a' b' ha' hb' _
    rw [ha, Finset.mem_singleton] at ha'
    rw [hb, Finset.mem_singleton] at hb'
    exact ⟨ha', hb'⟩
  have e1 := AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd hu
  rw [h] at e1
  have hfa0 : f.coeff a ≠ 0 := Finsupp.mem_support_iff.mp (by rw [ha]; exact Finset.mem_singleton_self a)
  have hgb0 : g.coeff b ≠ 0 := Finsupp.mem_support_iff.mp (by rw [hb]; exact Finset.mem_singleton_self b)
  have hab : a + b = 0 := by
    by_contra hz
    rw [hone1 _ hz] at e1
    exact mul_ne_zero hfa0 hgb0 e1.symm
  rw [hab, hone0] at e1
  exact ⟨a, b, hab, e1.symm, hfa, hgb⟩

instance twoUniqueSums_of_free (X : Type*) [AddCommGroup X] [Module.Free ℤ X] :
    TwoUniqueSums X :=
  (AddEquiv.twoUniqueSums_iff (Module.Free.chooseBasis ℤ X).repr.toAddEquiv).mpr inferInstance

end ReciprocityTheory.ChartRestriction.G.Semi
