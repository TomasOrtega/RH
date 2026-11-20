import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.OrbStabZ

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdE

section Gen

variable {G : Type} [Group G] {ι : Type} {H : ι → Type} [∀ i, Group (H i)] (π : ∀ i, G →* H i)

def glob (A : ∀ i, Subgroup (H i)) : Subgroup G := ⨅ i, (A i).comap (π i)

/- English proof (translation)
Simplify using `[glob, Subgroup.mem_iInf]`.
-/
theorem mem_glob {A : ∀ i, Subgroup (H i)} {g : G} : g ∈ glob π A ↔ ∀ i, π i g ∈ A i := by
  simp [glob, Subgroup.mem_iInf]

/- English proof (translation)
Use `set K := (glob π C).subgroupOf (glob π A) with hK`. Set `Φ : ↥(glob π A) → ∀ i : S, ↥(A (i : ι)) ⧸ (C (i : ι)).subgroupOf (A (i : ι))` to `fun g i => QuotientGroup.mk ⟨π i g, (mem_glob π).1 g.2 i⟩`. Establish `hrel : ∀ a b : ↥(glob π A), Φ a = Φ b ↔ a⁻¹ * b ∈ K`. Introduce `a b`. Rewrite using `[hK, Subgroup.mem_subgroupOf, mem_glob]`.

Simplify using `only [Φ, funext_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Distinguish the cases in `hi : i ∈ S`. Establish `h1` using `h ⟨i, hi⟩`.

Rewrite `h1` using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `using h1`. Rewrite using `[← hS i hi]`. Simplify using `using (A i).mul_mem ((A i).inv_mem ((mem_glob π).1 a.2 i)) ((mem_glob π).1 b.2 i)`. Introduce `h i`.

Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `using h i`. Establish `hsurj : Function.Surjective Φ`. Introduce `q`. Use `choose r hr using fun i : S => QuotientGroup.mk_surjective (q i)`.

Take `⟨g, hg1, hg2⟩` from `happrox (fun i => if hi : i ∈ S then ((r ⟨i, hi⟩ : A i) : H i) else 1)`. Establish `hgA : g ∈ glob π A`. Rewrite using `[mem_glob]`. Introduce `i`. Distinguish the cases in `hi : i ∈ S`.

Establish `h1` using `hg1 i hi`. Simplify using `only [dif_pos hi] at h1`. Establish `h2` using `(A i).mul_mem (r ⟨i, hi⟩).2 (Subgroup.mem_inf.1 h1).1`. Simplify using `using h2`. Conclude with `hg2 i hi`.

Use `⟨⟨g, hgA⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[← hr i]`. Simplify using `only [Φ]`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`.

Establish `h1` using `hg1 i.1 i.2`. Simplify using `only [dif_pos i.2] at h1`. Simplify using `using (C i).inv_mem (Subgroup.mem_inf.1 h1).2`. Set `Ψ : ↥(glob π A) ⧸ K → ∀ i : S, ↥(A (i : ι)) ⧸ (C (i : ι)).subgroupOf (A (i : ι))` to `Quotient.lift Φ (fun a b hab => (hrel a b).2 (QuotientGroup.leftRel_apply.1 hab))`. Establish `hbij : Function.Bijective Ψ`.

Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective x`. Take `⟨b, rfl⟩` from `QuotientGroup.mk_surjective y`. Conclude with `QuotientGroup.eq.2 ((hrel a b).1 hxy)`.

Introduce `q`. Take `⟨a, ha⟩` from `hsurj q`. Conclude with `⟨QuotientGroup.mk a, ha⟩`. Establish `hcard` using `Nat.card_congr (Equiv.ofBijective Ψ hbij)`. Rewrite `hcard` using `[Nat.card_pi]`.

Rewrite using `[← Finset.prod_coe_sort S]`. Conclude with `hcard`.
-/
theorem relIndex_glob (A C : ∀ i, Subgroup (H i)) (S : Finset ι) (hS : ∀ i ∉ S, A i = C i)
    (hfin : ∀ i, (C i).relIndex (A i) ≠ 0)
    (happrox : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ A i ⊓ C i) ∧ ∀ i ∉ S, π i g ∈ A i) :
    (glob π C).relIndex (glob π A) = ∏ i ∈ S, (C i).relIndex (A i) := by
  classical
  set K := (glob π C).subgroupOf (glob π A) with hK
  let Φ : ↥(glob π A) → ∀ i : S, ↥(A (i : ι)) ⧸ (C (i : ι)).subgroupOf (A (i : ι)) := fun g i =>
    QuotientGroup.mk ⟨π i g, (mem_glob π).1 g.2 i⟩
  have hrel : ∀ a b : ↥(glob π A), Φ a = Φ b ↔ a⁻¹ * b ∈ K := by
    intro a b
    rw [hK, Subgroup.mem_subgroupOf, mem_glob]
    simp only [Φ, funext_iff]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · have h1 := h ⟨i, hi⟩
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
        simpa using h1
      · rw [← hS i hi]
        simpa using (A i).mul_mem ((A i).inv_mem ((mem_glob π).1 a.2 i)) ((mem_glob π).1 b.2 i)
    · intro h i
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using h i
  have hsurj : Function.Surjective Φ := by
    intro q
    choose r hr using fun i : S => QuotientGroup.mk_surjective (q i)
    obtain ⟨g, hg1, hg2⟩ := happrox (fun i => if hi : i ∈ S then ((r ⟨i, hi⟩ : A i) : H i) else 1)
    have hgA : g ∈ glob π A := by
      rw [mem_glob]
      intro i
      by_cases hi : i ∈ S
      · have h1 := hg1 i hi
        simp only [dif_pos hi] at h1
        have h2 := (A i).mul_mem (r ⟨i, hi⟩).2 (Subgroup.mem_inf.1 h1).1
        simpa using h2
      · exact hg2 i hi
    refine ⟨⟨g, hgA⟩, ?_⟩
    funext i
    rw [← hr i]
    simp only [Φ]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := hg1 i.1 i.2
    simp only [dif_pos i.2] at h1
    simpa using (C i).inv_mem (Subgroup.mem_inf.1 h1).2
  let Ψ : ↥(glob π A) ⧸ K → ∀ i : S, ↥(A (i : ι)) ⧸ (C (i : ι)).subgroupOf (A (i : ι)) :=
    Quotient.lift Φ (fun a b hab => (hrel a b).2 (QuotientGroup.leftRel_apply.1 hab))
  have hbij : Function.Bijective Ψ := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      exact QuotientGroup.eq.2 ((hrel a b).1 hxy)
    · intro q
      obtain ⟨a, ha⟩ := hsurj q
      exact ⟨QuotientGroup.mk a, ha⟩
  have hcard := Nat.card_congr (Equiv.ofBijective Ψ hbij)
  rw [Nat.card_pi] at hcard
  rw [← Finset.prod_coe_sort S]
  exact hcard

/- English proof (translation)
Establish `happrox' : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ C i ⊓ A i) ∧ ∀ i ∉ S, π i g ∈ C i`. Introduce `h`. Take `⟨g, hg1, hg2⟩` from `happrox h`. Use `⟨g, fun i hi => ?_, fun i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[inf_comm]`.

Conclude with `hg1 i hi`. Rewrite using `[← hS i hi]`. Conclude with `hg2 i hi`. Unfold `Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio`. Rewrite using `[relIndex_glob π A C S hS hfinA happrox, relIndex_glob π C A S (fun i hi => (hS i hi).symm) hfinC happrox']`.

Use `push_cast`. Rewrite using `[Finset.prod_div_distrib]`.
-/
theorem idxRatio_glob (A C : ∀ i, Subgroup (H i)) (S : Finset ι) (hS : ∀ i ∉ S, A i = C i)
    (hfinA : ∀ i, (C i).relIndex (A i) ≠ 0) (hfinC : ∀ i, (A i).relIndex (C i) ≠ 0)
    (happrox : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ A i ⊓ C i) ∧ ∀ i ∉ S, π i g ∈ A i) :
    Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (glob π A) (glob π C) = ∏ i ∈ S, Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (A i) (C i) := by
  have happrox' : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ C i ⊓ A i) ∧ ∀ i ∉ S, π i g ∈ C i := by
    intro h
    obtain ⟨g, hg1, hg2⟩ := happrox h
    refine ⟨g, fun i hi => ?_, fun i hi => ?_⟩
    · rw [inf_comm]
      exact hg1 i hi
    · rw [← hS i hi]
      exact hg2 i hi
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio
  rw [relIndex_glob π A C S hS hfinA happrox,
    relIndex_glob π C A S (fun i hi => (hS i hi).symm) hfinC happrox']
  push_cast
  rw [Finset.prod_div_distrib]

end Gen

end Formalism.L2.SG.Pf.ProdE
