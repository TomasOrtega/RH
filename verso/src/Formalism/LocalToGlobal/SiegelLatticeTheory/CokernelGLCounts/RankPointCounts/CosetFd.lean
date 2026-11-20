import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdealCovol

noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

/- English proof (translation)
Use `set Λ' := Λ.addSubgroupOf L`. Establish `: Finite (L ⧸ Λ')` using `Λ'.finite_quotient_of_finiteIndex`. Establish `: Fintype (L ⧸ Λ')` using `Fintype.ofFinite _`. Set `rep : L ⧸ Λ' → L` to `fun q => q.out`. Set `G : Set V` to `⋃ q : L ⧸ Λ', (fun y => ((rep q : L) : V) + y) ⁻¹' FL`.

Use `⟨G, MeasurableSet.iUnion fun q => measurable_const_add _ hFL, fun v => ?_⟩` and prove the remaining obligations. Take `⟨l, hl, hlu⟩` from `hdL v`. Use `set q : L ⧸ Λ' := (l : L ⧸ Λ')`. Establish `hdiff : -(rep q) + l ∈ Λ'`. Establish `: ((rep q : L) : L ⧸ Λ') = q` using `QuotientAddGroup.out_eq' q`.

Rewrite using `[← QuotientAddGroup.eq]`. Conclude with `this`. Establish `hΛ : ((-(rep q) + l : L) : V) ∈ Λ`. Rewrite `hdiff` using `[AddSubgroup.mem_addSubgroupOf]`. Conclude with `hdiff`.

Use `⟨⟨_, hΛ⟩, Set.mem_iUnion.2 ⟨q, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show ((rep q : L) : V) + (((-(rep q) + l : L) : V) + v) ∈ FL`. Simplify using `only [AddSubgroup.coe_add, AddSubgroup.coe_neg]`. Rewrite using `[← add_assoc, add_neg_cancel_left]`. Conclude with `hl`.

Introduce and unpack `⟨a, ha⟩ haG`. Take `⟨q', hq'⟩` from `Set.mem_iUnion.1 haG`. Establish `hq'' : ((rep q' : L) : V) + (a + v) ∈ FL` using `hq'`. Establish `hmem : ((rep q' : V) + a) ∈ L` using `L.add_mem (rep q').2 (hle ha)`. Establish `h1 : (⟨(rep q' : V) + a, hmem⟩ : L) = l` using `hlu _ (by show (rep q' : V) + a + v ∈ FL; rw [add_assoc]; exact hq'')`.

Establish `hqq : q' = q`. Establish `e : (rep q' : L) + ⟨a, hle ha⟩ = l`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using congrArg Subtype.val h1`. Establish `hmk : ((l : L) : L ⧸ Λ') = ((rep q' : L) : L ⧸ Λ')`.

Rewrite using `[← e, QuotientAddGroup.eq]`. Simplify using `only [neg_add_rev, neg_add_cancel_right]`. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Simplify using `using Λ.neg_mem ha`. Rewrite `hmk` using `[show ((rep q' : L) : L ⧸ Λ') = q' from QuotientAddGroup.out_eq' q']`.

Conclude with `hmk.symm`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show a = ((-(rep q) + l : L) : V)`. Use `congrArg Subtype.val h1` as an intermediate fact. Simplify using `only at this`.

Rewrite using `[← hqq]`. Simplify using `only [AddSubgroup.coe_add, AddSubgroup.coe_neg]`. Rewrite using `[← this]`. Normalize the expressions using the abelian group laws.
-/
theorem coset_fd {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (L Λ : AddSubgroup V)
    (hle : Λ ≤ L) (hfin : (Λ.addSubgroupOf L).FiniteIndex) (FL : Set V) (hFL : MeasurableSet FL)
    (hdL : ∀ v, ∃! l : L, (l : V) + v ∈ FL) :
    ∃ G : Set V, MeasurableSet G ∧ ∀ v, ∃! a : Λ, (a : V) + v ∈ G := by
  set Λ' := Λ.addSubgroupOf L
  have : Finite (L ⧸ Λ') := Λ'.finite_quotient_of_finiteIndex
  have : Fintype (L ⧸ Λ') := Fintype.ofFinite _
  let rep : L ⧸ Λ' → L := fun q => q.out
  let G : Set V := ⋃ q : L ⧸ Λ', (fun y => ((rep q : L) : V) + y) ⁻¹' FL
  refine ⟨G, MeasurableSet.iUnion fun q => measurable_const_add _ hFL, fun v => ?_⟩
  obtain ⟨l, hl, hlu⟩ := hdL v
  set q : L ⧸ Λ' := (l : L ⧸ Λ')
  have hdiff : -(rep q) + l ∈ Λ' := by
    have : ((rep q : L) : L ⧸ Λ') = q := QuotientAddGroup.out_eq' q
    rw [← QuotientAddGroup.eq]; exact this
  have hΛ : ((-(rep q) + l : L) : V) ∈ Λ := by
    rw [AddSubgroup.mem_addSubgroupOf] at hdiff; exact hdiff
  refine ⟨⟨_, hΛ⟩, Set.mem_iUnion.2 ⟨q, ?_⟩, ?_⟩
  · show ((rep q : L) : V) + (((-(rep q) + l : L) : V) + v) ∈ FL
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [← add_assoc, add_neg_cancel_left]; exact hl
  · rintro ⟨a, ha⟩ haG
    obtain ⟨q', hq'⟩ := Set.mem_iUnion.1 haG
    have hq'' : ((rep q' : L) : V) + (a + v) ∈ FL := hq'
    have hmem : ((rep q' : V) + a) ∈ L := L.add_mem (rep q').2 (hle ha)
    have h1 : (⟨(rep q' : V) + a, hmem⟩ : L) = l := hlu _ (by show (rep q' : V) + a + v ∈ FL; rw [add_assoc]; exact hq'')

    have hqq : q' = q := by
      have e : (rep q' : L) + ⟨a, hle ha⟩ = l := by
        apply Subtype.ext; simpa using congrArg Subtype.val h1
      have hmk : ((l : L) : L ⧸ Λ') = ((rep q' : L) : L ⧸ Λ') := by
        rw [← e, QuotientAddGroup.eq]
        simp only [neg_add_rev, neg_add_cancel_right]
        rw [AddSubgroup.mem_addSubgroupOf]
        simpa using Λ.neg_mem ha
      rw [show ((rep q' : L) : L ⧸ Λ') = q' from QuotientAddGroup.out_eq' q'] at hmk
      exact hmk.symm
    apply Subtype.ext
    show a = ((-(rep q) + l : L) : V)
    have := congrArg Subtype.val h1
    simp only at this
    rw [← hqq]
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [← this]
    abel

end Formalism.L2.SG.NGCut.SplitEmbedding
