import ReciprocityTheory.SemistableReduction.LatSemiSt
import Lemmata.GeneralBFactBisAlt.Imports

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

namespace DegAdd

open NumberField

/- English proof (translation)
Take `⟨d, hd, h⟩` from `exists_integral_multiples ℤ ℚ (L := K) {a}`. Conclude with `⟨d, hd, ⟨d • a, h a (Finset.mem_singleton_self a)⟩, zsmul_eq_mul a d⟩`.
-/
theorem exists_int_mul_integral {K : Type} [Field K] [NumberField K] (a : K) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ α : 𝓞 K, (α : K) = d * a := by
  obtain ⟨d, hd, h⟩ := exists_integral_multiples ℤ ℚ (L := K) {a}
  exact ⟨d, hd, ⟨d • a, h a (Finset.mem_singleton_self a)⟩, zsmul_eq_mul a d⟩

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_bis_other.goal1 .. | (apply Bl.general_b_fact_bis_other.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_bis_other.goal1 <;> assumption)`.
-/
theorem exists_int_smul_mem_span {K : Type} [Field K] [NumberField K] {r n : ℕ}
    (v : Fin n → Fin r → K) {x : Fin r → K} (hx : x ∈ Submodule.span K (Set.range v)) :
    ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range v) := by
  first | exact Bl.general_b_fact_bis_other.goal1 .. | (apply Bl.general_b_fact_bis_other.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_bis_other.goal1 <;> assumption)

/- English proof (translation)
Use `set N := (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.addSubgroupOf L.toAddSubgroup`. Establish `: Module.Finite (𝓞 K) L` using `Module.Finite.iff_fg.mpr hL`. Establish `: Module.Finite ℤ L` using `Module.Finite.trans (𝓞 K) L`. Set `f : L →+ (L.toAddSubgroup ⧸ N)` to `{ toFun := fun x => QuotientAddGroup.mk (⟨x.1, x.2⟩ : L.toAddSubgroup) map_zero' := rfl map_add' := fun _ _ => rfl }`. Establish `: Module.Finite ℤ (L.toAddSubgroup ⧸ N)`.

Use `Module.Finite.of_surjective f.toIntLinearMap ?_` and prove the remaining obligations. Introduce `q`. Take `⟨⟨y, hy⟩, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Conclude with `⟨⟨y, hy⟩, rfl⟩`. Establish `: Finite (L.toAddSubgroup ⧸ N)`.

Apply `Module.finite_of_fg_torsion` to reduce the goal to its premises. Introduce `q`. Take `⟨⟨y, hy⟩, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Take `⟨d, hd, hdy⟩` from `exists_int_smul_mem_span v (hv y hy)`. Use `⟨⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(d • (QuotientAddGroup.mk (⟨y, hy⟩ : L.toAddSubgroup) : L.toAddSubgroup ⧸ N)) = 0`. Rewrite using `[← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Simplify using `using hdy`. Conclude with `AddSubgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_zero_of_fg {K : Type} [Field K] [NumberField K] {r n : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : L.FG) (v : Fin n → Fin r → K)
    (hv : ∀ x ∈ L, x ∈ Submodule.span K (Set.range v)) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
  set N := (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.addSubgroupOf L.toAddSubgroup
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 K) L
  let f : L →+ (L.toAddSubgroup ⧸ N) :=
    { toFun := fun x => QuotientAddGroup.mk (⟨x.1, x.2⟩ : L.toAddSubgroup)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have : Module.Finite ℤ (L.toAddSubgroup ⧸ N) := by
    refine Module.Finite.of_surjective f.toIntLinearMap ?_
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨⟨y, hy⟩, rfl⟩
  have : Finite (L.toAddSubgroup ⧸ N) := by
    apply Module.finite_of_fg_torsion
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨d, hd, hdy⟩ := exists_int_smul_mem_span v (hv y hy)
    refine ⟨⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩, ?_⟩
    change (d • (QuotientAddGroup.mk (⟨y, hy⟩ : L.toAddSubgroup) : L.toAddSubgroup ⧸ N)) = 0
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hdy
  exact AddSubgroup.index_ne_zero_of_finite

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left i => exact Or.inl ⟨i, (Fin.append_left b c i).symm⟩`.

Consider the case `right j => exact Or.inr ⟨j, (Fin.append_right b c j).symm⟩`. Introduce and unpack `(⟨i, rfl⟩ | ⟨j, rfl⟩)`. Conclude with `⟨Fin.castAdd m i, Fin.append_left b c i⟩`. Conclude with `⟨Fin.natAdd k j, Fin.append_right b c j⟩`.
-/
theorem range_fin_append {α : Type} {k m : ℕ} (b : Fin k → α) (c : Fin m → α) :
    Set.range (Fin.append b c) = Set.range b ∪ Set.range c := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, (Fin.append_left b c i).symm⟩
    | right j => exact Or.inr ⟨j, (Fin.append_right b c j).symm⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd m i, Fin.append_left b c i⟩
    · exact ⟨Fin.natAdd k j, Fin.append_right b c j⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `cases i <;> simp`.
-/
theorem fin_append_comp_equiv {α : Type} {k m : ℕ} (b : Fin k → α) (c : Fin m → α) :
    Fin.append b c ∘ finSumFinEquiv = Sum.elim b c := by
  funext i
  cases i <;> simp

/- English proof (translation)
Establish `h2` using `h.comp finSumFinEquiv finSumFinEquiv.injective`. Rewrite `h2` using `[fin_append_comp_equiv]`. Establish `h3` using `linearIndependent_sum.mp h2`. Simplify `h3` using `only [Sum.elim_comp_inl, Sum.elim_comp_inr]`.
-/
theorem indep_parts {K : Type} [Field K] {r k m : ℕ}
    {b : Fin k → Fin r → K} {c : Fin m → Fin r → K} (h : LinearIndependent K (Fin.append b c)) :
    LinearIndependent K b ∧ LinearIndependent K c ∧
      Disjoint (Submodule.span K (Set.range b)) (Submodule.span K (Set.range c)) := by
  have h2 := h.comp finSumFinEquiv finSumFinEquiv.injective
  rw [fin_append_comp_equiv] at h2
  have h3 := linearIndependent_sum.mp h2
  simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr] using h3

/- English proof (translation)
Use `set Sb := Submodule.span (𝓞 K) (Set.range b)`. Use `set Sc := Submodule.span (𝓞 K) (Set.range c)`. Use `set S := satSub L b`. Establish `hA : Submodule.span (𝓞 K) (Set.range (Fin.append b c)) = Sb ⊔ Sc`. Rewrite using `[range_fin_append, Submodule.span_union]`.

Establish `hSbS : Sb ≤ S`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨hb i, Submodule.subset_span ⟨i, rfl⟩⟩`. Establish `hScL : Sc ≤ L`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `hc j`. Establish `hSL : S ≤ L` using `inf_le_left`. Establish `hmeet : ∀ x, x ∈ Sb ⊔ Sc → x ∈ S → x ∈ Sb`.

Introduce `x hx1 hx2`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hx1`. Establish `hyK : y ∈ Submodule.span K (Set.range b)` using `Submodule.span_le_restrictScalars (𝓞 K) K _ hy`. Establish `hzK : z ∈ Submodule.span K (Set.range c)` using `Submodule.span_le_restrictScalars (𝓞 K) K _ hz`. Establish `hxK : y + z ∈ Submodule.span K (Set.range b)` using `hx2.2`.

Establish `hz' : z ∈ Submodule.span K (Set.range b)`. Establish `h` using `Submodule.sub_mem _ hxK hyK`. Simplify using `using h`. Establish `hz0 : z = 0` using `Submodule.disjoint_def.mp hdis z hz' hzK`. Simplify `hy` using `[hz0]`.

Establish `hinf : (Sb ⊔ Sc).toAddSubgroup ⊓ S.toAddSubgroup = Sb.toAddSubgroup`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `hmeet x (AddSubgroup.mem_inf.mp h).1 (AddSubgroup.mem_inf.mp h).2`.

Introduce `h`. Conclude with `AddSubgroup.mem_inf.mpr ⟨(le_sup_left : Sb ≤ Sb ⊔ Sc) h, hSbS h⟩`. Establish `key : (Sb ⊔ Sc).toAddSubgroup.relIndex (S ⊔ Sc).toAddSubgroup = Sb.toAddSubgroup.relIndex S.toAddSubgroup`. Establish `hsup : (S ⊔ Sc).toAddSubgroup = S.toAddSubgroup ⊔ (Sb ⊔ Sc).toAddSubgroup`. Rewrite using `[← Submodule.sup_toAddSubgroup, ← sup_assoc, sup_eq_left.mpr hSbS]`.

Rewrite using `[hsup, AddSubgroup.relIndex_sup_right, ← hinf, AddSubgroup.inf_relIndex_right]`. Establish `le1 : (Sb ⊔ Sc).toAddSubgroup ≤ (S ⊔ Sc).toAddSubgroup` using `fun x hx => (sup_le_sup_right hSbS Sc) hx`. Establish `le2 : (S ⊔ Sc).toAddSubgroup ≤ L.toAddSubgroup` using `fun x hx => (sup_le hSL hScL) hx`. Rewrite using `[hA, ← AddSubgroup.relIndex_mul_relIndex _ _ _ le1 le2, key]`.
-/
theorem index_split {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hb : ∀ i, b i ∈ L) (hc : ∀ j, c j ∈ L)
    (hdis : Disjoint (Submodule.span K (Set.range b)) (Submodule.span K (Set.range c))) :
    (Submodule.span (𝓞 K) (Set.range (Fin.append b c))).toAddSubgroup.relIndex L.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex (satSub L b).toAddSubgroup *
      (satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex
        L.toAddSubgroup := by
  set Sb := Submodule.span (𝓞 K) (Set.range b)
  set Sc := Submodule.span (𝓞 K) (Set.range c)
  set S := satSub L b
  have hA : Submodule.span (𝓞 K) (Set.range (Fin.append b c)) = Sb ⊔ Sc := by
    rw [range_fin_append, Submodule.span_union]
  have hSbS : Sb ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨hb i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hScL : Sc ≤ L := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hc j
  have hSL : S ≤ L := inf_le_left
  have hmeet : ∀ x, x ∈ Sb ⊔ Sc → x ∈ S → x ∈ Sb := by
    intro x hx1 hx2
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx1
    have hyK : y ∈ Submodule.span K (Set.range b) :=
      Submodule.span_le_restrictScalars (𝓞 K) K _ hy
    have hzK : z ∈ Submodule.span K (Set.range c) :=
      Submodule.span_le_restrictScalars (𝓞 K) K _ hz
    have hxK : y + z ∈ Submodule.span K (Set.range b) := hx2.2
    have hz' : z ∈ Submodule.span K (Set.range b) := by
      have h := Submodule.sub_mem _ hxK hyK
      simpa using h
    have hz0 : z = 0 := Submodule.disjoint_def.mp hdis z hz' hzK
    simpa [hz0] using hy
  have hinf : (Sb ⊔ Sc).toAddSubgroup ⊓ S.toAddSubgroup = Sb.toAddSubgroup := by
    ext x
    constructor
    · intro h
      exact hmeet x (AddSubgroup.mem_inf.mp h).1 (AddSubgroup.mem_inf.mp h).2
    · intro h
      exact AddSubgroup.mem_inf.mpr ⟨(le_sup_left : Sb ≤ Sb ⊔ Sc) h, hSbS h⟩
  have key : (Sb ⊔ Sc).toAddSubgroup.relIndex (S ⊔ Sc).toAddSubgroup =
      Sb.toAddSubgroup.relIndex S.toAddSubgroup := by
    have hsup : (S ⊔ Sc).toAddSubgroup = S.toAddSubgroup ⊔ (Sb ⊔ Sc).toAddSubgroup := by
      rw [← Submodule.sup_toAddSubgroup, ← sup_assoc, sup_eq_left.mpr hSbS]
    rw [hsup, AddSubgroup.relIndex_sup_right, ← hinf, AddSubgroup.inf_relIndex_right]
  have le1 : (Sb ⊔ Sc).toAddSubgroup ≤ (S ⊔ Sc).toAddSubgroup :=
    fun x hx => (sup_le_sup_right hSbS Sc) hx
  have le2 : (S ⊔ Sc).toAddSubgroup ≤ L.toAddSubgroup := fun x hx => (sup_le hSL hScL) hx
  rw [hA, ← AddSubgroup.relIndex_mul_relIndex _ _ _ le1 le2, key]

end DegAdd

end ReciprocityTheory.MultiplicativeHeights
