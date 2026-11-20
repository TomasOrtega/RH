import Mathlib

noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

/- English proof (translation)
The claim follows from `IsAddFundamentalDomain.mk' hF.nullMeasurableSet fun v => h v`.
-/
private theorem isAddFundamentalDomain_of_existsUnique {V : Type} [AddCommGroup V]
    [MeasurableSpace V] (μ : Measure V) (L : AddSubgroup V) (F : Set V) (hF : MeasurableSet F)
    (h : ∀ v, ∃! l : L, (l : V) + v ∈ F) : IsAddFundamentalDomain L F μ :=
  IsAddFundamentalDomain.mk' hF.nullMeasurableSet fun v => h v

/- English proof (translation)
Establish `key : ∀ q : L ⧸ Λ.addSubgroupOf L, (-((σ q : L) : V) + m ∈ Λ ↔ q = QuotientAddGroup.mk ⟨m, hm⟩)`. Introduce `q`. Establish `e : q = QuotientAddGroup.mk ⟨m, hm⟩ ↔ (QuotientAddGroup.mk (σ q) : L ⧸ Λ.addSubgroupOf L) = QuotientAddGroup.mk ⟨m, hm⟩`. Rewrite using `[hσ q]`. Rewrite using `[e]`.

Use `first`. Consider the case `rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Consider the case `rw [QuotientAddGroup.eq', AddSubgroup.mem_addSubgroupOf]`. Use `first`. Consider the case `exact Iff.rfl`.

Consider the case `simp`. Conclude with `⟨QuotientAddGroup.mk ⟨m, hm⟩, (key _).2 rfl, fun q hq => (key q).1 hq⟩`.
-/
private theorem existsUnique_neg_section_add_mem {V : Type} [AddCommGroup V]
    (L Λ : AddSubgroup V) (σ : L ⧸ Λ.addSubgroupOf L → L)
    (hσ : ∀ q, (QuotientAddGroup.mk (σ q) : L ⧸ Λ.addSubgroupOf L) = q)
    (m : V) (hm : m ∈ L) : ∃! q : L ⧸ Λ.addSubgroupOf L, -((σ q : L) : V) + m ∈ Λ := by
  have key : ∀ q : L ⧸ Λ.addSubgroupOf L,
      (-((σ q : L) : V) + m ∈ Λ ↔ q = QuotientAddGroup.mk ⟨m, hm⟩) := by
    intro q
    have e : q = QuotientAddGroup.mk ⟨m, hm⟩ ↔
        (QuotientAddGroup.mk (σ q) : L ⧸ Λ.addSubgroupOf L) = QuotientAddGroup.mk ⟨m, hm⟩ := by
      rw [hσ q]
    rw [e]
    first
    | rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    | rw [QuotientAddGroup.eq', AddSubgroup.mem_addSubgroupOf]
    first
    | exact Iff.rfl
    | simp
  exact ⟨QuotientAddGroup.mk ⟨m, hm⟩, (key _).2 rfl, fun q hq => (key q).1 hq⟩

/- English proof (translation)
Take `⟨l, hl, hlu⟩` from `hdL v`. Take `⟨i, hi, hiu⟩` from `hρ (-(l : V)) (L.neg_mem l.2)`. Establish `ha : (l : V) - ρ i ∈ Λ`. Establish `e : (l : V) - ρ i = -(ρ i + -(l : V))` using `by abel`. Rewrite using `[e]`.

Conclude with `Λ.neg_mem hi`. Use `⟨⟨(l : V) - ρ i, ha⟩, ?_, ?_⟩` and prove the remaining obligations. Use `Set.mem_iUnion.2 ⟨i, ?_⟩ show ρ i + (((l : V) - ρ i) + v) ∈ FL` and prove the remaining obligations. Rewrite using `[show ρ i + (((l : V) - ρ i) + v) = (l : V) + v by abel]`. Conclude with `hl`.

Introduce `b hb`. Take `⟨j, hj⟩` from `Set.mem_iUnion.1 hb`. Establish `hj' : ((⟨ρ j + (b : V), L.add_mem (hρL j) (hle b.2)⟩ : L) : V) + v ∈ FL` using `by show ρ j + (b : V) + v ∈ FL`. Rewrite using `[add_assoc]`. Conclude with `hj`.

Establish `hy : ρ j + (b : V) = l` using `congrArg Subtype.val (hlu _ hj')`. Establish `hj2 : ρ j + -(l : V) ∈ Λ`. Establish `e : ρ j + -(l : V) = -(b : V)` using `by rw [← hy]; abel`. Rewrite using `[e]`. Conclude with `Λ.neg_mem b.2`.

Establish `hji : j = i` using `hiu j hj2`. Rewrite `hy` using `[hji]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (b : V) = (l : V) - ρ i`. Rewrite using `[← hy]`.

Normalize the expressions using the abelian group laws.
-/
private theorem existsUnique_mem_iUnion_translate_preimage {V : Type} [AddCommGroup V]
    (L Λ : AddSubgroup V) (hle : Λ ≤ L) (FL : Set V) (hdL : ∀ v, ∃! l : L, (l : V) + v ∈ FL)
    {ι : Type*} (ρ : ι → V) (hρL : ∀ i, ρ i ∈ L) (hρ : ∀ m ∈ L, ∃! i, ρ i + m ∈ Λ) (v : V) :
    ∃! a : Λ, (a : V) + v ∈ ⋃ i, (fun w => ρ i + w) ⁻¹' FL := by
  obtain ⟨l, hl, hlu⟩ := hdL v
  obtain ⟨i, hi, hiu⟩ := hρ (-(l : V)) (L.neg_mem l.2)
  have ha : (l : V) - ρ i ∈ Λ := by
    have e : (l : V) - ρ i = -(ρ i + -(l : V)) := by abel
    rw [e]
    exact Λ.neg_mem hi
  refine ⟨⟨(l : V) - ρ i, ha⟩, ?_, ?_⟩
  · refine Set.mem_iUnion.2 ⟨i, ?_⟩
    show ρ i + (((l : V) - ρ i) + v) ∈ FL
    rw [show ρ i + (((l : V) - ρ i) + v) = (l : V) + v by abel]
    exact hl
  · intro b hb
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hb
    have hj' : ((⟨ρ j + (b : V), L.add_mem (hρL j) (hle b.2)⟩ : L) : V) + v ∈ FL := by
      show ρ j + (b : V) + v ∈ FL
      rw [add_assoc]
      exact hj
    have hy : ρ j + (b : V) = l := congrArg Subtype.val (hlu _ hj')
    have hj2 : ρ j + -(l : V) ∈ Λ := by
      have e : ρ j + -(l : V) = -(b : V) := by rw [← hy]; abel
      rw [e]
      exact Λ.neg_mem b.2
    have hji : j = i := hiu j hj2
    rw [hji] at hy
    apply Subtype.ext
    show (b : V) = (l : V) - ρ i
    rw [← hy]
    abel

/- English proof (translation)
Introduce `i j hij`. Use `Set.disjoint_left.2 fun w hi hj => hij ?_` and prove the remaining obligations. Establish `e : (⟨ρ i, hρL i⟩ : L) = ⟨ρ j, hρL j⟩` using `(hdL w).unique (show ((⟨ρ i, hρL i⟩ : L) : V) + w ∈ FL from hi) (show ((⟨ρ j, hρL j⟩ : L) : V) + w ∈ FL from hj)`. Establish `e' : ρ i = ρ j` using `congrArg Subtype.val e`. Take `⟨q, -, hq⟩` from `hρ (-ρ i) (L.neg_mem (hρL i))`.

Establish `h1 : i = q` using `hq i (by simp)`. Establish `h2 : j = q` using `hq j (by show ρ j + -ρ i ∈ Λ; rw [← e']; simp)`. Rewrite using `[h1, h2]`.
-/
private theorem pairwise_disjoint_translate_preimage {V : Type} [AddCommGroup V]
    (L Λ : AddSubgroup V) (FL : Set V) (hdL : ∀ v, ∃! l : L, (l : V) + v ∈ FL)
    {ι : Type*} (ρ : ι → V) (hρL : ∀ i, ρ i ∈ L) (hρ : ∀ m ∈ L, ∃! i, ρ i + m ∈ Λ) :
    Pairwise (Function.onFun Disjoint fun i => (fun w => ρ i + w) ⁻¹' FL) := by
  intro i j hij
  refine Set.disjoint_left.2 fun w hi hj => hij ?_
  have e : (⟨ρ i, hρL i⟩ : L) = ⟨ρ j, hρL j⟩ :=
    (hdL w).unique (show ((⟨ρ i, hρL i⟩ : L) : V) + w ∈ FL from hi)
      (show ((⟨ρ j, hρL j⟩ : L) : V) + w ∈ FL from hj)
  have e' : ρ i = ρ j := congrArg Subtype.val e
  obtain ⟨q, -, hq⟩ := hρ (-ρ i) (L.neg_mem (hρL i))
  have h1 : i = q := hq i (by simp)
  have h2 : j = q := hq j (by show ρ j + -ρ i ∈ Λ; rw [← e']; simp)
  rw [h1, h2]

/- English proof (translation)
Establish `hcard : Nat.card (L ⧸ Λ.addSubgroupOf L) = k` using `hk`. Use `haveI : Finite (L ⧸ Λ.addSubgroupOf L) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hk0)`. Use `haveI : Fintype (L ⧸ Λ.addSubgroupOf L) := Fintype.ofFinite _`. Use `haveI : Countable Λ := Function.Injective.countable (AddSubgroup.inclusion_injective hle)`. Use `haveI : MeasurableVAdd Λ V := by first`.

Consider the case `infer_instance`. Consider the case `exact ⟨fun c => measurable_const_add (c : V), fun v => (measurable_add_const v).comp measurable_subtype_coe⟩`. Use `haveI : VAddInvariantMeasure Λ V μ := by first`. Consider the case `infer_instance`. Consider the case `exact ⟨fun c s _ => measure_preimage_add μ (c : V) s⟩`.

Establish `hsurj : Function.Surjective (QuotientAddGroup.mk : L → L ⧸ Λ.addSubgroupOf L)` using `QuotientAddGroup.mk_surjective`. Take `⟨ρ, hρL, hρ⟩ : ∃ ρ : L ⧸ Λ.addSubgroupOf L → V, (∀ q, ρ q ∈ L) ∧ ∀ m ∈ L, ∃! q, ρ q + m ∈ Λ` from `⟨fun q => -((Function.surjInv hsurj q : L) : V), fun q => L.neg_mem (Function.surjInv hsurj q).2, fun m hm => existsUnique_neg_section_add_mem L Λ (Function.surjInv hsurj) (Function.surjInv_eq hsurj) m hm⟩`. Establish `hmeas : ∀ q, MeasurableSet ((fun w => ρ q + w) ⁻¹' FL)` using `fun q => measurable_const_add (ρ q) hFL`. Establish `hU : IsAddFundamentalDomain Λ (⋃ q, (fun w => ρ q + w) ⁻¹' FL) μ` using `isAddFundamentalDomain_of_existsUnique μ Λ _ (MeasurableSet.iUnion hmeas) (existsUnique_mem_iUnion_translate_preimage L Λ hle FL hdL ρ hρL hρ)`. Establish `hΛ : IsAddFundamentalDomain Λ FΛ μ` using `isAddFundamentalDomain_of_existsUnique μ Λ FΛ hFΛ hdΛ`.

Rewrite using `[hΛ.measure_eq hU, measure_iUnion (pairwise_disjoint_translate_preimage L Λ FL hdL ρ hρL hρ) hmeas]`. Simplify using `only [measure_preimage_add]`. Rewrite using `[tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hcard]`.
-/
theorem fund_index {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V)
    [μ.IsAddLeftInvariant] (L Λ : AddSubgroup V) [Countable L] (hle : Λ ≤ L) (k : ℕ)
    (hk : Λ.relIndex L = k) (hk0 : k ≠ 0) (FL FΛ : Set V) (hFL : MeasurableSet FL) (hFΛ : MeasurableSet FΛ)
    (hdL : ∀ v, ∃! l : L, (l : V) + v ∈ FL) (hdΛ : ∀ v, ∃! a : Λ, (a : V) + v ∈ FΛ) :
    μ FΛ = k * μ FL := by
  classical
  have hcard : Nat.card (L ⧸ Λ.addSubgroupOf L) = k := hk
  haveI : Finite (L ⧸ Λ.addSubgroupOf L) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hk0)
  haveI : Fintype (L ⧸ Λ.addSubgroupOf L) := Fintype.ofFinite _
  haveI : Countable Λ := Function.Injective.countable (AddSubgroup.inclusion_injective hle)
  haveI : MeasurableVAdd Λ V := by
    first
    | infer_instance
    | exact ⟨fun c => measurable_const_add (c : V), fun v => (measurable_add_const v).comp measurable_subtype_coe⟩
  haveI : VAddInvariantMeasure Λ V μ := by
    first
    | infer_instance
    | exact ⟨fun c s _ => measure_preimage_add μ (c : V) s⟩
  have hsurj : Function.Surjective (QuotientAddGroup.mk : L → L ⧸ Λ.addSubgroupOf L) :=
    QuotientAddGroup.mk_surjective
  obtain ⟨ρ, hρL, hρ⟩ : ∃ ρ : L ⧸ Λ.addSubgroupOf L → V,
      (∀ q, ρ q ∈ L) ∧ ∀ m ∈ L, ∃! q, ρ q + m ∈ Λ :=
    ⟨fun q => -((Function.surjInv hsurj q : L) : V), fun q => L.neg_mem (Function.surjInv hsurj q).2,
      fun m hm => existsUnique_neg_section_add_mem L Λ (Function.surjInv hsurj)
        (Function.surjInv_eq hsurj) m hm⟩
  have hmeas : ∀ q, MeasurableSet ((fun w => ρ q + w) ⁻¹' FL) := fun q =>
    measurable_const_add (ρ q) hFL
  have hU : IsAddFundamentalDomain Λ (⋃ q, (fun w => ρ q + w) ⁻¹' FL) μ :=
    isAddFundamentalDomain_of_existsUnique μ Λ _ (MeasurableSet.iUnion hmeas)
      (existsUnique_mem_iUnion_translate_preimage L Λ hle FL hdL ρ hρL hρ)
  have hΛ : IsAddFundamentalDomain Λ FΛ μ := isAddFundamentalDomain_of_existsUnique μ Λ FΛ hFΛ hdΛ
  rw [hΛ.measure_eq hU, measure_iUnion (pairwise_disjoint_translate_preimage L Λ FL hdL ρ hρL hρ) hmeas]
  simp only [measure_preimage_add]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    hcard]

end Formalism.L2.SG.NGCut.SplitEmbedding
