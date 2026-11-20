import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupMeas

open MeasureTheory Pointwise
open GlobalTheory.SupMeas

namespace GlobalTheory.FdTransfer

/- English proof (translation)
Use `set ι := Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) with hι`. Establish `hιinj : Function.Injective ι` using `Subgroup.inclusion_injective _`. Use `haveI : Countable ↥(R.subgroupOf (Q ⊔ N)) := by`. Use `Function.Injective.countable (f := fun g : ↥(R.subgroupOf (Q ⊔ N)) => (⟨((g : ↥(Q ⊔ N)) : G), Subgroup.mem_subgroupOf.mp g.2⟩ : R)) ?_` and prove the remaining obligations. Introduce `a b hab`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `congrArg Subtype.val hab`. Conclude with `h`. Establish `himg : ∀ T : Set N, MeasurableSet T → MeasurableSet (ι '' T)`.

Introduce `T hT`. Establish `h1 : MeasurableSet (((↑) : N → G) '' T)` using `(MeasurableEmbedding.subtype_coe hN.measurableSet).measurableSet_image' hT`. Establish `h2 : ι '' T = ((↑) : ↥(Q ⊔ N) → G) ⁻¹' (((↑) : N → G) '' T)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨n, hn, rfl⟩`. Conclude with `⟨n, hn, rfl⟩`. Introduce and unpack `⟨n, hn, hnx⟩`. Conclude with `⟨n, hn, Subtype.ext hnx⟩`. Rewrite using `[h2]`.

Conclude with `measurable_subtype_coe h1`. Establish `hqmp : ∀ g : ↥(R.subgroupOf (Q ⊔ N)), Measure.QuasiMeasurePreserving ((g • ·) : ↥(Q ⊔ N) → ↥(Q ⊔ N)) ν ν` using `fun g => (hinv (g : ↥(Q ⊔ N))).quasiMeasurePreserving`. Use `IsFundamentalDomain.mk'' ?_ ?_ ?_ hqmp` and prove the remaining obligations. Take `⟨T, hTE, hT, hTae⟩` from `hE.nullMeasurableSet.exists_measurable_subset_ae_eq`. Establish `hdiff : νN (E \ T) = 0` using `(ae_eq_set.mp hTae).2`.

Use `(himg T hT).nullMeasurableSet.congr ?_` and prove the remaining obligations. Rewrite using `[ae_eq_set]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Set.diff_eq_empty.mpr (Set.image_mono hTE)]`. Simplify using the standard rewrite rules.

Rewrite using `[← Set.image_diff hιinj, hmass]`. Conclude with `hdiff`. Use `set B : Set N := {n | ¬ ∃ l : ↥(R.subgroupOf N), l • n ∈ E} with hB`. Establish `hB0 : νN B = 0`. Use `hE.ae_covers` as an intermediate fact.

Rewrite `this` using `[ae_iff]`. Conclude with `this`. Establish `hιB : ∀ᵐ y ∂ν, y ∉ ι '' B`. Rewrite using `[ae_iff]`. Simplify using `only [not_not, Set.setOf_mem_eq]`.

Rewrite using `[hmass]`. Conclude with `hB0`. Establish `hall : ∀ᵐ x ∂ν, ∀ r : ↥(R.subgroupOf (Q ⊔ N)), (r • x) ∉ ι '' B`. Rewrite using `[ae_all_iff]`. Introduce `r`.

Conclude with `(hqmp r).ae hιB`. Use `filter_upwards [hall] with x hx`. Take `⟨r, hrR, hrN⟩` from `hcov x x.2`. Establish `hrQN : r ∈ Q ⊔ N`. Establish `: r = (r * x) * (x : G)⁻¹` using `by group`.

Rewrite using `[this]`. Conclude with `(Q ⊔ N).mul_mem (le_sup_right (a := Q) hrN) ((Q ⊔ N).inv_mem x.2)`. Set `rr : ↥(R.subgroupOf (Q ⊔ N))` to `⟨⟨r, hrQN⟩, Subgroup.mem_subgroupOf.mpr hrR⟩`. Set `n : N` to `⟨r * x, hrN⟩`. Establish `hrx : rr • x = ι n` using `Subtype.ext rfl`.

Establish `hn : n ∉ B` using `fun hnB => hx rr ⟨n, hnB, hrx.symm⟩`. Simplify using `only [hB, Set.mem_setOf_eq, not_not] at hn`. Take `⟨l, hl⟩` from `hn`. Set `l' : ↥(R.subgroupOf (Q ⊔ N))` to `⟨ι (l : N), Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp l.2)⟩`. Use `⟨l' * rr, l • n, hl, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((l : N) : G) * (r * x) = ((l : N) : G) * r * x`. Rewrite using `[mul_assoc]`. Introduce `g hg`. Use `show ν (g • (ι '' E) ∩ ι '' E) = 0`.

Distinguish the cases in `hgN : ((g : ↥(Q ⊔ N)) : G) ∈ N`. Set `l : ↥(R.subgroupOf N)` to `⟨⟨_, hgN⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp g.2)⟩`. Establish `hl : l ≠ 1`. Introduce `h`. Apply `hg` to reduce the goal to its premises.

Use `congrArg (fun z : ↥(R.subgroupOf N) => ((z : N) : G)) h` as an intermediate fact. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `this`. Establish `hlE : νN (l • E ∩ E) = 0`.

Use `hE.aedisjoint hl` as an intermediate fact. Simplify `this` using `[Function.onFun, AEDisjoint]`. Use `measure_mono_null ?_ (by rw [hmass]; exact hlE)` and prove the remaining obligations. Introduce `y hy`. Take `⟨hy1, n', hn'E, hy2⟩` from `hy`.

Rewrite `hy1` using `[Set.mem_smul_set]`. Take `⟨x, ⟨n, hnE, rfl⟩, hxy⟩` from `hy1`. Establish `key : ι (l • n) = g • ι n` using `Subtype.ext rfl`. Establish `hln : l • n = n'` using `hιinj (key.trans (hxy.trans hy2.symm))`. Use `⟨l • n, ⟨Set.smul_mem_smul_set hnE, hln ▸ hn'E⟩, key.trans hxy⟩` and prove the remaining obligations.

Use `measure_mono_null (t := ∅) ?_ measure_empty` and prove the remaining obligations. Introduce and unpack `y ⟨hy1, n', hn'E, hy2⟩`. Rewrite `hy1` using `[Set.mem_smul_set]`. Take `⟨x, ⟨n, hnE, rfl⟩, hxy⟩` from `hy1`. Apply `hgN` to reduce the goal to its premises.

Establish `h1 : ((g : ↥(Q ⊔ N)) : G) * n = n'` using `(congrArg (fun z : ↥(Q ⊔ N) => (z : G)) (hxy.trans hy2.symm))`. Establish `h2 : ((g : ↥(Q ⊔ N)) : G) = n' * (n : G)⁻¹` using `by rw [← h1]; group`. Rewrite using `[h2]`. Conclude with `N.mul_mem n'.2 (N.inv_mem n.2)`.
-/
theorem isFundamentalDomain_inclusion_image
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (N Q R : Subgroup G) [Countable R] (hN : IsClosed (N : Set G))
    (hcov : ∀ h ∈ Q ⊔ N, ∃ r ∈ R, r * h ∈ N) (νN : Measure N) (ν : Measure ↥(Q ⊔ N))
    (hmass : ∀ A : Set N, ν (Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) '' A) = νN A)
    (hinv : ∀ h : ↥(Q ⊔ N), MeasurePreserving (h * ·) ν ν)
    (E : Set N) (hE : IsFundamentalDomain (R.subgroupOf N) E νN) :
    IsFundamentalDomain (R.subgroupOf (Q ⊔ N))
      (Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) '' E) ν := by
  set ι := Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) with hι
  have hιinj : Function.Injective ι := Subgroup.inclusion_injective _
  haveI : Countable ↥(R.subgroupOf (Q ⊔ N)) := by
    refine Function.Injective.countable (f := fun g : ↥(R.subgroupOf (Q ⊔ N)) =>
      (⟨((g : ↥(Q ⊔ N)) : G), Subgroup.mem_subgroupOf.mp g.2⟩ : R)) ?_
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    have h := congrArg Subtype.val hab
    exact h
  have himg : ∀ T : Set N, MeasurableSet T → MeasurableSet (ι '' T) := by
    intro T hT
    have h1 : MeasurableSet (((↑) : N → G) '' T) :=
      (MeasurableEmbedding.subtype_coe hN.measurableSet).measurableSet_image' hT
    have h2 : ι '' T = ((↑) : ↥(Q ⊔ N) → G) ⁻¹' (((↑) : N → G) '' T) := by
      ext x
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, rfl⟩
      · rintro ⟨n, hn, hnx⟩
        exact ⟨n, hn, Subtype.ext hnx⟩
    rw [h2]
    exact measurable_subtype_coe h1
  have hqmp : ∀ g : ↥(R.subgroupOf (Q ⊔ N)),
      Measure.QuasiMeasurePreserving ((g • ·) : ↥(Q ⊔ N) → ↥(Q ⊔ N)) ν ν :=
    fun g => (hinv (g : ↥(Q ⊔ N))).quasiMeasurePreserving
  refine IsFundamentalDomain.mk'' ?_ ?_ ?_ hqmp
  ·
    obtain ⟨T, hTE, hT, hTae⟩ := hE.nullMeasurableSet.exists_measurable_subset_ae_eq
    have hdiff : νN (E \ T) = 0 := (ae_eq_set.mp hTae).2
    refine (himg T hT).nullMeasurableSet.congr ?_
    rw [ae_eq_set]
    constructor
    · rw [Set.diff_eq_empty.mpr (Set.image_mono hTE)]; simp
    · rw [← Set.image_diff hιinj, hmass]; exact hdiff
  ·
    set B : Set N := {n | ¬ ∃ l : ↥(R.subgroupOf N), l • n ∈ E} with hB
    have hB0 : νN B = 0 := by
      have := hE.ae_covers
      rw [ae_iff] at this
      exact this
    have hιB : ∀ᵐ y ∂ν, y ∉ ι '' B := by
      rw [ae_iff]; simp only [not_not, Set.setOf_mem_eq]; rw [hmass]; exact hB0
    have hall : ∀ᵐ x ∂ν, ∀ r : ↥(R.subgroupOf (Q ⊔ N)), (r • x) ∉ ι '' B := by
      rw [ae_all_iff]
      intro r
      exact (hqmp r).ae hιB
    filter_upwards [hall] with x hx
    obtain ⟨r, hrR, hrN⟩ := hcov x x.2
    have hrQN : r ∈ Q ⊔ N := by
      have : r = (r * x) * (x : G)⁻¹ := by group
      rw [this]
      exact (Q ⊔ N).mul_mem (le_sup_right (a := Q) hrN) ((Q ⊔ N).inv_mem x.2)
    let rr : ↥(R.subgroupOf (Q ⊔ N)) := ⟨⟨r, hrQN⟩, Subgroup.mem_subgroupOf.mpr hrR⟩
    let n : N := ⟨r * x, hrN⟩
    have hrx : rr • x = ι n := Subtype.ext rfl
    have hn : n ∉ B := fun hnB => hx rr ⟨n, hnB, hrx.symm⟩
    simp only [hB, Set.mem_setOf_eq, not_not] at hn
    obtain ⟨l, hl⟩ := hn
    let l' : ↥(R.subgroupOf (Q ⊔ N)) := ⟨ι (l : N), Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_subgroupOf.mp l.2)⟩
    refine ⟨l' * rr, l • n, hl, ?_⟩
    apply Subtype.ext
    show ((l : N) : G) * (r * x) = ((l : N) : G) * r * x
    rw [mul_assoc]
  ·
    intro g hg
    show ν (g • (ι '' E) ∩ ι '' E) = 0
    by_cases hgN : ((g : ↥(Q ⊔ N)) : G) ∈ N
    · let l : ↥(R.subgroupOf N) := ⟨⟨_, hgN⟩, Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_subgroupOf.mp g.2)⟩
      have hl : l ≠ 1 := by
        intro h
        apply hg
        have := congrArg (fun z : ↥(R.subgroupOf N) => ((z : N) : G)) h
        apply Subtype.ext; apply Subtype.ext
        exact this
      have hlE : νN (l • E ∩ E) = 0 := by
        have := hE.aedisjoint hl
        simpa [Function.onFun, AEDisjoint] using this
      refine measure_mono_null ?_ (by rw [hmass]; exact hlE)
      intro y hy
      obtain ⟨hy1, n', hn'E, hy2⟩ := hy
      rw [Set.mem_smul_set] at hy1
      obtain ⟨x, ⟨n, hnE, rfl⟩, hxy⟩ := hy1
      have key : ι (l • n) = g • ι n := Subtype.ext rfl
      have hln : l • n = n' := hιinj (key.trans (hxy.trans hy2.symm))
      refine ⟨l • n, ⟨Set.smul_mem_smul_set hnE, hln ▸ hn'E⟩, key.trans hxy⟩
    · refine measure_mono_null (t := ∅) ?_ measure_empty
      rintro y ⟨hy1, n', hn'E, hy2⟩
      rw [Set.mem_smul_set] at hy1
      obtain ⟨x, ⟨n, hnE, rfl⟩, hxy⟩ := hy1
      apply hgN
      have h1 : ((g : ↥(Q ⊔ N)) : G) * n = n' :=
        (congrArg (fun z : ↥(Q ⊔ N) => (z : G)) (hxy.trans hy2.symm))
      have h2 : ((g : ↥(Q ⊔ N)) : G) = n' * (n : G)⁻¹ := by rw [← h1]; group
      rw [h2]
      exact N.mul_mem n'.2 (N.inv_mem n.2)

end GlobalTheory.FdTransfer
