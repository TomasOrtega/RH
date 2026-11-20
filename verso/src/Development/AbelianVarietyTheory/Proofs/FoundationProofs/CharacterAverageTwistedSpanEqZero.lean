import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section AvgAux

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `hne : ∀ a : K, θ a ≠ 0`. Introduce `a ha`. Use `hmul a a⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, ha, zero_mul]`. Simplify using `[hone] at this`.

Establish `key : ∀ q : K ⧸ M, (θ (s q))⁻¹ • π (s q) (π h w) = θ h • ((θ (s (q * QuotientGroup.mk h)))⁻¹ • π (s (q * QuotientGroup.mk h)) w)`. Introduce `q`. Use `set q' := q * (QuotientGroup.mk h : K ⧸ M)`. Use `set m : K := (s q')⁻¹ * (s q * h) with hm_def`. Establish `hmM : m ∈ M`.

Rewrite using `[← QuotientGroup.eq_one_iff]`. Simplify using `only [hm_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hs, q']`. Use `group`. Establish `hsplit : s q * h = s q' * m` using `by simp [hm_def]`. Establish `h1 : π (s q) (π h w) = π (s q') w`.

Establish `: π ((s q * h : K) : G) w = π ((s q' * m : K) : G) w` using `by rw [hsplit]`. Simplify `this` using `[map_mul, hw m hmM]`. Establish `h2 : θ (s q) * θ h = θ (s q')`. Rewrite using `[← hmul, hsplit, hmul, hθM m hmM, mul_one]`. Rewrite using `[h1, smul_smul]`.

Use `congr 1`. Rewrite using `[← h2]`. Clear denominators, using `[hne (s q), hne h]` for the nonvanishing conditions. Rewrite using `[Finset.sum_congr rfl fun q _ => key q, ← Finset.smul_sum]`. Use `congr 1`.

Conclude with `Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk h : K ⧸ M)) (fun q => (θ (s q))⁻¹ • π (s q) w)`.
-/
theorem avg_shift {K : Subgroup G} (M : Subgroup K) [M.Normal] [Fintype (K ⧸ M)]
    (π : Representation ℂ G V) (θ : G → ℂ) (s : K ⧸ M → K)
    (hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ M) = q) (hone : θ 1 = 1)
    (hmul : ∀ a b : K, θ ((a * b : K) : G) = θ a * θ b)
    (w : V) (hw : ∀ m ∈ M, π (m : G) w = w) (hθM : ∀ m ∈ M, θ (m : G) = 1) (h : K) :
    ∑ q, (θ (s q))⁻¹ • π (s q) (π h w) = θ h • ∑ q, (θ (s q))⁻¹ • π (s q) w := by
  have hne : ∀ a : K, θ a ≠ 0 := by
    intro a ha
    have := hmul a a⁻¹
    rw [mul_inv_cancel, ha, zero_mul] at this
    simp [hone] at this
  have key : ∀ q : K ⧸ M, (θ (s q))⁻¹ • π (s q) (π h w) =
      θ h • ((θ (s (q * QuotientGroup.mk h)))⁻¹ • π (s (q * QuotientGroup.mk h)) w) := by
    intro q
    set q' := q * (QuotientGroup.mk h : K ⧸ M)
    set m : K := (s q')⁻¹ * (s q * h) with hm_def
    have hmM : m ∈ M := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [hm_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hs, q']
      group
    have hsplit : s q * h = s q' * m := by simp [hm_def]
    have h1 : π (s q) (π h w) = π (s q') w := by
      have : π ((s q * h : K) : G) w = π ((s q' * m : K) : G) w := by rw [hsplit]
      simpa [map_mul, hw m hmM] using this
    have h2 : θ (s q) * θ h = θ (s q') := by
      rw [← hmul, hsplit, hmul, hθM m hmM, mul_one]
    rw [h1, smul_smul]
    congr 1
    rw [← h2]
    field_simp [hne (s q), hne h]
  rw [Finset.sum_congr rfl fun q _ => key q, ← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk h : K ⧸ M))
    (fun q => (θ (s q))⁻¹ • π (s q) w)

end AvgAux

/- English proof (translation)
Introduce `G V _ _ _ _ _ π hsm H θ hD u hu`. Set `K : Subgroup G` to `{ carrier := H mul_mem' := fun {a b} ha hb => hD.mul a ha b hb one_mem' := hD.one inv_mem' := fun {a} ha => hD.inv a ha }`. Take `⟨n, c, g, rfl⟩` from `Submodule.mem_span_set'.mp hu`. Use `choose h hh w hw using fun i => (g i).2`. Establish `hmul : ∀ a b : K, θ ((a * b : K) : G) = θ a * θ b` using `fun a b => hD.val_mul a a.2 b b.2`.

Set `N : Subgroup K` to `{ carrier := {j | θ j = 1 ∧ ∀ i, π j (w i) = w i} mul_mem' := by`. Introduce `a b ha hb`. Use `⟨by rw [hmul, ha.1, hb.1, one_mul], fun i => ?_⟩` and prove the remaining obligations. Simplify using `[map_mul, ha.2 i, hb.2 i]`. Use the proof step `one_mem' := ⟨hD.val_one, fun i => by simp⟩`.

Use the proof step `inv_mem' := by`. Introduce `a ha`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Use `hmul a a⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, ha.1, one_mul]`.

Simplify `this.symm` using `[hD.val_one]`. Use `congrArg (π ((a⁻¹ : K) : G)) (ha.2 i)` as an intermediate fact. Simplify `this.symm }` using `[← map_mul]`. Establish `hNopen : IsOpen (N : Set K)`. Apply `Subgroup.isOpen_of_mem_nhds` to reduce the goal to its premises.

Take `⟨U, hU, hUθ⟩` from `hD.near`. Establish `hS : (U ∩ ⋂ i, {g : G | π g (w i) = w i}) ∈ nhds (1 : G)` using `Filter.inter_mem hU (Filter.iInter_mem.mpr fun i => (hsm (w i)).mem_nhds (by simp))`. Establish `hS'` using `continuous_subtype_val.continuousAt.preimage_mem_nhds (x := (1 : K)) hS`. Use `Filter.mem_of_superset hS' ?_` and prove the remaining obligations. Introduce `x hx`.

Simplify using `only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hx`. Conclude with `⟨hUθ x hx.1 x.2, hx.2⟩`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp (show IsCompact (K : Set G) from hD.compact)`. Use `haveI : Finite (K ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNopen`. Use `haveI : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`.

Set `M : Subgroup K` to `N.normalCore`. Use `haveI : Finite (K ⧸ M) := Subgroup.finite_quotient_of_finiteIndex`. Use `letI : Fintype (K ⧸ M) := Fintype.ofFinite _`. Set `s : K ⧸ M → K` to `fun q => if q = 1 then 1 else q.out`. Establish `hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ M) = q`.

Introduce `q`. Distinguish the cases in `hq : q = 1`. Simplify using `[s, hq]`. Simplify using `[s, hq]`. Establish `hMN : ∀ m ∈ M, m ∈ N` using `fun m hm => Subgroup.normalCore_le N hm`.

Establish `hinj : Function.Injective (fun q => ((s q : K) : G))`. Introduce `a b hab`. Rewrite using `[← hs a, ← hs b, Subtype.ext hab]`. Use `⟨Finset.univ.image (fun q => ((s q : K) : G)), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp [s]⟩`.

Introduce `j hj`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.mp hj`. Conclude with `(s q).2`. Rewrite using `[Finset.sum_image fun a _ b _ hab => hinj hab]`. Establish `hgen : ∀ i, ∑ q, (θ (s q))⁻¹ • π (s q) ((g i : V)) = 0`.

Introduce `i`. Rewrite using `[hw i]`. Simplify using `only [map_sub, map_smul, smul_sub, Finset.sum_sub_distrib]`. Use `avg_shift M π θ s hs hD.val_one hmul (w i) (fun m hm => (hMN m hm).2 i) (fun m hm => (hMN m hm).1) ⟨h i, hh i⟩` as an intermediate fact. Rewrite using `[this, Finset.smul_sum, sub_eq_zero]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`. Simplify using `only [map_sum, map_smul, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Establish `hc : ∀ q, (θ (s q : G))⁻¹ • c i • π (s q : G) (g i : V) = c i • ((θ (s q : G))⁻¹ • π (s q : G) (g i : V))` using `fun q => smul_comm _ _ _`. Simplify using `only [hc, ← Finset.smul_sum, hgen i, smul_zero]`.
-/
theorem aug_avg_zero : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ →
    ∀ u ∈ aug π H θ, ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧
      ∑ j ∈ R, (θ j)⁻¹ • π j u = 0 := by
  intro G V _ _ _ _ _ π hsm H θ hD u hu
  let K : Subgroup G :=
    { carrier := H
      mul_mem' := fun {a b} ha hb => hD.mul a ha b hb
      one_mem' := hD.one
      inv_mem' := fun {a} ha => hD.inv a ha }
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.mp hu
  choose h hh w hw using fun i => (g i).2
  have hmul : ∀ a b : K, θ ((a * b : K) : G) = θ a * θ b := fun a b => hD.val_mul a a.2 b b.2
  let N : Subgroup K :=
    { carrier := {j | θ j = 1 ∧ ∀ i, π j (w i) = w i}
      mul_mem' := by
        intro a b ha hb
        refine ⟨by rw [hmul, ha.1, hb.1, one_mul], fun i => ?_⟩
        simp [map_mul, ha.2 i, hb.2 i]
      one_mem' := ⟨hD.val_one, fun i => by simp⟩
      inv_mem' := by
        intro a ha
        refine ⟨?_, fun i => ?_⟩
        · have := hmul a a⁻¹
          rw [mul_inv_cancel, ha.1, one_mul] at this
          simpa [hD.val_one] using this.symm
        · have := congrArg (π ((a⁻¹ : K) : G)) (ha.2 i)
          simpa [← map_mul] using this.symm }
  have hNopen : IsOpen (N : Set K) := by
    apply Subgroup.isOpen_of_mem_nhds
    obtain ⟨U, hU, hUθ⟩ := hD.near
    have hS : (U ∩ ⋂ i, {g : G | π g (w i) = w i}) ∈ nhds (1 : G) :=
      Filter.inter_mem hU (Filter.iInter_mem.mpr fun i => (hsm (w i)).mem_nhds (by simp))
    have hS' := continuous_subtype_val.continuousAt.preimage_mem_nhds (x := (1 : K)) hS
    refine Filter.mem_of_superset hS' ?_
    intro x hx
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hx
    exact ⟨hUθ x hx.1 x.2, hx.2⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (show IsCompact (K : Set G) from hD.compact)
  haveI : Finite (K ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNopen
  haveI : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let M : Subgroup K := N.normalCore
  haveI : Finite (K ⧸ M) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (K ⧸ M) := Fintype.ofFinite _
  classical
  let s : K ⧸ M → K := fun q => if q = 1 then 1 else q.out
  have hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ M) = q := by
    intro q
    by_cases hq : q = 1
    · simp [s, hq]
    · simp [s, hq]
  have hMN : ∀ m ∈ M, m ∈ N := fun m hm => Subgroup.normalCore_le N hm
  have hinj : Function.Injective (fun q => ((s q : K) : G)) := by
    intro a b hab
    rw [← hs a, ← hs b, Subtype.ext hab]
  refine ⟨Finset.univ.image (fun q => ((s q : K) : G)), ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp [s]⟩
  · intro j hj
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hj
    exact (s q).2
  · rw [Finset.sum_image fun a _ b _ hab => hinj hab]
    have hgen : ∀ i, ∑ q, (θ (s q))⁻¹ • π (s q) ((g i : V)) = 0 := by
      intro i
      rw [hw i]
      simp only [map_sub, map_smul, smul_sub, Finset.sum_sub_distrib]
      have := avg_shift M π θ s hs hD.val_one hmul (w i) (fun m hm => (hMN m hm).2 i)
        (fun m hm => (hMN m hm).1) ⟨h i, hh i⟩
      rw [this, Finset.smul_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_comm]
    simp only [map_sum, map_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hc : ∀ q, (θ (s q : G))⁻¹ • c i • π (s q : G) (g i : V) =
        c i • ((θ (s q : G))⁻¹ • π (s q : G) (g i : V)) := fun q => smul_comm _ _ _
    simp only [hc, ← Finset.smul_sum, hgen i, smul_zero]

end GlobalTheory.PsType
