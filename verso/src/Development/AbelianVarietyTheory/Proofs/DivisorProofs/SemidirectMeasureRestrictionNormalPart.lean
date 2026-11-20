import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupMeas

open MeasureTheory Pointwise
open GlobalTheory.SupMeas

namespace GlobalTheory

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ N Q hN hQN _ νN hR A`. Use `set ι := Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) with hιdef`. Establish `hmeasN : MeasurableSet (N : Set G)` using `hN.measurableSet`. Establish `hιinj : Function.Injective ι` using `Subgroup.inclusion_injective _`. Establish `hιmeas : Measurable ι`.

Apply `Measurable.subtype_mk` to reduce the goal to its premises. Conclude with `measurable_subtype_coe`. Establish `hι : MeasurableEmbedding ι`. Use `⟨hιinj, hιmeas, ?_⟩` and prove the remaining obligations. Introduce `s hs`.

Establish `h1 : MeasurableSet (((↑) : N → G) '' s)` using `(MeasurableEmbedding.subtype_coe hmeasN).measurableSet_image' hs`. Establish `h2 : ι '' s = ((↑) : ↥(Q ⊔ N) → G) ⁻¹' (((↑) : N → G) '' s)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `⟨y, hy, rfl⟩`. Introduce and unpack `⟨y, hy, hyx⟩`. Conclude with `⟨y, hy, Subtype.ext hyx⟩`. Rewrite using `[h2]`. Conclude with `measurable_subtype_coe h1`.

Use `haveI : Countable (↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N)) := by`. Establish `hsurj : Function.Surjective (fun q : Q => (QuotientGroup.mk (⟨((q : G))⁻¹, (Q ⊔ N).inv_mem (le_sup_left (a` using `Q) (b := N) q.2)⟩ : ↥(Q ⊔ N)) : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N))) := by`. Introduce `k`. Proceed by induction on `k using QuotientGroup.induction_on with`. Consider the case `H h`.

Take `⟨n, hn, q, hq, hnq⟩` from `hQN ((h : G)⁻¹) ((Q ⊔ N).inv_mem h.2)`. Use `⟨⟨q, hq⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[QuotientGroup.eq]`. Simplify using `only [Subgroup.mem_subgroupOf]`. Establish `: ((q : G)) = n⁻¹ * (h : G)⁻¹` using `by rw [← hnq]; group`.

Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, this]`. Simplify `N.inv_mem hn` using `[mul_assoc]`. Conclude with `hsurj.countable`. Use `set k₀ : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N) := QuotientGroup.mk 1 with hk₀`. Establish `hkiff : ∀ k : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N), k = k₀ ↔ ((Quotient.out k : ↥(Q ⊔ N)) : G) ∈ N`.

Introduce `k`. Establish `hk : (QuotientGroup.mk (Quotient.out k) : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N)) = k` using `Quotient.out_eq' k`. Use `conv_lhs => rw [← hk]`. Rewrite using `[hk₀, QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `only [mul_one, Subgroup.coe_inv, inv_mem_iff]`.

Establish `key : ∀ k : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N), (νN.map fun n => ι n * Quotient.out k) (ι '' A) = if k = k₀ then νN A else 0`. Introduce `k`. Establish `hemb : MeasurableEmbedding (fun n => ι n * Quotient.out k)` using `(measurableEmbedding_mulRight (Quotient.out k)).comp hι`. Rewrite using `[hemb.map_apply]`. Distinguish the cases in `hk : k = k₀`.

Rewrite using `[if_pos hk]`. Establish `hmem : ((Quotient.out k : ↥(Q ⊔ N)) : G) ∈ N` using `(hkiff k).1 hk`. Use `set m : N := ⟨_, hmem⟩`. Establish `hpre : (fun n => ι n * Quotient.out k) ⁻¹' (ι '' A) = (· * m) ⁻¹' A`. Use extensionality with `n`.

Simplify using `only [Set.mem_preimage, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, hae⟩`. Establish `: n * m = a`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `congrArg (fun x : ↥(Q ⊔ N) => (x : G)) hae` as an intermediate fact. Simplify `this.symm` using `[ι, m]`. Rewrite using `[this]`. Conclude with `ha`. Introduce `h`.

Use `⟨n * m, h, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[ι, m]`. Rewrite using `[hpre]`. Conclude with `(hR m).measure_preimage_emb (measurableEmbedding_mulRight m) A`.

Rewrite using `[if_neg hk]`. Establish `hpre : (fun n => ι n * Quotient.out k) ⁻¹' (ι '' A) = ∅`. Use extensionality with `n`. Simplify using `only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨a, _, hae⟩`.

Apply `hk` to reduce the goal to its premises. Rewrite using `[hkiff]`. Establish `: ((Quotient.out k : ↥(Q ⊔ N)) : G) = (n : G)⁻¹ * (a : G)`. Use `congrArg (fun x : ↥(Q ⊔ N) => (x : G)) hae` as an intermediate fact. Simplify using `[ι] at this`.

Rewrite using `[this]`. Use `group`. Rewrite using `[this]`. Conclude with `N.mul_mem (N.inv_mem n.2) a.2`. Rewrite using `[hpre, measure_empty]`.

Establish `hsum : supMeas N Q νN (ι '' A) = ∑' k : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N), (νN.map fun n => ι n * Quotient.out k) (ι '' A)` using `Measure.sum_apply_of_countable _ _`. Rewrite using `[hsum, tsum_congr key, tsum_ite_eq]`.
-/
theorem supMeas_image_inclusion : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Q : Subgroup G), IsClosed (N : Set G) → (∀ h ∈ Q ⊔ N, ∃ n ∈ N, ∃ q ∈ Q, n * q = h) → ∀ [Countable Q] (νN : Measure N), (∀ n : N, MeasurePreserving (· * n) νN νN) → ∀ A : Set N, supMeas N Q νN (Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) '' A) = νN A := by
  intro G _ _ _ _ _ _ _ _ N Q hN hQN _ νN hR A
  classical
  set ι := Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) with hιdef
  have hmeasN : MeasurableSet (N : Set G) := hN.measurableSet
  have hιinj : Function.Injective ι := Subgroup.inclusion_injective _
  have hιmeas : Measurable ι := by
    apply Measurable.subtype_mk
    exact measurable_subtype_coe
  have hι : MeasurableEmbedding ι := by
    refine ⟨hιinj, hιmeas, ?_⟩
    intro s hs
    have h1 : MeasurableSet (((↑) : N → G) '' s) := (MeasurableEmbedding.subtype_coe hmeasN).measurableSet_image' hs
    have h2 : ι '' s = ((↑) : ↥(Q ⊔ N) → G) ⁻¹' (((↑) : N → G) '' s) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        exact ⟨y, hy, Subtype.ext hyx⟩
    rw [h2]
    exact measurable_subtype_coe h1
  haveI : Countable (↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N)) := by
    have hsurj : Function.Surjective (fun q : Q =>
        (QuotientGroup.mk (⟨((q : G))⁻¹, (Q ⊔ N).inv_mem (le_sup_left (a := Q) (b := N) q.2)⟩ : ↥(Q ⊔ N)) :
          ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N))) := by
      intro k
      induction k using QuotientGroup.induction_on with
      | H h =>
        obtain ⟨n, hn, q, hq, hnq⟩ := hQN ((h : G)⁻¹) ((Q ⊔ N).inv_mem h.2)
        refine ⟨⟨q, hq⟩, ?_⟩
        rw [QuotientGroup.eq]
        simp only [Subgroup.mem_subgroupOf]
        have : ((q : G)) = n⁻¹ * (h : G)⁻¹ := by rw [← hnq]; group
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, this]
        simpa [mul_assoc] using N.inv_mem hn
    exact hsurj.countable
  set k₀ : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N) := QuotientGroup.mk 1 with hk₀
  have hkiff : ∀ k : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N), k = k₀ ↔ ((Quotient.out k : ↥(Q ⊔ N)) : G) ∈ N := by
    intro k
    have hk : (QuotientGroup.mk (Quotient.out k) : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N)) = k := Quotient.out_eq' k
    conv_lhs => rw [← hk]
    rw [hk₀, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [mul_one, Subgroup.coe_inv, inv_mem_iff]
  have key : ∀ k : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N),
      (νN.map fun n => ι n * Quotient.out k) (ι '' A) = if k = k₀ then νN A else 0 := by
    intro k
    have hemb : MeasurableEmbedding (fun n => ι n * Quotient.out k) :=
      (measurableEmbedding_mulRight (Quotient.out k)).comp hι
    rw [hemb.map_apply]
    by_cases hk : k = k₀
    · rw [if_pos hk]
      have hmem : ((Quotient.out k : ↥(Q ⊔ N)) : G) ∈ N := (hkiff k).1 hk
      set m : N := ⟨_, hmem⟩
      have hpre : (fun n => ι n * Quotient.out k) ⁻¹' (ι '' A) = (· * m) ⁻¹' A := by
        ext n
        simp only [Set.mem_preimage, Set.mem_image]
        constructor
        · rintro ⟨a, ha, hae⟩
          have : n * m = a := by
            apply Subtype.ext
            have := congrArg (fun x : ↥(Q ⊔ N) => (x : G)) hae
            simpa [ι, m] using this.symm
          rw [this]; exact ha
        · intro h
          refine ⟨n * m, h, ?_⟩
          apply Subtype.ext
          simp [ι, m]
      rw [hpre]
      exact (hR m).measure_preimage_emb (measurableEmbedding_mulRight m) A
    · rw [if_neg hk]
      have hpre : (fun n => ι n * Quotient.out k) ⁻¹' (ι '' A) = ∅ := by
        ext n
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
        rintro ⟨a, _, hae⟩
        apply hk
        rw [hkiff]
        have : ((Quotient.out k : ↥(Q ⊔ N)) : G) = (n : G)⁻¹ * (a : G) := by
          have := congrArg (fun x : ↥(Q ⊔ N) => (x : G)) hae
          simp [ι] at this
          rw [this]; group
        rw [this]
        exact N.mul_mem (N.inv_mem n.2) a.2
      rw [hpre, measure_empty]
  have hsum : supMeas N Q νN (ι '' A) = ∑' k : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N), (νN.map fun n => ι n * Quotient.out k) (ι '' A) :=
    Measure.sum_apply_of_countable _ _
  rw [hsum, tsum_congr key, tsum_ite_eq]

end GlobalTheory
