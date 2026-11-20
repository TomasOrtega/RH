import Mathlib

open Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.HaarIndex

/- English proof (translation)
Introduce `G _ _ _ μ _ H K hHK hH hn`. Use `set H' := H.addSubgroupOf K`. Establish `hidx : H.relIndex K = H'.index` using `rfl`. Establish `: H'.FiniteIndex` using `⟨by rw [← hidx]; exact hn⟩`. Establish `: Finite (K ⧸ H')` using `inferInstance`.

Use `letI := Fintype.ofFinite (K ⧸ H')`. Set `o : K ⧸ H' → G` to `fun q => ((Quotient.out q : K) : G)`. Set `S : K ⧸ H' → Set G` to `fun q => (fun x => -o q + x) ⁻¹' (H : Set G)`. Establish `hS : ∀ q, MeasurableSet (S q)` using `fun q => (measurable_const_add (-o q)) hH`. Establish `hcover : (K : Set G) = ⋃ q, S q`.

Use extensionality with `x`. Simplify using `only [Set.mem_iUnion, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨((⟨x, hx⟩ : K) : K ⧸ H'), ?_⟩` and prove the remaining obligations.

Establish `h1` using `QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' ((⟨x, hx⟩ : K) : K ⧸ H'))`. Rewrite `h1` using `[AddSubgroup.mem_addSubgroupOf]`. Simplify `h1` using `[S, o]`. Introduce and unpack `⟨q, hq⟩`. Establish `hq' : -o q + x ∈ H` using `hq`.

Establish `hoK : o q ∈ K` using `(Quotient.out q).2`. Establish `hx : x = o q + (-o q + x)` using `(add_neg_cancel_left (o q) x).symm`. Rewrite using `[hx]`. Conclude with `K.add_mem hoK (hHK hq')`. Establish `hdisj : Pairwise (Function.onFun Disjoint S)`.

Introduce `q r hqr`. Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `x hxq hxr`. Apply `hqr` to reduce the goal to its premises. Establish `hq' : -o q + x ∈ H` using `hxq`.

Establish `hr' : -o r + x ∈ H` using `hxr`. Establish `h2 : -o q + o r ∈ H`. Use `H.add_mem hq' (H.neg_mem hr')` as an intermediate fact. Simplify `this` using `[neg_add_rev, add_assoc]`. Rewrite using `[← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' r]`.

Apply `QuotientAddGroup.eq.mpr` to reduce the goal to its premises. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Simplify `h2` using `[o]`. Establish `hμ : ∀ q, μ (S q) = μ (H : Set G)` using `fun q => MeasureTheory.measure_preimage_add μ (-o q) _`. Rewrite using `[hcover, MeasureTheory.measure_iUnion hdisj hS, tsum_fintype]`.

Simplify using `only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[hidx, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]`.
-/
theorem measure_eq_relIndex_mul : ∀ (G : Type) [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant] (H K : AddSubgroup G), H ≤ K →
    MeasurableSet (H : Set G) → H.relIndex K ≠ 0 →
    μ (K : Set G) = (H.relIndex K : ENNReal) * μ (H : Set G) := by
  intro G _ _ _ μ _ H K hHK hH hn
  classical
  set H' := H.addSubgroupOf K
  have hidx : H.relIndex K = H'.index := rfl
  have : H'.FiniteIndex := ⟨by rw [← hidx]; exact hn⟩
  have : Finite (K ⧸ H') := inferInstance
  letI := Fintype.ofFinite (K ⧸ H')
  let o : K ⧸ H' → G := fun q => ((Quotient.out q : K) : G)
  let S : K ⧸ H' → Set G := fun q => (fun x => -o q + x) ⁻¹' (H : Set G)
  have hS : ∀ q, MeasurableSet (S q) := fun q => (measurable_const_add (-o q)) hH
  have hcover : (K : Set G) = ⋃ q, S q := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨((⟨x, hx⟩ : K) : K ⧸ H'), ?_⟩
      have h1 := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' ((⟨x, hx⟩ : K) : K ⧸ H'))
      rw [AddSubgroup.mem_addSubgroupOf] at h1
      simpa [S, o] using h1
    · rintro ⟨q, hq⟩
      have hq' : -o q + x ∈ H := hq
      have hoK : o q ∈ K := (Quotient.out q).2
      have hx : x = o q + (-o q + x) := (add_neg_cancel_left (o q) x).symm
      rw [hx]
      exact K.add_mem hoK (hHK hq')
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro q r hqr
    rw [Function.onFun, Set.disjoint_left]
    intro x hxq hxr
    apply hqr
    have hq' : -o q + x ∈ H := hxq
    have hr' : -o r + x ∈ H := hxr
    have h2 : -o q + o r ∈ H := by
      have := H.add_mem hq' (H.neg_mem hr')
      simpa [neg_add_rev, add_assoc] using this
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' r]
    apply QuotientAddGroup.eq.mpr
    rw [AddSubgroup.mem_addSubgroupOf]
    simpa [o] using h2
  have hμ : ∀ q, μ (S q) = μ (H : Set G) := fun q => MeasureTheory.measure_preimage_add μ (-o q) _
  rw [hcover, MeasureTheory.measure_iUnion hdisj hS, tsum_fintype]
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hidx, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]

end GlobalTheory.CompanionTheory.HaarIndex
