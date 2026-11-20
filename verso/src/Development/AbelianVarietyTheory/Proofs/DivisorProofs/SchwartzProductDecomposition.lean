import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

open Topology Filter Set
open scoped Classical

noncomputable section

namespace GlobalTheory.SBProd

/- English proof (translation)
Take `⟨s, comp, xs, sU⟩` from `exists_compact_subset hU hx`. Take `⟨V, hV, hxV, hVs⟩` from `loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 (isOpen_interior.mem_nhds xs)`. Conclude with `⟨V, hV, comp.of_isClosed_subset hV.1 (hVs.trans interior_subset), hxV, (hVs.trans interior_subset).trans sU⟩`.
-/
theorem exists_compact_clopen_nhd {H : Type} [TopologicalSpace H] [LocallyCompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] {x : H} {U : Set H} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set H, IsClopen V ∧ IsCompact V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset hU hx
  obtain ⟨V, hV, hxV, hVs⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 (isOpen_interior.mem_nhds xs)
  exact ⟨V, hV, comp.of_isClosed_subset hV.1 (hVs.trans interior_subset), hxV,
    (hVs.trans interior_subset).trans sU⟩

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `: ∀ i ∈ F, ∀ᶠ y in 𝓝 x, (y ∈ U i ↔ x ∈ U i)`. Introduce `i _`. Distinguish the cases in `h : x ∈ U i`.

Use `filter_upwards [(hU i).isOpen.mem_nhds h] with y hy`. Conclude with `iff_of_true hy h`. Use `filter_upwards [(hU i).compl.isOpen.mem_nhds h] with y hy`. Conclude with `iff_of_false hy h`. Use `filter_upwards [(Filter.eventually_all_finset F).2 this] with y hy`.

Conclude with `Finset.filter_congr fun i hi => hy i hi`.
-/
theorem isLocallyConstant_filter {H ι : Type} [TopologicalSpace H] (F : Finset ι) (U : ι → Set H)
    (hU : ∀ i, IsClopen (U i)) : IsLocallyConstant fun a => F.filter (fun i => a ∈ U i) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ i ∈ F, ∀ᶠ y in 𝓝 x, (y ∈ U i ↔ x ∈ U i) := by
    intro i _
    by_cases h : x ∈ U i
    · filter_upwards [(hU i).isOpen.mem_nhds h] with y hy
      exact iff_of_true hy h
    · filter_upwards [(hU i).compl.isOpen.mem_nhds h] with y hy
      exact iff_of_false hy h
  filter_upwards [(Filter.eventually_all_finset F).2 this] with y hy
  exact Finset.filter_congr fun i hi => hy i hi

/- English proof (translation)
Take `⟨hlc, hcs⟩` from `hg`. Set `e : (κ ⊕ κ' → X) ≃ₜ (κ → X) × (κ' → X)` to `Homeomorph.sumArrowHomeomorphProdArrow`. Set `h : (κ → X) × (κ' → X) → ℂ` to `g ∘ e.symm`. Establish `hgh : ∀ z, g z = h (z ∘ Sum.inl, z ∘ Sum.inr)` using `fun z => by`. Establish `: (z ∘ Sum.inl, z ∘ Sum.inr) = e z` using `rfl`.

Simplify using `[h, this]`. Establish `hlc' : IsLocallyConstant h` using `hlc.comp_continuous e.symm.continuous`. Establish `hcs' : HasCompactSupport h` using `hcs.comp_homeomorph e.symm`. Establish `key : ∀ p : (κ → X) × (κ' → X), ∃ U : Set (κ → X), ∃ V : Set (κ' → X), IsClopen U ∧ IsCompact U ∧ IsClopen V ∧ IsCompact V ∧ p.1 ∈ U ∧ p.2 ∈ V ∧ ∀ a ∈ U, ∀ b ∈ V, h (a, b) = h p`. Introduce and unpack `⟨a₀, b₀⟩`.

Take `⟨u, v, hu, hv, hpu, hpv, huv⟩` from `isOpen_prod_iff.1 (hlc'.isOpen_fiber (h (a₀, b₀))) a₀ b₀ rfl`. Take `⟨U, hU, hUc, haU, hUu⟩` from `exists_compact_clopen_nhd hu hpu`. Take `⟨V, hV, hVc, hbV, hVv⟩` from `exists_compact_clopen_nhd hv hpv`. Conclude with `⟨U, V, hU, hUc, hV, hVc, haU, hbV, fun a ha b hb => huv (mk_mem_prod (hUu ha) (hVv hb))⟩`. Use `choose U V hU hUc hV hVc hpU hpV hconst using key`.

Take `⟨F, hF⟩` from `hcs'.isCompact.elim_finite_subcover (fun p => U p ×ˢ V p) (fun p => (hU p).isOpen.prod (hV p).isOpen) (fun q _ => mem_iUnion.2 ⟨q, hpU q, hpV q⟩)`. Set `σ : (κ → X) → Finset F` to `fun a => Finset.univ.filter (fun i : F => a ∈ U i)`. Set `τ : (κ' → X) → Finset F` to `fun b => Finset.univ.filter (fun i : F => b ∈ V i)`. Establish `hσ : IsLocallyConstant σ` using `isLocallyConstant_filter _ (fun i : F => U i) fun i => hU i`. Establish `hτ : IsLocallyConstant τ` using `isLocallyConstant_filter _ (fun i : F => V i) fun i => hV i`.

Set `c : Finset F → Finset F → ℂ` to `fun S T => if hx : (S ∩ T).Nonempty then h (hx.choose : (κ → X) × (κ' → X)) else 0`. Use `⟨Finset F × Finset F, inferInstance, fun x a => if σ a = x.1 ∧ x.1.Nonempty then c x.1 x.2 else 0, fun x b => if τ b = x.2 ∧ x.2.Nonempty then 1 else 0, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Use `⟨hσ.comp fun s => if s = x.1 ∧ x.1.Nonempty then c x.1 x.2 else 0, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x.1.Nonempty`.

Take `⟨i, hi⟩` from `hx`. Use `HasCompactSupport.intro (hUc i) fun a ha => if_neg fun hs => ha ?_` and prove the remaining obligations. Rewrite `hi` using `[← hs.1]`. Simplify `hi` using `[σ]`. Conclude with `HasCompactSupport.intro isCompact_empty fun a _ => if_neg fun hs => hx hs.2`.

Introduce `x`. Use `⟨hτ.comp fun s => if s = x.2 ∧ x.2.Nonempty then (1 : ℂ) else 0, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x.2.Nonempty`. Take `⟨i, hi⟩` from `hx`. Use `HasCompactSupport.intro (hVc i) fun b hb => if_neg fun hs => hb ?_` and prove the remaining obligations.

Rewrite `hi` using `[← hs.1]`. Simplify `hi` using `[τ]`. Conclude with `HasCompactSupport.intro isCompact_empty fun b _ => if_neg fun hs => hx hs.2`. Use function extensionality and compare the values at `z`. Rewrite using `[Finset.sum_apply, hgh z]`.

Generalize the expression as in `z ∘ Sum.inl = a`. Generalize the expression as in `z ∘ Sum.inr = b`. Rewrite using `[Fintype.sum_eq_single (σ a, τ b)]`. Distinguish the cases in `hst : (σ a ∩ τ b).Nonempty`. Establish `hs : (σ a).Nonempty` using `hst.mono Finset.inter_subset_left`.

Establish `ht : (τ b).Nonempty` using `hst.mono Finset.inter_subset_right`. Establish `hmem` using `Finset.mem_inter.1 hst.choose_spec`. Simplify using `only [σ, τ, Finset.mem_filter, Finset.mem_univ, true_and] at hmem`. Establish `hc : c (σ a) (τ b) = h (hst.choose : (κ → X) × (κ' → X))` using `dif_pos hst`. Simplify using `only [true_and, hs, ht, and_self, if_true, hc, mul_one]`.

Conclude with `hconst _ a hmem.1 b hmem.2`. Establish `hc : c (σ a) (τ b) = 0` using `dif_neg hst`. Simplify using `only [hc, ite_self, zero_mul]`. Assume the negation of the conclusion as `hne`. Take `⟨i, hi, hab⟩` from `mem_iUnion₂.1 (hF (subset_tsupport h hne))`.

Conclude with `hst ⟨⟨i, hi⟩, Finset.mem_inter.2 ⟨by simpa [σ] using hab.1, by simpa [τ] using hab.2⟩⟩`. Introduce `x hx`. Distinguish the cases in `h1 : σ a = x.1`. Establish `h2 : τ b ≠ x.2` using `fun h2 => hx (Prod.ext h1.symm h2.symm)`. Simplify using `[h2]`.

Simplify using `[h1]`.
-/
theorem exists_sum_box (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] (κ κ' : Type) [Fintype κ] [Fintype κ'] (g : (κ ⊕ κ' → X) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (κ ⊕ κ' → X)) :
    ∃ (ι : Type) (_ : Fintype ι) (g₁ : ι → (κ → X) → ℂ) (g₂ : ι → (κ' → X) → ℂ),
      (∀ i, g₁ i ∈ GlobalTheory.WeilM.SB (κ → X)) ∧ (∀ i, g₂ i ∈ GlobalTheory.WeilM.SB (κ' → X)) ∧
      g = ∑ i, fun z => g₁ i (z ∘ Sum.inl) * g₂ i (z ∘ Sum.inr) := by
  obtain ⟨hlc, hcs⟩ := hg
  let e : (κ ⊕ κ' → X) ≃ₜ (κ → X) × (κ' → X) := Homeomorph.sumArrowHomeomorphProdArrow
  let h : (κ → X) × (κ' → X) → ℂ := g ∘ e.symm
  have hgh : ∀ z, g z = h (z ∘ Sum.inl, z ∘ Sum.inr) := fun z => by
    have : (z ∘ Sum.inl, z ∘ Sum.inr) = e z := rfl
    simp [h, this]
  have hlc' : IsLocallyConstant h := hlc.comp_continuous e.symm.continuous
  have hcs' : HasCompactSupport h := hcs.comp_homeomorph e.symm
  have key : ∀ p : (κ → X) × (κ' → X), ∃ U : Set (κ → X), ∃ V : Set (κ' → X), IsClopen U ∧ IsCompact U ∧
      IsClopen V ∧ IsCompact V ∧ p.1 ∈ U ∧ p.2 ∈ V ∧ ∀ a ∈ U, ∀ b ∈ V, h (a, b) = h p := by
    rintro ⟨a₀, b₀⟩
    obtain ⟨u, v, hu, hv, hpu, hpv, huv⟩ :=
      isOpen_prod_iff.1 (hlc'.isOpen_fiber (h (a₀, b₀))) a₀ b₀ rfl
    obtain ⟨U, hU, hUc, haU, hUu⟩ := exists_compact_clopen_nhd hu hpu
    obtain ⟨V, hV, hVc, hbV, hVv⟩ := exists_compact_clopen_nhd hv hpv
    exact ⟨U, V, hU, hUc, hV, hVc, haU, hbV, fun a ha b hb => huv (mk_mem_prod (hUu ha) (hVv hb))⟩
  choose U V hU hUc hV hVc hpU hpV hconst using key
  obtain ⟨F, hF⟩ := hcs'.isCompact.elim_finite_subcover (fun p => U p ×ˢ V p)
    (fun p => (hU p).isOpen.prod (hV p).isOpen) (fun q _ => mem_iUnion.2 ⟨q, hpU q, hpV q⟩)
  let σ : (κ → X) → Finset F := fun a => Finset.univ.filter (fun i : F => a ∈ U i)
  let τ : (κ' → X) → Finset F := fun b => Finset.univ.filter (fun i : F => b ∈ V i)
  have hσ : IsLocallyConstant σ := isLocallyConstant_filter _ (fun i : F => U i) fun i => hU i
  have hτ : IsLocallyConstant τ := isLocallyConstant_filter _ (fun i : F => V i) fun i => hV i
  let c : Finset F → Finset F → ℂ := fun S T =>
    if hx : (S ∩ T).Nonempty then h (hx.choose : (κ → X) × (κ' → X)) else 0
  refine ⟨Finset F × Finset F, inferInstance,
    fun x a => if σ a = x.1 ∧ x.1.Nonempty then c x.1 x.2 else 0,
    fun x b => if τ b = x.2 ∧ x.2.Nonempty then 1 else 0, ?_, ?_, ?_⟩
  · intro x
    refine ⟨hσ.comp fun s => if s = x.1 ∧ x.1.Nonempty then c x.1 x.2 else 0, ?_⟩
    by_cases hx : x.1.Nonempty
    · obtain ⟨i, hi⟩ := hx
      refine HasCompactSupport.intro (hUc i) fun a ha => if_neg fun hs => ha ?_
      rw [← hs.1] at hi
      simpa [σ] using hi
    · exact HasCompactSupport.intro isCompact_empty fun a _ => if_neg fun hs => hx hs.2
  · intro x
    refine ⟨hτ.comp fun s => if s = x.2 ∧ x.2.Nonempty then (1 : ℂ) else 0, ?_⟩
    by_cases hx : x.2.Nonempty
    · obtain ⟨i, hi⟩ := hx
      refine HasCompactSupport.intro (hVc i) fun b hb => if_neg fun hs => hb ?_
      rw [← hs.1] at hi
      simpa [τ] using hi
    · exact HasCompactSupport.intro isCompact_empty fun b _ => if_neg fun hs => hx hs.2
  · funext z
    rw [Finset.sum_apply, hgh z]
    generalize z ∘ Sum.inl = a
    generalize z ∘ Sum.inr = b
    rw [Fintype.sum_eq_single (σ a, τ b)]
    · by_cases hst : (σ a ∩ τ b).Nonempty
      · have hs : (σ a).Nonempty := hst.mono Finset.inter_subset_left
        have ht : (τ b).Nonempty := hst.mono Finset.inter_subset_right
        have hmem := Finset.mem_inter.1 hst.choose_spec
        simp only [σ, τ, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        have hc : c (σ a) (τ b) = h (hst.choose : (κ → X) × (κ' → X)) := dif_pos hst
        simp only [true_and, hs, ht, and_self, if_true, hc, mul_one]
        exact hconst _ a hmem.1 b hmem.2
      · have hc : c (σ a) (τ b) = 0 := dif_neg hst
        simp only [hc, ite_self, zero_mul]
        by_contra hne
        obtain ⟨i, hi, hab⟩ := mem_iUnion₂.1 (hF (subset_tsupport h hne))
        exact hst ⟨⟨i, hi⟩, Finset.mem_inter.2 ⟨by simpa [σ] using hab.1, by simpa [τ] using hab.2⟩⟩
    · intro x hx
      by_cases h1 : σ a = x.1
      · have h2 : τ b ≠ x.2 := fun h2 => hx (Prod.ext h1.symm h2.symm)
        simp [h2]
      · simp [h1]

end GlobalTheory.SBProd
