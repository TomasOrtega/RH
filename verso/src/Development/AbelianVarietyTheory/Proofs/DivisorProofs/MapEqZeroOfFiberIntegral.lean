import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslationInvariantSchwartzBruhatMapFactorsInte

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SplitWeil.HaarFactor
open scoped Topology

noncomputable section
namespace GlobalTheory.DetEqv.Transl

/- English proof (translation)
Use `⟨hf, ?_⟩` and prove the remaining obligations. Establish `hcl : IsClosed (Function.support f)`. Establish `: Function.support f = (f ⁻¹' {0})ᶜ` using `by ext x; simp`. Rewrite using `[this]`. Conclude with `(hf _).isClosed_compl`.

Use `hK.of_isClosed_subset (isClosed_tsupport f) ?_` and prove the remaining obligations. Rewrite using `[tsupport, hcl.closure_eq]`. Introduce `x hx`. Assume the negation of the conclusion as `hx'`. Conclude with `hx (h x hx')`.
-/
theorem mem_SB_of_compact {X : Type*} [TopologicalSpace X] {f : X → ℂ} (hf : IsLocallyConstant f) {K : Set X}
    (hK : IsCompact K) (h : ∀ x ∉ K, f x = 0) : f ∈ SB X := by
  refine ⟨hf, ?_⟩
  have hcl : IsClosed (Function.support f) := by
    have : Function.support f = (f ⁻¹' {0})ᶜ := by ext x; simp
    rw [this]
    exact (hf _).isClosed_compl
  refine hK.of_isClosed_subset (isClosed_tsupport f) ?_
  rw [tsupport, hcl.closure_eq]
  intro x hx
  by_contra hx'
  exact hx (h x hx')

section General
variable {A Z : Type*} [TopologicalSpace Z] [AddCommGroup A] [TopologicalSpace A]

omit [AddCommGroup A] in
/- English proof (translation)
The claim follows from `mem_SB_of_compact (hG.1.comp_continuous (by fun_prop)) (hG.2.image continuous_snd) fun z hz => image_eq_zero_of_notMem_tsupport fun h => hz ⟨(c, z), h, rfl⟩`.
-/
theorem slice_mem' {G : A × Z → ℂ} (hG : G ∈ SB (A × Z)) (c : A) : (fun z => G (c, z)) ∈ SB Z :=
  mem_SB_of_compact (hG.1.comp_continuous (by fun_prop)) (hG.2.image continuous_snd) fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz ⟨(c, z), h, rfl⟩

omit [AddCommGroup A] in
/- English proof (translation)
Use `mem_SB_of_compact ((hf.1.comp_continuous continuous_snd).mul (hφ.1.comp_continuous continuous_fst)) (hφ.2.prod hf.2) fun z hz => ?_` and prove the remaining obligations. Break down `not_and_or.mp (Set.mem_prod.not.mp hz) with h | h` into its components or cases. Rewrite using `[image_eq_zero_of_notMem_tsupport h, mul_zero]`. Rewrite using `[image_eq_zero_of_notMem_tsupport h, zero_mul]`.
-/
theorem tens_mem' {φ : A → ℂ} (hφ : φ ∈ SB A) {f : Z → ℂ} (hf : f ∈ SB Z) :
    (fun y : A × Z => f y.2 * φ y.1) ∈ SB (A × Z) := by
  refine mem_SB_of_compact ((hf.1.comp_continuous continuous_snd).mul (hφ.1.comp_continuous continuous_fst))
    (hφ.2.prod hf.2) fun z hz => ?_
  rcases not_and_or.mp (Set.mem_prod.not.mp hz) with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]

variable [IsTopologicalAddGroup A]

/- English proof (translation)
Use `⟨hG.1.comp_continuous (by fun_prop), ?_⟩` and prove the remaining obligations. Conclude with `hG.2.comp_homeomorph ((Homeomorph.subRight c).prodCongr (Homeomorph.refl Z))`.
-/
theorem transl_mem' {G : A × Z → ℂ} (hG : G ∈ SB (A × Z)) (c : A) :
    (fun y : A × Z => G (y.1 - c, y.2)) ∈ SB (A × Z) := by
  refine ⟨hG.1.comp_continuous (by fun_prop), ?_⟩
  exact hG.2.comp_homeomorph ((Homeomorph.subRight c).prodCongr (Homeomorph.refl Z))

/- English proof (translation)
Establish `h1 : ∀ᶠ t in 𝓝 (0 : A), ∀ y ∈ tsupport G, G (y.1 + t, y.2) = G y`. Use `IsCompact.eventually_forall_of_forall_eventually hG.2 fun z _ => ?_` and prove the remaining obligations. Establish `h2 : IsLocallyConstant fun q : A × (A × Z) => (G (q.2.1 + q.1, q.2.2), G q.2)` using `(hG.1.comp_continuous (by fun_prop)).prodMk (hG.1.comp_continuous continuous_snd)`. Use `filter_upwards [h2.eventually_eq (0, z)] with q hq`. Simplify using `only [Prod.mk.injEq, add_zero, Prod.mk.eta] at hq`.

Rewrite using `[hq.1, hq.2]`. Take `⟨U, hUo, hUc, hUs⟩` from `hbasis _ h1`. Use `⟨U, hUo, hUc, fun u hu z => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hz : z ∈ tsupport G`. Conclude with `hUs hu z hz`.

Distinguish the cases in `hz' : (z.1 + u, z.2) ∈ tsupport G`. Use `hUs (U.neg_mem hu) _ hz'` as an intermediate fact. Simplify using `only [add_neg_cancel_right, Prod.mk.eta] at this`. Conclude with `this.symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']`.
-/
theorem exists_subgroup_invariant'
    (hbasis : ∀ V ∈ 𝓝 (0 : A), ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧ (U : Set A) ⊆ V)
    {G : A × Z → ℂ} (hG : G ∈ SB (A × Z)) :
    ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧
      ∀ u ∈ U, ∀ y : A × Z, G (y.1 + u, y.2) = G y := by
  have h1 : ∀ᶠ t in 𝓝 (0 : A), ∀ y ∈ tsupport G, G (y.1 + t, y.2) = G y := by
    refine IsCompact.eventually_forall_of_forall_eventually hG.2 fun z _ => ?_
    have h2 : IsLocallyConstant fun q : A × (A × Z) => (G (q.2.1 + q.1, q.2.2), G q.2) :=
      (hG.1.comp_continuous (by fun_prop)).prodMk (hG.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, z)] with q hq
    simp only [Prod.mk.injEq, add_zero, Prod.mk.eta] at hq
    rw [hq.1, hq.2]
  obtain ⟨U, hUo, hUc, hUs⟩ := hbasis _ h1
  refine ⟨U, hUo, hUc, fun u hu z => ?_⟩
  by_cases hz : z ∈ tsupport G
  · exact hUs hu z hz
  by_cases hz' : (z.1 + u, z.2) ∈ tsupport G
  · have := hUs (U.neg_mem hu) _ hz'
    simp only [add_neg_cancel_right, Prod.mk.eta] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

/- English proof (translation)
Establish `hK : IsCompact (Prod.fst '' tsupport G)` using `hG.2.image continuous_fst`. Take `⟨t, -, ht⟩` from `hK.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (U : Set A)) (fun a _ => (hU.preimage (by fun_prop)).mem_nhds (by simp))`. Use `⟨t.image (QuotientAddGroup.mk : A → A ⧸ U), fun z => ?_⟩` and prove the remaining obligations. Establish `hind : ∀ q : A ⧸ U, (U : Set A).indicator (fun _ => (1 : ℂ)) (z.1 - q.out) = if (z.1 : A ⧸ U) = q then 1 else 0`. Introduce `q`.

Establish `: (z.1 : A ⧸ U) = q ↔ z.1 - q.out ∈ U` using `by conv_lhs => rw [← QuotientAddGroup.out_eq' q]`. Conclude with `QuotientAddGroup.eq_iff_sub_mem`. Distinguish the cases in `h : z.1 - q.out ∈ U`. Rewrite using `[Set.indicator_of_mem (show z.1 - q.out ∈ (U : Set A) from h), if_pos (this.mpr h)]`. Rewrite using `[Set.indicator_of_notMem (show z.1 - q.out ∉ (U : Set A) from h), if_neg (fun h' => h (this.mp h'))]`.

Simplify using `only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]`. Use `split_ifs with h`. Establish `h2 : -z.1 + (z.1 : A ⧸ U).out ∈ U` using `QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm`. Use `hinv _ h2 z` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_left]`.

Conclude with `this.symm`. Use `image_eq_zero_of_notMem_tsupport fun hz => h ?_` and prove the remaining obligations. Take `⟨a, ha, hza⟩` from `Set.mem_iUnion₂.mp (ht ⟨z, hz, rfl⟩)`. Conclude with `Finset.mem_image.mpr ⟨a, ha, (QuotientAddGroup.eq_iff_sub_mem.mpr hza).symm⟩`.
-/
theorem exists_decomp' {U : AddSubgroup A} (hU : IsOpen (U : Set A)) {G : A × Z → ℂ} (hG : G ∈ SB (A × Z))
    (hinv : ∀ u ∈ U, ∀ y : A × Z, G (y.1 + u, y.2) = G y) :
    ∃ T : Finset (A ⧸ U), ∀ y : A × Z,
      G y = ∑ q ∈ T, G (q.out, y.2) * (U : Set A).indicator (fun _ => (1 : ℂ)) (y.1 - q.out) := by
  classical
  have hK : IsCompact (Prod.fst '' tsupport G) := hG.2.image continuous_fst
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (U : Set A))
    (fun a _ => (hU.preimage (by fun_prop)).mem_nhds (by simp))
  refine ⟨t.image (QuotientAddGroup.mk : A → A ⧸ U), fun z => ?_⟩
  have hind : ∀ q : A ⧸ U, (U : Set A).indicator (fun _ => (1 : ℂ)) (z.1 - q.out) =
      if (z.1 : A ⧸ U) = q then 1 else 0 := by
    intro q
    have : (z.1 : A ⧸ U) = q ↔ z.1 - q.out ∈ U := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      exact QuotientAddGroup.eq_iff_sub_mem
    by_cases h : z.1 - q.out ∈ U
    · rw [Set.indicator_of_mem (show z.1 - q.out ∈ (U : Set A) from h), if_pos (this.mpr h)]
    · rw [Set.indicator_of_notMem (show z.1 - q.out ∉ (U : Set A) from h), if_neg (fun h' => h (this.mp h'))]
  simp only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  split_ifs with h
  · have h2 : -z.1 + (z.1 : A ⧸ U).out ∈ U := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm
    have := hinv _ h2 z
    rw [add_neg_cancel_left] at this
    exact this.symm
  · refine image_eq_zero_of_notMem_tsupport fun hz => h ?_
    obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.mp (ht ⟨z, hz, rfl⟩)
    exact Finset.mem_image.mpr ⟨a, ha, (QuotientAddGroup.eq_iff_sub_mem.mpr hza).symm⟩

variable [T2Space A] [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]

omit [TopologicalSpace Z] in

/- English proof (translation)
Establish `he` using `integrable_of_SB μ (ind_mem hUo hUc)`. Establish `hshift : ∀ c : A, ∫ a, (U : Set A).indicator (fun _ => (1 : ℂ)) (a - c) ∂μ = (μ.real (U : Set A) : ℂ)`. Introduce `c`. Rewrite using `[integral_sub_right_eq_self (fun a => (U : Set A).indicator (fun _ => (1 : ℂ)) a) c, integral_indicator_const _ hUo.measurableSet]`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[integral_finsetSum _ fun q _ => (he.comp_sub_right _).const_mul _]`. Simplify using `only [integral_const_mul, hshift, ← Finset.sum_mul]`.
-/
theorem fiber_integral' {U : AddSubgroup A} (hUo : IsOpen (U : Set A)) (hUc : IsCompact (U : Set A))
    {G : A × Z → ℂ} (T : Finset (A ⧸ U))
    (hT : ∀ y : A × Z, G y = ∑ q ∈ T, G (q.out, y.2) * (U : Set A).indicator (fun _ => (1 : ℂ)) (y.1 - q.out))
    (z : Z) : ∫ a, G (a, z) ∂μ = (∑ q ∈ T, G (q.out, z)) * (μ.real (U : Set A) : ℂ) := by
  have he := integrable_of_SB μ (ind_mem hUo hUc)
  have hshift : ∀ c : A, ∫ a, (U : Set A).indicator (fun _ => (1 : ℂ)) (a - c) ∂μ = (μ.real (U : Set A) : ℂ) := by
    intro c
    rw [integral_sub_right_eq_self (fun a => (U : Set A).indicator (fun _ => (1 : ℂ)) a) c,
      integral_indicator_const _ hUo.measurableSet]
    simp
  calc ∫ a, G (a, z) ∂μ
      = ∫ a, ∑ q ∈ T, G (q.out, z) * (U : Set A).indicator (fun _ => (1 : ℂ)) (a - q.out) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun a => hT (a, z))
    _ = (∑ q ∈ T, G (q.out, z)) * (μ.real (U : Set A) : ℂ) := by
      rw [integral_finsetSum _ fun q _ => (he.comp_sub_right _).const_mul _]
      simp only [integral_const_mul, hshift, ← Finset.sum_mul]

/- English proof (translation)
Take `⟨U, hUo, hUc, hinv⟩` from `exists_subgroup_invariant' hbasis G.2`. Take `⟨T, hT⟩` from `exists_decomp' hUo G.2 hinv`. Establish `hsum : ∀ z, ∑ q ∈ T, G.1 (q.out, z) = 0` using `fun z => by`. Use `(fiber_integral' μ hUo hUc T hT z).symm.trans (hG z)` as an intermediate fact. Conclude with `(mul_eq_zero.mp this).resolve_right (real_ne_zero μ hUo hUc)`.

Set `H : A ⧸ U → SB (A × Z)` to `fun q => ⟨fun y => G.1 (q.out, y.2) * (U : Set A).indicator (fun _ => (1 : ℂ)) y.1, tens_mem' (ind_mem hUo hUc) (slice_mem' G.2 q.out)⟩`. Set `Gq : A ⧸ U → SB (A × Z)` to `fun q => ⟨fun y => (H q).1 (y.1 - q.out, y.2), transl_mem' (H q).2 q.out⟩`. Establish `hdec : G = ∑ q ∈ T, Gq q`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `z`.

Rewrite using `[hT z, Submodule.coe_sum, Finset.sum_apply]`. Establish `hq : ∀ q, L (Gq q) = L (H q)` using `fun q => (hL q.out (Gq q) (H q) fun u z => by simp [Gq]).symm`. Establish `hg : ∑ q ∈ T, H q = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `y`.

Rewrite using `[Submodule.coe_sum, Finset.sum_apply]`. Use `show ∑ q ∈ T, G.1 (q.out, y.2) * (U : Set A).indicator (fun _ => (1 : ℂ)) y.1 = 0`. Rewrite using `[← Finset.sum_mul, hsum, zero_mul]`. Rewrite using `[hdec, map_sum, Finset.sum_congr rfl fun q _ => hq q, ← map_sum, hg, map_zero]`.
-/
theorem map_eq_zero_of_fiber'
    (hbasis : ∀ V ∈ 𝓝 (0 : A), ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧ (U : Set A) ⊆ V)
    (L : SB (A × Z) →ₗ[ℂ] ℂ)
    (hL : ∀ (c : A) (G G' : SB (A × Z)), (∀ u z, G'.1 (u, z) = G.1 (u + c, z)) → L G' = L G)
    (G : SB (A × Z)) (hG : ∀ z, ∫ a, G.1 (a, z) ∂μ = 0) : L G = 0 := by
  obtain ⟨U, hUo, hUc, hinv⟩ := exists_subgroup_invariant' hbasis G.2
  obtain ⟨T, hT⟩ := exists_decomp' hUo G.2 hinv
  have hsum : ∀ z, ∑ q ∈ T, G.1 (q.out, z) = 0 := fun z => by
    have := (fiber_integral' μ hUo hUc T hT z).symm.trans (hG z)
    exact (mul_eq_zero.mp this).resolve_right (real_ne_zero μ hUo hUc)
  let H : A ⧸ U → SB (A × Z) := fun q =>
    ⟨fun y => G.1 (q.out, y.2) * (U : Set A).indicator (fun _ => (1 : ℂ)) y.1,
      tens_mem' (ind_mem hUo hUc) (slice_mem' G.2 q.out)⟩
  let Gq : A ⧸ U → SB (A × Z) := fun q =>
    ⟨fun y => (H q).1 (y.1 - q.out, y.2), transl_mem' (H q).2 q.out⟩
  have hdec : G = ∑ q ∈ T, Gq q := by
    apply Subtype.ext
    funext z
    rw [hT z, Submodule.coe_sum, Finset.sum_apply]
  have hq : ∀ q, L (Gq q) = L (H q) := fun q =>
    (hL q.out (Gq q) (H q) fun u z => by simp [Gq]).symm
  have hg : ∑ q ∈ T, H q = 0 := by
    apply Subtype.ext
    funext y
    rw [Submodule.coe_sum, Finset.sum_apply]
    show ∑ q ∈ T, G.1 (q.out, y.2) * (U : Set A).indicator (fun _ => (1 : ℂ)) y.1 = 0
    rw [← Finset.sum_mul, hsum, zero_mul]
  rw [hdec, map_sum, Finset.sum_congr rfl fun q _ => hq q, ← map_sum, hg, map_zero]

end General

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ν _ Z _ p L hL Φ hΦ`. Use `haveI := secondCountable k`. Use `haveI := t2Space k`. Use `haveI : LocallyCompactSpace k := inferInstance`. Use `haveI : SigmaFinite ν := inferInstance`.

Use `haveI : (Measure.pi fun _ : Fin p => ν).IsAddHaarMeasure := inferInstance`. Use `map_eq_zero_of_fiber' (Measure.pi fun _ : Fin p => ν) (fun V hV => ?_) L hL Φ hΦ` and prove the remaining obligations. Take `⟨s, hs⟩` from `FourierPi.exists_box_subset hV`. Apply the tactic sequence `refine ⟨boxSub (Fin p) s, ?_, ?_, ?_⟩ <;> rw [coe_boxSub]`. Conclude with `FourierPi.isOpen_box s`.

Conclude with `FourierPi.isCompact_box s`. Conclude with `hs`.
-/
theorem map_eq_zero_of_fiber_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : MeasureTheory.Measure k) [ν.IsAddHaarMeasure]
    (Z : Type) [TopologicalSpace Z] (p : ℕ) (L : GlobalTheory.SplitWeil.SB ((Fin p → k) × Z) →ₗ[ℂ] ℂ),
      (∀ (c : Fin p → k) (Φ Φ' : GlobalTheory.SplitWeil.SB ((Fin p → k) × Z)),
        (∀ (u : Fin p → k) (z : Z), (Φ' : (Fin p → k) × Z → ℂ) (u, z) = (Φ : (Fin p → k) × Z → ℂ) (u + c, z)) → L Φ' = L Φ) →
      ∀ Φ : GlobalTheory.SplitWeil.SB ((Fin p → k) × Z),
        (∀ z : Z, ∫ u, (Φ : (Fin p → k) × Z → ℂ) (u, z) ∂(MeasureTheory.Measure.pi fun _ : Fin p => ν) = 0) → L Φ = 0 := by
  intro k _ _ _ _ _ _ ν _ Z _ p L hL Φ hΦ
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace k := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : (Measure.pi fun _ : Fin p => ν).IsAddHaarMeasure := inferInstance
  refine map_eq_zero_of_fiber' (Measure.pi fun _ : Fin p => ν) (fun V hV => ?_) L hL Φ hΦ
  obtain ⟨s, hs⟩ := FourierPi.exists_box_subset hV
  refine ⟨boxSub (Fin p) s, ?_, ?_, ?_⟩ <;> rw [coe_boxSub]
  · exact FourierPi.isOpen_box s
  · exact FourierPi.isCompact_box s
  · exact hs

end GlobalTheory.DetEqv.Transl
