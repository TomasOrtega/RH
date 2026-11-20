import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitWeil.HaarFactor

section General
variable {X₀ A : Type*} [TopologicalSpace X₀] [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [T2Space X₀] [T2Space A]

/- English proof (translation)
The claim follows from `QuotientAddGroup.eq_iff_sub_mem`.
-/
example (U : AddSubgroup A) (a b : A) : ((a : A ⧸ U) = b) ↔ a - b ∈ U := QuotientAddGroup.eq_iff_sub_mem

/- English proof (translation)
Use `⟨hG.1.comp_continuous (by fun_prop), HasCompactSupport.intro (hG.2.image continuous_fst) fun x hx => ?_⟩` and prove the remaining obligations. Use `image_eq_zero_of_notMem_tsupport fun h => hx ⟨(x, c), h, rfl⟩` and prove the remaining obligations.
-/
theorem slice_mem {G : X₀ × A → ℂ} (hG : G ∈ SB (X₀ × A)) (c : A) : (fun x => G (x, c)) ∈ SB X₀ := by
  refine ⟨hG.1.comp_continuous (by fun_prop), HasCompactSupport.intro (hG.2.image continuous_fst) fun x hx => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun h => hx ⟨(x, c), h, rfl⟩

/- English proof (translation)
Use `⟨hG.1.comp_continuous (by fun_prop), HasCompactSupport.intro (hG.2.image continuous_snd) fun a ha => ?_⟩` and prove the remaining obligations. Use `image_eq_zero_of_notMem_tsupport fun h => ha ⟨(x, a), h, rfl⟩` and prove the remaining obligations.
-/
theorem fiber_mem {G : X₀ × A → ℂ} (hG : G ∈ SB (X₀ × A)) (x : X₀) : (fun a => G (x, a)) ∈ SB A := by
  refine ⟨hG.1.comp_continuous (by fun_prop), HasCompactSupport.intro (hG.2.image continuous_snd) fun a ha => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun h => ha ⟨(x, a), h, rfl⟩

/- English proof (translation)
Use `⟨(hf.1.comp_continuous continuous_fst).mul (hφ.1.comp_continuous continuous_snd), HasCompactSupport.intro (hf.2.prod hφ.2) fun z hz => ?_⟩` and prove the remaining obligations. Break down `not_and_or.mp (Set.mem_prod.not.mp hz) with h | h` into its components or cases. Rewrite using `[image_eq_zero_of_notMem_tsupport h, zero_mul]`. Rewrite using `[image_eq_zero_of_notMem_tsupport h, mul_zero]`.
-/
theorem tens_mem {f : X₀ → ℂ} (hf : f ∈ SB X₀) {φ : A → ℂ} (hφ : φ ∈ SB A) :
    (fun z : X₀ × A => f z.1 * φ z.2) ∈ SB (X₀ × A) := by
  refine ⟨(hf.1.comp_continuous continuous_fst).mul (hφ.1.comp_continuous continuous_snd),
    HasCompactSupport.intro (hf.2.prod hφ.2) fun z hz => ?_⟩
  rcases not_and_or.mp (Set.mem_prod.not.mp hz) with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

/- English proof (translation)
Use `⟨hG.1.comp_continuous (by fun_prop), ?_⟩` and prove the remaining obligations. Conclude with `hG.2.comp_homeomorph ((Homeomorph.refl X₀).prodCongr (Homeomorph.subRight c))`.
-/
theorem transl_mem {G : X₀ × A → ℂ} (hG : G ∈ SB (X₀ × A)) (c : A) :
    (fun z : X₀ × A => G (z.1, z.2 - c)) ∈ SB (X₀ × A) := by
  refine ⟨hG.1.comp_continuous (by fun_prop), ?_⟩
  exact hG.2.comp_homeomorph ((Homeomorph.refl X₀).prodCongr (Homeomorph.subRight c))

/- English proof (translation)
Establish `hcl : IsClopen (U : Set A)` using `⟨U.isClosed_of_isOpen hUo, hUo⟩`. Use `⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_, HasCompactSupport.intro hUc fun y hy => Set.indicator_of_notMem hy _⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ (U : Set A)`. Use `filter_upwards [hcl.isOpen.mem_nhds hx] with z hz`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem hz]`.

Use `filter_upwards [hcl.compl.isOpen.mem_nhds hx] with z hz`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem hz]`.
-/
theorem ind_mem {U : AddSubgroup A} (hUo : IsOpen (U : Set A)) (hUc : IsCompact (U : Set A)) :
    (U : Set A).indicator (fun _ => (1 : ℂ)) ∈ SB A := by
  have hcl : IsClopen (U : Set A) := ⟨U.isClosed_of_isOpen hUo, hUo⟩
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro hUc fun y hy => Set.indicator_of_notMem hy _⟩
  by_cases hx : x ∈ (U : Set A)
  · filter_upwards [hcl.isOpen.mem_nhds hx] with z hz
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hz]
  · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with z hz
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hz]

def tensL (φ : SB A) : SB X₀ →ₗ[ℂ] SB (X₀ × A) where
  toFun f := ⟨fun z => f.1 z.1 * φ.1 z.2, tens_mem f.2 φ.2⟩
  map_add' f g := by ext z; simp [add_mul]
  map_smul' c f := by ext z; simp [mul_assoc]

/- English proof (translation)
Establish `h1 : ∀ᶠ t in 𝓝 (0 : A), ∀ z ∈ tsupport G, G (z.1, z.2 + t) = G z`. Use `IsCompact.eventually_forall_of_forall_eventually hG.2 fun z _ => ?_` and prove the remaining obligations. Establish `h2 : IsLocallyConstant fun q : A × (X₀ × A) => (G (q.2.1, q.2.2 + q.1), G q.2)` using `(hG.1.comp_continuous (by fun_prop)).prodMk (hG.1.comp_continuous continuous_snd)`. Use `filter_upwards [h2.eventually_eq (0, z)] with q hq`. Simplify using `only [Prod.mk.injEq, add_zero, Prod.mk.eta] at hq`.

Rewrite using `[hq.1, hq.2]`. Take `⟨U, hUo, hUc, hUs⟩` from `hbasis _ h1`. Use `⟨U, hUo, hUc, fun u hu z => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hz : z ∈ tsupport G`. Conclude with `hUs hu z hz`.

Distinguish the cases in `hz' : (z.1, z.2 + u) ∈ tsupport G`. Use `hUs (U.neg_mem hu) _ hz'` as an intermediate fact. Simplify using `only [add_neg_cancel_right, Prod.mk.eta] at this`. Conclude with `this.symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']`.
-/
theorem exists_subgroup_invariant
    (hbasis : ∀ V ∈ 𝓝 (0 : A), ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧ (U : Set A) ⊆ V)
    {G : X₀ × A → ℂ} (hG : G ∈ SB (X₀ × A)) :
    ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧
      ∀ u ∈ U, ∀ z : X₀ × A, G (z.1, z.2 + u) = G z := by
  have h1 : ∀ᶠ t in 𝓝 (0 : A), ∀ z ∈ tsupport G, G (z.1, z.2 + t) = G z := by
    refine IsCompact.eventually_forall_of_forall_eventually hG.2 fun z _ => ?_
    have h2 : IsLocallyConstant fun q : A × (X₀ × A) => (G (q.2.1, q.2.2 + q.1), G q.2) :=
      (hG.1.comp_continuous (by fun_prop)).prodMk (hG.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, z)] with q hq
    simp only [Prod.mk.injEq, add_zero, Prod.mk.eta] at hq
    rw [hq.1, hq.2]
  obtain ⟨U, hUo, hUc, hUs⟩ := hbasis _ h1
  refine ⟨U, hUo, hUc, fun u hu z => ?_⟩
  by_cases hz : z ∈ tsupport G
  · exact hUs hu z hz
  by_cases hz' : (z.1, z.2 + u) ∈ tsupport G
  · have := hUs (U.neg_mem hu) _ hz'
    simp only [add_neg_cancel_right, Prod.mk.eta] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

/- English proof (translation)
Establish `hK : IsCompact (Prod.snd '' tsupport G)` using `hG.2.image continuous_snd`. Take `⟨t, -, ht⟩` from `hK.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (U : Set A)) (fun a _ => (hU.preimage (by fun_prop)).mem_nhds (by simp))`. Use `⟨t.image (QuotientAddGroup.mk : A → A ⧸ U), fun z => ?_⟩` and prove the remaining obligations. Establish `hind : ∀ q : A ⧸ U, (U : Set A).indicator (fun _ => (1 : ℂ)) (z.2 - q.out) = if (z.2 : A ⧸ U) = q then 1 else 0`. Introduce `q`.

Establish `: (z.2 : A ⧸ U) = q ↔ z.2 - q.out ∈ U` using `by conv_lhs => rw [← QuotientAddGroup.out_eq' q]`. Conclude with `QuotientAddGroup.eq_iff_sub_mem`. Distinguish the cases in `h : z.2 - q.out ∈ U`. Rewrite using `[Set.indicator_of_mem (show z.2 - q.out ∈ (U : Set A) from h), if_pos (this.mpr h)]`. Rewrite using `[Set.indicator_of_notMem (show z.2 - q.out ∉ (U : Set A) from h), if_neg (fun h' => h (this.mp h'))]`.

Simplify using `only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']`. Use `split_ifs with h`. Establish `h2 : -z.2 + (z.2 : A ⧸ U).out ∈ U` using `QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm`. Use `hinv _ h2 z` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_left]`.

Conclude with `this.symm`. Use `image_eq_zero_of_notMem_tsupport fun hz => h ?_` and prove the remaining obligations. Take `⟨a, ha, hza⟩` from `Set.mem_iUnion₂.mp (ht ⟨z, hz, rfl⟩)`. Conclude with `Finset.mem_image.mpr ⟨a, ha, (QuotientAddGroup.eq_iff_sub_mem.mpr hza).symm⟩`.
-/
theorem exists_decomp {U : AddSubgroup A} (hU : IsOpen (U : Set A)) {G : X₀ × A → ℂ} (hG : G ∈ SB (X₀ × A))
    (hinv : ∀ u ∈ U, ∀ z : X₀ × A, G (z.1, z.2 + u) = G z) :
    ∃ T : Finset (A ⧸ U), ∀ z : X₀ × A,
      G z = ∑ q ∈ T, G (z.1, q.out) * (U : Set A).indicator (fun _ => (1 : ℂ)) (z.2 - q.out) := by
  classical
  have hK : IsCompact (Prod.snd '' tsupport G) := hG.2.image continuous_snd
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (U : Set A))
    (fun a _ => (hU.preimage (by fun_prop)).mem_nhds (by simp))
  refine ⟨t.image (QuotientAddGroup.mk : A → A ⧸ U), fun z => ?_⟩
  have hind : ∀ q : A ⧸ U, (U : Set A).indicator (fun _ => (1 : ℂ)) (z.2 - q.out) =
      if (z.2 : A ⧸ U) = q then 1 else 0 := by
    intro q
    have : (z.2 : A ⧸ U) = q ↔ z.2 - q.out ∈ U := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      exact QuotientAddGroup.eq_iff_sub_mem
    by_cases h : z.2 - q.out ∈ U
    · rw [Set.indicator_of_mem (show z.2 - q.out ∈ (U : Set A) from h), if_pos (this.mpr h)]
    · rw [Set.indicator_of_notMem (show z.2 - q.out ∉ (U : Set A) from h), if_neg (fun h' => h (this.mp h'))]
  simp only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']
  split_ifs with h
  · have h2 : -z.2 + (z.2 : A ⧸ U).out ∈ U := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm
    have := hinv _ h2 z
    rw [add_neg_cancel_left] at this
    exact this.symm
  · refine image_eq_zero_of_notMem_tsupport fun hz => h ?_
    obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.mp (ht ⟨z, hz, rfl⟩)
    exact Finset.mem_image.mpr ⟨a, ha, (QuotientAddGroup.eq_iff_sub_mem.mpr hza).symm⟩

section Meas
variable [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]

/- English proof (translation)
The claim follows from `hφ.1.continuous.integrable_of_hasCompactSupport hφ.2`.
-/
theorem integrable_of_SB {φ : A → ℂ} (hφ : φ ∈ SB A) : Integrable φ μ :=
  hφ.1.continuous.integrable_of_hasCompactSupport hφ.2

/- English proof (translation)
Establish `h1 : 0 < μ (U : Set A)` using `hUo.measure_pos μ ⟨0, U.zero_mem⟩`. Establish `h2 : μ (U : Set A) ≠ ⊤` using `hUc.measure_lt_top.ne`. Conclude with `(ENNReal.toReal_pos h1.ne' h2).ne'` after adjusting the coercions.
-/
theorem real_ne_zero {U : AddSubgroup A} (hUo : IsOpen (U : Set A)) (hUc : IsCompact (U : Set A)) :
    (μ.real (U : Set A) : ℂ) ≠ 0 := by
  have h1 : 0 < μ (U : Set A) := hUo.measure_pos μ ⟨0, U.zero_mem⟩
  have h2 : μ (U : Set A) ≠ ⊤ := hUc.measure_lt_top.ne
  exact_mod_cast (ENNReal.toReal_pos h1.ne' h2).ne'

/- English proof (translation)
Establish `he` using `integrable_of_SB μ (ind_mem hUo hUc)`. Establish `hshift : ∀ c : A, ∫ a, (U : Set A).indicator (fun _ => (1 : ℂ)) (a - c) ∂μ = (μ.real (U : Set A) : ℂ)`. Introduce `c`. Rewrite using `[integral_sub_right_eq_self (fun a => (U : Set A).indicator (fun _ => (1 : ℂ)) a) c, integral_indicator_const _ hUo.measurableSet]`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[integral_finset_sum _ fun q _ => (he.comp_sub_right _).const_mul _]`. Simplify using `only [integral_const_mul, hshift, ← Finset.sum_mul]`.
-/
theorem fiber_integral {U : AddSubgroup A} (hUo : IsOpen (U : Set A)) (hUc : IsCompact (U : Set A))
    {G : X₀ × A → ℂ} (T : Finset (A ⧸ U))
    (hT : ∀ z : X₀ × A, G z = ∑ q ∈ T, G (z.1, q.out) * (U : Set A).indicator (fun _ => (1 : ℂ)) (z.2 - q.out))
    (x : X₀) : ∫ a, G (x, a) ∂μ = (∑ q ∈ T, G (x, q.out)) * (μ.real (U : Set A) : ℂ) := by
  have he := integrable_of_SB μ (ind_mem hUo hUc)
  have hshift : ∀ c : A, ∫ a, (U : Set A).indicator (fun _ => (1 : ℂ)) (a - c) ∂μ = (μ.real (U : Set A) : ℂ) := by
    intro c
    rw [integral_sub_right_eq_self (fun a => (U : Set A).indicator (fun _ => (1 : ℂ)) a) c,
      integral_indicator_const _ hUo.measurableSet]
    simp
  calc ∫ a, G (x, a) ∂μ
      = ∫ a, ∑ q ∈ T, G (x, q.out) * (U : Set A).indicator (fun _ => (1 : ℂ)) (a - q.out) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun a => hT (x, a))
    _ = (∑ q ∈ T, G (x, q.out)) * (μ.real (U : Set A) : ℂ) := by
      rw [integral_finset_sum _ fun q _ => (he.comp_sub_right _).const_mul _]
      simp only [integral_const_mul, hshift, ← Finset.sum_mul]

/- English proof (translation)
Take `⟨U, hUo, hUc, hinv⟩` from `exists_subgroup_invariant hbasis G.2`. Take `⟨T, hT⟩` from `exists_decomp hUo G.2 hinv`. Establish `hsum : ∀ x, ∑ q ∈ T, G.1 (x, q.out) = 0` using `fun x => by`. Use `(fiber_integral μ hUo hUc T hT x).symm.trans (hG x)` as an intermediate fact. Conclude with `(mul_eq_zero.mp this).resolve_right (real_ne_zero μ hUo hUc)`.

Set `e : SB A` to `⟨_, ind_mem hUo hUc⟩`. Set `g : A ⧸ U → SB X₀` to `fun q => ⟨_, slice_mem G.2 q.out⟩`. Set `Gq : A ⧸ U → SB (X₀ × A)` to `fun q => ⟨fun z => (tensL e (g q)).1 (z.1, z.2 - q.out), transl_mem (tensL e (g q)).2 q.out⟩`. Establish `hdec : G = ∑ q ∈ T, Gq q`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `z`. Rewrite using `[hT z, Submodule.coe_sum, Finset.sum_apply]`. Both sides reduce to the same expression. Establish `hq : ∀ q, L (Gq q) = L (tensL e (g q))` using `fun q => (hL q.out (Gq q) (tensL e (g q)) fun z => by simp [Gq, tensL, g, e]).symm`. Establish `hg : ∑ q ∈ T, g q = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Rewrite using `[Submodule.coe_sum, Finset.sum_apply]`. Conclude with `hsum x`. Rewrite using `[hdec, map_sum, Finset.sum_congr rfl fun q _ => hq q, ← map_sum, ← map_sum, hg, map_zero, map_zero]`.
-/
theorem map_eq_zero_of_fiber
    (hbasis : ∀ V ∈ 𝓝 (0 : A), ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧ (U : Set A) ⊆ V)
    {M : Type*} [AddCommGroup M] [Module ℂ M] (L : SB (X₀ × A) →ₗ[ℂ] M)
    (hL : ∀ (a : A) (G G' : SB (X₀ × A)), (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L G' = L G)
    (G : SB (X₀ × A)) (hG : ∀ x, ∫ a, G.1 (x, a) ∂μ = 0) : L G = 0 := by
  obtain ⟨U, hUo, hUc, hinv⟩ := exists_subgroup_invariant hbasis G.2
  obtain ⟨T, hT⟩ := exists_decomp hUo G.2 hinv
  have hsum : ∀ x, ∑ q ∈ T, G.1 (x, q.out) = 0 := fun x => by
    have := (fiber_integral μ hUo hUc T hT x).symm.trans (hG x)
    exact (mul_eq_zero.mp this).resolve_right (real_ne_zero μ hUo hUc)
  let e : SB A := ⟨_, ind_mem hUo hUc⟩
  let g : A ⧸ U → SB X₀ := fun q => ⟨_, slice_mem G.2 q.out⟩
  let Gq : A ⧸ U → SB (X₀ × A) := fun q =>
    ⟨fun z => (tensL e (g q)).1 (z.1, z.2 - q.out), transl_mem (tensL e (g q)).2 q.out⟩
  have hdec : G = ∑ q ∈ T, Gq q := by
    apply Subtype.ext
    funext z
    rw [hT z, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hq : ∀ q, L (Gq q) = L (tensL e (g q)) := fun q =>
    (hL q.out (Gq q) (tensL e (g q)) fun z => by simp [Gq, tensL, g, e]).symm
  have hg : ∑ q ∈ T, g q = 0 := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    exact hsum x
  rw [hdec, map_sum, Finset.sum_congr rfl fun q _ => hq q, ← map_sum, ← map_sum, hg, map_zero, map_zero]

/- English proof (translation)
Take `⟨B, hBo, hBc, -⟩` from `hbasis Set.univ Filter.univ_mem`. Establish `hpos` using `real_ne_zero μ hBo hBc`. Set `φ₀ : SB A` to `(μ.real (B : Set A) : ℂ)⁻¹ • ⟨_, ind_mem hBo hBc⟩`. Establish `hφ₀ : ∫ a, φ₀.1 a ∂μ = 1` using `by show ∫ a, (μ.real (B : Set A) : ℂ)⁻¹ * (B : Set A).indicator (fun _ => (1 : ℂ)) a ∂μ = 1`. Rewrite using `[integral_const_mul, integral_indicator_const _ hBo.measurableSet]`.

Simplify using `[hpos]`. Use `⟨L ∘ₗ tensL φ₀, fun G => ?_⟩` and prove the remaining obligations. Take `⟨U, hUo, hUc, hinv⟩` from `exists_subgroup_invariant hbasis G.2`. Take `⟨T, hT⟩` from `exists_decomp hUo G.2 hinv`. Establish `hΨ : (fun x => ∫ a, G.1 (x, a) ∂μ) ∈ SB X₀`.

Use `(SB X₀).smul_mem (μ.real (U : Set A) : ℂ) (Submodule.sum_mem _ fun q (_ : q ∈ T) => slice_mem G.2 q.out)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Rewrite using `[fiber_integral μ hUo hUc T hT x]`. Simplify using `[Finset.sum_apply, mul_comm]`.

Use `⟨⟨_, hΨ⟩, fun x => rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero, LinearMap.comp_apply, ← map_sub]`. Use `map_eq_zero_of_fiber μ hbasis L hL _ fun x => ?_` and prove the remaining obligations. Use `show ∫ a, (G.1 (x, a) - (∫ a', G.1 (x, a') ∂μ) * φ₀.1 a) ∂μ = 0`. Rewrite using `[integral_sub (integrable_of_SB μ (fiber_mem G.2 x)) ((integrable_of_SB μ φ₀.2).const_mul _), integral_const_mul, hφ₀, mul_one, sub_self]`.
-/
theorem exists_factor
    (hbasis : ∀ V ∈ 𝓝 (0 : A), ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧ (U : Set A) ⊆ V)
    {M : Type*} [AddCommGroup M] [Module ℂ M] (L : SB (X₀ × A) →ₗ[ℂ] M)
    (hL : ∀ (a : A) (G G' : SB (X₀ × A)), (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L G' = L G) :
    ∃ l₀ : SB X₀ →ₗ[ℂ] M, ∀ G : SB (X₀ × A), ∃ Ψ : SB X₀,
      (∀ x, Ψ.1 x = ∫ a, G.1 (x, a) ∂μ) ∧ L G = l₀ Ψ := by
  obtain ⟨B, hBo, hBc, -⟩ := hbasis Set.univ Filter.univ_mem
  have hpos := real_ne_zero μ hBo hBc
  let φ₀ : SB A := (μ.real (B : Set A) : ℂ)⁻¹ • ⟨_, ind_mem hBo hBc⟩
  have hφ₀ : ∫ a, φ₀.1 a ∂μ = 1 := by
    show ∫ a, (μ.real (B : Set A) : ℂ)⁻¹ * (B : Set A).indicator (fun _ => (1 : ℂ)) a ∂μ = 1
    rw [integral_const_mul, integral_indicator_const _ hBo.measurableSet]
    simp [hpos]
  refine ⟨L ∘ₗ tensL φ₀, fun G => ?_⟩
  obtain ⟨U, hUo, hUc, hinv⟩ := exists_subgroup_invariant hbasis G.2
  obtain ⟨T, hT⟩ := exists_decomp hUo G.2 hinv
  have hΨ : (fun x => ∫ a, G.1 (x, a) ∂μ) ∈ SB X₀ := by
    have := (SB X₀).smul_mem (μ.real (U : Set A) : ℂ)
      (Submodule.sum_mem _ fun q (_ : q ∈ T) => slice_mem G.2 q.out)
    convert this using 1
    funext x
    rw [fiber_integral μ hUo hUc T hT x]
    simp [Finset.sum_apply, mul_comm]
  refine ⟨⟨_, hΨ⟩, fun x => rfl, ?_⟩
  rw [← sub_eq_zero, LinearMap.comp_apply, ← map_sub]
  refine map_eq_zero_of_fiber μ hbasis L hL _ fun x => ?_
  show ∫ a, (G.1 (x, a) - (∫ a', G.1 (x, a') ∂μ) * φ₀.1 a) ∂μ = 0
  rw [integral_sub (integrable_of_SB μ (fiber_mem G.2 x)) ((integrable_of_SB μ φ₀.2).const_mul _),
    integral_const_mul, hφ₀, mul_one, sub_self]

end Meas
end General

section Concrete
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cballSub (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' := add_mem_cball
  neg_mem' := neg_mem_cball

def boxSub (n : Type*) (s : kˣ) : AddSubgroup (n → k) := AddSubgroup.pi Set.univ fun _ => cballSub s

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, boxSub, AddSubgroup.mem_pi, FourierPi.box, Set.mem_pi]`. Both sides reduce to the same expression.
-/
theorem coe_boxSub (n : Type*) (s : kˣ) : (boxSub n s : Set (n → k)) = FourierPi.box n s := by
  ext x
  simp only [SetLike.mem_coe, boxSub, AddSubgroup.mem_pi, FourierPi.box, Set.mem_pi]
  rfl

/- English proof (translation)
Introduce `V hV`. Rewrite `hV` using `[Prod.zero_eq_mk, nhds_prod_eq, Filter.mem_prod_iff]`. Take `⟨t₁, h₁, t₂, h₂, hsub⟩` from `hV`. Take `⟨s₁, hs₁⟩` from `FourierPi.exists_box_subset h₁`. Take `⟨s₂, hs₂⟩` from `FourierPi.exists_box_subset h₂`.

Apply the tactic sequence `refine ⟨(boxSub m₁ s₁).prod (boxSub m₂ s₂), ?_, ?_, ?_⟩ <;> rw [AddSubgroup.coe_prod, coe_boxSub, coe_boxSub]`. Conclude with `(FourierPi.isOpen_box s₁).prod (FourierPi.isOpen_box s₂)`. Conclude with `(FourierPi.isCompact_box s₁).prod (FourierPi.isCompact_box s₂)`. Conclude with `(Set.prod_mono hs₁ hs₂).trans hsub`.
-/
theorem basis_prod (m₁ m₂ : Type*) [Fintype m₁] [Fintype m₂] :
    ∀ V ∈ 𝓝 (0 : (m₁ → k) × (m₂ → k)), ∃ U : AddSubgroup ((m₁ → k) × (m₂ → k)),
      IsOpen (U : Set ((m₁ → k) × (m₂ → k))) ∧ IsCompact (U : Set ((m₁ → k) × (m₂ → k))) ∧
        (U : Set ((m₁ → k) × (m₂ → k))) ⊆ V := by
  intro V hV
  rw [Prod.zero_eq_mk, nhds_prod_eq, Filter.mem_prod_iff] at hV
  obtain ⟨t₁, h₁, t₂, h₂, hsub⟩ := hV
  obtain ⟨s₁, hs₁⟩ := FourierPi.exists_box_subset h₁
  obtain ⟨s₂, hs₂⟩ := FourierPi.exists_box_subset h₂
  refine ⟨(boxSub m₁ s₁).prod (boxSub m₂ s₂), ?_, ?_, ?_⟩ <;> rw [AddSubgroup.coe_prod, coe_boxSub, coe_boxSub]
  · exact (FourierPi.isOpen_box s₁).prod (FourierPi.isOpen_box s₂)
  · exact (FourierPi.isCompact_box s₁).prod (FourierPi.isCompact_box s₂)
  · exact (Set.prod_mono hs₁ hs₂).trans hsub

end Concrete

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ν hν X₀ _ _ _ _ m₁ m₂ _ _ M _ _ L hL`. Use `haveI := secondCountable k`. Use `haveI := t2Space k`. Use `haveI := hν`. Use `haveI : LocallyCompactSpace k := inferInstance`.

Use `haveI : SigmaFinite ν := inferInstance`. Use `haveI : (Measure.pi fun _ : m₁ => ν).IsAddHaarMeasure := inferInstance`. Use `haveI : (Measure.pi fun _ : m₂ => ν).IsAddHaarMeasure := inferInstance`. Take `⟨l₀, hl₀⟩` from `exists_factor ((Measure.pi fun _ : m₁ => ν).prod (Measure.pi fun _ : m₂ => ν)) (basis_prod m₁ m₂) L hL`. Use `⟨l₀, fun G => ?_⟩` and prove the remaining obligations.

Take `⟨Ψ, hΨ, hLG⟩` from `hl₀ G`. Use `⟨Ψ, fun x => ?_, hLG⟩` and prove the remaining obligations. Rewrite using `[hΨ x, integral_prod _ (integrable_of_SB _ (fiber_mem G.2 x))]`.
-/
theorem translation_invariant_factors : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (X₀ : Type) [TopologicalSpace X₀] [T2Space X₀] [LocallyCompactSpace X₀] [TotallyDisconnectedSpace X₀] (m₁ m₂ : Type) [Fintype m₁] [Fintype m₂] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (X₀ × ((m₁ → k) × (m₂ → k))) →ₗ[ℂ] M), (∀ (a : (m₁ → k) × (m₂ → k)) (G G' : SB (X₀ × ((m₁ → k) × (m₂ → k)))), (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L G' = L G) → ∃ l₀ : SB X₀ →ₗ[ℂ] M, ∀ G, ∃ Ψ : SB X₀, (∀ x, Ψ.1 x = ∫ a₁, ∫ a₂, G.1 (x, (a₁, a₂)) ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν)) ∧ L G = l₀ Ψ := by
  intro k _ _ _ _ _ _ ν hν X₀ _ _ _ _ m₁ m₂ _ _ M _ _ L hL
  haveI := secondCountable k
  haveI := t2Space k
  haveI := hν
  haveI : LocallyCompactSpace k := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : (Measure.pi fun _ : m₁ => ν).IsAddHaarMeasure := inferInstance
  haveI : (Measure.pi fun _ : m₂ => ν).IsAddHaarMeasure := inferInstance
  obtain ⟨l₀, hl₀⟩ := exists_factor ((Measure.pi fun _ : m₁ => ν).prod (Measure.pi fun _ : m₂ => ν))
    (basis_prod m₁ m₂) L hL
  refine ⟨l₀, fun G => ?_⟩
  obtain ⟨Ψ, hΨ, hLG⟩ := hl₀ G
  refine ⟨Ψ, fun x => ?_, hLG⟩
  rw [hΨ x, integral_prod _ (integrable_of_SB _ (fiber_mem G.2 x))]

end GlobalTheory.SplitWeil.HaarFactor
