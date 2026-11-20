import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LCIntegralField

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

def stab (f : X → ℂ) : AddSubgroup X where
  carrier := {v | ∀ y, f (y + v) = f y}
  zero_mem' := fun y => by simp
  add_mem' := by
    intro a b (ha : ∀ y, f (y + a) = f y) (hb : ∀ y, f (y + b) = f y) y
    show f (y + (a + b)) = f y
    rw [← add_assoc, hb, ha]
  neg_mem' := by
    intro a (ha : ∀ y, f (y + a) = f y) y
    show f (y + -a) = f y
    have := ha (y + -a)
    rw [neg_add_cancel_right] at this
    exact this.symm

/- English proof (translation)
Establish `hT : IsCompact (tsupport f)` using `hc`. Use `haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hT`. Establish `hfin : (f '' tsupport f).Finite`. Use `(hf.comp_continuous (continuous_subtype_val : Continuous (Subtype.val : tsupport f → X))).range_finite` as an intermediate fact. Rewrite `this` using `[Set.range_comp, Subtype.range_coe]`. Then use the resulting hypothesis.

Establish `key : ∀ c ∈ f '' tsupport f, c ≠ 0 → ∀ᶠ v in nhds (0 : X), ∀ y, f y = c → f (y + v) = c`. Introduce `c _ hc0`. Establish `hLT : f ⁻¹' {c} ⊆ tsupport f` using `fun y hy => subset_tsupport f (by rw [Function.mem_support, show f y = c from hy]; exact hc0)`. Establish `hLc : IsCompact (f ⁻¹' {c})` using `hT.of_isClosed_subset (isClosed_singleton.preimage hf.continuous) hLT`. Take `⟨V, hV, hKV⟩` from `compact_open_separated_add_right hLc (hf.isOpen_fiber c) subset_rfl`.

Use `filter_upwards [hV] with v hv y hy`. Conclude with `hKV (Set.add_mem_add hy hv)`. Establish `h1 : ∀ᶠ v in nhds (0 : X), ∀ c ∈ f '' tsupport f, c ≠ 0 → ∀ y, f y = c → f (y + v) = c` using `(Filter.eventually_all_finite hfin).2 fun c hc => by`. Distinguish the cases in `h0 : c = 0`. Conclude with `Filter.Eventually.of_forall fun _ h => absurd h0 h`.

Conclude with `(key c hc h0).mono fun v hv _ => hv`. Establish `h2` using `(continuous_neg.tendsto' (0 : X) 0 neg_zero).eventually h1`. Use `AddSubgroup.isOpen_of_mem_nhds (g := 0) _ ?_` and prove the remaining obligations. Use `filter_upwards [h1, h2] with v hv hv'`. Use `show ∀ y, f (y + v) = f y`.

Introduce `y`. Distinguish the cases in `hy : f y = 0`. Assume the negation of the conclusion as `hne`. Establish `hne' : f (y + v) ≠ 0` using `by rw [hy] at hne; exact hne`. Establish `hmem : f (y + v) ∈ f '' tsupport f` using `⟨y + v, subset_tsupport f hne', rfl⟩`.

Use `hv' _ hmem hne' (y + v) rfl` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_right]`. Conclude with `hne this.symm`. Conclude with `hv (f y) ⟨y, subset_tsupport f hy, rfl⟩ hy y rfl`.
-/
theorem isOpen_stab {f : X → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    IsOpen (stab f : Set X) := by
  classical
  have hT : IsCompact (tsupport f) := hc
  haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hT
  have hfin : (f '' tsupport f).Finite := by
    have := (hf.comp_continuous (continuous_subtype_val : Continuous (Subtype.val : tsupport f → X))).range_finite
    rwa [Set.range_comp, Subtype.range_coe] at this
  have key : ∀ c ∈ f '' tsupport f, c ≠ 0 → ∀ᶠ v in nhds (0 : X), ∀ y, f y = c → f (y + v) = c := by
    intro c _ hc0
    have hLT : f ⁻¹' {c} ⊆ tsupport f := fun y hy =>
      subset_tsupport f (by rw [Function.mem_support, show f y = c from hy]; exact hc0)
    have hLc : IsCompact (f ⁻¹' {c}) :=
      hT.of_isClosed_subset (isClosed_singleton.preimage hf.continuous) hLT
    obtain ⟨V, hV, hKV⟩ := compact_open_separated_add_right hLc (hf.isOpen_fiber c) subset_rfl
    filter_upwards [hV] with v hv y hy
    exact hKV (Set.add_mem_add hy hv)
  have h1 : ∀ᶠ v in nhds (0 : X), ∀ c ∈ f '' tsupport f, c ≠ 0 → ∀ y, f y = c → f (y + v) = c :=
    (Filter.eventually_all_finite hfin).2 fun c hc => by
      by_cases h0 : c = 0
      · exact Filter.Eventually.of_forall fun _ h => absurd h0 h
      · exact (key c hc h0).mono fun v hv _ => hv
  have h2 := (continuous_neg.tendsto' (0 : X) 0 neg_zero).eventually h1
  refine AddSubgroup.isOpen_of_mem_nhds (g := 0) _ ?_
  filter_upwards [h1, h2] with v hv hv'
  show ∀ y, f (y + v) = f y
  intro y
  by_cases hy : f y = 0
  · by_contra hne
    have hne' : f (y + v) ≠ 0 := by rw [hy] at hne; exact hne
    have hmem : f (y + v) ∈ f '' tsupport f := ⟨y + v, subset_tsupport f hne', rfl⟩
    have := hv' _ hmem hne' (y + v) rfl
    rw [add_neg_cancel_right] at this
    exact hne this.symm
  · exact hv (f y) ⟨y, subset_tsupport f hy, rfl⟩ hy y rfl

/- English proof (translation)
Rewrite using `[discreteTopology_iff_isOpen_singleton]`. Introduce `c`. Proceed by induction on `c using QuotientAddGroup.induction_on with`. Consider the case `H g`. Establish `hpre : (QuotientAddGroup.mk : X → X ⧸ U) ⁻¹' {(g : X ⧸ U)} = (fun x => -g + x) ⁻¹' (U : Set X)`.

Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]`. Rewrite using `[eq_comm, QuotientAddGroup.eq]`. Rewrite using `[← (QuotientAddGroup.isQuotientMap_mk (N := U)).isOpen_preimage, hpre]`. Conclude with `hU.preimage (continuous_const.add continuous_id)`.
-/
theorem discrete_quot (U : AddSubgroup X) (hU : IsOpen (U : Set X)) : DiscreteTopology (X ⧸ U) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro c
  induction c using QuotientAddGroup.induction_on with
  | H g =>
    have hpre : (QuotientAddGroup.mk : X → X ⧸ U) ⁻¹' {(g : X ⧸ U)} = (fun x => -g + x) ⁻¹' (U : Set X) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
      rw [eq_comm, QuotientAddGroup.eq]
    rw [← (QuotientAddGroup.isQuotientMap_mk (N := U)).isOpen_preimage, hpre]
    exact hU.preimage (continuous_const.add continuous_id)

/- English proof (translation)
Use `haveI := discrete_quot U hU`. Establish `hfin : ((QuotientAddGroup.mk : X → X ⧸ U) '' tsupport g).Finite` using `(hc.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete`. Use `set T := hfin.toFinset with hT`. Establish `hind : ∀ (c : X ⧸ U) y, (Quotient.out c : X) = (Quotient.out c : X) → (-(Quotient.out c) + y ∈ U ↔ c = (y : X ⧸ U))`. Introduce `c y _`.

Rewrite using `[← QuotientAddGroup.eq, QuotientAddGroup.out_eq']`. Establish `hdec : g = fun y => ∑ c ∈ T, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator (fun _ => g (Quotient.out c)) y`. Use function extensionality and compare the values at `y`. Establish `key : ∀ c : X ⧸ U, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator (fun _ => g (Quotient.out c)) y = if c = (y : X ⧸ U) then g y else 0`. Introduce `c`.

Distinguish the cases in `h : c = (y : X ⧸ U)`. Rewrite using `[if_pos h, Set.indicator_of_mem (show y ∈ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from (hind c y rfl).2 h)]`. Establish `hm : -(Quotient.out c) + y ∈ U` using `(hind c y rfl).2 h`. Use `hg _ hm (Quotient.out c)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_left]`.

Conclude with `this.symm`. Rewrite using `[if_neg h, Set.indicator_of_notMem (show y ∉ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from fun hm => h ((hind c y rfl).1 hm))]`. Simplify using `only [key]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with hmem`.

Both sides reduce to the same expression. Rewrite `hmem` using `[hT, Set.Finite.mem_toFinset]`. Conclude with `image_eq_zero_of_notMem_tsupport (fun hs => hmem ⟨y, hs, rfl⟩)`. Establish `hmeas : ∀ c : X ⧸ U, MeasurableSet ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X))` using `fun c => (hU.preimage (continuous_const.add continuous_id)).measurableSet`. Establish `hvol : ∀ c : X ⧸ U, μ ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)) = μ U` using `fun c => measure_preimage_add μ _ _`.

Use `⟨T.image Quotient.out, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_image (fun a _ b _ h => Quotient.out_injective h)]`. Use `conv_lhs => rw [hdec]`. Rewrite using `[integral_finset_sum]`. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[integral_indicator_const _ (hmeas c)]`. Simplify using `only [Measure.real, hvol, Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `c _`.

Use `(integrable_indicator_iff (hmeas c)).2 (integrableOn_const ?_)` and prove the remaining obligations. Rewrite using `[hvol]`. Conclude with `hUfin`.
-/
theorem integral_eq_sum [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableAdd X] (μ : Measure X) [μ.IsAddLeftInvariant]
    (U : AddSubgroup X) (hU : IsOpen (U : Set X)) (hUfin : μ U ≠ ⊤) (g : X → ℂ)
    (hg : ∀ u ∈ U, ∀ y, g (y + u) = g y) (hc : HasCompactSupport g) :
    ∃ s : Finset X, ∫ y, g y ∂μ = (∑ γ ∈ s, g γ) * ((μ.real (U : Set X) : ℝ) : ℂ) := by
  classical
  haveI := discrete_quot U hU
  have hfin : ((QuotientAddGroup.mk : X → X ⧸ U) '' tsupport g).Finite :=
    (hc.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T := hfin.toFinset with hT
  have hind : ∀ (c : X ⧸ U) y, (Quotient.out c : X) = (Quotient.out c : X) →
      (-(Quotient.out c) + y ∈ U ↔ c = (y : X ⧸ U)) := by
    intro c y _
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
  have hdec : g = fun y => ∑ c ∈ T,
      ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator (fun _ => g (Quotient.out c)) y := by
    funext y
    have key : ∀ c : X ⧸ U, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator
        (fun _ => g (Quotient.out c)) y = if c = (y : X ⧸ U) then g y else 0 := by
      intro c
      by_cases h : c = (y : X ⧸ U)
      · rw [if_pos h, Set.indicator_of_mem (show y ∈ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from (hind c y rfl).2 h)]
        have hm : -(Quotient.out c) + y ∈ U := (hind c y rfl).2 h
        have := hg _ hm (Quotient.out c)
        rw [add_neg_cancel_left] at this
        exact this.symm
      · rw [if_neg h, Set.indicator_of_notMem (show y ∉ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from fun hm => h ((hind c y rfl).1 hm))]
    simp only [key]
    rw [Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · rw [hT, Set.Finite.mem_toFinset] at hmem
      exact image_eq_zero_of_notMem_tsupport (fun hs => hmem ⟨y, hs, rfl⟩)
  have hmeas : ∀ c : X ⧸ U, MeasurableSet ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)) := fun c =>
    (hU.preimage (continuous_const.add continuous_id)).measurableSet
  have hvol : ∀ c : X ⧸ U, μ ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)) = μ U := fun c =>
    measure_preimage_add μ _ _
  refine ⟨T.image Quotient.out, ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => Quotient.out_injective h)]
  conv_lhs => rw [hdec]
  rw [integral_finset_sum]
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_indicator_const _ (hmeas c)]
    simp only [Measure.real, hvol, Complex.real_smul]
    ring
  · intro c _
    refine (integrable_indicator_iff (hmeas c)).2 (integrableOn_const ?_)
    rw [hvol]; exact hUfin

/- English proof (translation)
Use `set h : X → ℂ := H.indicator (fun _ => 1) with hh`. Establish `hloc : IsLocallyConstant h`. Use `(IsLocallyConstant.iff_exists_open _).2 fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ H`. Conclude with `⟨H, hHo, hx, fun y hy => by rw [hh, Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩`.

Conclude with `⟨Hᶜ, hHc.isClosed.isOpen_compl, hx, fun y hy => by`. Rewrite using `[hh, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩`. Establish `hch : HasCompactSupport h` using `HasCompactSupport.intro hHc fun x hx => Set.indicator_of_notMem hx _`. Use `set U := stab f ⊓ stab h with hU`. Establish `hUo : IsOpen (U : Set X)`.

Rewrite using `[hU, AddSubgroup.coe_inf]`. Conclude with `(isOpen_stab hf hc).inter (isOpen_stab hloc hch)`. Establish `hUH : (U : Set X) ⊆ H`. Introduce `u hu`. Establish `h1` using `(AddSubgroup.mem_inf.1 hu).2 0`.

Rewrite `h1` using `[zero_add]`. Assume the negation of the conclusion as `hn`. Rewrite `h1` using `[hh, Set.indicator_of_notMem hn, Set.indicator_of_mem hH0]`. Conclude with `zero_ne_one h1`. Establish `hUfin : μ U ≠ ⊤` using `ne_top_of_le_ne_top (by rw [hμH]; exact ENNReal.one_ne_top) (measure_mono hUH)`.

Take `⟨s, hs⟩` from `integral_eq_sum μ U hUo hUfin f (fun u hu => (AddSubgroup.mem_inf.1 hu).1) hc`. Take `⟨s', hs'⟩` from `integral_eq_sum μ U hUo hUfin h (fun u hu => (AddSubgroup.mem_inf.1 hu).2) hch`. Establish `hint : ∫ y, h y ∂μ = 1`. Rewrite using `[hh, integral_indicator_const _ hHo.measurableSet]`. Simplify using `[Measure.real, hμH]`.

Rewrite `hs'` using `[hint]`. Establish `hr` using `eq_inv_of_mul_eq_one_right hs'.symm`. Rewrite using `[hs, hr, ← RingHom.coe_fieldRange]`. Establish `hv' : ∀ e, f e ∈ σ.fieldRange` using `fun e => by rw [← SetLike.mem_coe, RingHom.coe_fieldRange]; exact hv e`. Establish `hh' : ∀ e, h e ∈ σ.fieldRange` using `fun e => by`.

Rewrite using `[hh, Set.indicator_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Conclude with `mul_mem (sum_mem fun γ _ => hv' γ) (inv_mem (sum_mem fun γ _ => hh' γ))`.
-/
theorem integral_mem_range [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableAdd X] [T2Space X]
    (μ : Measure X) [μ.IsAddLeftInvariant] (H : Set X) (hHo : IsOpen H) (hHc : IsCompact H) (hH0 : (0 : X) ∈ H)
    (hμH : μ H = 1) {K : Type} [Field K] (σ : K →+* ℂ) (f : X → ℂ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) (hv : ∀ e, f e ∈ Set.range σ) : ∫ e, f e ∂μ ∈ Set.range σ := by
  classical
  set h : X → ℂ := H.indicator (fun _ => 1) with hh
  have hloc : IsLocallyConstant h := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
    by_cases hx : x ∈ H
    · exact ⟨H, hHo, hx, fun y hy => by rw [hh, Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
    · exact ⟨Hᶜ, hHc.isClosed.isOpen_compl, hx, fun y hy => by
        rw [hh, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  have hch : HasCompactSupport h := HasCompactSupport.intro hHc fun x hx => Set.indicator_of_notMem hx _
  set U := stab f ⊓ stab h with hU
  have hUo : IsOpen (U : Set X) := by
    rw [hU, AddSubgroup.coe_inf]; exact (isOpen_stab hf hc).inter (isOpen_stab hloc hch)
  have hUH : (U : Set X) ⊆ H := by
    intro u hu
    have h1 := (AddSubgroup.mem_inf.1 hu).2 0
    rw [zero_add] at h1
    by_contra hn
    rw [hh, Set.indicator_of_notMem hn, Set.indicator_of_mem hH0] at h1
    exact zero_ne_one h1
  have hUfin : μ U ≠ ⊤ := ne_top_of_le_ne_top (by rw [hμH]; exact ENNReal.one_ne_top) (measure_mono hUH)
  obtain ⟨s, hs⟩ := integral_eq_sum μ U hUo hUfin f (fun u hu => (AddSubgroup.mem_inf.1 hu).1) hc
  obtain ⟨s', hs'⟩ := integral_eq_sum μ U hUo hUfin h (fun u hu => (AddSubgroup.mem_inf.1 hu).2) hch
  have hint : ∫ y, h y ∂μ = 1 := by
    rw [hh, integral_indicator_const _ hHo.measurableSet]
    simp [Measure.real, hμH]
  rw [hint] at hs'
  have hr := eq_inv_of_mul_eq_one_right hs'.symm
  rw [hs, hr, ← RingHom.coe_fieldRange]
  have hv' : ∀ e, f e ∈ σ.fieldRange := fun e => by rw [← SetLike.mem_coe, RingHom.coe_fieldRange]; exact hv e
  have hh' : ∀ e, h e ∈ σ.fieldRange := fun e => by
    rw [hh, Set.indicator_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  exact mul_mem (sum_mem fun γ _ => hv' γ) (inv_mem (sum_mem fun γ _ => hh' γ))

end GlobalTheory.LCIntegralField

namespace GlobalTheory.LCIntegralField
open GlobalTheory.FunObj ValuativeRel

/- English proof (translation)
Introduce `k _ _ _ _ _ _ G ν hν K _ σ f hf hc hv`. Take `⟨_, _⟩` from `Model.secondCountable_and_t2_local_field (k := k)`. Use `haveI := hν.1`. Use `haveI : (varsVol G ν).IsAddLeftInvariant := by unfold varsVol; infer_instance`. Use `integral_mem_range (varsVol G ν) (Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k)) ?_ ?_ ?_ ?_ σ f hf hc hv` and prove the remaining obligations.

Conclude with `isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => Model.isOpen_int`. Conclude with `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1`. Conclude with `fun _ _ _ _ => zero_mem _`. Simplify using `[varsVol, Measure.pi_pi, hν.2]`.
-/
theorem integral_vars_mem_range : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {G : GlobalTheory.SplitFlip.Grid k} (ν : MeasureTheory.Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ {K : Type} [Field K] (σ : K →+* ℂ) (f : Vars G → ℂ), IsLocallyConstant f → HasCompactSupport f → (∀ e, f e ∈ Set.range σ) → ∫ e, f e ∂(varsVol G ν) ∈ Set.range σ := by
  intro k _ _ _ _ _ _ G ν hν K _ σ f hf hc hv
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI := hν.1
  haveI : (varsVol G ν).IsAddLeftInvariant := by unfold varsVol; infer_instance
  refine integral_mem_range (varsVol G ν) (Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k)) ?_ ?_ ?_ ?_
    σ f hf hc hv
  · exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => Model.isOpen_int
  · exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  · exact fun _ _ _ _ => zero_mem _
  · simp [varsVol, Measure.pi_pi, hν.2]

end GlobalTheory.LCIntegralField
