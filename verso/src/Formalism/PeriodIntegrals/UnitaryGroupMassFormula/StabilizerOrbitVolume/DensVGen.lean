import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibFour

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Set Filter
open scoped Pointwise

def IsLCcOn {V : Type} [TopologicalSpace V] (U : Set V) (φ : V → ℝ) : Prop :=
  IsLocallyConstant φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

def HasCOSub (V : Type) [AddGroup V] [TopologicalSpace V] : Prop :=
  ∀ N ∈ 𝓝 (0 : V), ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧
    (Λ : Set V) ⊆ N

section Dens

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

def HasDens (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (φ : V → ℝ) (g : X → ℝ) :
    Prop :=
  Integrable φ μ ∧ Continuous g ∧ ∀ S : Set X, IsCompact S →
    ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν

/- English proof (translation)
Take `⟨i1, c1, e1⟩` from `h₁`. Take `⟨i2, c2, e2⟩` from `h₂`. Use `⟨i1.sub i2, c1.sub c2, fun S hS => ?_⟩` and prove the remaining obligations. Rewrite using `[integral_sub i1.integrableOn i2.integrableOn, integral_sub (c1.continuousOn.integrableOn_compact hS) (c2.continuousOn.integrableOn_compact hS), e1 S hS, e2 S hS]`.
-/
theorem HasDens.sub [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v - φ₂ v) (fun b => g₁ b - g₂ b) := by
  obtain ⟨i1, c1, e1⟩ := h₁
  obtain ⟨i2, c2, e2⟩ := h₂
  refine ⟨i1.sub i2, c1.sub c2, fun S hS => ?_⟩
  rw [integral_sub i1.integrableOn i2.integrableOn,
    integral_sub (c1.continuousOn.integrableOn_compact hS) (c2.continuousOn.integrableOn_compact hS),
    e1 S hS, e2 S hS]

/- English proof (translation)
Take `⟨hi, hc, he⟩` from `h`. Use `⟨hi.const_mul c, continuous_const.mul hc, fun S hS => ?_⟩` and prove the remaining obligations. Rewrite using `[integral_const_mul, integral_const_mul, he S hS]`.
-/
theorem HasDens.const_mul (c : ℝ) {φ : V → ℝ} {g : X → ℝ} (h : HasDens μ f ι ν φ g) :
    HasDens μ f ι ν (fun v => c * φ v) (fun b => c * g b) := by
  obtain ⟨hi, hc, he⟩ := h
  refine ⟨hi.const_mul c, continuous_const.mul hc, fun S hS => ?_⟩
  rw [integral_const_mul, integral_const_mul, he S hS]

/- English proof (translation)
Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`. Establish `hU : {b | D b < D b0 / 2} ∈ 𝓝 b0` using `(isOpen_lt hD continuous_const).mem_nhds (by show D b0 < D b0 / 2; linarith)`. Take `⟨K, hKn, hKU, hKc⟩` from `local_compact_nhds hU`. Establish `hpos : 0 < ν K` using `ν.measure_pos_of_mem_nhds hKn`.

Establish `hfin : ν K < ⊤` using `hKc.measure_lt_top`. Establish `h1 : ∫ b in K, D b ∂ν ≤ ∫ b in K, D b0 / 2 ∂ν` using `setIntegral_mono_on (hD.continuousOn.integrableOn_compact hKc) (continuousOn_const.integrableOn_compact hKc) hKc.measurableSet (fun x hx => le_of_lt (hKU hx))`. Rewrite `h1` using `[setIntegral_const, smul_eq_mul]`. Apply the tactic sequence `try simp only [Measure.real] at h1`. Establish `h2 : 0 < (ν K).toReal` using `ENNReal.toReal_pos hpos.ne' hfin.ne`.

Establish `h3` using `h0 K hKc`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nonneg_of_setIntegral [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] (D : X → ℝ) (hD : Continuous D)
    (h0 : ∀ S, IsCompact S → 0 ≤ ∫ b in S, D b ∂ν) (b0 : X) : 0 ≤ D b0 := by
  by_contra hneg
  push_neg at hneg
  have hU : {b | D b < D b0 / 2} ∈ 𝓝 b0 :=
    (isOpen_lt hD continuous_const).mem_nhds (by show D b0 < D b0 / 2; linarith)
  obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds hU
  have hpos : 0 < ν K := ν.measure_pos_of_mem_nhds hKn
  have hfin : ν K < ⊤ := hKc.measure_lt_top
  have h1 : ∫ b in K, D b ∂ν ≤ ∫ b in K, D b0 / 2 ∂ν :=
    setIntegral_mono_on (hD.continuousOn.integrableOn_compact hKc)
      (continuousOn_const.integrableOn_compact hKc) hKc.measurableSet
      (fun x hx => le_of_lt (hKU hx))
  rw [setIntegral_const, smul_eq_mul] at h1
  try simp only [Measure.real] at h1
  have h2 : 0 < (ν K).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have h3 := h0 K hKc
  nlinarith

/- English proof (translation)
Establish `h` using `h₂.sub h₁`. Establish `hS : ∀ S, IsCompact S → 0 ≤ ∫ x in S, g₂ x - g₁ x ∂ν`. Introduce `S hS`. Rewrite using `[← h.2.2 S hS]`. Conclude with `integral_nonneg fun v => sub_nonneg.mpr (hle v)`.

Establish `key : 0 ≤ g₂ b - g₁ b` using `nonneg_of_setIntegral (fun x => g₂ x - g₁ x) h.2.1 hS b`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem HasDens.le [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
    {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) (hle : ∀ v, φ₁ v ≤ φ₂ v) (b : X) :
    g₁ b ≤ g₂ b := by
  have h := h₂.sub h₁
  have hS : ∀ S, IsCompact S → 0 ≤ ∫ x in S, g₂ x - g₁ x ∂ν := by
    intro S hS
    rw [← h.2.2 S hS]
    exact integral_nonneg fun v => sub_nonneg.mpr (hle v)
  have key : 0 ≤ g₂ b - g₁ b := nonneg_of_setIntegral (fun x => g₂ x - g₁ x) h.2.1 hS b
  linarith

end Dens

section Approx

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

/- English proof (translation)
Use `AddSubgroup.isOpen_of_mem_nhds _ (g := (0 : V)) ?_` and prove the remaining obligations. Establish `h1 : (Λ₀ : Set V) ∈ 𝓝 (0 : V)` using `h₀o.mem_nhds Λ₀.zero_mem`. Establish `h2 : (⋂ i ∈ t, (L i : Set V)) ∈ 𝓝 (0 : V)` using `(Filter.biInter_finset_mem t).2 fun i _ => (hLo i).mem_nhds (L i).zero_mem`. Use `filter_upwards [h1, h2] with x hx1 hx2`. Simplify using `only [Set.mem_iInter, SetLike.mem_coe] at hx1 hx2`.

Simplify using `only [SetLike.mem_coe, AddSubgroup.mem_inf, AddSubgroup.mem_iInf]`. Conclude with `⟨hx1, fun i hi => hx2 i hi⟩`.
-/
theorem isOpen_inf_iInf (Λ₀ : AddSubgroup V) (h₀o : IsOpen (Λ₀ : Set V)) {ι : Type}
    (t : Finset ι) (L : ι → AddSubgroup V) (hLo : ∀ i, IsOpen (L i : Set V)) :
    IsOpen ((Λ₀ ⊓ ⨅ i ∈ t, L i : AddSubgroup V) : Set V) := by
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := (0 : V)) ?_
  have h1 : (Λ₀ : Set V) ∈ 𝓝 (0 : V) := h₀o.mem_nhds Λ₀.zero_mem
  have h2 : (⋂ i ∈ t, (L i : Set V)) ∈ 𝓝 (0 : V) :=
    (Filter.biInter_finset_mem t).2 fun i _ => (hLo i).mem_nhds (L i).zero_mem
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [Set.mem_iInter, SetLike.mem_coe] at hx1 hx2
  simp only [SetLike.mem_coe, AddSubgroup.mem_inf, AddSubgroup.mem_iInf]
  exact ⟨hx1, fun i hi => hx2 i hi⟩

/- English proof (translation)
Establish `hloc : ∀ x : V, ∃ W : AddSubgroup V, IsOpen (W : Set V) ∧ ∀ w ∈ W, |φ (x + w) - φ x| < ε / 2`. Introduce `x`. Establish `hcx : ContinuousAt (fun w => φ (x + w)) 0` using `(hc.comp (continuous_const.add continuous_id)).continuousAt`. Establish `hN : {w | |φ (x + w) - φ x| < ε / 2} ∈ 𝓝 (0 : V)`. Establish `h1` using `hcx.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hε))`.

Use `filter_upwards [h1] with w hw`. Simplify `hw` using `[Real.dist_eq]`. Take `⟨W, hWo, -, hWN⟩` from `hNA _ hN`. Conclude with `⟨W, hWo, fun w hw => hWN hw⟩`. Use `choose W hWo hW using hloc`.

Establish `hUo : ∀ i, IsOpen ((fun y => -i + y) ⁻¹' (W i : Set V))` using `fun i => (hWo i).preimage (continuous_const.add continuous_id)`. Establish `hcov : tsupport φ ⊆ ⋃ i, (fun y => -i + y) ⁻¹' (W i : Set V)`. Introduce `y _`. Use `Set.mem_iUnion.mpr ⟨y, ?_⟩` and prove the remaining obligations. Use `show -y + y ∈ W y`.

Simplify using the standard rewrite rules. Take `⟨t, ht⟩` from `hs.elim_finite_subcover (fun i => (fun y => -i + y) ⁻¹' (W i : Set V)) hUo hcov`. Establish `hΛo` using `isOpen_inf_iInf Λ₀ h₀o t W hWo`. Use `⟨Λ₀ ⊓ ⨅ i ∈ t, W i, hΛo, h₀c.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ hΛo) (SetLike.coe_subset_coe.mpr inf_le_left), inf_le_left, ?_⟩` and prove the remaining obligations. Introduce `x z hz`.

Establish `hz'` using `hz`. Simplify using `only [AddSubgroup.mem_inf, AddSubgroup.mem_iInf] at hz'`. Establish `hzW : ∀ i ∈ t, z ∈ W i` using `hz'.2`. Establish `hzero : ∀ y, y ∉ tsupport φ → φ y = 0` using `fun y hy => by`. Assume the negation of the conclusion as `hne`.

Conclude with `hy (subset_tsupport φ (Function.mem_support.mpr hne))`. Distinguish the cases in `hx : x ∈ ⋃ i ∈ t, (fun y => -i + y) ⁻¹' (W i : Set V)`. Simplify using `only [Set.mem_iUnion] at hx`. Take `⟨i, hi, hxi⟩` from `hx`. Establish `hxi' : -i + x ∈ W i` using `hxi`.

Establish `h1` using `hW i (-i + x) hxi'`. Establish `h2` using `hW i (-i + (x + z)) (by`. Establish `e : -i + (x + z) = (-i + x) + z` using `by abel`. Rewrite using `[e]`. Conclude with `(W i).add_mem hxi' (hzW i hi))`.

Simplify using `only [add_neg_cancel_left] at h1 h2`. Rewrite `h1`, `h2`, the goal using `[abs_lt]`. Apply the tactic sequence `constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]`. Establish `hxz : x + z ∉ ⋃ i ∈ t, (fun y => -i + y) ⁻¹' (W i : Set V)`. Introduce `hc'`.

Apply `hx` to reduce the goal to its premises. Simplify using `only [Set.mem_iUnion] at hc' ⊢`. Take `⟨i, hi, hxi⟩` from `hc'`. Use `⟨i, hi, ?_⟩` and prove the remaining obligations. Establish `hxi' : -i + (x + z) ∈ W i` using `hxi`.

Use `show -i + x ∈ W i`. Establish `e : -i + x = (-i + (x + z)) + -z` using `by abel`. Rewrite using `[e]`. Conclude with `(W i).add_mem hxi' ((W i).neg_mem (hzW i hi))`. Rewrite using `[hzero x (fun h => hx (ht h)), hzero (x + z) (fun h => hxz (ht h))]`.

Simplify using `using hε`.
-/
theorem exists_sub_osc (hNA : HasCOSub V) {φ : V → ℝ} (hc : Continuous φ)
    (hs : HasCompactSupport φ) {ε : ℝ} (hε : 0 < ε) (Λ₀ : AddSubgroup V)
    (h₀o : IsOpen (Λ₀ : Set V)) (h₀c : IsCompact (Λ₀ : Set V)) :
    ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧ Λ ≤ Λ₀ ∧
      ∀ x z, z ∈ Λ → |φ (x + z) - φ x| < ε := by
  have hloc : ∀ x : V, ∃ W : AddSubgroup V, IsOpen (W : Set V) ∧
      ∀ w ∈ W, |φ (x + w) - φ x| < ε / 2 := by
    intro x
    have hcx : ContinuousAt (fun w => φ (x + w)) 0 :=
      (hc.comp (continuous_const.add continuous_id)).continuousAt
    have hN : {w | |φ (x + w) - φ x| < ε / 2} ∈ 𝓝 (0 : V) := by
      have h1 := hcx.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hε))
      filter_upwards [h1] with w hw
      simpa [Real.dist_eq] using hw
    obtain ⟨W, hWo, -, hWN⟩ := hNA _ hN
    exact ⟨W, hWo, fun w hw => hWN hw⟩
  choose W hWo hW using hloc
  have hUo : ∀ i, IsOpen ((fun y => -i + y) ⁻¹' (W i : Set V)) :=
    fun i => (hWo i).preimage (continuous_const.add continuous_id)
  have hcov : tsupport φ ⊆ ⋃ i, (fun y => -i + y) ⁻¹' (W i : Set V) := by
    intro y _
    refine Set.mem_iUnion.mpr ⟨y, ?_⟩
    show -y + y ∈ W y
    simp
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover (fun i => (fun y => -i + y) ⁻¹' (W i : Set V)) hUo hcov
  have hΛo := isOpen_inf_iInf Λ₀ h₀o t W hWo
  refine ⟨Λ₀ ⊓ ⨅ i ∈ t, W i, hΛo,
    h₀c.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ hΛo)
      (SetLike.coe_subset_coe.mpr inf_le_left), inf_le_left, ?_⟩
  intro x z hz
  have hz' := hz
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_iInf] at hz'
  have hzW : ∀ i ∈ t, z ∈ W i := hz'.2
  have hzero : ∀ y, y ∉ tsupport φ → φ y = 0 := fun y hy => by
    by_contra hne
    exact hy (subset_tsupport φ (Function.mem_support.mpr hne))
  by_cases hx : x ∈ ⋃ i ∈ t, (fun y => -i + y) ⁻¹' (W i : Set V)
  · simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    have hxi' : -i + x ∈ W i := hxi
    have h1 := hW i (-i + x) hxi'
    have h2 := hW i (-i + (x + z)) (by
      have e : -i + (x + z) = (-i + x) + z := by abel
      rw [e]
      exact (W i).add_mem hxi' (hzW i hi))
    simp only [add_neg_cancel_left] at h1 h2
    rw [abs_lt] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · have hxz : x + z ∉ ⋃ i ∈ t, (fun y => -i + y) ⁻¹' (W i : Set V) := by
      intro hc'
      apply hx
      simp only [Set.mem_iUnion] at hc' ⊢
      obtain ⟨i, hi, hxi⟩ := hc'
      refine ⟨i, hi, ?_⟩
      have hxi' : -i + (x + z) ∈ W i := hxi
      show -i + x ∈ W i
      have e : -i + x = (-i + (x + z)) + -z := by abel
      rw [e]
      exact (W i).add_mem hxi' ((W i).neg_mem (hzW i hi))
    rw [hzero x (fun h => hx (ht h)), hzero (x + z) (fun h => hxz (ht h))]
    simpa using hε

end Approx

section Main

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]

def cosApx (Λ : AddSubgroup V) (φ : V → ℝ) (x : V) : ℝ := φ ((x : V ⧸ Λ).out)

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [OpensMeasurableSpace V]
  in
/- English proof (translation)
Establish `h : ((((x : V ⧸ Λ).out : V) : V ⧸ Λ)) = (x : V ⧸ Λ)` using `Quotient.out_eq _`. Conclude with `QuotientAddGroup.eq.mp h`.
-/
theorem cosApx_sub_mem (Λ : AddSubgroup V) (x : V) : -((x : V ⧸ Λ).out) + x ∈ Λ := by
  have h : ((((x : V ⧸ Λ).out : V) : V ⧸ Λ)) = (x : V ⧸ Λ) := Quotient.out_eq _
  exact QuotientAddGroup.eq.mp h

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [OpensMeasurableSpace V]
  in
/- English proof (translation)
Establish `e : (y : V ⧸ Λ) = (x : V ⧸ Λ)` using `(QuotientAddGroup.eq.mpr h).symm`. Use `show φ ((y : V ⧸ Λ).out) = φ ((x : V ⧸ Λ).out)`. Rewrite using `[e]`.
-/
theorem cosApx_eq (Λ : AddSubgroup V) (φ : V → ℝ) {x y : V} (h : -x + y ∈ Λ) :
    cosApx Λ φ y = cosApx Λ φ x := by
  have e : (y : V ⧸ Λ) = (x : V ⧸ Λ) := (QuotientAddGroup.eq.mpr h).symm
  show φ ((y : V ⧸ Λ).out) = φ ((x : V ⧸ Λ).out)
  rw [e]

omit [MeasurableSpace V] [OpensMeasurableSpace V] in
/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `hc : Continuous fun y : V => -x + y` using `continuous_const.add continuous_id`. Establish `hm : (fun y : V => -x + y) ⁻¹' (Λ : Set V) ∈ 𝓝 x` using `(hΛ.preimage hc).mem_nhds (by show -x + x ∈ Λ; simp)`. Use `filter_upwards [hm] with y hy`.

Conclude with `cosApx_eq Λ φ hy`.
-/
theorem cosApx_lc (Λ : AddSubgroup V) (hΛ : IsOpen (Λ : Set V)) (φ : V → ℝ) :
    IsLocallyConstant (cosApx Λ φ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : V => -x + y := continuous_const.add continuous_id
  have hm : (fun y : V => -x + y) ⁻¹' (Λ : Set V) ∈ 𝓝 x :=
    (hΛ.preimage hc).mem_nhds (by show -x + x ∈ Λ; simp)
  filter_upwards [hm] with y hy
  exact cosApx_eq Λ φ hy

/- English proof (translation)
Introduce `hLC φ hφ`. Take `⟨hc, hs, hsU⟩` from `hφ`. Take `⟨W, hW, hKW⟩` from `compact_open_separated_add_right hs.isCompact hU hsU`. Take `⟨Λ₀, h₀o, h₀c, h₀W⟩` from `hNA W hW`. Use `set K' : Set V := tsupport φ + (Λ₀ : Set V) with hK'`.

Establish `hcos : ∀ x y, -x + y ∈ Λ₀ → y ∈ K' → x ∈ K'`. Introduce `x y h hy`. Take `⟨k, hk, l, hl, rfl⟩` from `hy`. Conclude with `⟨k, hk, l - (-x + (k + l)), Λ₀.sub_mem hl h, by abel⟩`. Establish `hcos' : ∀ x y, -x + y ∈ Λ₀ → (y ∈ K' ↔ x ∈ K')`.

Introduce `x y h`. Use `⟨hcos x y h, hcos y x ?_⟩` and prove the remaining obligations. Use `Λ₀.neg_mem h` as an intermediate fact. Rewrite `this` using `[neg_add_rev, neg_neg]`. Then use the resulting hypothesis. Establish `hnb : ∀ x : V, {y | -x + y ∈ Λ₀} ∈ 𝓝 x`.

Introduce `x`. Use `(h₀o.preimage (continuous_const.add continuous_id)).mem_nhds ?_` and prove the remaining obligations. Use `show -x + x ∈ Λ₀`. Rewrite using `[neg_add_cancel]`. Conclude with `Λ₀.zero_mem`.

Establish `hK'cl : IsClosed K'`. Rewrite using `[← isOpen_compl_iff, isOpen_iff_mem_nhds]`. Introduce `x hx`. Conclude with `Filter.mem_of_superset (hnb x) fun y hy hyK => hx (hcos x y hy hyK)`. Establish `hK'c : IsCompact K'` using `hs.isCompact.add h₀c`.

Establish `hK'U : K' ⊆ U` using `(Set.add_subset_add subset_rfl h₀W).trans hKW`. Establish `hKK' : tsupport φ ⊆ K'` using `fun x hx => ⟨x, hx, 0, Λ₀.zero_mem, add_zero x⟩`. Establish `hlcc : ∀ ψ : V → ℝ, IsLocallyConstant ψ → Function.support ψ ⊆ K' → IsLCcOn U ψ` using `fun ψ h1 h2 => ⟨h1, hK'c.of_isClosed_subset isClosed_closure (closure_minimal h2 hK'cl), (closure_minimal h2 hK'cl).trans hK'U⟩`. Establish `hdens : ∀ ψ, IsLCcOn U ψ → ∃ g, HasDens μ f ι ν ψ g` using `fun ψ h => by`. Take `⟨g, hg, hS⟩` from `hLC ψ h`.

Conclude with `⟨g, h.1.continuous.integrable_of_hasCompactSupport h.2.1, hg, hS⟩`. Use `set ind : V → ℝ := K'.indicator fun _ => 1 with hind_def`. Establish `hind : IsLCcOn U ind`. Use `hlcc ind ?_ Set.support_indicator_subset` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_exists_open]`.

Introduce `x`. Use `⟨{y | -x + y ∈ Λ₀}, h₀o.preimage (continuous_const.add continuous_id), mem_of_mem_nhds (hnb x), fun y hy => ?_⟩` and prove the remaining obligations. Use `hcos' x y hy` as an intermediate fact. Rewrite using `[hind_def]`. Distinguish the cases in `hx : x ∈ K'`.

Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx)]`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem fun h => hx (this.1 h)]`. Take `⟨g0, hg0⟩` from `hdens ind hind`. Establish `hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1)` using `fun n => by positivity`. Use `choose Λ hΛo hΛc hΛ0 hosc using fun n : ℕ => exists_sub_osc hNA hc hs (hε n) Λ₀ h₀o h₀c`.

Use `set φn : ℕ → V → ℝ := fun n => cosApx (Λ n) φ with hφn_def`. Establish `hφn_close : ∀ n x, |φn n x - φ x| < 1 / ((n : ℝ) + 1)`. Introduce `n x`. Use `hosc n ((x : V ⧸ Λ n).out) _ (cosApx_sub_mem (Λ n) x)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_left]`.

Rewrite using `[abs_sub_comm]`. Conclude with `this`. Establish `hφn_supp : ∀ n, Function.support (φn n) ⊆ K'`. Introduce `n x hx`. Conclude with `⟨_, subset_tsupport φ hx, _, hΛ0 n (cosApx_sub_mem (Λ n) x), add_neg_cancel_left _ x⟩`.

Establish `hφn : ∀ n, IsLCcOn U (φn n)` using `fun n => hlcc _ (cosApx_lc _ (hΛo n) φ) (hφn_supp n)`. Use `choose g hg using fun n => hdens (φn n) (hφn n)`. Establish `hbd : ∀ n x, |φn n x - φ x| ≤ 1 / ((n : ℝ) + 1) * ind x`. Introduce `n x`. Distinguish the cases in `hx : x ∈ K'`.

Rewrite using `[hind_def, Set.indicator_of_mem hx, mul_one]`. Conclude with `(hφn_close n x).le`. Establish `h1 : φn n x = 0`. Assume the negation of the conclusion as `h`. Conclude with `hx (hφn_supp n h)`.

Establish `h2 : φ x = 0` using `image_eq_zero_of_notMem_tsupport fun h => hx (hKK' h)`. Rewrite using `[hind_def, Set.indicator_of_notMem hx, h1, h2]`. Simplify using the standard rewrite rules. Establish `hgg : ∀ n m b, |g n b - g m b| ≤ (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * g0 b`. Introduce `n m b`.

Establish `hA` using `hg0.const_mul (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1))`. Establish `hle : ∀ n m x, φn n x - φn m x ≤ (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * ind x`. Introduce `n m x`. Establish `h1` using `abs_le.1 (hbd n x)`. Establish `h2` using `abs_le.1 (hbd m x)`.

Rewrite using `[add_mul]`. Combine the linear relations using `[h1.1, h1.2, h2.1, h2.2]`. Establish `u1` using `((hg n).sub (hg m)).le hA (hle n m) b`. Establish `hA'` using `hg0.const_mul (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1))`. Establish `u2` using `((hg m).sub (hg n)).le hA' (hle m n) b`.

Use `abs_le.2 ⟨?_, u1⟩` and prove the remaining obligations. Establish `: (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1))` using `add_comm _ _`. Rewrite `u2` using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcauchy : ∀ b, CauchySeq fun n => g n b`.

Introduce `b`. Use `cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 * (1 / ((N : ℝ) + 1)) * |g0 b|) (fun n m N hn hm => ?_) ?_` and prove the remaining obligations. Rewrite using `[Real.dist_eq]`. Establish `hN : (N : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hM : (N : ℝ) ≤ m` using `by exact_mod_cast hm`.

Establish `h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1)` using `one_div_le_one_div_of_le (by positivity) (by linarith)`. Establish `h2 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1)` using `one_div_le_one_div_of_le (by positivity) (by linarith)`. Combine the equalities or inequalities in the displayed calculation. Use `(tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)).mul_const |g0 b|` as an intermediate fact. Rewrite `this` using `[mul_zero, zero_mul]`. Then use the resulting hypothesis.

Use `set G : X → ℝ := fun b => limUnder atTop fun n => g n b with hG_def`. Establish `hlim : ∀ b, Tendsto (fun n => g n b) atTop (𝓝 (G b))` using `fun b => (hcauchy b).tendsto_limUnder`. Establish `hGn : ∀ n b, |G b - g n b| ≤ 1 / ((n : ℝ) + 1) * g0 b`. Introduce `n b`. Establish `ht : Tendsto (fun m => |g m b - g n b|) atTop (𝓝 |G b - g n b|)` using `((hlim b).sub_const _).abs`.

Establish `ht2 : Tendsto (fun m : ℕ => (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * g0 b) atTop (𝓝 ((1 / ((n : ℝ) + 1) + 0) * g0 b))` using `(tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).mul_const _`. Use `le_of_tendsto_of_tendsto' ht ht2 fun m => by` as an intermediate fact. Rewrite using `[abs_sub_comm]`. Conclude with `hgg n m b`. Rewrite `this` using `[add_zero]`. Then use the resulting hypothesis.

Establish `hGc : Continuous G`. Use `TendstoLocallyUniformly.continuous (F := g) (p := atTop) ?_ (Eventually.of_forall fun n => (hg n).2.1).frequently` and prove the remaining obligations. Rewrite using `[Metric.tendstoLocallyUniformly_iff]`. Introduce `ε hεp x`. Use `⟨{y | g0 y < g0 x + 1}, (isOpen_lt hg0.2.1 continuous_const).mem_nhds (by simp), ?_⟩` and prove the remaining obligations.

Establish `ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * (|g0 x| + 1)) atTop (𝓝 0)`. Use `tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (|g0 x| + 1)` as an intermediate fact. Rewrite `this` using `[zero_mul]`. Then use the resulting hypothesis. Use `filter_upwards [ht.eventually (Iio_mem_nhds hεp)] with n hn y hy`. Establish `hy' : g0 y < g0 x + 1` using `hy`.

Establish `hx'` using `le_abs_self (g0 x)`. Rewrite using `[Real.dist_eq]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨G, hGc, fun S hS => ?_⟩` and prove the remaining obligations. Establish `hφi : Integrable φ μ` using `hc.integrable_of_hasCompactSupport hs`.

Establish `hC : ∀ n : ℕ, |∫ v in f ⁻¹' (ι '' S), φ v ∂μ - ∫ b in S, G b ∂ν| ≤ 2 * (1 / ((n : ℝ) + 1)) * |∫ b in S, g0 b ∂ν|`. Introduce `n`. Establish `e1 : |∫ v in f ⁻¹' (ι '' S), φ v ∂μ - ∫ v in f ⁻¹' (ι '' S), φn n v ∂μ| ≤ ∫ v in f ⁻¹' (ι '' S), 1 / ((n : ℝ) + 1) * ind v ∂μ`. Rewrite using `[← integral_sub hφi.integrableOn (hg n).1.integrableOn, ← Real.norm_eq_abs]`. Use `norm_integral_le_of_norm_le (g := fun v => 1 / ((n : ℝ) + 1) * ind v) (hg0.1.const_mul _).integrableOn (ae_of_all _ ?_)` and prove the remaining obligations.

Introduce `x`. Rewrite using `[Real.norm_eq_abs, abs_sub_comm]`. Conclude with `hbd n x`. Establish `e2 : |∫ b in S, g n b ∂ν - ∫ b in S, G b ∂ν| ≤ ∫ b in S, 1 / ((n : ℝ) + 1) * g0 b ∂ν`. Rewrite using `[← integral_sub ((hg n).2.1.continuousOn.integrableOn_compact hS) (hGc.continuousOn.integrableOn_compact hS), ← Real.norm_eq_abs]`.

Use `norm_integral_le_of_norm_le (g := fun b => 1 / ((n : ℝ) + 1) * g0 b) ((continuous_const.mul hg0.2.1).continuousOn.integrableOn_compact hS) (ae_of_all _ ?_)` and prove the remaining obligations. Introduce `b`. Rewrite using `[Real.norm_eq_abs, abs_sub_comm]`. Conclude with `hGn n b`. Rewrite `e1` using `[integral_const_mul, hg0.2.2 S hS]`.

Rewrite `e2` using `[integral_const_mul]`. Rewrite `e1` using `[(hg n).2.2 S hS]`. Establish `h3` using `abs_sub_le (∫ v in f ⁻¹' (ι '' S), φ v ∂μ) (∫ b in S, g n b ∂ν) (∫ b in S, G b ∂ν)`. Establish `h4 : 1 / ((n : ℝ) + 1) * ∫ b in S, g0 b ∂ν ≤ 1 / ((n : ℝ) + 1) * |∫ b in S, g0 b ∂ν|` using `mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.

Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < |∫ v in f ⁻¹' (ι '' S), φ v ∂μ - ∫ b in S, G b ∂ν|` using `abs_pos.2 (sub_ne_zero.2 hne)`. Establish `ht : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1)) * |∫ b in S, g0 b ∂ν|) atTop (𝓝 0)`. Use `(tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)).mul_const |∫ b in S, g0 b ∂ν|` as an intermediate fact. Rewrite `this` using `[mul_zero, zero_mul]`. Then use the resulting hypothesis.

Take `⟨n, hn⟩` from `(ht.eventually (Iio_mem_nhds hpos)).exists`. Conclude with `absurd (hC n) (not_le.2 hn)`.
-/
theorem densApprox_lc (μ : Measure V) [IsFiniteMeasureOnCompacts μ] (f : V → Y) (ι : X → Y)
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] (U : Set V)
    (hU : IsOpen U) (hNA : HasCOSub V) : DensApprox (IsLCcOn U) μ f ι ν U := by
  intro hLC φ hφ
  obtain ⟨hc, hs, hsU⟩ := hφ
  obtain ⟨W, hW, hKW⟩ := compact_open_separated_add_right hs.isCompact hU hsU
  obtain ⟨Λ₀, h₀o, h₀c, h₀W⟩ := hNA W hW
  set K' : Set V := tsupport φ + (Λ₀ : Set V) with hK'
  have hcos : ∀ x y, -x + y ∈ Λ₀ → y ∈ K' → x ∈ K' := by
    intro x y h hy
    obtain ⟨k, hk, l, hl, rfl⟩ := hy
    exact ⟨k, hk, l - (-x + (k + l)), Λ₀.sub_mem hl h, by abel⟩
  have hcos' : ∀ x y, -x + y ∈ Λ₀ → (y ∈ K' ↔ x ∈ K') := by
    intro x y h
    refine ⟨hcos x y h, hcos y x ?_⟩
    have := Λ₀.neg_mem h
    rwa [neg_add_rev, neg_neg] at this
  have hnb : ∀ x : V, {y | -x + y ∈ Λ₀} ∈ 𝓝 x := by
    intro x
    refine (h₀o.preimage (continuous_const.add continuous_id)).mem_nhds ?_
    show -x + x ∈ Λ₀
    rw [neg_add_cancel]
    exact Λ₀.zero_mem
  have hK'cl : IsClosed K' := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    exact Filter.mem_of_superset (hnb x) fun y hy hyK => hx (hcos x y hy hyK)
  have hK'c : IsCompact K' := hs.isCompact.add h₀c
  have hK'U : K' ⊆ U := (Set.add_subset_add subset_rfl h₀W).trans hKW
  have hKK' : tsupport φ ⊆ K' := fun x hx => ⟨x, hx, 0, Λ₀.zero_mem, add_zero x⟩
  have hlcc : ∀ ψ : V → ℝ, IsLocallyConstant ψ → Function.support ψ ⊆ K' → IsLCcOn U ψ :=
    fun ψ h1 h2 => ⟨h1, hK'c.of_isClosed_subset isClosed_closure (closure_minimal h2 hK'cl),
      (closure_minimal h2 hK'cl).trans hK'U⟩
  have hdens : ∀ ψ, IsLCcOn U ψ → ∃ g, HasDens μ f ι ν ψ g := fun ψ h => by
    obtain ⟨g, hg, hS⟩ := hLC ψ h
    exact ⟨g, h.1.continuous.integrable_of_hasCompactSupport h.2.1, hg, hS⟩
  set ind : V → ℝ := K'.indicator fun _ => 1 with hind_def
  have hind : IsLCcOn U ind := by
    refine hlcc ind ?_ Set.support_indicator_subset
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{y | -x + y ∈ Λ₀}, h₀o.preimage (continuous_const.add continuous_id),
      mem_of_mem_nhds (hnb x), fun y hy => ?_⟩
    have := hcos' x y hy
    rw [hind_def]
    by_cases hx : x ∈ K'
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem fun h => hx (this.1 h)]
  obtain ⟨g0, hg0⟩ := hdens ind hind
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose Λ hΛo hΛc hΛ0 hosc using fun n : ℕ => exists_sub_osc hNA hc hs (hε n) Λ₀ h₀o h₀c
  set φn : ℕ → V → ℝ := fun n => cosApx (Λ n) φ with hφn_def
  have hφn_close : ∀ n x, |φn n x - φ x| < 1 / ((n : ℝ) + 1) := by
    intro n x
    have := hosc n ((x : V ⧸ Λ n).out) _ (cosApx_sub_mem (Λ n) x)
    rw [add_neg_cancel_left] at this
    rw [abs_sub_comm]
    exact this
  have hφn_supp : ∀ n, Function.support (φn n) ⊆ K' := by
    intro n x hx
    exact ⟨_, subset_tsupport φ hx, _, hΛ0 n (cosApx_sub_mem (Λ n) x), add_neg_cancel_left _ x⟩
  have hφn : ∀ n, IsLCcOn U (φn n) := fun n => hlcc _ (cosApx_lc _ (hΛo n) φ) (hφn_supp n)
  choose g hg using fun n => hdens (φn n) (hφn n)
  have hbd : ∀ n x, |φn n x - φ x| ≤ 1 / ((n : ℝ) + 1) * ind x := by
    intro n x
    by_cases hx : x ∈ K'
    · rw [hind_def, Set.indicator_of_mem hx, mul_one]
      exact (hφn_close n x).le
    · have h1 : φn n x = 0 := by
        by_contra h
        exact hx (hφn_supp n h)
      have h2 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hKK' h)
      rw [hind_def, Set.indicator_of_notMem hx, h1, h2]
      simp
  have hgg : ∀ n m b, |g n b - g m b| ≤ (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * g0 b := by
    intro n m b
    have hA := hg0.const_mul (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1))
    have hle : ∀ n m x, φn n x - φn m x ≤ (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * ind x := by
      intro n m x
      have h1 := abs_le.1 (hbd n x)
      have h2 := abs_le.1 (hbd m x)
      rw [add_mul]
      linarith [h1.1, h1.2, h2.1, h2.2]
    have u1 := ((hg n).sub (hg m)).le hA (hle n m) b
    have hA' := hg0.const_mul (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1))
    have u2 := ((hg m).sub (hg n)).le hA' (hle m n) b
    refine abs_le.2 ⟨?_, u1⟩
    have : (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) :=
      add_comm _ _
    rw [this] at u2
    linarith
  have hcauchy : ∀ b, CauchySeq fun n => g n b := by
    intro b
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 * (1 / ((N : ℝ) + 1)) * |g0 b|)
      (fun n m N hn hm => ?_) ?_
    · rw [Real.dist_eq]
      have hN : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hM : (N : ℝ) ≤ m := by exact_mod_cast hm
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h2 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      calc |g n b - g m b| ≤ (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * g0 b := hgg n m b
        _ ≤ (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * |g0 b| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
        _ ≤ (1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1)) * |g0 b| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ = 2 * (1 / ((N : ℝ) + 1)) * |g0 b| := by ring
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)).mul_const |g0 b|
      rwa [mul_zero, zero_mul] at this
  set G : X → ℝ := fun b => limUnder atTop fun n => g n b with hG_def
  have hlim : ∀ b, Tendsto (fun n => g n b) atTop (𝓝 (G b)) := fun b =>
    (hcauchy b).tendsto_limUnder
  have hGn : ∀ n b, |G b - g n b| ≤ 1 / ((n : ℝ) + 1) * g0 b := by
    intro n b
    have ht : Tendsto (fun m => |g m b - g n b|) atTop (𝓝 |G b - g n b|) :=
      ((hlim b).sub_const _).abs
    have ht2 : Tendsto (fun m : ℕ => (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * g0 b) atTop
        (𝓝 ((1 / ((n : ℝ) + 1) + 0) * g0 b)) :=
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).mul_const _
    have := le_of_tendsto_of_tendsto' ht ht2 fun m => by
      rw [abs_sub_comm]
      exact hgg n m b
    rwa [add_zero] at this
  have hGc : Continuous G := by
    refine TendstoLocallyUniformly.continuous (F := g) (p := atTop) ?_
      (Eventually.of_forall fun n => (hg n).2.1).frequently
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hεp x
    refine ⟨{y | g0 y < g0 x + 1}, (isOpen_lt hg0.2.1 continuous_const).mem_nhds (by simp), ?_⟩
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * (|g0 x| + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (|g0 x| + 1)
      rwa [zero_mul] at this
    filter_upwards [ht.eventually (Iio_mem_nhds hεp)] with n hn y hy
    have hy' : g0 y < g0 x + 1 := hy
    have hx' := le_abs_self (g0 x)
    rw [Real.dist_eq]
    calc |G y - g n y| ≤ 1 / ((n : ℝ) + 1) * g0 y := hGn n y
      _ ≤ 1 / ((n : ℝ) + 1) * (|g0 x| + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ < ε := hn
  refine ⟨G, hGc, fun S hS => ?_⟩
  have hφi : Integrable φ μ := hc.integrable_of_hasCompactSupport hs
  have hC : ∀ n : ℕ, |∫ v in f ⁻¹' (ι '' S), φ v ∂μ - ∫ b in S, G b ∂ν| ≤
      2 * (1 / ((n : ℝ) + 1)) * |∫ b in S, g0 b ∂ν| := by
    intro n
    have e1 : |∫ v in f ⁻¹' (ι '' S), φ v ∂μ - ∫ v in f ⁻¹' (ι '' S), φn n v ∂μ| ≤
        ∫ v in f ⁻¹' (ι '' S), 1 / ((n : ℝ) + 1) * ind v ∂μ := by
      rw [← integral_sub hφi.integrableOn (hg n).1.integrableOn, ← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (g := fun v => 1 / ((n : ℝ) + 1) * ind v)
        (hg0.1.const_mul _).integrableOn (ae_of_all _ ?_)
      intro x
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hbd n x
    have e2 : |∫ b in S, g n b ∂ν - ∫ b in S, G b ∂ν| ≤ ∫ b in S, 1 / ((n : ℝ) + 1) * g0 b ∂ν := by
      rw [← integral_sub ((hg n).2.1.continuousOn.integrableOn_compact hS)
        (hGc.continuousOn.integrableOn_compact hS), ← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (g := fun b => 1 / ((n : ℝ) + 1) * g0 b)
        ((continuous_const.mul hg0.2.1).continuousOn.integrableOn_compact hS) (ae_of_all _ ?_)
      intro b
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hGn n b
    rw [integral_const_mul, hg0.2.2 S hS] at e1
    rw [integral_const_mul] at e2
    rw [(hg n).2.2 S hS] at e1
    have h3 := abs_sub_le (∫ v in f ⁻¹' (ι '' S), φ v ∂μ) (∫ b in S, g n b ∂ν) (∫ b in S, G b ∂ν)
    have h4 : 1 / ((n : ℝ) + 1) * ∫ b in S, g0 b ∂ν ≤ 1 / ((n : ℝ) + 1) * |∫ b in S, g0 b ∂ν| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    linarith
  by_contra hne
  have hpos : 0 < |∫ v in f ⁻¹' (ι '' S), φ v ∂μ - ∫ b in S, G b ∂ν| :=
    abs_pos.2 (sub_ne_zero.2 hne)
  have ht : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1)) * |∫ b in S, g0 b ∂ν|) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)).mul_const
      |∫ b in S, g0 b ∂ν|
    rwa [mul_zero, zero_mul] at this
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hpos)).exists
  exact absurd (hC n) (not_le.2 hn)

end Main

end PI.VolStabSW
