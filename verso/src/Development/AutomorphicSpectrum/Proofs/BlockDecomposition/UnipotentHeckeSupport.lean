import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableT2LocalField

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal Topology

namespace GlobalTheory.CompanionTheory.QuotU

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def coset (U : Subgroup G) (r : G) : Set G := {x | r⁻¹ * x ∈ U}

/- English proof (translation)
The claim follows from `hU.preimage (continuous_const.mul continuous_id)`.
-/
theorem isOpen_coset {U : Subgroup G} (hU : IsOpen (U : Set G)) (r : G) : IsOpen (coset U r) :=
  hU.preimage (continuous_const.mul continuous_id)

/- English proof (translation)
Simplify using `[coset, U.one_mem]`.
-/
theorem mem_coset_self (U : Subgroup G) (r : G) : r ∈ coset U r := by
  simp [coset, U.one_mem]

def conjSet (H U : Subgroup G) (r : G) : Set H := {h | r⁻¹ * (h : G) * r ∈ U}

/- English proof (translation)
The claim follows from `hU.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)`.
-/
theorem isOpen_conjSet {H U : Subgroup G} (hU : IsOpen (U : Set G)) (r : G) :
    IsOpen (conjSet H U r) :=
  hU.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)

/- English proof (translation)
Simplify using `[conjSet, U.one_mem]`.
-/
theorem one_mem_conjSet (H U : Subgroup G) (r : G) : (1 : H) ∈ conjSet H U r := by
  simp [conjSet, U.one_mem]

/- English proof (translation)
Establish `hK : IsCompact ((fun u => r * u * r⁻¹) '' (U : Set G))` using `hUc.image (by fun_prop)`. Establish `hs : conjSet H U r = Subtype.val ⁻¹' ((fun u => r * u * r⁻¹) '' (U : Set G))`. Use extensionality with `h`. Prove the components needed by the constructor for the conclusion. Introduce `hh`.

Conclude with `⟨_, hh, by group⟩`. Introduce and unpack `⟨u, hu, e⟩`. Establish `e' : r⁻¹ * (h : G) * r = u`. Establish `e2 : r * u * r⁻¹ = (h : G)` using `e`. Rewrite using `[← e2]`.

Use `group`. Use `show r⁻¹ * (h : G) * r ∈ U`. Rewrite using `[e']`. Conclude with `hu`. Rewrite using `[hs]`.

Conclude with `hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK`.
-/
theorem isCompact_conjSet {H U : Subgroup G} (hUc : IsCompact (U : Set G))
    (hH : IsClosed (H : Set G)) (r : G) : IsCompact (conjSet H U r) := by
  have hK : IsCompact ((fun u => r * u * r⁻¹) '' (U : Set G)) :=
    hUc.image (by fun_prop)
  have hs : conjSet H U r = Subtype.val ⁻¹' ((fun u => r * u * r⁻¹) '' (U : Set G)) := by
    ext h
    constructor
    · intro hh
      exact ⟨_, hh, by group⟩
    · rintro ⟨u, hu, e⟩
      have e' : r⁻¹ * (h : G) * r = u := by
        have e2 : r * u * r⁻¹ = (h : G) := e
        rw [← e2]; group
      show r⁻¹ * (h : G) * r ∈ U
      rw [e']; exact hu
  rw [hs]
  exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK

/- English proof (translation)
Establish `h1 : r⁻¹ * x ∈ U` using `hx`. Establish `h2 : r'⁻¹ * x ∈ U` using `hx'`. Use `huniq r hr r' hr' ⟨1, H.one_mem, (r⁻¹ * x) * (r'⁻¹ * x)⁻¹, U.mul_mem h1 (U.inv_mem h2), by group⟩` and prove the remaining obligations.
-/
theorem rep_eq_of_mem {H U : Subgroup G} {Rp : Set G}
    (huniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r')
    {r r' x : G} (hr : r ∈ Rp) (hr' : r' ∈ Rp) (hx : x ∈ coset U r) (hx' : x ∈ coset U r') :
    r = r' := by
  have h1 : r⁻¹ * x ∈ U := hx
  have h2 : r'⁻¹ * x ∈ U := hx'
  refine huniq r hr r' hr' ⟨1, H.one_mem, (r⁻¹ * x) * (r'⁻¹ * x)⁻¹,
    U.mul_mem h1 (U.inv_mem h2), by group⟩

/- English proof (translation)
Establish `hd : Rp.PairwiseDisjoint (coset U)`. Introduce `r hr r' hr' hne`. Use `Set.disjoint_left.mpr fun x hx hx' => hne ?_` and prove the remaining obligations. Conclude with `rep_eq_of_mem huniq hr hr' hx hx'`. Conclude with `(hd.countable_of_isOpen (fun r _ => isOpen_coset hU r) (fun r _ => ⟨r, mem_coset_self U r⟩)).to_subtype`.
-/
theorem countable_reps [SecondCountableTopology G] {H U : Subgroup G} {Rp : Set G}
    (hU : IsOpen (U : Set G))
    (huniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r') :
    Countable Rp := by
  have hd : Rp.PairwiseDisjoint (coset U) := by
    intro r hr r' hr' hne
    refine Set.disjoint_left.mpr fun x hx hx' => hne ?_
    exact rep_eq_of_mem huniq hr hr' hx hx'
  exact (hd.countable_of_isOpen (fun r _ => isOpen_coset hU r)
    (fun r _ => ⟨r, mem_coset_self U r⟩)).to_subtype

variable [MeasurableSpace G] [BorelSpace G]

noncomputable def rho {H : Subgroup G} (μH : Measure H) (U : Subgroup G) (Rp : Set G) (g : G) :
    ℝ≥0∞ :=
  ∑' r : Rp, (coset U (r : G)).indicator (fun _ => (μH (conjSet H U r))⁻¹) g

/- English proof (translation)
Rewrite using `[rho, tsum_eq_single (⟨r, hr⟩ : Rp)]`. Conclude with `Set.indicator_of_mem hx _`. Introduce `r' hne`. Use `Set.indicator_of_notMem (fun hx' => hne ?_) _` and prove the remaining obligations. Conclude with `Subtype.ext (rep_eq_of_mem huniq r'.2 hr hx' hx)`.
-/
theorem rho_of_mem {H U : Subgroup G} {μH : Measure H} {Rp : Set G}
    (huniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r')
    {r x : G} (hr : r ∈ Rp) (hx : x ∈ coset U r) :
    rho μH U Rp x = (μH (conjSet H U r))⁻¹ := by
  rw [rho, tsum_eq_single (⟨r, hr⟩ : Rp)]
  · exact Set.indicator_of_mem hx _
  · intro r' hne
    refine Set.indicator_of_notMem (fun hx' => hne ?_) _
    exact Subtype.ext (rep_eq_of_mem huniq r'.2 hr hx' hx)

/- English proof (translation)
Rewrite using `[rho]`. Use `tsum_zero with r` and compare the differences between its conclusion and the goal. Conclude with `Set.indicator_of_notMem (hx r r.2) _`.
-/
theorem rho_of_notMem {H U : Subgroup G} {μH : Measure H} {Rp : Set G} {x : G}
    (hx : ∀ r ∈ Rp, x ∉ coset U r) : rho μH U Rp x = 0 := by
  rw [rho]
  convert tsum_zero with r
  exact Set.indicator_of_notMem (hx r r.2) _

/- English proof (translation)
Use `Measurable.ennreal_tsum fun r => ?_` and prove the remaining obligations. Conclude with `measurable_const.indicator (isOpen_coset hU (r : G)).measurableSet`.
-/
theorem measurable_rho {H U : Subgroup G} {μH : Measure H} {Rp : Set G} [Countable Rp]
    (hU : IsOpen (U : Set G)) : Measurable (rho μH U Rp) := by
  refine Measurable.ennreal_tsum fun r => ?_
  exact measurable_const.indicator (isOpen_coset hU (r : G)).measurableSet

/- English proof (translation)
Use `haveI : Countable Rp := countable_reps hU huniq`. Use `⟨measurable_rho hU, fun g => ?_⟩` and prove the remaining obligations. Take `⟨r, hr, h0, hh0, κ, hκ, rfl⟩` from `hcov g`. Establish `hpos : μH (conjSet H U r) ≠ 0` using `((isOpen_conjSet hU r).measure_pos μH ⟨1, one_mem_conjSet H U r⟩).ne'`. Establish `htop : μH (conjSet H U r) ≠ ∞` using `(isCompact_conjSet hUc hH r).measure_lt_top.ne`.

Establish `hiff : ∀ h : H, (h : G) * (h0 * r * κ) ∈ coset U r ↔ (⟨h0, hh0⟩ * h : H) ∈ conjSet H U r`. Introduce `h`. Establish `e : r⁻¹ * ((h : G) * (h0 * r * κ)) = (r⁻¹ * (h0 * (h : G)) * r) * κ`. Rewrite using `[show (h : G) * (h0 * r * κ) = ((h : G) * h0) * r * κ by group, hcomm _ h.2 _ hh0]`. Use `group`.

Use `show r⁻¹ * ((h : G) * (h0 * r * κ)) ∈ U ↔ r⁻¹ * (h0 * (h : G)) * r ∈ U`. Rewrite using `[e]`. Conclude with `U.mul_mem_cancel_right hκ`. Establish `hS : (fun h : H => rho μH U Rp ((h : G) * (h0 * r * κ))) = ((fun h : H => (⟨h0, hh0⟩ : H) * h) ⁻¹' conjSet H U r).indicator (fun _ => (μH (conjSet H U r))⁻¹)`. Use function extensionality and compare the values at `h`.

Distinguish the cases in `hm : (⟨h0, hh0⟩ * h : H) ∈ conjSet H U r`. Rewrite using `[Set.indicator_of_mem (show h ∈ _ from hm)]`. Conclude with `rho_of_mem huniq hr ((hiff h).mpr hm)`. Rewrite using `[Set.indicator_of_notMem (show h ∉ _ from hm)]`. Use `rho_of_notMem fun r' hr' hx => hm ((hiff h).mp ?_)` and prove the remaining obligations.

Establish `hu : r'⁻¹ * ((h : G) * (h0 * r * κ)) ∈ U` using `hx`. Use `huniq r hr r' hr' ⟨(h : G) * h0, H.mul_mem h.2 hh0, κ * (r'⁻¹ * ((h : G) * (h0 * r * κ)))⁻¹, U.mul_mem hκ (U.inv_mem hu), by group⟩` as an intermediate fact. Rewrite `hx` using `[← this]`. Conclude with `hx`. Establish `hmeas : MeasurableSet ((fun h : H => (⟨h0, hh0⟩ : H) * h) ⁻¹' conjSet H U r)` using `((isOpen_conjSet hU r).preimage (continuous_const.mul continuous_id)).measurableSet`.

Rewrite using `[hS, lintegral_indicator_const hmeas, measure_preimage_mul]`. Conclude with `ENNReal.inv_mul_cancel hpos htop`.
-/
theorem rho_isQuotNormaliser [SecondCountableTopology G] {H U : Subgroup G} {μH : Measure H}
    [μH.IsHaarMeasure] {Rp : Set G}
    (hU : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G)) (hH : IsClosed (H : Set G))
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hcov : ∀ g, ∃ r ∈ Rp, ∃ h ∈ H, ∃ κ ∈ U, g = h * r * κ)
    (huniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r') :
    IsQuotNormaliser H μH (rho μH U Rp) := by
  haveI : Countable Rp := countable_reps hU huniq
  refine ⟨measurable_rho hU, fun g => ?_⟩
  obtain ⟨r, hr, h0, hh0, κ, hκ, rfl⟩ := hcov g
  have hpos : μH (conjSet H U r) ≠ 0 :=
    ((isOpen_conjSet hU r).measure_pos μH ⟨1, one_mem_conjSet H U r⟩).ne'
  have htop : μH (conjSet H U r) ≠ ∞ := (isCompact_conjSet hUc hH r).measure_lt_top.ne
  have hiff : ∀ h : H, (h : G) * (h0 * r * κ) ∈ coset U r ↔
      (⟨h0, hh0⟩ * h : H) ∈ conjSet H U r := by
    intro h
    have e : r⁻¹ * ((h : G) * (h0 * r * κ)) = (r⁻¹ * (h0 * (h : G)) * r) * κ := by
      rw [show (h : G) * (h0 * r * κ) = ((h : G) * h0) * r * κ by group, hcomm _ h.2 _ hh0]
      group
    show r⁻¹ * ((h : G) * (h0 * r * κ)) ∈ U ↔ r⁻¹ * (h0 * (h : G)) * r ∈ U
    rw [e]
    exact U.mul_mem_cancel_right hκ
  have hS : (fun h : H => rho μH U Rp ((h : G) * (h0 * r * κ))) =
      ((fun h : H => (⟨h0, hh0⟩ : H) * h) ⁻¹' conjSet H U r).indicator
        (fun _ => (μH (conjSet H U r))⁻¹) := by
    funext h
    by_cases hm : (⟨h0, hh0⟩ * h : H) ∈ conjSet H U r
    · rw [Set.indicator_of_mem (show h ∈ _ from hm)]
      exact rho_of_mem huniq hr ((hiff h).mpr hm)
    · rw [Set.indicator_of_notMem (show h ∉ _ from hm)]
      refine rho_of_notMem fun r' hr' hx => hm ((hiff h).mp ?_)
      have hu : r'⁻¹ * ((h : G) * (h0 * r * κ)) ∈ U := hx
      have := huniq r hr r' hr' ⟨(h : G) * h0, H.mul_mem h.2 hh0,
        κ * (r'⁻¹ * ((h : G) * (h0 * r * κ)))⁻¹, U.mul_mem hκ (U.inv_mem hu), by group⟩
      rw [← this] at hx; exact hx
  have hmeas : MeasurableSet ((fun h : H => (⟨h0, hh0⟩ : H) * h) ⁻¹' conjSet H U r) :=
    ((isOpen_conjSet hU r).preimage (continuous_const.mul continuous_id)).measurableSet
  rw [hS, lintegral_indicator_const hmeas, measure_preimage_mul]
  exact ENNReal.inv_mul_cancel hpos htop

/- English proof (translation)
Introduce `s _`. Use `IsOpen.measurableSet (isOpen_iff_mem_nhds.mpr fun x hx => ?_)` and prove the remaining obligations. Use `Filter.mem_of_superset ((isOpen_coset hU x).mem_nhds (mem_coset_self U x)) ?_` and prove the remaining obligations. Introduce `y hy`. Establish `: Fn (x * (x⁻¹ * y)) = Fn x` using `hFU x _ hy`.

Rewrite `this` using `[mul_inv_cancel_left]`. Use `show Fn y ∈ s`. Rewrite using `[this]`. Conclude with `hx`.
-/
theorem measurable_of_right_invariant {U : Subgroup G} (hU : IsOpen (U : Set G))
    {Fn : G → ℝ≥0∞} (hFU : ∀ g, ∀ κ ∈ U, Fn (g * κ) = Fn g) : Measurable Fn := by
  intro s _
  refine IsOpen.measurableSet (isOpen_iff_mem_nhds.mpr fun x hx => ?_)
  refine Filter.mem_of_superset ((isOpen_coset hU x).mem_nhds (mem_coset_self U x)) ?_
  intro y hy
  have : Fn (x * (x⁻¹ * y)) = Fn x := hFU x _ hy
  rw [mul_inv_cancel_left] at this
  show Fn y ∈ s
  rw [this]; exact hx

/- English proof (translation)
Use `haveI : LocallyCompactSpace G := hUc.locallyCompactSpace_of_mem_nhds_of_group (hU.mem_nhds U.one_mem)`. Use `haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology H := Topology.IsInducing.subtypeVal.secondCountableTopology`. Use `haveI : Countable Rp := countable_reps hU huniq`. Use `haveI : μH.IsInvInvariant := by`.

Use `letI : CommGroup H := { (inferInstance : Group H) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }`. Use `haveI : μH.Regular := inferInstance`. Conclude with `Measure.IsHaarMeasure.isInvInvariant_of_regular μH`. Establish `hFm : Measurable Fn` using `measurable_of_right_invariant hU hFU`. Rewrite using `[quotLIntegral_eq hFm hFH (rho_isQuotNormaliser hU hUc hH hcomm hcov huniq)]`.

Establish `hpt : ∀ g, Fn g * rho μH U Rp g = ∑' r : Rp, (coset U (r : G)).indicator (fun _ => Fn r * (μH (conjSet H U r))⁻¹) g`. Introduce `g`. Rewrite using `[rho, ← ENNReal.tsum_mul_left]`. Use `tsum_congr fun r => ?_` and prove the remaining obligations. Distinguish the cases in `hg : g ∈ coset U (r : G)`.

Establish `e : Fn ((r : G) * ((r : G)⁻¹ * g)) = Fn r` using `hFU _ _ hg`. Rewrite `e` using `[mul_inv_cancel_left]`. Rewrite using `[Set.indicator_of_mem hg, Set.indicator_of_mem hg, e]`. Rewrite using `[Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, mul_zero]`. Rewrite using `[lintegral_congr hpt, lintegral_tsum]`.

Use `tsum_congr fun r => ?_` and prove the remaining obligations. Establish `hms : MeasurableSet (coset U (r : G))` using `(isOpen_coset hU (r : G)).measurableSet`. Establish `hvol : μG (coset U (r : G)) = μG (U : Set G)` using `measure_preimage_mul μG (r : G)⁻¹ (U : Set G)`. Rewrite using `[lintegral_indicator_const hms, hvol, div_eq_mul_inv, mul_right_comm]`. Both sides reduce to the same expression.

Introduce `r`. Conclude with `(measurable_const.indicator (isOpen_coset hU (r : G)).measurableSet).aemeasurable`.
-/
theorem quotLIntegral_eq_tsum [SecondCountableTopology G] [T2Space G]
    (μG : Measure G) (H : Subgroup G) (μH : Measure H) (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G)) [μG.IsHaarMeasure]
    (hH : IsClosed (H : Set G)) (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) [μH.IsHaarMeasure]
    (Fn : G → ℝ≥0∞) (hFH : ∀ h ∈ H, ∀ g, Fn (h * g) = Fn g)
    (hFU : ∀ g, ∀ κ ∈ U, Fn (g * κ) = Fn g) (Rp : Set G)
    (hcov : ∀ g, ∃ r ∈ Rp, ∃ h ∈ H, ∃ κ ∈ U, g = h * r * κ)
    (huniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r') :
    quotLIntegral μG H μH Fn =
      ∑' r : Rp, Fn r * μG (U : Set G) / μH {h : H | (r : G)⁻¹ * (h : G) * r ∈ U} := by
  haveI : LocallyCompactSpace G :=
    hUc.locallyCompactSpace_of_mem_nhds_of_group (hU.mem_nhds U.one_mem)
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : Countable Rp := countable_reps hU huniq
  haveI : μH.IsInvInvariant := by
    letI : CommGroup H := { (inferInstance : Group H) with
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
    haveI : μH.Regular := inferInstance
    exact Measure.IsHaarMeasure.isInvInvariant_of_regular μH
  have hFm : Measurable Fn := measurable_of_right_invariant hU hFU
  rw [quotLIntegral_eq hFm hFH (rho_isQuotNormaliser hU hUc hH hcomm hcov huniq)]
  have hpt : ∀ g, Fn g * rho μH U Rp g =
      ∑' r : Rp, (coset U (r : G)).indicator
        (fun _ => Fn r * (μH (conjSet H U r))⁻¹) g := by
    intro g
    rw [rho, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun r => ?_
    by_cases hg : g ∈ coset U (r : G)
    · have e : Fn ((r : G) * ((r : G)⁻¹ * g)) = Fn r := hFU _ _ hg
      rw [mul_inv_cancel_left] at e
      rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, e]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, mul_zero]
  rw [lintegral_congr hpt, lintegral_tsum]
  · refine tsum_congr fun r => ?_
    have hms : MeasurableSet (coset U (r : G)) := (isOpen_coset hU (r : G)).measurableSet
    have hvol : μG (coset U (r : G)) = μG (U : Set G) :=
      measure_preimage_mul μG (r : G)⁻¹ (U : Set G)
    rw [lintegral_indicator_const hms, hvol, div_eq_mul_inv, mul_right_comm]
    rfl
  · intro r
    exact (measurable_const.indicator (isOpen_coset hU (r : G)).measurableSet).aemeasurable

end Abstract

/- English proof (translation)
Introduce `F _ _ _ _ n _ _ μG H μH U hUo hUc hμG hH hcomm hμH Fn hFH hFU Rp hcov huniq`. Use `haveI := GlobalTheory.CompanionTheory.GLMeasure.secondCountable_GL F n`. Take `⟨_, _⟩` from `GlobalTheory.CompanionTheory.GLMeasure.secondCountable_t2_local_field F`. Use `haveI : T2Space (Matrix (Fin n) (Fin n) F) := inferInstanceAs (T2Space (Fin n → Fin n → F))`. Use `haveI : T2Space (GL (Fin n) F) := inferInstance`.

Conclude with `quotLIntegral_eq_tsum μG H μH U hUo hUc hH hcomm Fn hFH hFU Rp hcov huniq`.
-/
theorem h2U : PositivityTheory.Rg.Tf.Loc.QuotientIntegralCompactOpen := by
  intro F _ _ _ _ n _ _ μG H μH U hUo hUc hμG hH hcomm hμH Fn hFH hFU Rp hcov huniq
  haveI := GlobalTheory.CompanionTheory.GLMeasure.secondCountable_GL F n
  obtain ⟨_, _⟩ := GlobalTheory.CompanionTheory.GLMeasure.secondCountable_t2_local_field F
  haveI : T2Space (Matrix (Fin n) (Fin n) F) := inferInstanceAs (T2Space (Fin n → Fin n → F))
  haveI : T2Space (GL (Fin n) F) := inferInstance
  exact quotLIntegral_eq_tsum μG H μH U hUo hUc hH hcomm Fn hFH hFU Rp hcov huniq

end GlobalTheory.CompanionTheory.QuotU
