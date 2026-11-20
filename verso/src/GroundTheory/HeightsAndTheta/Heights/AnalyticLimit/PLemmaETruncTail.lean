import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETruncTail
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaEScale
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaEEnergy
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaEWeight
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLogNormSecIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsPsh MIntegrable mInt logNormSec
  mIntLinear mIntNonneg maMeasure_thm mIntCongrNull mIntegrableCont mIntegrableMul
  isPotentialAdd isPotential_ofFun st_smooth_continuous st_mInt_zero)

/- English proof (translation)
Introduce `x`. Use `⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hs.1 x, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Simplify using `only [Set.mem_inter_iff, Set.mem_compl_iff, secOpen, Set.mem_ofPred_eq, not_not]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hy, hyU⟩`. Use `⟨hyU, fun _ => ?_⟩` and prove the remaining obligations. Establish `h` using `hs.2 x y y ⟨hyU, L.mem_U y⟩`. Rewrite `h` using `[hy, norm_zero, zero_mul]`. Conclude with `norm_eq_zero.1 ((mul_eq_zero.1 h).resolve_right (Real.exp_ne_zero _))`.

Introduce and unpack `⟨hyU, hy⟩`. Establish `h` using `hs.2 x y y ⟨hyU, L.mem_U y⟩`. Rewrite `h` using `[hy 0, norm_zero, zero_mul]`. Conclude with `⟨norm_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_right (Real.exp_ne_zero _)), hyU⟩`.
-/
theorem isAnalyticSubset_compl_secOpen {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    {L : LocPot X} {s : X → X → ℂ} (hs : IsSection A L s) : A.IsAnalyticSubset (secOpen s)ᶜ := by
  intro x
  refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hs.1 x, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, secOpen, Set.mem_ofPred_eq, not_not]
  constructor
  · rintro ⟨hy, hyU⟩
    refine ⟨hyU, fun _ => ?_⟩
    have h := hs.2 x y y ⟨hyU, L.mem_U y⟩
    rw [hy, norm_zero, zero_mul] at h
    exact norm_eq_zero.1 ((mul_eq_zero.1 h).resolve_right (Real.exp_ne_zero _))
  · rintro ⟨hyU, hy⟩
    have h := hs.2 x y y ⟨hyU, L.mem_U y⟩
    rw [hy 0, norm_zero, zero_mul] at h
    exact ⟨norm_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_right (Real.exp_ne_zero _)), hyU⟩

/- English proof (translation)
Introduce `X _ _ _ D A Om L s hL hs hd hle`. Take `⟨c₀, hc₀, hw⟩` from `h₃ D A Om L s hL hs`. Establish `hΩ : ∀ _ : Fin D, IsPotential A Om.pot` using `fun _ => Om.isPot`. Establish `hΩp : ∀ _ : Fin D, IsPsh A Om.pot` using `fun _ => Om.isPsh`. Establish `hr : MIntegrable A (fun _ => Om.pot) (rSec L s)` using `fun j K hK hKc => IntegrableOn.congr_fun (((h₄ A L s hL hs hd _ hΩ j K hK hKc).const_mul (-2)).add (mIntegrableCont A _ hΩ (fun _ => Real.exp 1) continuous_const j K hK hKc)) (fun y _ => by simp only [Pi.add_apply, rSec]; ring) hKc.measurableSet`.

Establish `hI₀ : 0 ≤ mInt A (fun _ => Om.pot) (rSec L s)` using `mIntNonneg A _ hΩ hΩp _ fun x => (Real.exp_pos 1).le.trans (exp_one_le_rSec hle x)`. Establish `hvol : Om.vol = mInt A (fun _ => Om.pot) (fun _ => 1)` using `rfl`. Establish `hV : 0 ≤ Om.vol` using `mIntNonneg A _ hΩ hΩp _ fun _ => zero_le_one`. Use `⟨(c₀ * mInt A (fun _ => Om.pot) (rSec L s) + ((D : ℝ) + 1) * Om.vol) / c₀, div_nonneg (add_nonneg (mul_nonneg hc₀.le hI₀) (mul_nonneg (by positivity) hV)) hc₀.le, fun M hM v hvs hvp hvb ρ hρ => ?_⟩` and prove the remaining obligations. Establish `hcρ : 0 < c₀ * ρ` using `mul_pos hc₀ ((Real.exp_pos 1).trans_le hρ)`.

Take `⟨w, hws, hwp, hwY, hwN⟩` from `hw (max 1 (c₀ * ρ)) (le_max_left _ _)`. Establish `hwc : Continuous w` using `st_smooth_continuous A hws`. Establish `hg0 : ∀ x, 0 ≤ -w x`. Introduce `x`. Distinguish the cases in `hx : x ∈ secOpen s`.

Establish `h1 : 0 < c₀ * rSec L s x` using `mul_pos hc₀ ((Real.exp_pos 1).trans_le (exp_one_le_rSec hle x))`. Conclude with `(lt_min h1 (one_pos.trans_le (le_max_left _ _))).le.trans (hwY x hx).1`. Conclude with `(zero_le_one.trans (le_max_left _ _)).trans (hwN x hx)`. Use `set S := {x | x ∉ secOpen s ∨ ρ ≤ rSec L s x} with hSdef`. Establish `hgS : ∀ x ∈ S, c₀ * ρ ≤ -w x`.

Introduce and unpack `x (hx | hx)`. Conclude with `(le_max_right _ _).trans (hwN x hx)`. Distinguish the cases in `hY : x ∈ secOpen s`. Conclude with `(le_min (mul_le_mul_of_nonneg_left hx hc₀.le) (le_max_right _ _)).trans (hwY x hY).1`. Conclude with `(le_max_right _ _).trans (hwN x hY)`.

Establish `hΦv : ∀ i, IsPotential A (potForm Om.pot (v i))` using `fun i => isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ (hvs i))`. Use `letI : MeasurableSpace X := borel X`. Use `haveI : BorelSpace X := ⟨rfl⟩`. Establish `hrm : Measurable (rSec L s)` using `measurable_const.sub (measurable_const.mul (Real.measurable_log.comp (continuous_normSec hL hs).measurable))`. Establish `hSm : MeasurableSet S` using `(isOpen_secOpen hL hs).measurableSet.compl.union (measurableSet_le measurable_const hrm)`.

Take `⟨hfin, hmeas⟩` from `maMeasure_thm A _ hΦv hvp`. Establish `hSi : MIntegrable A (fun i => potForm Om.pot (v i)) (S.indicator 1)` using `((hmeas _ (measurable_const.indicator hSm)).1).2 ((integrable_const (1 : ℝ)).indicator hSm)`. Establish `hA : mInt A (fun i => potForm Om.pot (v i)) (S.indicator 1) ≤ mInt A (fun i => potForm Om.pot (v i)) (fun x => -w x) / (c₀ * ρ)`. Establish `e1` using `mIntLinear A _ hΦv (-1) (S.indicator 1) (fun x => (c₀ * ρ)⁻¹ * -w x) hSi (mIntegrableCont A _ hΦv _ (continuous_const.mul hwc.neg))`. Establish `e2` using `mIntLinear A _ hΦv (c₀ * ρ)⁻¹ (fun x => -w x) (fun _ => 0) (mIntegrableCont A _ hΦv _ hwc.neg) (mIntegrableCont A _ hΦv _ continuous_const)`.

Simplify using `only [add_zero, st_mInt_zero] at e2`. Establish `hn` using `mIntNonneg A _ hΦv hvp (fun x => -1 * S.indicator 1 x + (c₀ * ρ)⁻¹ * -w x) fun x => by`. Establish `h0` using `mul_nonneg (inv_nonneg.2 hcρ.le) (hg0 x)`. Distinguish the cases in `hx : x ∈ S`. Establish `h1 : 1 ≤ (c₀ * ρ)⁻¹ * -w x`.

Rewrite using `[inv_mul_eq_div, le_div_iff₀ hcρ, one_mul]`. Conclude with `hgS x hx`. Rewrite using `[Set.indicator_of_mem hx, Pi.one_apply]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Set.indicator_of_notMem hx]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hn` using `[e1, e2]`. Rewrite using `[div_eq_inv_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hpsM, hsc⟩` from `h₁ A Om M v hM hvs hvp`.

Establish `hM0 : 0 < M` using `one_pos.trans_le hM`. Establish `hB1` using `hsc (fun x => -w x) hwc.neg hg0`. Establish `hB2 : mInt A (fun i => potForm Om.pot fun x => v i x / M) (fun x => -w x) ≤ mInt A (fun _ => Om.pot) (fun x => -w x) + D * Om.vol` using `h₂ A Om (fun i x => v i x / M) w (fun i j => (hvs i j).div_const M) hpsM (fun i x => ⟨by rw [le_div_iff₀ hM0]; linarith [(hvb i x).1], div_nonpos_of_nonpos_of_nonneg (hvb i x).2 hM0.le⟩) hws hwp`. Establish `hint : interior (secOpen s)ᶜ = ∅`. Rewrite using `[interior_compl, hd.closure_eq, Set.compl_univ]`.

Establish `e3` using `mIntLinear A _ hΩ c₀ (rSec L s) (fun x => 1 + w x) hr (mIntegrableCont A _ hΩ _ (continuous_const.add hwc))`. Establish `e4` using `mIntLinear A _ hΩ 1 (fun _ => 1) w (mIntegrableCont A _ hΩ _ continuous_const) (mIntegrableCont A _ hΩ _ hwc)`. Simplify using `only [one_mul] at e4`. Establish `e5` using `mInt_neg A _ hΩ w (mIntegrableCont A _ hΩ _ hwc)`. Establish `e6` using `mIntCongrNull A (fun _ => Om.pot) _ (isAnalyticSubset_compl_secOpen hs) hint (fun x => c₀ * rSec L s x + (1 + w x)) (fun x => if x ∈ secOpen s then c₀ * rSec L s x + (1 + w x) else 0) fun x hx => by`.

Simplify using `only [Set.mem_compl_iff, not_not] at hx`. Simplify using `only [hx, ↓reduceIte]`. Establish `hn2` using `mIntNonneg A _ hΩ hΩp (fun x => if x ∈ secOpen s then c₀ * rSec L s x + (1 + w x) else 0) fun x => by`. Distinguish the cases in `hx : x ∈ secOpen s`. Simplify using `only [hx, ↓reduceIte]`.

Combine the linear relations using `[(hwY x hx).2]`. Simplify using `only [hx, ↓reduceIte, le_refl]`. Establish `hB : mInt A (fun _ => Om.pot) (fun x => -w x) ≤ c₀ * mInt A (fun _ => Om.pot) (rSec L s) + Om.vol`. Rewrite using `[hvol]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `key : mInt A (fun i => potForm Om.pot (v i)) (fun x => -w x) ≤ M ^ D * (c₀ * mInt A (fun _ => Om.pot) (rSec L s) + ((D : ℝ) + 1) * Om.vol)`. Establish `hMD : 0 ≤ M ^ D` using `pow_nonneg hM0.le D`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem LemmaETruncTail.proof (h₁ : LemmaEScale.Statement) (h₂ : LemmaEEnergy.Statement)
    (h₃ : LemmaEWeight.Statement) (h₄ : LogNormSecIntegrable.Statement) :
    LemmaETruncTail.Statement := by
  intro X _ _ _ D A Om L s hL hs hd hle
  classical
  obtain ⟨c₀, hc₀, hw⟩ := h₃ D A Om L s hL hs
  have hΩ : ∀ _ : Fin D, IsPotential A Om.pot := fun _ => Om.isPot
  have hΩp : ∀ _ : Fin D, IsPsh A Om.pot := fun _ => Om.isPsh
  have hr : MIntegrable A (fun _ => Om.pot) (rSec L s) := fun j K hK hKc =>
    IntegrableOn.congr_fun (((h₄ A L s hL hs hd _ hΩ j K hK hKc).const_mul (-2)).add
      (mIntegrableCont A _ hΩ (fun _ => Real.exp 1) continuous_const j K hK hKc))
      (fun y _ => by simp only [Pi.add_apply, rSec]; ring) hKc.measurableSet
  have hI₀ : 0 ≤ mInt A (fun _ => Om.pot) (rSec L s) := mIntNonneg A _ hΩ hΩp _ fun x =>
    (Real.exp_pos 1).le.trans (exp_one_le_rSec hle x)
  have hvol : Om.vol = mInt A (fun _ => Om.pot) (fun _ => 1) := rfl
  have hV : 0 ≤ Om.vol := mIntNonneg A _ hΩ hΩp _ fun _ => zero_le_one
  refine ⟨(c₀ * mInt A (fun _ => Om.pot) (rSec L s) + ((D : ℝ) + 1) * Om.vol) / c₀,
    div_nonneg (add_nonneg (mul_nonneg hc₀.le hI₀) (mul_nonneg (by positivity) hV)) hc₀.le,
    fun M hM v hvs hvp hvb ρ hρ => ?_⟩
  have hcρ : 0 < c₀ * ρ := mul_pos hc₀ ((Real.exp_pos 1).trans_le hρ)
  obtain ⟨w, hws, hwp, hwY, hwN⟩ := hw (max 1 (c₀ * ρ)) (le_max_left _ _)
  have hwc : Continuous w := st_smooth_continuous A hws
  have hg0 : ∀ x, 0 ≤ -w x := by
    intro x
    by_cases hx : x ∈ secOpen s
    · have h1 : 0 < c₀ * rSec L s x :=
        mul_pos hc₀ ((Real.exp_pos 1).trans_le (exp_one_le_rSec hle x))
      exact (lt_min h1 (one_pos.trans_le (le_max_left _ _))).le.trans (hwY x hx).1
    · exact (zero_le_one.trans (le_max_left _ _)).trans (hwN x hx)
  set S := {x | x ∉ secOpen s ∨ ρ ≤ rSec L s x} with hSdef
  have hgS : ∀ x ∈ S, c₀ * ρ ≤ -w x := by
    rintro x (hx | hx)
    · exact (le_max_right _ _).trans (hwN x hx)
    · by_cases hY : x ∈ secOpen s
      · exact (le_min (mul_le_mul_of_nonneg_left hx hc₀.le) (le_max_right _ _)).trans (hwY x hY).1
      · exact (le_max_right _ _).trans (hwN x hY)

  have hΦv : ∀ i, IsPotential A (potForm Om.pot (v i)) := fun i =>
    isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ (hvs i))
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  have hrm : Measurable (rSec L s) := measurable_const.sub (measurable_const.mul
    (Real.measurable_log.comp (continuous_normSec hL hs).measurable))
  have hSm : MeasurableSet S :=
    (isOpen_secOpen hL hs).measurableSet.compl.union (measurableSet_le measurable_const hrm)
  obtain ⟨hfin, hmeas⟩ := maMeasure_thm A _ hΦv hvp
  have hSi : MIntegrable A (fun i => potForm Om.pot (v i)) (S.indicator 1) :=
    ((hmeas _ (measurable_const.indicator hSm)).1).2 ((integrable_const (1 : ℝ)).indicator hSm)
  have hA : mInt A (fun i => potForm Om.pot (v i)) (S.indicator 1) ≤
      mInt A (fun i => potForm Om.pot (v i)) (fun x => -w x) / (c₀ * ρ) := by
    have e1 := mIntLinear A _ hΦv (-1) (S.indicator 1) (fun x => (c₀ * ρ)⁻¹ * -w x) hSi
      (mIntegrableCont A _ hΦv _ (continuous_const.mul hwc.neg))
    have e2 := mIntLinear A _ hΦv (c₀ * ρ)⁻¹ (fun x => -w x) (fun _ => 0)
      (mIntegrableCont A _ hΦv _ hwc.neg) (mIntegrableCont A _ hΦv _ continuous_const)
    simp only [add_zero, st_mInt_zero] at e2
    have hn := mIntNonneg A _ hΦv hvp (fun x => -1 * S.indicator 1 x + (c₀ * ρ)⁻¹ * -w x) fun x => by
      have h0 := mul_nonneg (inv_nonneg.2 hcρ.le) (hg0 x)
      by_cases hx : x ∈ S
      · have h1 : 1 ≤ (c₀ * ρ)⁻¹ * -w x := by
          rw [inv_mul_eq_div, le_div_iff₀ hcρ, one_mul]
          exact hgS x hx
        rw [Set.indicator_of_mem hx, Pi.one_apply]
        linarith
      · rw [Set.indicator_of_notMem hx]
        linarith
    rw [e1, e2] at hn
    rw [div_eq_inv_mul]
    linarith

  obtain ⟨hpsM, hsc⟩ := h₁ A Om M v hM hvs hvp
  have hM0 : 0 < M := one_pos.trans_le hM
  have hB1 := hsc (fun x => -w x) hwc.neg hg0
  have hB2 : mInt A (fun i => potForm Om.pot fun x => v i x / M) (fun x => -w x) ≤
      mInt A (fun _ => Om.pot) (fun x => -w x) + D * Om.vol :=
    h₂ A Om (fun i x => v i x / M) w (fun i j => (hvs i j).div_const M) hpsM
      (fun i x => ⟨by rw [le_div_iff₀ hM0]; linarith [(hvb i x).1],
        div_nonpos_of_nonpos_of_nonneg (hvb i x).2 hM0.le⟩) hws hwp

  have hint : interior (secOpen s)ᶜ = ∅ := by
    rw [interior_compl, hd.closure_eq, Set.compl_univ]
  have e3 := mIntLinear A _ hΩ c₀ (rSec L s) (fun x => 1 + w x) hr
    (mIntegrableCont A _ hΩ _ (continuous_const.add hwc))
  have e4 := mIntLinear A _ hΩ 1 (fun _ => 1) w (mIntegrableCont A _ hΩ _ continuous_const)
    (mIntegrableCont A _ hΩ _ hwc)
  simp only [one_mul] at e4
  have e5 := mInt_neg A _ hΩ w (mIntegrableCont A _ hΩ _ hwc)
  have e6 := mIntCongrNull A (fun _ => Om.pot) _ (isAnalyticSubset_compl_secOpen hs) hint
    (fun x => c₀ * rSec L s x + (1 + w x))
    (fun x => if x ∈ secOpen s then c₀ * rSec L s x + (1 + w x) else 0) fun x hx => by
      simp only [Set.mem_compl_iff, not_not] at hx
      simp only [hx, ↓reduceIte]
  have hn2 := mIntNonneg A _ hΩ hΩp
    (fun x => if x ∈ secOpen s then c₀ * rSec L s x + (1 + w x) else 0) fun x => by
      by_cases hx : x ∈ secOpen s
      · simp only [hx, ↓reduceIte]
        linarith [(hwY x hx).2]
      · simp only [hx, ↓reduceIte, le_refl]
  have hB : mInt A (fun _ => Om.pot) (fun x => -w x) ≤
      c₀ * mInt A (fun _ => Om.pot) (rSec L s) + Om.vol := by
    rw [hvol]
    linarith
  have key : mInt A (fun i => potForm Om.pot (v i)) (fun x => -w x) ≤
      M ^ D * (c₀ * mInt A (fun _ => Om.pot) (rSec L s) + ((D : ℝ) + 1) * Om.vol) := by
    have hMD : 0 ≤ M ^ D := pow_nonneg hM0.le D
    calc _ ≤ M ^ D * mInt A (fun i => potForm Om.pot fun x => v i x / M) (fun x => -w x) := hB1
      _ ≤ M ^ D * (mInt A (fun _ => Om.pot) (fun x => -w x) + D * Om.vol) :=
        mul_le_mul_of_nonneg_left hB2 hMD
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hMD
  calc _ ≤ _ := hA
    _ ≤ M ^ D * (c₀ * mInt A (fun _ => Om.pot) (rSec L s) + ((D : ℝ) + 1) * Om.vol) / (c₀ * ρ) :=
      div_le_div_of_nonneg_right key hcρ.le
    _ = _ := by rw [mul_div_assoc', div_div]

end GroundTheory.Heights₂.Heights.AnalyticLimit
