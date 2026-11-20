import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StTailLogOfMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PTailLogOfMassCharts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable locDens ChartPartition)

noncomputable section

namespace TailLogOfMass

/- English proof (translation)
Establish `hs` using `summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (D + 1) (r := 1 / 2) (by norm_num)`. Establish `h2` using `((summable_nat_add_iff 2).2 hs).mul_left 4`. Use `h2.congr fun n => ?_` and prove the remaining obligations. Use `push_cast`. Rewrite using `[one_div, inv_pow, pow_add]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem summable_shell (D : ℕ) : Summable fun k : ℕ => ((k : ℝ) + 2) ^ (D + 1) / 2 ^ k := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (D + 1) (r := 1 / 2) (by norm_num)
  have h2 := ((summable_nat_add_iff 2).2 hs).mul_left 4
  refine h2.congr fun n => ?_
  push_cast
  rw [one_div, inv_pow, pow_add]
  field_simp
  ring

/- English proof (translation)
Establish `hRpos : 0 < R` using `lt_of_lt_of_le (Real.exp_pos 1) hR`. Establish `hL : 1 ≤ Real.log R`. Rewrite using `[← Real.log_exp 1]`. Conclude with `Real.log_le_log (Real.exp_pos 1) hR`. Take `⟨k, hk1, hk2⟩` from `exists_nat_pow_near (x := s / R) (y := (2 : ℝ)) ((one_le_div hRpos).2 hs) one_lt_two`.

Use `⟨k, (le_div_iff₀ hRpos).1 hk1, ?_⟩` and prove the remaining obligations. Establish `hspos : 0 < s` using `lt_of_lt_of_le hRpos hs`. Establish `h1 : s < 2 ^ (k + 1) * R` using `(div_lt_iff₀ hRpos).1 hk2`. Establish `h2 : Real.log s ≤ Real.log (2 ^ (k + 1) * R)` using `Real.log_le_log hspos h1.le`. Rewrite `h2` using `[Real.log_mul (by positivity) hRpos.ne', Real.log_pow]`.

Establish `hl2 : Real.log 2 ≤ 1` using `by have := Real.log_two_lt_d9; linarith`. Move the coercions through the operations in `at h2`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1), mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]`.
-/
theorem shell_exists {R s : ℝ} (hR : Real.exp 1 ≤ R) (hs : R ≤ s) :
    ∃ k : ℕ, 2 ^ k * R ≤ s ∧ Real.log s ≤ ((k : ℝ) + 2) * Real.log R := by
  have hRpos : 0 < R := lt_of_lt_of_le (Real.exp_pos 1) hR
  have hL : 1 ≤ Real.log R := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hR
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := s / R) (y := (2 : ℝ))
    ((one_le_div hRpos).2 hs) one_lt_two
  refine ⟨k, (le_div_iff₀ hRpos).1 hk1, ?_⟩
  have hspos : 0 < s := lt_of_lt_of_le hRpos hs
  have h1 : s < 2 ^ (k + 1) * R := (div_lt_iff₀ hRpos).1 hk2
  have h2 : Real.log s ≤ Real.log (2 ^ (k + 1) * R) := Real.log_le_log hspos h1.le
  rw [Real.log_mul (by positivity) hRpos.ne', Real.log_pow] at h2
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  push_cast at h2
  nlinarith [mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1),
    mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {Yo : Set X} {r : X → ℝ}
  {th : LocPot X} {u : Fin D → X → ℝ}

/- English proof (translation)
Use `set U := (A.chart k).target ∩ (A.chart k).symm ⁻¹' Yo with hUdef`. Establish `hU : IsOpen U` using `(A.chart k).isOpen_inter_preimage_symm hYo`. Establish `hF : ContinuousOn (fun y => r ((A.chart k).symm y)) U` using `hr.comp ((A.chart k).continuousOn_symm.mono inter_subset_left) fun y hy => hy.2`. Use `set Ms := U ∩ (fun y => r ((A.chart k).symm y)) ⁻¹' Ici R with hMs`. Establish `hM : MeasurableSet Ms`.

Establish `ho` using `hF.isOpen_inter_preimage hU (isOpen_Iio (a := R))`. Establish `e : Ms = U \ (U ∩ (fun y => r ((A.chart k).symm y)) ⁻¹' Iio R)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hu, hge⟩`.

Conclude with `⟨hu, fun hm => (not_le.2 (show r ((A.chart k).symm y) < R from hm.2)) (show R ≤ r ((A.chart k).symm y) from hge)⟩`. Introduce and unpack `⟨hu, hn⟩`. Conclude with `⟨hu, show R ≤ r ((A.chart k).symm y) from not_lt.1 fun hlt => hn ⟨hu, hlt⟩⟩`. Rewrite using `[e]`. Conclude with `hU.measurableSet.diff ho.measurableSet`.

Establish `hlog : ContinuousOn (fun y => Real.log (r ((A.chart k).symm y))) Ms` using `(hF.mono inter_subset_left).log fun y hy => by`. Establish `: R ≤ r ((A.chart k).symm y)` using `hy.2`. Conclude with `(by linarith : (0 : ℝ) < _).ne'`. Establish `hcongr : (fun y => (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart k).symm y)) =ᵐ[volume.restrict (A.chart k).target] Ms.indicator fun y => Real.log (r ((A.chart k).symm y))`. Use `ae_restrict_of_forall_mem (A.chart k).open_target.measurableSet fun y hyt => ?_` and prove the remaining obligations.

Use `show (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart k).symm y) = _`. Distinguish the cases in `hc : (A.chart k).symm y ∈ tail Yo r R`. Rewrite using `[indicator_of_mem hc, indicator_of_mem (show y ∈ Ms from ⟨⟨hyt, hc.1⟩, hc.2⟩)]`. Rewrite using `[indicator_of_notMem hc, indicator_of_notMem (show y ∉ Ms from fun hm => hc ⟨hm.1.2, hm.2⟩)]`. Conclude with `((aestronglyMeasurable_indicator_iff hM).2 (hlog.aestronglyMeasurable hM)).congr hcongr.symm`.
-/
theorem logTail_aesm (hYo : IsOpen Yo) (hr : ContinuousOn r Yo) (R : ℝ) (hR : 0 < R)
    (k : Fin A.n) :
    AEStronglyMeasurable
      (fun y => (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart k).symm y))
      (volume.restrict (A.chart k).target) := by
  set U := (A.chart k).target ∩ (A.chart k).symm ⁻¹' Yo with hUdef
  have hU : IsOpen U := (A.chart k).isOpen_inter_preimage_symm hYo
  have hF : ContinuousOn (fun y => r ((A.chart k).symm y)) U :=
    hr.comp ((A.chart k).continuousOn_symm.mono inter_subset_left) fun y hy => hy.2
  set Ms := U ∩ (fun y => r ((A.chart k).symm y)) ⁻¹' Ici R with hMs
  have hM : MeasurableSet Ms := by
    have ho := hF.isOpen_inter_preimage hU (isOpen_Iio (a := R))
    have e : Ms = U \ (U ∩ (fun y => r ((A.chart k).symm y)) ⁻¹' Iio R) := by
      ext y
      constructor
      · rintro ⟨hu, hge⟩
        exact ⟨hu, fun hm => (not_le.2 (show r ((A.chart k).symm y) < R from hm.2))
          (show R ≤ r ((A.chart k).symm y) from hge)⟩
      · rintro ⟨hu, hn⟩
        exact ⟨hu, show R ≤ r ((A.chart k).symm y) from not_lt.1 fun hlt => hn ⟨hu, hlt⟩⟩
    rw [e]
    exact hU.measurableSet.diff ho.measurableSet
  have hlog : ContinuousOn (fun y => Real.log (r ((A.chart k).symm y))) Ms :=
    (hF.mono inter_subset_left).log fun y hy => by
      have : R ≤ r ((A.chart k).symm y) := hy.2
      exact (by linarith : (0 : ℝ) < _).ne'
  have hcongr : (fun y => (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart k).symm y))
      =ᵐ[volume.restrict (A.chart k).target]
        Ms.indicator fun y => Real.log (r ((A.chart k).symm y)) := by
    refine ae_restrict_of_forall_mem (A.chart k).open_target.measurableSet fun y hyt => ?_
    show (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart k).symm y) = _
    by_cases hc : (A.chart k).symm y ∈ tail Yo r R
    · rw [indicator_of_mem hc, indicator_of_mem (show y ∈ Ms from ⟨⟨hyt, hc.1⟩, hc.2⟩)]
    · rw [indicator_of_notMem hc,
        indicator_of_notMem (show y ∉ Ms from fun hm => hc ⟨hm.1.2, hm.2⟩)]
  exact ((aestronglyMeasurable_indicator_iff hM).2 (hlog.aestronglyMeasurable hM)).congr
    hcongr.symm

/- English proof (translation)
Establish `hd : AEStronglyMeasurable (fun y => (tail Yo r (Real.exp 1)).indicator 1 ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y) (volume.restrict (A.chart j).target)` using `((locallyIntegrableOn_iff (A.chart j).open_target.isLocallyClosed).2 fun K hK hKc => hT0 j K hK hKc).aestronglyMeasurable`. Use `((logTail_aesm hYo hr R hR j).mul hd).congr (ae_of_all _ fun y => ?_)` and prove the remaining obligations. Use `show (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) * ((tail Yo r (Real.exp 1)).indicator 1 ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y) = (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A (fun i => pot …`. Distinguish the cases in `hy : (A.chart j).symm y ∈ Yo`. Rewrite using `[indicator_of_mem (show (A.chart j).symm y ∈ tail Yo r (Real.exp 1) from ⟨hy, hre _ hy⟩)]`.

Simplify using the standard rewrite rules. Rewrite using `[indicator_of_notMem (show (A.chart j).symm y ∉ tail Yo r R from fun h => hy h.1)]`. Simplify using the standard rewrite rules.
-/
theorem logTail_dens_aesm (hYo : IsOpen Yo) (hr : ContinuousOn r Yo)
    (hre : ∀ x ∈ Yo, Real.exp 1 ≤ r x)
    (hT0 : MIntegrable A (fun i => potForm th (u i)) ((tail Yo r (Real.exp 1)).indicator 1)) (R : ℝ) (hR : 0 < R)
    (j : Fin A.n) :
    AEStronglyMeasurable (fun y => (tail Yo r R).indicator (fun x => Real.log (r x))
      ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y) (volume.restrict (A.chart j).target) := by
  have hd : AEStronglyMeasurable (fun y => (tail Yo r (Real.exp 1)).indicator 1 ((A.chart j).symm y) *
      locDens A (fun i => potForm th (u i)) j y) (volume.restrict (A.chart j).target) :=
    ((locallyIntegrableOn_iff (A.chart j).open_target.isLocallyClosed).2
      fun K hK hKc => hT0 j K hK hKc).aestronglyMeasurable
  refine ((logTail_aesm hYo hr R hR j).mul hd).congr (ae_of_all _ fun y => ?_)
  show (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) *
      ((tail Yo r (Real.exp 1)).indicator 1 ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y) =
    (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y
  by_cases hy : (A.chart j).symm y ∈ Yo
  · rw [indicator_of_mem (show (A.chart j).symm y ∈ tail Yo r (Real.exp 1) from ⟨hy, hre _ hy⟩)]
    simp
  · rw [indicator_of_notMem (show (A.chart j).symm y ∉ tail Yo r R from fun h => hy h.1)]
    simp

/- English proof (translation)
Establish `hRpos : 0 < R` using `lt_of_lt_of_le (Real.exp_pos 1) hR`. Establish `hL : 1 ≤ Real.log R`. Rewrite using `[← Real.log_exp 1]`. Conclude with `Real.log_le_log (Real.exp_pos 1) hR`. Establish `hk2 : ∀ k : ℕ, Real.exp 1 ≤ 2 ^ k * R` using `fun k => hR.trans (le_mul_of_one_le_left hRpos.le (one_le_pow₀ one_le_two))`.

Establish `hS : ∀ k : ℕ, ∑ i, ∫⁻ z in (A.chart i).target, ENNReal.ofReal ((ReciprocityTheory.AnForm.M.existsPartition A).some.χ i ((A.chart i).symm z) * (tail Yo r (2 ^ k * R)).indicator 1 ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) = ENNReal.ofReal (mInt A (fun i => p …` using `fun k => sum_lintegral_eq_mInt hYo hth hu hnn _ (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x) (fun x hx => indicator_of_notMem (fun h => hx h.1) _) (hT _ (hk2 k)).1`. Establish `hW : ∀ (k : ℕ) (i : Fin A.n), IntegrableOn (fun z => (ReciprocityTheory.AnForm.M.existsPartition A).some.χ i ((A.chart i).symm z) * (tail Yo r (2 ^ k * R)).indicator 1 ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) (A.chart i).target` using `fun k i => ReciprocityTheory.AnForm.M.integrableOn_weight A _ _ _ (hT _ (hk2 k)).1 i`. Generalize the expression as in `(ReciprocityTheory.AnForm.M.existsPartition A).some = P at hS hW ⊢`. Establish `hpt : ∀ i, ∀ z ∈ (A.chart i).target, ENNReal.ofReal (P.χ i ((A.chart i).symm z) * (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) ≤ ∑' k : ℕ, ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) * ENNReal.ofReal (P.χ i (( …`. Introduce `i z hz`.

Distinguish the cases in `hx : (A.chart i).symm z ∈ tail Yo r R`. Take `⟨k, hk1, hk2'⟩` from `shell_exists hR hx.2`. Establish `hw : 0 ≤ P.χ i ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z` using `mul_nonneg (P.nonneg i _) (locDens_nonneg_on hYo hth hu hnn i hz hx.1)`. Use `le_trans ?_ (ENNReal.le_tsum k)` and prove the remaining obligations. Rewrite using `[indicator_of_mem hx, indicator_of_mem (show (A.chart i).symm z ∈ tail Yo r (2 ^ k * R) from ⟨hx.1, hk1⟩), ← ENNReal.ofReal_mul (by positivity)]`.

Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Simplify using `only [Pi.one_apply, mul_one]`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ((k : ℝ) + 2) * Real.log R * (P.χ i ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) := mul_le_mul_of_nonneg_right hk2' hw`.

Use `_ = _ := by ring`. Rewrite using `[indicator_of_notMem hx]`. Simplify using the standard rewrite rules. Establish `hchart : ∀ i, ∫⁻ z in (A.chart i).target, ENNReal.ofReal (P.χ i ((A.chart i).symm z) * (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) ≤ ∑' k : ℕ, ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) * ∫⁻ z in (A.chart i) …`. Introduce `i`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `k`. Conclude with `lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`. Establish `hshell : ∀ k : ℕ, ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) * ENNReal.ofReal (mInt A (fun i => potForm th (u i)) ((tail Yo r (2 ^ k * R)).indicator 1)) ≤ ENNReal.ofReal (CE * Real.log R ^ (D + 1) / R * (((k : ℝ) + 2) ^ (D + 1) / 2 ^ k))`.

Introduce `k`. Establish `hc : 0 ≤ ((k : ℝ) + 2) * Real.log R` using `by positivity`. Rewrite using `[← ENNReal.ofReal_mul hc]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `hm` using `(hT _ (hk2 k)).2`.

Establish `hlog0 : 0 ≤ Real.log (2 ^ k * R)` using `Real.log_nonneg (by`. Use `hk2 k` as an intermediate fact. Combine the linear relations using `[Real.add_one_le_exp (1 : ℝ)])`. Establish `hlogk : Real.log (2 ^ k * R) ≤ ((k : ℝ) + 2) * Real.log R`. Rewrite using `[Real.log_mul (by positivity) hRpos.ne', Real.log_pow]`.

Establish `hl2 : Real.log 2 ≤ 1` using `by have := Real.log_two_lt_d9; linarith`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]`. Establish `hpow` using `pow_le_pow_left₀ hlog0 hlogk D`. Establish `h2kR : 0 < 2 ^ k * R` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[← Finset.mul_sum, hS k]`. Use `_ ≤ ∑' k : ℕ, ENNReal.ofReal (CE * Real.log R ^ (D + 1) / R * (((k : ℝ) + 2) ^ (D + 1) / 2 ^ k)) := ENNReal.tsum_le_tsum hshell`. Use `_ = ENNReal.ofReal (shellConst D * CE * Real.log R ^ (D + 1) / R) := by`.

Rewrite using `[← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) ((summable_shell D).mul_left _), tsum_mul_left, shellConst]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_lintegral_logTail_le [CompactSpace X] [T2Space X] (hYo : IsOpen Yo)
    (hth : IsPotential A th)
    (hu : ∀ i, A.SmoothOn Yo (u i)) (hnn : ∀ i, FormNonneg A Yo (potForm th (u i)))
    {CE : ℝ} (hCE : 0 ≤ CE) (hT : TailMassBound A Yo r (fun i => potForm th (u i)) CE) (R : ℝ) (hR : Real.exp 1 ≤ R) :
    ∑ i, ∫⁻ z in (A.chart i).target, ENNReal.ofReal ((ReciprocityTheory.AnForm.M.existsPartition A).some.χ i ((A.chart i).symm z) *
      (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) ≤
      ENNReal.ofReal (shellConst D * CE * Real.log R ^ (D + 1) / R) := by
  have hRpos : 0 < R := lt_of_lt_of_le (Real.exp_pos 1) hR
  have hL : 1 ≤ Real.log R := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hR
  have hk2 : ∀ k : ℕ, Real.exp 1 ≤ 2 ^ k * R := fun k =>
    hR.trans (le_mul_of_one_le_left hRpos.le (one_le_pow₀ one_le_two))
  have hS : ∀ k : ℕ, ∑ i, ∫⁻ z in (A.chart i).target, ENNReal.ofReal ((ReciprocityTheory.AnForm.M.existsPartition A).some.χ i ((A.chart i).symm z) *
      (tail Yo r (2 ^ k * R)).indicator 1 ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) =
      ENNReal.ofReal (mInt A (fun i => potForm th (u i)) ((tail Yo r (2 ^ k * R)).indicator 1)) := fun k =>
    sum_lintegral_eq_mInt hYo hth hu hnn _ (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
      (fun x hx => indicator_of_notMem (fun h => hx h.1) _) (hT _ (hk2 k)).1
  have hW : ∀ (k : ℕ) (i : Fin A.n), IntegrableOn (fun z => (ReciprocityTheory.AnForm.M.existsPartition A).some.χ i ((A.chart i).symm z) *
      (tail Yo r (2 ^ k * R)).indicator 1 ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z)
      (A.chart i).target := fun k i =>
    ReciprocityTheory.AnForm.M.integrableOn_weight A _ _ _ (hT _ (hk2 k)).1 i
  generalize (ReciprocityTheory.AnForm.M.existsPartition A).some = P at hS hW ⊢

  have hpt : ∀ i, ∀ z ∈ (A.chart i).target, ENNReal.ofReal (P.χ i ((A.chart i).symm z) *
      (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) ≤
      ∑' k : ℕ, ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) * ENNReal.ofReal (P.χ i ((A.chart i).symm z) *
        (tail Yo r (2 ^ k * R)).indicator 1 ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) := by
    intro i z hz
    by_cases hx : (A.chart i).symm z ∈ tail Yo r R
    · obtain ⟨k, hk1, hk2'⟩ := shell_exists hR hx.2
      have hw : 0 ≤ P.χ i ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z :=
        mul_nonneg (P.nonneg i _) (locDens_nonneg_on hYo hth hu hnn i hz hx.1)
      refine le_trans ?_ (ENNReal.le_tsum k)
      rw [indicator_of_mem hx, indicator_of_mem (show (A.chart i).symm z ∈ tail Yo r (2 ^ k * R)
        from ⟨hx.1, hk1⟩), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [Pi.one_apply, mul_one]
      calc P.χ i ((A.chart i).symm z) * Real.log (r ((A.chart i).symm z)) * locDens A (fun i => potForm th (u i)) i z
          = Real.log (r ((A.chart i).symm z)) * (P.χ i ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) := by
            ring
        _ ≤ ((k : ℝ) + 2) * Real.log R * (P.χ i ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) :=
            mul_le_mul_of_nonneg_right hk2' hw
        _ = _ := by ring
    · rw [indicator_of_notMem hx]
      simp

  have hchart : ∀ i, ∫⁻ z in (A.chart i).target, ENNReal.ofReal (P.χ i ((A.chart i).symm z) *
      (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) ≤
      ∑' k : ℕ, ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) * ∫⁻ z in (A.chart i).target,
        ENNReal.ofReal (P.χ i ((A.chart i).symm z) *
          (tail Yo r (2 ^ k * R)).indicator 1 ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) := by
    intro i
    calc _ ≤ ∫⁻ z in (A.chart i).target, ∑' k : ℕ, ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) *
          ENNReal.ofReal (P.χ i ((A.chart i).symm z) *
            (tail Yo r (2 ^ k * R)).indicator 1 ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) :=
          lintegral_mono_ae (ae_restrict_of_forall_mem (A.chart i).open_target.measurableSet
            (hpt i))
      _ = ∑' k : ℕ, ∫⁻ z in (A.chart i).target, ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) *
          ENNReal.ofReal (P.χ i ((A.chart i).symm z) *
            (tail Yo r (2 ^ k * R)).indicator 1 ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) :=
          lintegral_tsum fun k => ((hW k i).aemeasurable.ennreal_ofReal).const_mul _
      _ = _ := by
          congr 1
          funext k
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

  have hshell : ∀ k : ℕ, ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) *
      ENNReal.ofReal (mInt A (fun i => potForm th (u i)) ((tail Yo r (2 ^ k * R)).indicator 1)) ≤
      ENNReal.ofReal (CE * Real.log R ^ (D + 1) / R * (((k : ℝ) + 2) ^ (D + 1) / 2 ^ k)) := by
    intro k
    have hc : 0 ≤ ((k : ℝ) + 2) * Real.log R := by positivity
    rw [← ENNReal.ofReal_mul hc]
    refine ENNReal.ofReal_le_ofReal ?_
    have hm := (hT _ (hk2 k)).2
    have hlog0 : 0 ≤ Real.log (2 ^ k * R) := Real.log_nonneg (by
      have := hk2 k; linarith [Real.add_one_le_exp (1 : ℝ)])
    have hlogk : Real.log (2 ^ k * R) ≤ ((k : ℝ) + 2) * Real.log R := by
      rw [Real.log_mul (by positivity) hRpos.ne', Real.log_pow]
      have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      nlinarith [mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hpow := pow_le_pow_left₀ hlog0 hlogk D
    have h2kR : 0 < 2 ^ k * R := by positivity
    calc ((k : ℝ) + 2) * Real.log R * mInt A (fun i => potForm th (u i)) ((tail Yo r (2 ^ k * R)).indicator 1)
        ≤ ((k : ℝ) + 2) * Real.log R * (CE * Real.log (2 ^ k * R) ^ D / (2 ^ k * R)) :=
          mul_le_mul_of_nonneg_left hm hc
      _ ≤ ((k : ℝ) + 2) * Real.log R * (CE * (((k : ℝ) + 2) * Real.log R) ^ D / (2 ^ k * R)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow hCE) h2kR.le) hc
      _ = _ := by
          rw [mul_pow]
          field_simp
          ring

  calc ∑ i, ∫⁻ z in (A.chart i).target, ENNReal.ofReal (P.χ i ((A.chart i).symm z) *
        (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z)
      ≤ ∑ i, ∑' k : ℕ, ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) * ∫⁻ z in (A.chart i).target,
          ENNReal.ofReal (P.χ i ((A.chart i).symm z) *
            (tail Yo r (2 ^ k * R)).indicator 1 ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) :=
        Finset.sum_le_sum fun i _ => hchart i
    _ = ∑' k : ℕ, ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) *
          ENNReal.ofReal (mInt A (fun i => potForm th (u i)) ((tail Yo r (2 ^ k * R)).indicator 1)) := by
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        congr 1
        funext k
        rw [← Finset.mul_sum, hS k]
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (CE * Real.log R ^ (D + 1) / R *
          (((k : ℝ) + 2) ^ (D + 1) / 2 ^ k)) := ENNReal.tsum_le_tsum hshell
    _ = ENNReal.ofReal (shellConst D * CE * Real.log R ^ (D + 1) / R) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
          ((summable_shell D).mul_left _), tsum_mul_left, shellConst]
        congr 1
        ring

end TailLogOfMass

open TailLogOfMass in

/- English proof (translation)
Introduce `X _ _ _ D A Yo r th u hYo hr hre hth hu hnn CE hT`. Establish `he` using `Real.exp_pos 1`. Establish `hoffT : ∀ R : ℝ, ∀ x, x ∉ Yo → (tail Yo r R).indicator (fun x => Real.log (r x)) x = 0` using `fun R x hx => indicator_of_notMem (fun h => hx h.1) _`. Establish `hCE : 0 ≤ CE`. Establish `h1` using `(hT _ le_rfl).2`.

Establish `h0` using `mInt_nonneg_of hYo hth hu hnn ((tail Yo r (Real.exp 1)).indicator 1) (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x) (fun x hx => indicator_of_notMem (fun h => hx h.1) _)`. Rewrite `h1` using `[Real.log_exp, one_pow, mul_one]`. Assume the negation of the conclusion as `hneg`. Establish `: CE / Real.exp 1 < 0` using `div_neg_of_neg_of_pos (lt_of_not_ge hneg) he`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `R hR`. Establish `hRpos : 0 < R` using `lt_of_lt_of_le he hR`. Establish `hL : 0 ≤ Real.log R` using `Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])`. Establish `h0 : ∀ x, 0 ≤ (tail Yo r R).indicator (fun x => Real.log (r x)) x`. Introduce `x`.

Distinguish the cases in `hx : x ∈ tail Yo r R`. Rewrite using `[indicator_of_mem hx]`. Conclude with `Real.log_nonneg (by linarith [hx.2, Real.add_one_le_exp (1 : ℝ)])`. Rewrite using `[indicator_of_notMem hx]`. Establish `hmeas` using `logTail_dens_aesm (A := A) (th := th) (u := u) hYo hr hre (hT _ le_rfl).1 R hRpos`.

Establish `hfin` using `sum_lintegral_logTail_le hYo hth hu hnn hCE hT R hR`. Establish `hb : 0 ≤ shellConst D * CE * Real.log R ^ (D + 1) / R` using `div_nonneg (mul_nonneg (mul_nonneg (tsum_nonneg fun k => by positivity) hCE) (pow_nonneg hL _)) hRpos.le`. Establish `hI : MIntegrable A (fun i => potForm th (u i)) ((tail Yo r R).indicator fun x => Real.log (r x))`. Introduce `j K hK hKc`. Establish `hnnK : 0 ≤ᵐ[volume.restrict K] fun y => (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y` using `ae_restrict_of_forall_mem hKc.measurableSet fun y hy => by`.

Distinguish the cases in `hx : (A.chart j).symm y ∈ Yo`. Conclude with `mul_nonneg (h0 _) (locDens_nonneg_on hYo hth hu hnn j (hK hy) hx)`. Use `beta_reduce`. Rewrite using `[hoffT R _ hx, zero_mul]`. Conclude with `le_rfl`.

Use `⟨(hmeas j).mono_set hK, (hasFiniteIntegral_iff_ofReal hnnK).2 ?_⟩` and prove the remaining obligations. Conclude with `lt_of_le_of_lt ((lintegral_mono_set hK).trans ((lintegral_target_le hYo hth hu hnn (ReciprocityTheory.AnForm.M.existsPartition A).some _ h0 (hoffT R) j (hmeas j).aemeasurable).trans hfin)) ENNReal.ofReal_lt_top`. Use `⟨hI, ?_⟩` and prove the remaining obligations. Establish `hS` using `sum_lintegral_eq_mInt hYo hth hu hnn _ h0 (hoffT R) hI`. Rewrite `hfin` using `[hS]`.

Conclude with `(ENNReal.ofReal_le_ofReal_iff hb).1 hfin`.
-/
theorem TailLogOfMass.proof : TailLogOfMass.Statement := by
  intro X _ _ _ D A Yo r th u hYo hr hre hth hu hnn CE hT
  have he := Real.exp_pos 1
  have hoffT : ∀ R : ℝ, ∀ x, x ∉ Yo → (tail Yo r R).indicator (fun x => Real.log (r x)) x = 0 :=
    fun R x hx => indicator_of_notMem (fun h => hx h.1) _
  have hCE : 0 ≤ CE := by
    have h1 := (hT _ le_rfl).2
    have h0 := mInt_nonneg_of hYo hth hu hnn ((tail Yo r (Real.exp 1)).indicator 1)
      (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
      (fun x hx => indicator_of_notMem (fun h => hx h.1) _)
    rw [Real.log_exp, one_pow, mul_one] at h1
    by_contra hneg
    have : CE / Real.exp 1 < 0 := div_neg_of_neg_of_pos (lt_of_not_ge hneg) he
    linarith
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le he hR
  have hL : 0 ≤ Real.log R := Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have h0 : ∀ x, 0 ≤ (tail Yo r R).indicator (fun x => Real.log (r x)) x := by
    intro x
    by_cases hx : x ∈ tail Yo r R
    · rw [indicator_of_mem hx]
      exact Real.log_nonneg (by linarith [hx.2, Real.add_one_le_exp (1 : ℝ)])
    · rw [indicator_of_notMem hx]
  have hmeas := logTail_dens_aesm (A := A) (th := th) (u := u) hYo hr hre (hT _ le_rfl).1 R hRpos
  have hfin := sum_lintegral_logTail_le hYo hth hu hnn hCE hT R hR
  have hb : 0 ≤ shellConst D * CE * Real.log R ^ (D + 1) / R :=
    div_nonneg (mul_nonneg (mul_nonneg (tsum_nonneg fun k => by positivity) hCE)
      (pow_nonneg hL _)) hRpos.le
  have hI : MIntegrable A (fun i => potForm th (u i)) ((tail Yo r R).indicator fun x => Real.log (r x)) := by
    intro j K hK hKc
    have hnnK : 0 ≤ᵐ[volume.restrict K] fun y =>
        (tail Yo r R).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y :=
      ae_restrict_of_forall_mem hKc.measurableSet fun y hy => by
        by_cases hx : (A.chart j).symm y ∈ Yo
        · exact mul_nonneg (h0 _) (locDens_nonneg_on hYo hth hu hnn j (hK hy) hx)
        · beta_reduce
          rw [hoffT R _ hx, zero_mul]
          exact le_rfl
    refine ⟨(hmeas j).mono_set hK, (hasFiniteIntegral_iff_ofReal hnnK).2 ?_⟩
    exact lt_of_le_of_lt ((lintegral_mono_set hK).trans
      ((lintegral_target_le hYo hth hu hnn (ReciprocityTheory.AnForm.M.existsPartition A).some _ h0 (hoffT R) j (hmeas j).aemeasurable).trans hfin))
      ENNReal.ofReal_lt_top
  refine ⟨hI, ?_⟩
  have hS := sum_lintegral_eq_mInt hYo hth hu hnn _ h0 (hoffT R) hI
  rw [hS] at hfin
  exact (ENNReal.ofReal_le_ofReal_iff hb).1 hfin

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
