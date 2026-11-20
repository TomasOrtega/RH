import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsPosDensMeasurable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsPosDensMeasurable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

/- English proof (translation)
Introduce `K _ ι _ P e Ψ L g hP hΨ hL hg hdeg`. Establish `hfin` using `fibreFinite K ι P e Ψ hP hΨ`. Take `⟨B, γ, hBo, hlift, hcov⟩` from `PtsSumMeasurable.exists_lift_family (P := P) (Ψ := Ψ) hfin`. Establish `hd1 : IsDegZeroSmooth (fun _ : (Σ k, ι k) → ℂ => (1 : ℝ))` using `⟨contDiffOn_const, fun _ _ _ => rfl⟩`. Establish `hind` using `sheetIndep K ι P e Ψ L _ 1 hP hΨ hL (PtsPosDens.isSmoothHerm_ofWeight hd1) (PtsPosDens.isSectionOn_ofWeight_one hP hd1)`.

Rewrite `hind` using `[PtsPosDens.logNorm_ofWeight_one hd1]`. Simplify using `only [one_mul] at hind`. Establish `hsheet : ∀ m, ∀ y ∈ B m, IsSheet P Ψ y (segre (γ m y)) (γ m)` using `fun m y hy => ⟨rfl, Filter.eventually_of_mem ((hBo m).mem_nhds hy) fun y' hy' => hlift m y' hy'⟩`. Establish `hγc : ∀ m, ContinuousOn (γ m) (B m)` using `fun m y hy => (hlift m y hy).1.continuousAt.continuousWithinAt`. Establish `hO : ∀ m, Set.MapsTo (γ m) (B m) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}` using `fun m y hy => (hlift m y hy).2.1.1`.

Establish `hseg : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ)` using `continuous_pi fun i => continuous_finsetProd _ fun k _ => continuous_apply _`. Use `set σ : ℕ → (Fin e → ℂ) → ((k : K) → ι k) → ℂ := fun m => (B m).piecewise (fun y => segre (γ m y)) 0 with hσdef`. Establish `hσB : ∀ m, ∀ y ∈ B m, σ m y = segre (γ m y)` using `fun m y hy => Set.piecewise_eq_of_mem _ _ _ hy`. Establish `hσm : ∀ m, Measurable (σ m)` using `fun m => (hseg.comp_continuousOn (hγc m)).measurable_piecewise continuousOn_const (hBo m).measurableSet`. Use `set γt : ℕ → (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun m => (B m).piecewise (γ m) 0 with hγtdef`.

Establish `hγtm : ∀ m, Measurable (γt m)` using `fun m => (hγc m).measurable_piecewise continuousOn_const (hBo m).measurableSet`. Use `set dens : ℕ → (Fin e → ℂ) → ℝ := fun m y => max (g (γt m y) * maDensity (fun j y' => pot L j (γ m y')) y) 0 with hddef`. Establish `hdm : ∀ m, Measurable (dens m)` using `fun m => ((hg.comp (hγtm m)).mul (PtsSumMeasurable.measurable_maDensity _)).max measurable_const`. Establish `hdens : ∀ m, ∀ y ∈ B m, dens m y = max (g (γ m y) * maDensity (fun j y' => pot L j (γ m y')) y) 0`. Introduce `m y hy`.

Simplify using `only [hddef, hγtdef, Set.piecewise_eq_of_mem _ _ _ hy]`. Use `set S : ℕ → Set (Fin e → ℂ) := fun m => {y | y ∈ B m ∧ ∀ m' < m, ¬ (y ∈ B m' ∧ σ m' y = σ m y)} with hSdef`. Establish `hSm : ∀ m, MeasurableSet (S m)`. Introduce `m`. Establish `: S m = B m ∩ ⋂ m' ∈ Finset.range m, (B m' ∩ {y | σ m' y = σ m y})ᶜ`.

Use extensionality with `y`. Simplify using `[hSdef]`. Rewrite using `[this]`. Conclude with `(hBo m).measurableSet.inter (Finset.measurableSet_biInter _ fun m' _ => ((hBo m').measurableSet.inter (measurableSet_eq_fun (hσm m') (hσm m))).compl)`. Use `set f : ℕ → (Fin e → ℂ) → ℝ := fun m => (S m).indicator (dens m) with hfdef`.

Establish `hfm : ∀ m, Measurable (f m)` using `fun m => (hdm m).indicator (hSm m)`. Establish `key : AEStronglyMeasurable (ptsPosDens P Ψ (pot L) g) volume`. Establish `hpp : ptsPosDens P Ψ (pot L) g = fun y => ∑ᶠ w ∈ fibre P Ψ y, max (sheetDensity P Ψ (pot L) g y w) 0` using `rfl`. Rewrite using `[hpp]`. Use `aestronglyMeasurable_of_tendsto_ae atTop (f := fun N y => ∑ m ∈ Finset.range N, f m y) (fun N => (Finset.measurable_sum _ fun m _ => hfm m).aestronglyMeasurable) ?_` and prove the remaining obligations.

Use `filter_upwards [hind] with y hy`. Establish `hterm : ∀ m, y ∈ S m → f m y = max (sheetDensity P Ψ (pot L) g y (σ m y)) 0`. Introduce `m hm`. Establish `hsh` using `hsheet m y hm.1`. Rewrite `hsh` using `[← hσB m y hm.1]`.

Establish `hex : ∃ γ', IsSheet P Ψ y (σ m y) γ'` using `⟨_, hsh⟩`. Rewrite using `[hfdef]`. Simplify using `only`. Rewrite using `[Set.indicator_of_mem hm, hdens m y hm.1]`. Unfold `sheetDensity`.

Rewrite using `[dif_pos hex, hy _ _ _ hex.choose_spec hsh]`. Use `choose i0 hi0 using hO m hm.1`. Establish `hs : segre (γ m y) = segre (hex.choose y)`. Rewrite using `[hex.choose_spec.1, hσB m y hm.1]`. Take `⟨hc', hrel⟩` from `eq_bsmul_of_segre_eq i0 hi0 hs`.

Establish `hgy : g (hex.choose y) = g (γ m y)`. Rewrite using `[hrel]`. Conclude with `hdeg _ _ fun k => div_ne_zero (hc' k) (hi0 k)`. Rewrite using `[hgy]`. Establish `hmemF : ∀ m, y ∈ S m → σ m y ∈ (hfin y).toFinset`.

Introduce `m hm`. Rewrite using `[Set.Finite.mem_toFinset, hσB m y hm.1]`. Conclude with `⟨γ m y, (hlift m y hm.1).2.1, rfl, (hlift m y hm.1).2.2⟩`. Establish `hfy : ∀ m, (∑ w ∈ (hfin y).toFinset, if σ m y = w then f m y else 0) = f m y`. Introduce `m`.

Rewrite using `[Finset.sum_ite_eq]`. Distinguish the cases in `hm : y ∈ S m`. Rewrite using `[if_pos (hmemF m hm)]`. Use `split_ifs`. Both sides reduce to the same expression.

Rewrite using `[hfdef]`. Simplify using `only`. Rewrite using `[Set.indicator_of_notMem hm]`. Establish `hev : ∀ w ∈ (hfin y).toFinset, ∀ᶠ N in atTop, max (sheetDensity P Ψ (pot L) g y w) 0 = ∑ m ∈ Finset.range N, if σ m y = w then f m y else 0`. Introduce `w _`.

Distinguish the cases in `hex : ∃ γ', IsSheet P Ψ y w γ'`. Take `⟨γ', hγ'⟩` from `hex`. Establish `hP' : ∃ m, y ∈ B m ∧ σ m y = w`. Take `⟨m, hm, hmw⟩` from `hcov y w γ' hγ'`. Conclude with `⟨m, hm, (hσB m y hm).trans hmw⟩`.

Take `⟨hm1B, hm1w⟩` from `Nat.find_spec hP'`. Establish `hm1S : y ∈ S (Nat.find hP')` using `⟨hm1B, fun m' hm' h => Nat.find_min hP' hm' ⟨h.1, h.2.trans hm1w⟩⟩`. Use `filter_upwards [eventually_gt_atTop (Nat.find hP')] with N hN`. Rewrite using `[Finset.sum_eq_single_of_mem (Nat.find hP') (Finset.mem_range.2 hN), if_pos hm1w, hterm _ hm1S, hm1w]`. Introduce `m _ hne`.

Use `split_ifs with hmw`. Distinguish the cases in `hmS : y ∈ S m`. It suffices to derive a contradiction. Establish `hle : Nat.find hP' ≤ m` using `Nat.find_min' hP' ⟨hmS.1, hmw⟩`. Conclude with `hmS.2 _ (lt_of_le_of_ne hle (Ne.symm hne)) ⟨hm1B, hm1w.trans hmw.symm⟩`.

Rewrite using `[hfdef]`. Simplify using `only`. Rewrite using `[Set.indicator_of_notMem hmS]`. Both sides reduce to the same expression. Establish `h0 : sheetDensity P Ψ (pot L) g y w = 0`.

Unfold `sheetDensity`. Rewrite using `[dif_neg hex]`. Use `Eventually.of_forall fun N => ?_` and prove the remaining obligations. Rewrite using `[h0, max_self]`. Use `(Finset.sum_eq_zero fun m _ => ?_).symm` and prove the remaining obligations.

Use `split_ifs with hmw`. Distinguish the cases in `hmS : y ∈ S m`. Establish `hsh` using `hsheet m y hmS.1`. Rewrite `hsh` using `[← hσB m y hmS.1, hmw]`. Conclude with `absurd ⟨_, hsh⟩ hex`.

Rewrite using `[hfdef]`. Simplify using `only`. Rewrite using `[Set.indicator_of_notMem hmS]`. Both sides reduce to the same expression. Establish `hsum : ∑ᶠ w ∈ fibre P Ψ y, max (sheetDensity P Ψ (pot L) g y w) 0 = ∑ w ∈ (hfin y).toFinset, max (sheetDensity P Ψ (pot L) g y w) 0` using `finsum_mem_eq_finite_toFinset_sum _ (hfin y)`.

Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [(eventually_all_finset _).2 hev] with N hN`. Rewrite using `[hsum, Finset.sum_congr rfl hN, Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun m _ => hfy m`. Conclude with `key.aemeasurable`.
-/
theorem PtsPosDensMeasurable.proof : PtsPosDensMeasurable.Statement := by
  intro K _ ι _ P e Ψ L g hP hΨ hL hg hdeg
  classical
  have hfin := fibreFinite K ι P e Ψ hP hΨ
  obtain ⟨B, γ, hBo, hlift, hcov⟩ := PtsSumMeasurable.exists_lift_family (P := P) (Ψ := Ψ) hfin

  have hd1 : IsDegZeroSmooth (fun _ : (Σ k, ι k) → ℂ => (1 : ℝ)) := ⟨contDiffOn_const, fun _ _ _ => rfl⟩
  have hind := sheetIndep K ι P e Ψ L _ 1 hP hΨ hL (PtsPosDens.isSmoothHerm_ofWeight hd1)
    (PtsPosDens.isSectionOn_ofWeight_one hP hd1)
  rw [PtsPosDens.logNorm_ofWeight_one hd1] at hind
  simp only [one_mul] at hind
  have hsheet : ∀ m, ∀ y ∈ B m, IsSheet P Ψ y (segre (γ m y)) (γ m) := fun m y hy =>
    ⟨rfl, Filter.eventually_of_mem ((hBo m).mem_nhds hy) fun y' hy' => hlift m y' hy'⟩
  have hγc : ∀ m, ContinuousOn (γ m) (B m) := fun m y hy =>
    (hlift m y hy).1.continuousAt.continuousWithinAt
  have hO : ∀ m, Set.MapsTo (γ m) (B m) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun m y hy =>
    (hlift m y hy).2.1.1
  have hseg : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
    continuous_pi fun i => continuous_finsetProd _ fun k _ => continuous_apply _
  set σ : ℕ → (Fin e → ℂ) → ((k : K) → ι k) → ℂ := fun m =>
    (B m).piecewise (fun y => segre (γ m y)) 0 with hσdef
  have hσB : ∀ m, ∀ y ∈ B m, σ m y = segre (γ m y) := fun m y hy =>
    Set.piecewise_eq_of_mem _ _ _ hy
  have hσm : ∀ m, Measurable (σ m) := fun m =>
    (hseg.comp_continuousOn (hγc m)).measurable_piecewise continuousOn_const (hBo m).measurableSet

  set γt : ℕ → (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun m => (B m).piecewise (γ m) 0 with hγtdef
  have hγtm : ∀ m, Measurable (γt m) := fun m =>
    (hγc m).measurable_piecewise continuousOn_const (hBo m).measurableSet
  set dens : ℕ → (Fin e → ℂ) → ℝ := fun m y =>
    max (g (γt m y) * maDensity (fun j y' => pot L j (γ m y')) y) 0 with hddef
  have hdm : ∀ m, Measurable (dens m) := fun m =>
    ((hg.comp (hγtm m)).mul (PtsSumMeasurable.measurable_maDensity _)).max measurable_const
  have hdens : ∀ m, ∀ y ∈ B m,
      dens m y = max (g (γ m y) * maDensity (fun j y' => pot L j (γ m y')) y) 0 := by
    intro m y hy
    simp only [hddef, hγtdef, Set.piecewise_eq_of_mem _ _ _ hy]
  set S : ℕ → Set (Fin e → ℂ) := fun m =>
    {y | y ∈ B m ∧ ∀ m' < m, ¬ (y ∈ B m' ∧ σ m' y = σ m y)} with hSdef
  have hSm : ∀ m, MeasurableSet (S m) := by
    intro m
    have : S m = B m ∩ ⋂ m' ∈ Finset.range m, (B m' ∩ {y | σ m' y = σ m y})ᶜ := by
      ext y
      simp [hSdef]
    rw [this]
    exact (hBo m).measurableSet.inter (Finset.measurableSet_biInter _ fun m' _ =>
      ((hBo m').measurableSet.inter (measurableSet_eq_fun (hσm m') (hσm m))).compl)
  set f : ℕ → (Fin e → ℂ) → ℝ := fun m => (S m).indicator (dens m) with hfdef
  have hfm : ∀ m, Measurable (f m) := fun m => (hdm m).indicator (hSm m)
  have key : AEStronglyMeasurable (ptsPosDens P Ψ (pot L) g) volume := by
    have hpp : ptsPosDens P Ψ (pot L) g =
        fun y => ∑ᶠ w ∈ fibre P Ψ y, max (sheetDensity P Ψ (pot L) g y w) 0 := rfl
    rw [hpp]
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N y => ∑ m ∈ Finset.range N, f m y)
      (fun N => (Finset.measurable_sum _ fun m _ => hfm m).aestronglyMeasurable) ?_
    filter_upwards [hind] with y hy
    have hterm : ∀ m, y ∈ S m → f m y = max (sheetDensity P Ψ (pot L) g y (σ m y)) 0 := by
      intro m hm
      have hsh := hsheet m y hm.1
      rw [← hσB m y hm.1] at hsh
      have hex : ∃ γ', IsSheet P Ψ y (σ m y) γ' := ⟨_, hsh⟩
      rw [hfdef]
      simp only
      rw [Set.indicator_of_mem hm, hdens m y hm.1]
      unfold sheetDensity
      rw [dif_pos hex, hy _ _ _ hex.choose_spec hsh]

      choose i0 hi0 using hO m hm.1
      have hs : segre (γ m y) = segre (hex.choose y) := by
        rw [hex.choose_spec.1, hσB m y hm.1]
      obtain ⟨hc', hrel⟩ := eq_bsmul_of_segre_eq i0 hi0 hs
      have hgy : g (hex.choose y) = g (γ m y) := by
        rw [hrel]
        exact hdeg _ _ fun k => div_ne_zero (hc' k) (hi0 k)
      rw [hgy]
    have hmemF : ∀ m, y ∈ S m → σ m y ∈ (hfin y).toFinset := by
      intro m hm
      rw [Set.Finite.mem_toFinset, hσB m y hm.1]
      exact ⟨γ m y, (hlift m y hm.1).2.1, rfl, (hlift m y hm.1).2.2⟩
    have hfy : ∀ m, (∑ w ∈ (hfin y).toFinset, if σ m y = w then f m y else 0) = f m y := by
      intro m
      rw [Finset.sum_ite_eq]
      by_cases hm : y ∈ S m
      · rw [if_pos (hmemF m hm)]
      · split_ifs
        · rfl
        · rw [hfdef]
          simp only
          rw [Set.indicator_of_notMem hm]
    have hev : ∀ w ∈ (hfin y).toFinset, ∀ᶠ N in atTop,
        max (sheetDensity P Ψ (pot L) g y w) 0 =
          ∑ m ∈ Finset.range N, if σ m y = w then f m y else 0 := by
      intro w _
      by_cases hex : ∃ γ', IsSheet P Ψ y w γ'
      · obtain ⟨γ', hγ'⟩ := hex
        have hP' : ∃ m, y ∈ B m ∧ σ m y = w := by
          obtain ⟨m, hm, hmw⟩ := hcov y w γ' hγ'
          exact ⟨m, hm, (hσB m y hm).trans hmw⟩
        obtain ⟨hm1B, hm1w⟩ := Nat.find_spec hP'
        have hm1S : y ∈ S (Nat.find hP') :=
          ⟨hm1B, fun m' hm' h => Nat.find_min hP' hm' ⟨h.1, h.2.trans hm1w⟩⟩
        filter_upwards [eventually_gt_atTop (Nat.find hP')] with N hN
        rw [Finset.sum_eq_single_of_mem (Nat.find hP') (Finset.mem_range.2 hN), if_pos hm1w,
          hterm _ hm1S, hm1w]
        intro m _ hne
        split_ifs with hmw
        · by_cases hmS : y ∈ S m
          · exfalso
            have hle : Nat.find hP' ≤ m := Nat.find_min' hP' ⟨hmS.1, hmw⟩
            exact hmS.2 _ (lt_of_le_of_ne hle (Ne.symm hne)) ⟨hm1B, hm1w.trans hmw.symm⟩
          · rw [hfdef]
            simp only
            rw [Set.indicator_of_notMem hmS]
        · rfl
      · have h0 : sheetDensity P Ψ (pot L) g y w = 0 := by
          unfold sheetDensity
          rw [dif_neg hex]
        refine Eventually.of_forall fun N => ?_
        rw [h0, max_self]
        refine (Finset.sum_eq_zero fun m _ => ?_).symm
        split_ifs with hmw
        · by_cases hmS : y ∈ S m
          · have hsh := hsheet m y hmS.1
            rw [← hσB m y hmS.1, hmw] at hsh
            exact absurd ⟨_, hsh⟩ hex
          · rw [hfdef]
            simp only
            rw [Set.indicator_of_notMem hmS]
        · rfl
    have hsum : ∑ᶠ w ∈ fibre P Ψ y, max (sheetDensity P Ψ (pot L) g y w) 0 =
        ∑ w ∈ (hfin y).toFinset, max (sheetDensity P Ψ (pot L) g y w) 0 :=
      finsum_mem_eq_finite_toFinset_sum _ (hfin y)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(eventually_all_finset _).2 hev] with N hN
    rw [hsum, Finset.sum_congr rfl hN, Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => hfy m
  exact key.aemeasurable

end GroundTheory.Heights₂.Heights
