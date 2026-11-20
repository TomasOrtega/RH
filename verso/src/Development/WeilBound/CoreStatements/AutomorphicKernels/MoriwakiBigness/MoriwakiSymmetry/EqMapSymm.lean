import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine
import Development.WeilBound.CoreStatements.AmpleLineBundles.IntersectionNumberEqLineHeight
import Development.WeilBound.CoreStatements.AmpleLineBundles.ExistsPointsBoundedLineHeights
set_option maxSynthPendingDepth 1

noncomputable section

namespace PositivityTheory.MbAis.DenseCurves

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo CoverDenseAlt.Rename₂ CoverDenseAlt.HtF
open GroundTheory.Heights₂.Heights (blockIdx Cone BlockNonzero orbitIdeal ArithVariety chartMonomial)

/- English proof (translation)
Use extensionality with `f`. Rewrite using `[← GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e) W f, h, ← GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren fun k ↦ (e k).symm) Q (ren e f)]`. Establish `: ren (fun k ↦ (e k).symm) (ren e f) = f` using `(ren e).symm_apply_apply f`. Rewrite using `[this]`.
-/
theorem eq_map_symm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : K → ℕ}
    (e : ∀ k, ι k ≃ blockIdx n k) {W : Ideal (MRing ι)} {Q : Ideal (MRing (blockIdx n))}
    (h : W.map (ren e) = Q) : W = Q.map (ren fun k ↦ (e k).symm) := by
  ext f
  rw [← GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e) W f, h,
    ← GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren fun k ↦ (e k).symm) Q (ren e f)]
  have : ren (fun k ↦ (e k).symm) (ren e f) = f := (ren e).symm_apply_apply f
  rw [this]

/- English proof (translation)
Introduce `K _ ι _ I P D H hI hP hH hHa`. Use `haveI : Nonempty K := hP.1`. Set `n : K → ℕ` to `fun k ↦ Fintype.card (ι k) - 1`. Establish `hn : ∀ k, Fintype.card (ι k) = n k + 1` using `fun k ↦ by`. Take `⟨i, -⟩` from `hP.2.1.2.2 k`.

Establish `: 0 < Fintype.card (ι k)` using `Fintype.card_pos_iff.2 ⟨i⟩`. Simplify using `only [n]`. Use linear arithmetic over natural numbers and integers. Set `e : ∀ k, ι k ≃ blockIdx n k` to `fun k ↦ Fintype.equivFinOfCardEq (hn k)`. Set `Pv : ArithVariety n` to `CoverDenseAlt.Dense0.var e hP`.

Establish `hPv : Pv.ideal = P.map (ren e)` using `rfl`. Take `⟨S, C₀, hS, hdense, hC₀⟩` from `GroundTheory.Heights₂.Heights.DenseBoundedHeight.main K n Pv`. Set `B' : GroundTheory.Heights₂.Heights.HermLine n` to `toNum e H hH`. Take `⟨m, C₁, hC₁⟩` from `GroundTheory.Heights₂.Heights.HeightComparison.main K n Pv B'`. Use `⟨m * C₀ + C₁, {W | ∃ x ∈ S, W.map (ren e) = orbitIdeal x}, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `f ⟨a, ha⟩ hfP`. Establish `hdens` using `(GroundTheory.Heights₂.Heights.zariskiDense_iff_orbitIdeal Pv S).mp hdense`. Take `⟨W', ⟨x, hx, rfl⟩, hW'⟩` from `hdens (ren e f) ⟨a, homog_ren e ha⟩ (fun h ↦ hfP ((GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e) P f).mp h))`. Use `⟨(orbitIdeal x).map (ren fun k ↦ (e k).symm), ⟨x, hx, ?_⟩, fun h ↦ hW' ?_⟩` and prove the remaining obligations. Use extensionality with `g`.

Establish `h1 : g = ren e (ren (fun k ↦ (e k).symm) g)` using `((ren e).apply_symm_apply g).symm`. Rewrite using `[h1, GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e), GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren fun k ↦ (e k).symm), ← h1]`. Establish `h1 : f = ren (fun k ↦ (e k).symm) (ren e f)` using `((ren e).symm_apply_apply f).symm`. Rewrite `h` using `[h1]`. Conclude with `(GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren fun k ↦ (e k).symm) _ _).mp h`.

Introduce and unpack `W ⟨x, hxS, hWx⟩`. Establish `hxP` using `hS hxS`. Establish `hx : BlockNonzero x` using `hxP.1`. Establish `hW : IsArithVar W 1`. Rewrite using `[eq_map_symm e hWx]`.

Conclude with `arithVar_map _ (GroundTheory.Heights₂.Heights.OrbitCurve.full K n x hx)`. Establish `hPW : P ≤ W` using `fun f hf ↦ by`. Rewrite using `[← GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e) W f, hWx]`. Conclude with `((GroundTheory.Heights₂.Heights.mem_points_iff_le_orbitIdeal Pv x).mp hxP).2 ((GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e) P f).mpr hf)`. Use `⟨hW, hPW, ?_⟩` and prove the remaining obligations.

Establish `hdeg' : degC (ι` using `blockIdx n) (orbitIdeal x) = degC W := by rw [← hWx, degC_map]`. Establish `hdegN : 0 < degC W` using `hdeg' ▸ GroundTheory.Heights₂.Heights.OrbitDegree.full K n x hx`. Establish `hdeg : (0 : ℝ) < degC W` using `by exact_mod_cast hdegN`. Establish `hfin : Finite (GroundTheory.Heights₂.Heights.projPts W)` using `(Nat.card_pos_iff.mp hdegN).2`. Take `⟨c, hc⟩` from `GroundTheory.Heights₂.Heights.exists_chart hx`.

Set `d : K → ℕ` to `fun _ ↦ 1`. Establish `hd : ∀ k, H.a k = d k` using `fun k ↦ by simp [hHa, d]`. Establish `hsec` using `GroundTheory.Heights₂.Heights.isSectionOn_chartMonomial B' x c hc d hd`. Establish `hhom : IsMultiHomog (ι` using `blockIdx n) (chartMonomial c d) d := (GroundTheory.Heights₂.Heights.geoMultiHomog_iff _ d).mpr (GroundTheory.Heights₂.Heights.isWeightedHomogeneous_chartMonomial c d)`. Take `⟨s, hs⟩` from `(ren e).surjective (chartMonomial c d)`.

Establish `hsh : IsMultiHomog s d`. Establish `h1 : s = ren (fun k ↦ (e k).symm) (chartMonomial c d)`. Rewrite using `[← hs]`. Conclude with `((ren e).symm_apply_apply s).symm`. Rewrite using `[h1]`.

Conclude with `homog_ren _ hhom`. Establish `hsW : s ∉ W`. Rewrite using `[← GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e), hs, hWx]`. Conclude with `GroundTheory.Heights₂.Heights.chartMonomial_notMem_orbitIdeal x c hc d`. Establish `hL : ∀ j : Fin 0, IsSmoothHerm ((Fin.elim0 : Fin 0 → HermLine ι) j)` using `fun j ↦ j.elim0`.

Establish `hsnoc : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine ι) H : Fin 1 → _) = ![H]`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Both sides reduce to the same expression. Establish `h` using `hI.2.2 W 0 Fin.elim0 H s d hW hL hH hd hsh hsW`.

Rewrite `h` using `[hsnoc]`. Establish `h3` using `CoverDenseAlt.heightRecR_full K n (fun _ _ _ ↦ 0) B' x _ hx hsec`. Establish `h4` using `recR_map e I (fun _ _ _ ↦ 0) W hW.2.1.2.1 hfin H B'.toGeo s (by`. Introduce `t z ht _`. Rewrite using `[hs, logNorm, logNorm, B'.toGeo.smul t z ht, GroundTheory.Heights₂.Heights.eval_smul_of_isMultiHomog _ d hhom t z, norm_mul, norm_prod]`.

Establish `hd' : ∀ k, B'.toGeo.a k = d k` using `hd`. Simplify using `only [hd', zpow_natCast, norm_pow]`. Rewrite using `[mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (ht k)))])`. Use the proof step `(fun z hz ↦ B'.toGeo_h_of_blockNonzero ((GroundTheory.Heights₂.Heights.blockNonzero_unflatCone_iff z).2 hz))`. Use the proof step `(by`.

Rewrite using `[hs, hWx]`. Conclude with `GroundTheory.Heights₂.Heights.OrbitDivVertical.proof K n B' x _ hx hsec)`. Use the proof step `(by`. Rewrite using `[hs, hWx]`. Conclude with `fun V hV c₁ c₂ h₁ h₂ ↦ (CoverDenseAlt.chartDehom_full K n B' x _ hx hsec V hV c₁ c₂ h₁ h₂).2)`.

Rewrite `h4` using `[hs, hWx, h3, hdeg']`. Establish `hval : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.height I H W = GroundTheory.Heights₂.Heights.height B' x`. Unfold `GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.height`. Rewrite using `[h, ← h4, mul_div_cancel_left₀ _ hdeg.ne']`. Rewrite using `[hval]`.

Establish `h1` using `hC₁ x hxP`. Establish `h2 : (m : ℝ) * GroundTheory.Heights₂.Heights.height (GroundTheory.Heights₂.Heights.HermLine.standard n) x ≤ m * C₀` using `mul_le_mul_of_nonneg_left (hC₀ x hxS) (Nat.cast_nonneg _)`. Establish `h5` using `le_abs_self (GroundTheory.Heights₂.Heights.height B' x)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.DenseBoundedHeight.Statement := by
  intro K _ ι _ I P D H hI hP hH hHa
  classical
  haveI : Nonempty K := hP.1
  let n : K → ℕ := fun k ↦ Fintype.card (ι k) - 1
  have hn : ∀ k, Fintype.card (ι k) = n k + 1 := fun k ↦ by
    obtain ⟨i, -⟩ := hP.2.1.2.2 k
    have : 0 < Fintype.card (ι k) := Fintype.card_pos_iff.2 ⟨i⟩
    simp only [n]
    omega
  let e : ∀ k, ι k ≃ blockIdx n k := fun k ↦ Fintype.equivFinOfCardEq (hn k)
  let Pv : ArithVariety n := CoverDenseAlt.Dense0.var e hP
  have hPv : Pv.ideal = P.map (ren e) := rfl
  obtain ⟨S, C₀, hS, hdense, hC₀⟩ := GroundTheory.Heights₂.Heights.DenseBoundedHeight.main K n Pv
  let B' : GroundTheory.Heights₂.Heights.HermLine n := toNum e H hH
  obtain ⟨m, C₁, hC₁⟩ := GroundTheory.Heights₂.Heights.HeightComparison.main K n Pv B'
  refine ⟨m * C₀ + C₁, {W | ∃ x ∈ S, W.map (ren e) = orbitIdeal x}, ?_, ?_⟩
  · rintro f ⟨a, ha⟩ hfP
    have hdens := (GroundTheory.Heights₂.Heights.zariskiDense_iff_orbitIdeal Pv S).mp hdense
    obtain ⟨W', ⟨x, hx, rfl⟩, hW'⟩ := hdens (ren e f) ⟨a, homog_ren e ha⟩
      (fun h ↦ hfP ((GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e) P f).mp h))
    refine ⟨(orbitIdeal x).map (ren fun k ↦ (e k).symm), ⟨x, hx, ?_⟩, fun h ↦ hW' ?_⟩
    · ext g
      have h1 : g = ren e (ren (fun k ↦ (e k).symm) g) := ((ren e).apply_symm_apply g).symm
      rw [h1, GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e),
        GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren fun k ↦ (e k).symm), ← h1]
    · have h1 : f = ren (fun k ↦ (e k).symm) (ren e f) := ((ren e).symm_apply_apply f).symm
      rw [h1] at h
      exact (GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren fun k ↦ (e k).symm) _ _).mp h
  · rintro W ⟨x, hxS, hWx⟩
    have hxP := hS hxS
    have hx : BlockNonzero x := hxP.1
    have hW : IsArithVar W 1 := by
      rw [eq_map_symm e hWx]
      exact arithVar_map _ (GroundTheory.Heights₂.Heights.OrbitCurve.full K n x hx)
    have hPW : P ≤ W := fun f hf ↦ by
      rw [← GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e) W f, hWx]
      exact ((GroundTheory.Heights₂.Heights.mem_points_iff_le_orbitIdeal Pv x).mp hxP).2
        ((GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e) P f).mpr hf)
    refine ⟨hW, hPW, ?_⟩
    have hdeg' : degC (ι := blockIdx n) (orbitIdeal x) = degC W := by rw [← hWx, degC_map]
    have hdegN : 0 < degC W := hdeg' ▸ GroundTheory.Heights₂.Heights.OrbitDegree.full K n x hx
    have hdeg : (0 : ℝ) < degC W := by exact_mod_cast hdegN
    have hfin : Finite (GroundTheory.Heights₂.Heights.projPts W) := (Nat.card_pos_iff.mp hdegN).2
    obtain ⟨c, hc⟩ := GroundTheory.Heights₂.Heights.exists_chart hx
    let d : K → ℕ := fun _ ↦ 1
    have hd : ∀ k, H.a k = d k := fun k ↦ by simp [hHa, d]
    have hsec := GroundTheory.Heights₂.Heights.isSectionOn_chartMonomial B' x c hc d hd
    have hhom : IsMultiHomog (ι := blockIdx n) (chartMonomial c d) d :=
      (GroundTheory.Heights₂.Heights.geoMultiHomog_iff _ d).mpr
        (GroundTheory.Heights₂.Heights.isWeightedHomogeneous_chartMonomial c d)
    obtain ⟨s, hs⟩ := (ren e).surjective (chartMonomial c d)
    have hsh : IsMultiHomog s d := by
      have h1 : s = ren (fun k ↦ (e k).symm) (chartMonomial c d) := by
        rw [← hs]
        exact ((ren e).symm_apply_apply s).symm
      rw [h1]
      exact homog_ren _ hhom
    have hsW : s ∉ W := by
      rw [← GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e), hs, hWx]
      exact GroundTheory.Heights₂.Heights.chartMonomial_notMem_orbitIdeal x c hc d
    have hL : ∀ j : Fin 0, IsSmoothHerm ((Fin.elim0 : Fin 0 → HermLine ι) j) := fun j ↦ j.elim0
    have hsnoc : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine ι) H : Fin 1 → _) = ![H] := by
      funext i
      fin_cases i
      rfl
    have h := hI.2.2 W 0 Fin.elim0 H s d hW hL hH hd hsh hsW
    rw [hsnoc] at h
    have h3 := CoverDenseAlt.heightRecR_full K n (fun _ _ _ ↦ 0) B' x _ hx hsec
    have h4 := recR_map e I (fun _ _ _ ↦ 0) W hW.2.1.2.1 hfin H B'.toGeo s
      (by
        intro t z ht _
        rw [hs, logNorm, logNorm, B'.toGeo.smul t z ht,
          GroundTheory.Heights₂.Heights.eval_smul_of_isMultiHomog _ d hhom t z, norm_mul, norm_prod]
        have hd' : ∀ k, B'.toGeo.a k = d k := hd
        simp only [hd', zpow_natCast, norm_pow]
        rw [mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.mpr fun k _ ↦
          pow_ne_zero _ (norm_ne_zero_iff.mpr (ht k)))])
      (fun z hz ↦ B'.toGeo_h_of_blockNonzero
        ((GroundTheory.Heights₂.Heights.blockNonzero_unflatCone_iff z).2 hz))
      (by
        rw [hs, hWx]
        exact GroundTheory.Heights₂.Heights.OrbitDivVertical.proof K n B' x _ hx hsec)
      (by
        rw [hs, hWx]
        exact fun V hV c₁ c₂ h₁ h₂ ↦ (CoverDenseAlt.chartDehom_full K n B' x _ hx hsec V hV c₁ c₂ h₁ h₂).2)
    rw [hs, hWx, h3, hdeg'] at h4
    have hval : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.height I H W =
        GroundTheory.Heights₂.Heights.height B' x := by
      unfold GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.height
      rw [h, ← h4, mul_div_cancel_left₀ _ hdeg.ne']
    rw [hval]
    have h1 := hC₁ x hxP
    have h2 : (m : ℝ) * GroundTheory.Heights₂.Heights.height (GroundTheory.Heights₂.Heights.HermLine.standard n) x ≤
        m * C₀ := mul_le_mul_of_nonneg_left (hC₀ x hxS) (Nat.cast_nonneg _)
    have h5 := le_abs_self (GroundTheory.Heights₂.Heights.height B' x)
    linarith

end PositivityTheory.MbAis.DenseCurves

end
