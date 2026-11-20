import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetFormCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace RegularizedFormComparison

open TubeFormComparison

/- English proof (translation)
Use `set τ : (Fin D → ℂ) → Fin 1 → ℂ := fun z _ => ((√ε : ℝ) : ℂ)⁻¹ * linEval u (s z) with hτ`. Establish `hτa : AnalyticAt ℂ τ y`. Use `analyticAt_pi_iff.2 fun _ => analyticAt_const.mul ?_` and prove the remaining obligations. Unfold `linEval`. Conclude with `Finset.analyticAt_fun_sum (f := fun j z => u j * s z j) _ fun j _ => analyticAt_const.mul (analyticAt_pi_iff.1 hs j)`.

Establish `hsq : ((√ε : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (Real.sqrt_pos.2 hε).ne'`. Establish `he : logReg u ε ∘ s = fun z => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot (τ z) + Real.log ε / 2`. Use function extensionality and compare the values at `z`. Establish `h1 : HilbertSamuel.ProjFS.logPot (τ z) = Real.log (1 + ‖linEval u (s z)‖ ^ 2 / ε)` using `by show Real.log (1 + euclPot (τ z)) = _`. Use `congr 2`.

Simplify using `only [euclPot, hτ, Finset.univ_unique, Finset.sum_singleton, norm_mul, norm_inv, mul_pow, inv_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg ε), Real.sq_sqrt hε.le]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ‖linEval u (s z)‖ ^ 2 + ε = ε * (1 + ‖linEval u (s z)‖ ^ 2 / ε)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Function.comp_apply, logReg]`. Rewrite using `[h1, h2, Real.log_mul hε.ne' (by positivity)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hconst : ∀ (F : (Fin D → ℂ) → ℝ) (c : ℝ), hessC (fun z => F z + c) y = hessC F y`. Introduce `F c`.

Establish `h : fderiv ℝ (fun z => F z + c) = fderiv ℝ F` using `funext fun z => fderiv_add_const c`. Unfold `hessC`. Rewrite using `[h]`. Establish `hL2 : ContDiffAt ℝ 2 (HilbertSamuel.ProjFS.logPot (N` using `1)) (τ y) := ((SheetFormComparison.contDiff_logPot 1).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt`. Rewrite using `[he, hconst (fun z => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot (τ z)), ReciprocityTheory.AnForm.M.hessC_const_mul']`.

Establish `hcomp : hessC (fun z => HilbertSamuel.ProjFS.logPot (τ z)) y = hessC (HilbertSamuel.ProjFS.logPot ∘ τ) y` using `rfl`. Rewrite using `[hcomp, ReciprocityTheory.AnForm.A.hessC_comp _ τ y hτa hL2]`. Establish `hP : (hessC (HilbertSamuel.ProjFS.logPot (N` using `1)) (τ y)).PosSemidef := ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ hL2 fun w => HilbertSamuel.ProjFS.levi_logPot_nonneg _ w`. Use `set B := (ReciprocityTheory.AnForm.A.jacC τ y).map (starRingEnd ℂ) with hB`. Establish `hBJ : Bᴴ = (ReciprocityTheory.AnForm.A.jacC τ y)ᵀ`.

Use extensionality with `a b`. Simplify using `[hB]`. Rewrite using `[← hBJ]`. Conclude with `(hP.conjTranspose_mul_mul_same B).smul (Complex.zero_le_real.2 (by norm_num))`.
-/
theorem posSemidef_hessC_logReg_comp {n D : ℕ} (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε)
    (s : (Fin D → ℂ) → Fin n → ℂ) (y : Fin D → ℂ) (hs : AnalyticAt ℂ s y) :
    (hessC (logReg u ε ∘ s) y).PosSemidef := by
  set τ : (Fin D → ℂ) → Fin 1 → ℂ := fun z _ => ((√ε : ℝ) : ℂ)⁻¹ * linEval u (s z) with hτ
  have hτa : AnalyticAt ℂ τ y := by
    refine analyticAt_pi_iff.2 fun _ => analyticAt_const.mul ?_
    unfold linEval
    exact Finset.analyticAt_fun_sum (f := fun j z => u j * s z j) _ fun j _ =>
      analyticAt_const.mul (analyticAt_pi_iff.1 hs j)
  have hsq : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hε).ne'
  have he : logReg u ε ∘ s =
      fun z => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot (τ z) + Real.log ε / 2 := by
    funext z
    have h1 : HilbertSamuel.ProjFS.logPot (τ z) = Real.log (1 + ‖linEval u (s z)‖ ^ 2 / ε) := by
      show Real.log (1 + euclPot (τ z)) = _
      congr 2
      simp only [euclPot, hτ, Finset.univ_unique, Finset.sum_singleton, norm_mul, norm_inv, mul_pow,
        inv_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg ε),
        Real.sq_sqrt hε.le]
      ring
    have h2 : ‖linEval u (s z)‖ ^ 2 + ε = ε * (1 + ‖linEval u (s z)‖ ^ 2 / ε) := by
      field_simp
      ring
    simp only [Function.comp_apply, logReg]
    rw [h1, h2, Real.log_mul hε.ne' (by positivity)]
    ring
  have hconst : ∀ (F : (Fin D → ℂ) → ℝ) (c : ℝ), hessC (fun z => F z + c) y = hessC F y := by
    intro F c
    have h : fderiv ℝ (fun z => F z + c) = fderiv ℝ F := funext fun z => fderiv_add_const c
    unfold hessC
    rw [h]
  have hL2 : ContDiffAt ℝ 2 (HilbertSamuel.ProjFS.logPot (N := 1)) (τ y) :=
    ((SheetFormComparison.contDiff_logPot 1).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  rw [he, hconst (fun z => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot (τ z)),
    ReciprocityTheory.AnForm.M.hessC_const_mul']
  have hcomp : hessC (fun z => HilbertSamuel.ProjFS.logPot (τ z)) y =
      hessC (HilbertSamuel.ProjFS.logPot ∘ τ) y := rfl
  rw [hcomp, ReciprocityTheory.AnForm.A.hessC_comp _ τ y hτa hL2]
  have hP : (hessC (HilbertSamuel.ProjFS.logPot (N := 1)) (τ y)).PosSemidef :=
    ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ hL2 fun w => HilbertSamuel.ProjFS.levi_logPot_nonneg _ w
  set B := (ReciprocityTheory.AnForm.A.jacC τ y).map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = (ReciprocityTheory.AnForm.A.jacC τ y)ᵀ := by
    ext a b
    simp [hB]
  rw [← hBJ]
  exact (hP.conjTranspose_mul_mul_same B).smul (Complex.zero_le_real.2 (by norm_num))

/- English proof (translation)
Establish `hE2 : ∀ _ : Fin d, ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y)` using `fun _ => ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt`. Establish `hb : ∀ _ : Fin d, (hessC (euclPot : (Fin n → ℂ) → ℝ) (s y) + ((1 : ℝ) : ℂ) • 1).PosSemidef ∧ (-hessC (euclPot : (Fin n → ℂ) → ℝ) (s y) + ((1 : ℝ) : ℂ) • 1).PosSemidef` using `fun _ => by`. Rewrite using `[hessC_euclPot]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `using Matrix.PosSemidef.one.add Matrix.PosSemidef.one`.

Simplify using `using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℂ).PosSemidef)`. Establish `key` using `abs_maDens_cons_le g (fun _ : Fin d => euclPot) s y hs hE2 hb hM`. Establish `h0` using `(abs_nonneg _).trans key`. Rewrite `h0` using `[one_pow, mul_one]`. Conclude with `nonneg_of_mul_nonneg_right h0 (by positivity)`.
-/
theorem maDens_euclPot_nonneg {n d : ℕ} (g : (Fin n → ℂ) → ℝ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (y : Fin (d + 1) → ℂ) (hs : AnalyticAt ℂ s y) (hM : (hessC (g ∘ s) y).PosSemidef) :
    0 ≤ maDens (fun k => vecCons g (fun _ : Fin d => euclPot) k ∘ s) y := by
  have hE2 : ∀ _ : Fin d, ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) := fun _ =>
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hb : ∀ _ : Fin d, (hessC (euclPot : (Fin n → ℂ) → ℝ) (s y) + ((1 : ℝ) : ℂ) • 1).PosSemidef ∧
      (-hessC (euclPot : (Fin n → ℂ) → ℝ) (s y) + ((1 : ℝ) : ℂ) • 1).PosSemidef := fun _ => by
    rw [hessC_euclPot]
    refine ⟨?_, ?_⟩
    · simpa using Matrix.PosSemidef.one.add Matrix.PosSemidef.one
    · simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℂ).PosSemidef)
  have key := abs_maDens_cons_le g (fun _ : Fin d => euclPot) s y hs hE2 hb hM
  have h0 := (abs_nonneg _).trans key
  rw [one_pow, mul_one] at h0
  exact nonneg_of_mul_nonneg_right h0 (by positivity)

end RegularizedFormComparison

open TubeFormComparison RegularizedFormComparison in

/- English proof (translation)
Introduce `n d J A φ f _hJ _hdim hA hφ hfc hfs`. Use `set K := zeroSet J ∩ tsupport f with hKdef`. Establish `hK : IsCompact K` using `hfs.isCompact.inter_left (isClosed_zeroSet J)`. Use `choose U hU hZU hφU using hφ`. Take `⟨c, hc, hb⟩` from `exists_hessC_bound φ K hK U hU (fun i => Set.inter_subset_left.trans (hZU i)) (fun i => (hφU i).of_le (WithTop.coe_le_coe.2 le_top))`.

Take `⟨M, hM⟩` from `hfc.bounded_above_of_compact_support hfs`. Establish `hM0 : 0 ≤ max M 0` using `le_max_right _ _`. Establish `hC : 0 ≤ max M 0 * (3 ^ (d + 1) * c ^ d)` using `by positivity`. Use `⟨max M 0 * (3 ^ (d + 1) * c ^ d), hC, fun u ε hε v w hw hvw y => ?_⟩` and prove the remaining obligations. Unfold `chartDens chartAbsDens sheetSum`.

Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y), finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y), Finset.mul_sum]`. Use `Finset.sum_le_sum fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[Set.Finite.mem_toFinset]`. Take `⟨hxZ, hxy⟩` from `hx`. Substitute `hxy` using the available equality.

Use `split_ifs with hsx`. Use `swap`. Simplify using the standard rewrite rules. Simplify using `only`. Take `⟨V, hV, hyV, hsd, hsx', -, -⟩` from `hsx.choose_spec`.

Use `set s := hsx.choose with hsdef`. Establish `hsa : AnalyticAt ℂ s (A *ᵥ x)` using `analyticAt_pi_iff.2 fun i => ReciprocityTheory.AnForm.Osgood.osgood _ V (fun z => s z i) hV (differentiableOn_pi.1 hsd i) _ hyV`. Establish `hMs` using `posSemidef_hessC_logReg_comp u hε s (A *ᵥ x) hsa`. Establish `hE` using `maDens_euclPot_nonneg (logReg u ε) s (A *ᵥ x) hsa hMs`. Distinguish the cases in `hxf : x ∈ tsupport f`.

Establish `hφx : ∀ i, ContDiffAt ℝ 2 (φ i) (s (A *ᵥ x))` using `fun i => by`. Rewrite using `[hsx']`. Conclude with `((hφU i).contDiffAt ((hU i).mem_nhds (hZU i hxZ))).of_le (WithTop.coe_le_coe.2 le_top)`. Establish `hbx : ∀ i, (hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef ∧ (-hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef` using `fun i => by`. Rewrite using `[hsx']`.

Conclude with `hb i x ⟨hxZ, hxf⟩`. Establish `key` using `abs_maDens_cons_le _ φ s (A *ᵥ x) hsa hφx hbx hMs`. Establish `hfx : |f x| ≤ max M 0` using `(Real.norm_eq_abs (f x) ▸ hM x).trans (le_max_left _ _)`. Establish `hvx : |v x| ≤ w x` using `hvw x hxf`. Rewrite using `[abs_mul, abs_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hwx` using `hw x`. Establish `hK0 : 0 ≤ (3 : ℝ) ^ (d + 1) * c ^ d` using `by positivity`. Establish `h1 : |v x| * |f x| ≤ w x * max M 0` using `mul_le_mul hvx hfx (abs_nonneg _) (hw x)`. Combine the equalities or inequalities in the displayed calculation.

Use `_ = _ := by ring`. Rewrite using `[image_eq_zero_of_notMem_tsupport hxf, mul_zero, zero_mul, abs_zero]`. Conclude with `mul_nonneg hC (mul_nonneg (hw x) hE)`.
-/
theorem RegFormCompare.proof : RegFormCompare.Statement := by
  intro n d J A φ f _hJ _hdim hA hφ hfc hfs
  set K := zeroSet J ∩ tsupport f with hKdef
  have hK : IsCompact K := hfs.isCompact.inter_left (isClosed_zeroSet J)
  choose U hU hZU hφU using hφ
  obtain ⟨c, hc, hb⟩ := exists_hessC_bound φ K hK U hU
    (fun i => Set.inter_subset_left.trans (hZU i)) (fun i => (hφU i).of_le (WithTop.coe_le_coe.2 le_top))
  obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hC : 0 ≤ max M 0 * (3 ^ (d + 1) * c ^ d) := by positivity
  refine ⟨max M 0 * (3 ^ (d + 1) * c ^ d), hC, fun u ε hε v w hw hvw y => ?_⟩
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y),
    finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y), Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, hxy⟩ := hx
  subst hxy
  split_ifs with hsx
  swap
  · simp
  dsimp only
  obtain ⟨V, hV, hyV, hsd, hsx', -, -⟩ := hsx.choose_spec
  set s := hsx.choose with hsdef
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ V (fun z => s z i) hV (differentiableOn_pi.1 hsd i) _ hyV
  have hMs := posSemidef_hessC_logReg_comp u hε s (A *ᵥ x) hsa
  have hE := maDens_euclPot_nonneg (logReg u ε) s (A *ᵥ x) hsa hMs
  by_cases hxf : x ∈ tsupport f
  · have hφx : ∀ i, ContDiffAt ℝ 2 (φ i) (s (A *ᵥ x)) := fun i => by
      rw [hsx']
      exact ((hφU i).contDiffAt ((hU i).mem_nhds (hZU i hxZ))).of_le (WithTop.coe_le_coe.2 le_top)
    have hbx : ∀ i, (hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef ∧
        (-hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef := fun i => by
      rw [hsx']
      exact hb i x ⟨hxZ, hxf⟩
    have key := abs_maDens_cons_le _ φ s (A *ᵥ x) hsa hφx hbx hMs
    have hfx : |f x| ≤ max M 0 := (Real.norm_eq_abs (f x) ▸ hM x).trans (le_max_left _ _)
    have hvx : |v x| ≤ w x := hvw x hxf
    rw [abs_mul, abs_mul]
    calc |v x| * |f x| * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)|
        ≤ w x * max M 0 * (3 ^ (d + 1) * c ^ d *
            maDens (fun k => vecCons (logReg u ε) (fun _ => euclPot) k ∘ s) (A *ᵥ x)) := by
          have hwx := hw x
          have hK0 : 0 ≤ (3 : ℝ) ^ (d + 1) * c ^ d := by positivity
          have h1 : |v x| * |f x| ≤ w x * max M 0 := mul_le_mul hvx hfx (abs_nonneg _) (hw x)
          calc |v x| * |f x| * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)|
              ≤ w x * max M 0 * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left key (mul_nonneg hwx hM0)
      _ = _ := by ring
  · rw [image_eq_zero_of_notMem_tsupport hxf, mul_zero, zero_mul, abs_zero]
    exact mul_nonneg hC (mul_nonneg (hw x) hE)

end

end GroundTheory.Heights₂.Heights
