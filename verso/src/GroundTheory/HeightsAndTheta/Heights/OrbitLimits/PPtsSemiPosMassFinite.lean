import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSemiPosMassFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSegreChartFibreSum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartProjFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreCoordGoodProj
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSheetHessPSD
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open scoped ComplexOrder
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj pot sheetDensity fibre mcPts segre
  maDensity cxHessian IsSheet)

namespace PtsSemiPosMassFinite

/- English proof (translation)
Establish `hs : (Function.support fun x => |G x|) = Function.support G`. Use extensionality with `x`. Simplify using the standard rewrite rules. Distinguish the cases in `h : (Function.support G).Finite`. Rewrite using `[finsum_eq_sum_of_support_subset G (s := h.toFinset) (by simp), finsum_eq_sum_of_support_subset (fun x => |G x|) (s := h.toFinset) (by simp [hs])]`.

Conclude with `Finset.sum_le_sum fun x _ => le_abs_self _`. Rewrite using `[finsum_of_infinite_support h, finsum_of_infinite_support (by rwa [hs])]`.
-/
theorem finsum_le_finsum_abs {α : Type*} (G : α → ℝ) : ∑ᶠ x, G x ≤ ∑ᶠ x, |G x| := by
  have hs : (Function.support fun x => |G x|) = Function.support G := by
    ext x
    simp
  by_cases h : (Function.support G).Finite
  · rw [finsum_eq_sum_of_support_subset G (s := h.toFinset) (by simp),
      finsum_eq_sum_of_support_subset (fun x => |G x|) (s := h.toFinset) (by simp [hs])]
    exact Finset.sum_le_sum fun x _ => le_abs_self _
  · rw [finsum_of_infinite_support h, finsum_of_infinite_support (by rwa [hs])]

/- English proof (translation)
Unfold `chartDens chartAbsDens sheetSum`. Use `(finsum_le_finsum_abs _).trans (le_of_eq (finsum_congr fun x => ?_))` and prove the remaining obligations. Rewrite using `[finsum_eq_if, finsum_eq_if]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem chartDens_le_chartAbsDens {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    chartDens J A f φ y ≤ chartAbsDens J A f φ y := by
  classical
  unfold chartDens chartAbsDens sheetSum
  refine (finsum_le_finsum_abs _).trans (le_of_eq (finsum_congr fun x => ?_))
  rw [finsum_eq_if, finsum_eq_if]
  split_ifs <;> simp

/- English proof (translation)
Unfold `sheetDensity`. Use `split_ifs with hγ`. Rewrite using `[one_mul]`. Establish `hpsd : ∀ j, (cxHessian (fun y' => pot N j (hγ.choose y')) y).PosSemidef` using `fun j => Inter.SheetHessPSD.proof K ι P e Ψ (N j) y w _ (hNs j) (hNp j) hγ.choose_spec`. Unfold `maDensity`.

Conclude with `mul_nonneg (by positivity) (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef _ hpsd).2`. Conclude with `le_rfl`.
-/
theorem sheetDensity_nonneg {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {N : Fin e → HermLine ι}
    (hNs : ∀ j, IsSmoothHerm (N j)) (hNp : ∀ j, Inter.IsSemiPosHerm (N j)) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : 0 ≤ sheetDensity P Ψ (pot N) (fun _ => 1) y w := by
  unfold sheetDensity
  split_ifs with hγ
  · rw [one_mul]
    have hpsd : ∀ j, (cxHessian (fun y' => pot N j (hγ.choose y')) y).PosSemidef := fun j =>
      Inter.SheetHessPSD.proof K ι P e Ψ (N j) y w _ (hNs j) (hNp j) hγ.choose_spec
    unfold maDensity
    exact mul_nonneg (by positivity) (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef _ hpsd).2
  · exact le_rfl

end PtsSemiPosMassFinite

/- English proof (translation)
Introduce `K _ ι _ P e Ψ N hP hΨ hNs hNp`. Distinguish the cases in `hZ : (mcPts P).Nonempty`. Take `⟨z0, hz0⟩` from `hZ choose i hi using hz0.1`. Establish `hsi : segre z0 i ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => hi k`. Take `⟨Ψ', hΨ', hΨ'0⟩` from `SegreCoordGoodProj.proof K ι P e i hP ⟨z0, hz0, hsi⟩`.

Rewrite using `[hI K ι P e Ψ Ψ' N (fun _ => 1) hP hΨ hΨ' hNs measurable_const (fun _ _ _ => rfl)]`. Use `set σ : Fin (Fintype.card ((k : K) → ι k)) ≃ ((k : K) → ι k) := (Fintype.equivFin _).symm`. Establish `hfs` using `hF K ι P e _ σ i N (fun _ => 1) Ψ' hP hNs (isDegZeroSmooth_const 1) hΨ' hΨ'0`. Establish `hint : Integrable (fun y => ∑ J ∈ segreChartComponents P σ i, chartAbsDens J (chartProjMatrix σ Ψ') (chartWeight σ i (fun _ => 1)) (chartPot σ i N) y)` using `integrable_finsetSum _ fun J hJ => hA K ι P e _ σ i N (fun _ => 1) hP hNs (isDegZeroSmooth_const 1) J hJ _ (SegreChartProjFinite.proof K ι P e _ σ i Ψ' hP hΨ' hΨ'0 J hJ)`. Use `lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top` and prove the remaining obligations.

Use `filter_upwards [hfs] with y hy`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `hpos : ptsPosDens P Ψ' (pot N) (fun _ => 1) y = ∑ᶠ w ∈ fibre P Ψ' y, sheetDensity P Ψ' (pot N) (fun _ => 1) y w`. Unfold `ptsPosDens`. Conclude with `finsum_congr fun w => finsum_congr fun _ => max_eq_left (PtsSemiPosMassFinite.sheetDensity_nonneg hNs hNp y w)`.

Rewrite using `[hpos, hy]`. Conclude with `Finset.sum_le_sum fun J _ => PtsSemiPosMassFinite.chartDens_le_chartAbsDens _ _ _ _ _`. Establish `h0 : ∀ y, ptsPosDens P Ψ (pot N) (fun _ => 1) y = 0`. Introduce `y`. Establish `hf : fibre P Ψ y = ∅`.

Use extensionality with `w`. Simplify using `only [fibre, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨z, hz, -⟩`. Conclude with `hZ ⟨z, hz⟩`. Simplify using `[ptsPosDens, hf]`.

Simplify using `[h0]`.
-/
theorem PtsSemiPosMassFinite.proof (hI : PtsPosPartProjIndep.Statement) (hF : PtsSegreChartFibreSum.Statement)
    (hA : SegreChartAbsIntegrable.Statement) : PtsSemiPosMassFinite.Statement := by
  intro K _ ι _ P e Ψ N hP hΨ hNs hNp
  classical
  by_cases hZ : (mcPts P).Nonempty
  · obtain ⟨z0, hz0⟩ := hZ
    choose i hi using hz0.1
    have hsi : segre z0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hi k
    obtain ⟨Ψ', hΨ', hΨ'0⟩ := SegreCoordGoodProj.proof K ι P e i hP ⟨z0, hz0, hsi⟩
    rw [hI K ι P e Ψ Ψ' N (fun _ => 1) hP hΨ hΨ' hNs measurable_const (fun _ _ _ => rfl)]
    set σ : Fin (Fintype.card ((k : K) → ι k)) ≃ ((k : K) → ι k) := (Fintype.equivFin _).symm
    have hfs := hF K ι P e _ σ i N (fun _ => 1) Ψ' hP hNs (isDegZeroSmooth_const 1) hΨ' hΨ'0
    have hint : Integrable (fun y => ∑ J ∈ segreChartComponents P σ i,
        chartAbsDens J (chartProjMatrix σ Ψ') (chartWeight σ i (fun _ => 1)) (chartPot σ i N) y) :=
      integrable_finsetSum _ fun J hJ =>
        hA K ι P e _ σ i N (fun _ => 1) hP hNs (isDegZeroSmooth_const 1) J hJ _
          (SegreChartProjFinite.proof K ι P e _ σ i Ψ' hP hΨ' hΨ'0 J hJ)
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
    filter_upwards [hfs] with y hy
    refine ENNReal.ofReal_le_ofReal ?_
    have hpos : ptsPosDens P Ψ' (pot N) (fun _ => 1) y =
        ∑ᶠ w ∈ fibre P Ψ' y, sheetDensity P Ψ' (pot N) (fun _ => 1) y w := by
      unfold ptsPosDens
      exact finsum_congr fun w => finsum_congr fun _ =>
        max_eq_left (PtsSemiPosMassFinite.sheetDensity_nonneg hNs hNp y w)
    rw [hpos, hy]
    exact Finset.sum_le_sum fun J _ => PtsSemiPosMassFinite.chartDens_le_chartAbsDens _ _ _ _ _
  · have h0 : ∀ y, ptsPosDens P Ψ (pot N) (fun _ => 1) y = 0 := by
      intro y
      have hf : fibre P Ψ y = ∅ := by
        ext w
        simp only [fibre, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨z, hz, -⟩
        exact hZ ⟨z, hz⟩
      simp [ptsPosDens, hf]
    simp [h0]

end GroundTheory.Heights₂.Heights
