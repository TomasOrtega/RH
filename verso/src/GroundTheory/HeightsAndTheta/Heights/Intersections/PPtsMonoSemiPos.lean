import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsMonoSemiPos
import GroundTheory.HeightsAndTheta.Heights.Intersections.StSheetHessPSD
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

/- English proof (translation)
Introduce `K _ ι _ Q e M E D t hQ hMs hMp hE ht hD hDa hle`. Unfold `ptsIntegral`. Distinguish the cases in `hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ`. Use `swap`. Rewrite using `[dif_neg hΨ, dif_neg hΨ]`.

Rewrite using `[dif_pos hΨ, dif_pos hΨ]`. Use `set Ψ := hΨ.choose with hΨdef`. Establish `hΨg : IsGoodProj Q Ψ` using `hΨ.choose_spec`. Unfold `ptsIntegralAt`. Establish `hD1 : IsSectionOn Q D 1`.

Use `⟨0, fun k => by simp [hDa], fun m hm k => ?_, fun h => hQ.2.1.1.ne_top ((Ideal.eq_top_iff_one Q).2 h)⟩` and prove the remaining obligations. Rewrite `hm` using `[MvPolynomial.support_one, Finset.mem_singleton]`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules. Establish `key : ∀ y w, sheetDensity Q Ψ (pot M) (fun z => Real.log (D.h z)) y w = -sheetDensity Q Ψ (pot M) (logNorm D 1) y w`.

Introduce `y w`. Unfold `sheetDensity`. Apply the tactic sequence `split_ifs <;> simp [logNorm, Real.log_inv]`. Establish `h1` using `hInt K ι Q e Ψ M E t hQ hΨg hMs hE ht`. Establish `h2 : Integrable (fun y => ∑ᶠ w ∈ fibre Q Ψ y, sheetDensity Q Ψ (pot M) (fun z => Real.log (D.h z)) y w)`.

Simplify using `only [key, finsum_neg_distrib]`. Conclude with `(hInt K ι Q e Ψ M D 1 hQ hΨg hMs hD hD1).neg`. Take `⟨a, -, hta, htQ⟩` from `ht`. Establish `hJ : IsMultiHomogIdeal (Ideal.span {t})` using `⟨{t}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hta⟩, rfl⟩`. Establish `hJQ : ¬ Ideal.span {t} ≤ Q` using `fun h => htQ (h (Ideal.subset_span rfl))`.

Establish `hnull` using `projB_null Ψ hQ hΨg hJ hJQ`. Use `integral_mono_ae h1 h2 ?_` and prove the remaining obligations. Rewrite using `[Filter.EventuallyLE, ae_iff]`. Use `measure_mono_null (fun y hy => ?_) hnull` and prove the remaining obligations. Assume the negation of the conclusion as `hyB`.

Apply `hy` to reduce the goal to its premises. Establish `hfin` using `fibreFinite K ι Q e Ψ hQ hΨg y`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]`. Use `Finset.sum_le_sum fun w _ => ?_` and prove the remaining obligations. Unfold `sheetDensity`.

Distinguish the cases in `hγ : ∃ γ, IsSheet Q Ψ y w γ`. Rewrite using `[dif_pos hγ, dif_pos hγ]`. Take `⟨-, hev⟩` from `hγ.choose_spec`. Take `⟨-, hmem, hproj⟩` from `hev.self_of_nhds`. Establish `ht0 : eval (hγ.choose y) (map (Int.castRingHom ℂ) t) ≠ 0`.

Introduce `h0`. Use `hyB ⟨hγ.choose y, hmem, ⟨hmem.1, fun f hf => ?_⟩, hproj⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hf`. Rewrite using `[map_mul, map_mul, h0, mul_zero]`. Establish `hma : 0 ≤ maDensity (fun j y' => pot M j (hγ.choose y')) y` using `ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun j => hHess K ι Q e Ψ (M j) y w hγ.choose (hMs j) (hMp j) hγ.choose_spec`.

Conclude with `mul_le_mul_of_nonneg_right (hle _ hmem ht0) hma`. Rewrite using `[dif_neg hγ, dif_neg hγ]`.
-/
theorem PtsMonoSemiPos.proof (hInt : PtsIntegrableStatement) (hHess : SheetHessPSD.Statement) :
    PtsMonoSemiPos.Statement := by
  intro K _ ι _ Q e M E D t hQ hMs hMp hE ht hD hDa hle
  classical
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ
  swap
  · rw [dif_neg hΨ, dif_neg hΨ]
  rw [dif_pos hΨ, dif_pos hΨ]
  set Ψ := hΨ.choose with hΨdef
  have hΨg : IsGoodProj Q Ψ := hΨ.choose_spec
  unfold ptsIntegralAt
  have hD1 : IsSectionOn Q D 1 := by
    refine ⟨0, fun k => by simp [hDa], fun m hm k => ?_,
      fun h => hQ.2.1.1.ne_top ((Ideal.eq_top_iff_one Q).2 h)⟩
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have key : ∀ y w, sheetDensity Q Ψ (pot M) (fun z => Real.log (D.h z)) y w =
      -sheetDensity Q Ψ (pot M) (logNorm D 1) y w := by
    intro y w
    unfold sheetDensity
    split_ifs <;> simp [logNorm, Real.log_inv]
  have h1 := hInt K ι Q e Ψ M E t hQ hΨg hMs hE ht
  have h2 : Integrable (fun y => ∑ᶠ w ∈ fibre Q Ψ y,
      sheetDensity Q Ψ (pot M) (fun z => Real.log (D.h z)) y w) := by
    simp only [key, finsum_neg_distrib]
    exact (hInt K ι Q e Ψ M D 1 hQ hΨg hMs hD hD1).neg
  obtain ⟨a, -, hta, htQ⟩ := ht
  have hJ : IsMultiHomogIdeal (Ideal.span {t}) :=
    ⟨{t}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hta⟩, rfl⟩
  have hJQ : ¬ Ideal.span {t} ≤ Q := fun h => htQ (h (Ideal.subset_span rfl))
  have hnull := projB_null Ψ hQ hΨg hJ hJQ
  refine integral_mono_ae h1 h2 ?_
  rw [Filter.EventuallyLE, ae_iff]
  refine measure_mono_null (fun y hy => ?_) hnull
  by_contra hyB
  apply hy
  have hfin := fibreFinite K ι Q e Ψ hQ hΨg y
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_le_sum fun w _ => ?_
  unfold sheetDensity
  by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
  · rw [dif_pos hγ, dif_pos hγ]
    obtain ⟨-, hev⟩ := hγ.choose_spec
    obtain ⟨-, hmem, hproj⟩ := hev.self_of_nhds
    have ht0 : eval (hγ.choose y) (map (Int.castRingHom ℂ) t) ≠ 0 := by
      intro h0
      refine hyB ⟨hγ.choose y, hmem, ⟨hmem.1, fun f hf => ?_⟩, hproj⟩
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
      rw [map_mul, map_mul, h0, mul_zero]
    have hma : 0 ≤ maDensity (fun j y' => pot M j (hγ.choose y')) y :=
      ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun j =>
        hHess K ι Q e Ψ (M j) y w hγ.choose (hMs j) (hMp j) hγ.choose_spec
    exact mul_le_mul_of_nonneg_right (hle _ hmem ht0) hma
  · rw [dif_neg hγ, dif_neg hγ]

end GroundTheory.Heights₂.Heights.Inter
