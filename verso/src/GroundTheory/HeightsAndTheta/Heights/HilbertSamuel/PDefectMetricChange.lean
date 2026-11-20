import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRealGramComparison
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexGramMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMixedIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ATeleSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

/- English proof (translation)
Establish `hB` using `tele_smooth_ratio hs₀ hs₁`. Establish `hsymm` using `(hI Unit (GlobalTheory κ)).1`. Establish `hadd` using `(hI Unit (GlobalTheory κ)).2.1`. Establish `htel` using `Finset.sum_range_sub (fun i => I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i)) (D + 1)`. Establish `hT0 : tele_fam m₀ m₁ (D + 1) 0 = fun _ => HermLine.ofCone m₀`.

Use function extensionality and compare the values at `j`. Simplify using `[tele_fam]`. Establish `hT1 : tele_fam m₀ m₁ (D + 1) (D + 1) = fun _ => HermLine.ofCone m₁`. Use function extensionality and compare the values at `j`. Simplify using `[tele_fam, j.isLt]`.

Simplify using `only [hT0, hT1] at htel`. Unfold `top`. Rewrite using `[← htel]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_range]`.

Establish `e1 : I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) (i + 1)) = I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (Fin.snoc (tele_fam m₀ m₁ D i) (HermLine.ofCone m₁))`. Rewrite using `[← tele_fam_succAbove m₀ m₁ D i hi (i + 1) (Or.inr rfl)]`. Establish `: HermLine.ofCone m₁ = tele_fam m₀ m₁ (D + 1) (i + 1) ⟨i, hi⟩`. Simplify using `[tele_fam]`. Rewrite using `[this, ← tele_comp_perm]`.

Conclude with `(hsymm _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _)).symm`. Establish `e0 : I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i) = I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (Fin.snoc (tele_fam m₀ m₁ D i) (HermLine.ofCone m₀))`. Rewrite using `[← tele_fam_succAbove m₀ m₁ D i hi i (Or.inl rfl)]`. Establish `: HermLine.ofCone m₀ = tele_fam m₀ m₁ (D + 1) i ⟨i, hi⟩`. Simplify using `[tele_fam]`.

Rewrite using `[this, ← tele_comp_perm]`. Conclude with `(hsymm _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _)).symm`. Rewrite using `[e1, e0, tele_ofCone_tensor m₀ m₁, hadd _ _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _) (tele_smooth_ofCone hs₀) hB, add_sub_cancel_left, fam_degZero I hI hP _ (tele_fam_smooth hs₀ hs₁ _ _) _ hB rfl]`. Establish `hpot : pot (tele_fam m₀ m₁ D i) = mixPot m₀ m₁ D i`. Use function extensionality and compare the values at `j z`.

Simplify using `only [pot, mixPot, tele_fam]`. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[hpot]`. Both sides reduce to the same expression.
-/
theorem top_sub_top_mixPot (I : AllFam) (hI : I.IsFamily) {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type}
    [Fintype κ] {x : Ix κ → Ω} {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    (hP : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) (hs₀ : IsSmoothMetric m₀)
    (hs₁ : IsSmoothMetric m₁) :
    top I x m₁ D - top I x m₀ D = ∑ i ∈ Finset.range (D + 1),
      ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ x) (mixPot m₀ m₁ D i) (logRatio m₀ m₁) := by
  classical
  have hB := tele_smooth_ratio hs₀ hs₁
  have hsymm := (hI Unit (GlobalTheory κ)).1
  have hadd := (hI Unit (GlobalTheory κ)).2.1
  have htel := Finset.sum_range_sub
    (fun i => I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i)) (D + 1)
  have hT0 : tele_fam m₀ m₁ (D + 1) 0 = fun _ => HermLine.ofCone m₀ := by
    funext j
    simp [tele_fam]
  have hT1 : tele_fam m₀ m₁ (D + 1) (D + 1) = fun _ => HermLine.ofCone m₁ := by
    funext j
    simp [tele_fam, j.isLt]
  simp only [hT0, hT1] at htel
  unfold top
  rw [← htel]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have e1 : I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) (i + 1)) =
      I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
        (Fin.snoc (tele_fam m₀ m₁ D i) (HermLine.ofCone m₁)) := by
    rw [← tele_fam_succAbove m₀ m₁ D i hi (i + 1) (Or.inr rfl)]
    have : HermLine.ofCone m₁ = tele_fam m₀ m₁ (D + 1) (i + 1) ⟨i, hi⟩ := by
      simp [tele_fam]
    rw [this, ← tele_comp_perm]
    exact (hsymm _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _)).symm
  have e0 : I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i) =
      I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
        (Fin.snoc (tele_fam m₀ m₁ D i) (HermLine.ofCone m₀)) := by
    rw [← tele_fam_succAbove m₀ m₁ D i hi i (Or.inl rfl)]
    have : HermLine.ofCone m₀ = tele_fam m₀ m₁ (D + 1) i ⟨i, hi⟩ := by
      simp [tele_fam]
    rw [this, ← tele_comp_perm]
    exact (hsymm _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _)).symm
  rw [e1, e0, tele_ofCone_tensor m₀ m₁,
    hadd _ _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _) (tele_smooth_ofCone hs₀) hB,
    add_sub_cancel_left, fam_degZero I hI hP _ (tele_fam_smooth hs₀ hs₁ _ _) _ hB rfl]
  have hpot : pot (tele_fam m₀ m₁ D i) = mixPot m₀ m₁ D i := by
    funext j z
    simp only [pot, mixPot, tele_fam]
    split_ifs <;> rfl
  rw [hpot]
  rfl

/- English proof (translation)
Introduce `D Ω _ _ κ _ I d m₁ P0₁ hs hc hle hp e hI he`. Establish `h₁` using `hR D Ω κ (d.withMetric m₁ P0₁ hs hc hle hp) e he`. Establish `h₀` using `hR D Ω κ d e he`. Establish `hc₁` using `hC D Ω κ d m₁ P0₁ hs hc hle hp e he`. Establish `htop : top I d.x m₁ D = top I d.x d.m D + ((D : ℝ) + 1) * resMetricInt d m₁`.

Rewrite using `[← hM D Ω κ d m₁ hs, ← top_sub_top_mixPot I hI d.arith d.smooth hs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlog` using `isLittleO_pow_mul_log D`. Use `(((h₁.trans_isLittleO hlog).sub (h₀.trans_isLittleO hlog)).add hc₁).congr_left fun n => ?_` and prove the remaining obligations. Simplify using `only [hsDefect, htop, Nat.factorial_succ]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem DefectMetricChange.proof (hR : RealGramComparison.Statement)
    (hC : ComplexGramMetricChange.Statement) (hM : ResolutionMixedIntegral.Statement) :
    DefectMetricChange.Statement := by
  intro D Ω _ _ κ _ I d m₁ P0₁ hs hc hle hp e hI he
  have h₁ := hR D Ω κ (d.withMetric m₁ P0₁ hs hc hle hp) e he
  have h₀ := hR D Ω κ d e he
  have hc₁ := hC D Ω κ d m₁ P0₁ hs hc hle hp e he
  have htop : top I d.x m₁ D = top I d.x d.m D + ((D : ℝ) + 1) * resMetricInt d m₁ := by
    rw [← hM D Ω κ d m₁ hs, ← top_sub_top_mixPot I hI d.arith d.smooth hs]
    ring
  have hlog := isLittleO_pow_mul_log D
  refine (((h₁.trans_isLittleO hlog).sub (h₀.trans_isLittleO hlog)).add hc₁).congr_left fun n => ?_
  simp only [hsDefect, htop, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
