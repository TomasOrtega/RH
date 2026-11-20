import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFinNormComparison
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise

noncomputable section

namespace GlobalTheory.LevelGrowth

/- English proof (translation)
Introduce `D ψ θ hθ ε M X χ χ' ω hω Φ hΦ C₁ hC₁`. Take `⟨U, hU, hΦU⟩` from `GlobalTheory.Size.isTheta_iff_level.1 hΦ`. Take `⟨K₀, h0, hK₀, m, hlev⟩` from `GlobalTheory.KernelSeminorm.exists_level_multiple (S := sgn ε M) (T := X) hU`. Take `⟨B, hB⟩` from `hC₁.bddAbove_image ((GlobalTheory.Grow.continuous_height (sgn ε M)).comp (continuous_ofSgn_symm ε M)).continuousOn`. Take `⟨C, hC, hcmp⟩` from `GlobalTheory.Grow.height_comparison X hθ`.

Use `⟨K₀, h0, hK₀, m * max B 0 * C, 1, fun y hy h => ?_⟩` and prove the remaining obligations. Use `set g := (ofSgn ε M).symm y with hg`. Take `⟨n, hn, hnle, hmem⟩` from `hlev g h`. Use `⟨n, hn, ?_, fun u hu hinf => ?_⟩` and prove the remaining obligations. Establish `hgB : GlobalTheory.Grow.height (sgn ε M) g ≤ max B 0` using `(hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)`.

Establish `hhC : GlobalTheory.Grow.height X h ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ)` using `(hcmp h).2`. Establish `hm0 : (0 : ℝ) ≤ m` using `m.cast_nonneg`. Establish `hg0` using `(GlobalTheory.Grow.height_pos (sgn ε M) g).le`. Establish `hh0` using `(GlobalTheory.Grow.height_pos X h).le`. Combine the equalities or inequalities in the displayed calculation.

Establish `hv : (actO (sgn ε M) X g⁻¹ h⁻¹ (n • u)).map (infPart D) = 0`. Establish `: (n • u).map (infPart D) = 0`. Use extensionality with `i j`. Establish `h3 : infPart D (u i j) = 0` using `congrFun (congrFun hinf i) j`. Conclude with `(map_nsmul (infPart D) n (u i j)).trans ((congrArg (n • ·) h3).trans (nsmul_zero n))`.

Unfold `actO`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, this, Matrix.mul_zero, Matrix.zero_mul]`. Establish `hfix` using `hΦU.2 _ (hmem u hu hinf) hv`. Establish `e` using `hω.om_heis g h (actO (sgn ε M) X g⁻¹ h⁻¹ (n • u)) Φ hΦ`. Rewrite `e` using `[hfix, GlobalTheory.ThetaGrowth.actO_mul, mul_inv_cancel, mul_inv_cancel, GlobalTheory.ThetaGrowth.actO_one]`.

Establish `e2 : (WRep.toSgn ε ω) (g, h) = ω (y, h)`. Simplify using `[WRep.toSgn, hg]`. Rewrite `e` using `[e2]`. Conclude with `e.symm`.
-/
theorem level_poly : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (Φ : WO M X → ℂ) (hΦ : IsThetaFunO ψ (sgn ε M) X Φ)
    (C₁ : Set (GA D M)) (hC₁ : IsCompact C₁),
    ∃ K₀ : Set (WO M X), K₀ ∈ nhds (0 : WO M X) ∧ IsCompact K₀ ∧ ∃ (m : ℝ) (e : ℕ), ∀ y ∈ C₁, ∀ h : GA D X,
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ m * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ e ∧
        ∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ (sgn ε M) X (n • u) (ω (y, h) Φ) = ω (y, h) Φ := by
  intro D ψ θ hθ ε M X χ χ' ω hω Φ hΦ C₁ hC₁
  obtain ⟨U, hU, hΦU⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨K₀, h0, hK₀, m, hlev⟩ := GlobalTheory.KernelSeminorm.exists_level_multiple (S := sgn ε M) (T := X) hU
  obtain ⟨B, hB⟩ := hC₁.bddAbove_image
    ((GlobalTheory.Grow.continuous_height (sgn ε M)).comp (continuous_ofSgn_symm ε M)).continuousOn
  obtain ⟨C, hC, hcmp⟩ := GlobalTheory.Grow.height_comparison X hθ
  refine ⟨K₀, h0, hK₀, m * max B 0 * C, 1, fun y hy h => ?_⟩
  set g := (ofSgn ε M).symm y with hg
  obtain ⟨n, hn, hnle, hmem⟩ := hlev g h
  refine ⟨n, hn, ?_, fun u hu hinf => ?_⟩
  · have hgB : GlobalTheory.Grow.height (sgn ε M) g ≤ max B 0 := (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)
    have hhC : GlobalTheory.Grow.height X h ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := (hcmp h).2
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    have hg0 := (GlobalTheory.Grow.height_pos (sgn ε M) g).le
    have hh0 := (GlobalTheory.Grow.height_pos X h).le
    calc (n : ℝ) ≤ m * (GlobalTheory.Grow.height (sgn ε M) g * GlobalTheory.Grow.height X h) := hnle
      _ ≤ m * (max B 0 * (C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hgB hhC hh0 (le_max_right _ _)) hm0
      _ = m * max B 0 * C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ 1 := by ring
  · have hv : (actO (sgn ε M) X g⁻¹ h⁻¹ (n • u)).map (infPart D) = 0 := by
      have : (n • u).map (infPart D) = 0 := by
        ext i j
        have h3 : infPart D (u i j) = 0 := congrFun (congrFun hinf i) j
        exact (map_nsmul (infPart D) n (u i j)).trans ((congrArg (n • ·) h3).trans (nsmul_zero n))
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, this, Matrix.mul_zero, Matrix.zero_mul]
    have hfix := hΦU.2 _ (hmem u hu hinf) hv
    have e := hω.om_heis g h (actO (sgn ε M) X g⁻¹ h⁻¹ (n • u)) Φ hΦ
    rw [hfix, GlobalTheory.ThetaGrowth.actO_mul, mul_inv_cancel, mul_inv_cancel, GlobalTheory.ThetaGrowth.actO_one] at e
    have e2 : (WRep.toSgn ε ω) (g, h) = ω (y, h) := by
      simp [WRep.toSgn, hg]
    rw [e2] at e
    exact e.symm

end GlobalTheory.LevelGrowth
