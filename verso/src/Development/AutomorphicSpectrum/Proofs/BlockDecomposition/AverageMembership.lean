import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

open MeasureTheory PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.EisMirGen

/- English proof (translation)
Unfold `AvgMem ForRep`. Introduce `G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hHaar _ _Γ P c _ φ hφ hLaw w`. Use `haveI := hHaar`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK`. Use `haveI : CompleteSpace W := FiniteDimensional.complete ℂ W`.

Express the relevant statement in the definitionally equal form `∀ r : K, (r : G) ∈ P → c r • ρ r (avg μ ρ φ w) = avg μ ρ φ w`. Introduce `r hr`. Establish `hcont : Continuous fun κ : K => φ κ • ρ κ` using `hφ.smul hρ`. Establish `hint : Integrable (fun κ : K => φ κ • ρ κ) μ` using `hcont.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))`. Establish `key : avg μ ρ φ = c r • (ρ r).comp (avg μ ρ φ)` using `by show ∫ κ, φ κ • ρ κ ∂μ = c r • (ρ r).comp (∫ κ, φ κ • ρ κ ∂μ)`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `κ`. Rewrite using `[hLaw r κ hr, map_mul]`. Use extensionality with `x`.

Simplify using `[mul_smul]`. Use `_ = c r • ∫ κ, (ContinuousLinearMap.compL ℂ W W W (ρ r)) (φ κ • ρ κ) ∂μ := integral_smul _ _`. Use `_ = c r • (ρ r).comp (∫ κ, φ κ • ρ κ ∂μ) := by`. Rewrite using `[(ContinuousLinearMap.compL ℂ W W W (ρ r)).integral_comp_comm hint]`. Both sides reduce to the same expression.

Establish `hw` using `congrArg (fun T : W →L[ℂ] W => T w) key`. Simplify using `only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply] at hw`. Conclude with `hw.symm`.
-/
theorem avgMem : AvgMem := by
  unfold AvgMem ForRep
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hHaar _ _Γ P c _ φ hφ hLaw w
  haveI := hHaar
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  change ∀ r : K, (r : G) ∈ P → c r • ρ r (avg μ ρ φ w) = avg μ ρ φ w
  intro r hr
  have hcont : Continuous fun κ : K => φ κ • ρ κ := hφ.smul hρ
  have hint : Integrable (fun κ : K => φ κ • ρ κ) μ :=
    hcont.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  have key : avg μ ρ φ = c r • (ρ r).comp (avg μ ρ φ) := by
    show ∫ κ, φ κ • ρ κ ∂μ = c r • (ρ r).comp (∫ κ, φ κ • ρ κ ∂μ)
    calc ∫ κ, φ κ • ρ κ ∂μ = ∫ κ, φ (r * κ) • ρ (r * κ) ∂μ :=
          (integral_mul_left_eq_self (fun κ => φ κ • ρ κ) r).symm
      _ = ∫ κ, c r • (ContinuousLinearMap.compL ℂ W W W (ρ r)) (φ κ • ρ κ) ∂μ := by
          congr 1
          funext κ
          rw [hLaw r κ hr, map_mul]
          ext x
          simp [mul_smul]
      _ = c r • ∫ κ, (ContinuousLinearMap.compL ℂ W W W (ρ r)) (φ κ • ρ κ) ∂μ := integral_smul _ _
      _ = c r • (ρ r).comp (∫ κ, φ κ • ρ κ ∂μ) := by
          rw [(ContinuousLinearMap.compL ℂ W W W (ρ r)).integral_comp_comm hint]
          rfl
  have hw := congrArg (fun T : W →L[ℂ] W => T w) key
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply] at hw
  exact hw.symm

end GlobalTheory.CompanionTheory.EisMirGen
