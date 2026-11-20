import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveZNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodReductionModelCmPeriodFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmExistsClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Introduce a local definition for the expression. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify using the standard rewrite rules. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem exists_curve0_hasPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d]
    (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) →
    ∃ (Z : Curve0 H ρ) (x : ℝ), Z.z ≠ 0 ∧ Z.C.HasPeriod x ∧
      (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) -
        deriv χ.LFunction 1 / χ.LFunction 1 := by
  intro E _ _ _ H _ χ hχ ρ hρ
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hU := GlobalTheory.thetaUnifAV_closed
  have hX := GlobalTheory.CM.homExtDvr_of_card_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional
  obtain ⟨M, _, ω, C, x, hω, hpr, hper, hx⟩ := GlobalTheory.T.exists_cmEllipticCurve_integers_with_period GlobalTheory.T.exists_cmEllipticCurve_withPeriod hU hL hX E H χ hχ ρ hρ
  obtain ⟨C', π, c'⟩ := exists_ellMap hL.polBaseChange E H _ ω C ℂ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))
  obtain ⟨u, hu⟩ := PureType.exists_isThetaUnif hU C'.P
  obtain ⟨c, hc, hΛ⟩ := hpr C'.P π c'.2.1 u
  obtain ⟨Hm, χ', Ef, h1, h2, h3⟩ := id hu
  obtain ⟨w, hw, -⟩ := h2 C'.v (C'.basis.1 0)
  have hd := C'.dim
  let Z : Curve0 H ρ := ⟨M, ω, C, hω, C', π, c', u, hu, c, hc, hΛ, w ⟨0, by omega⟩ / c, by
    convert hw using 1
    funext j
    rw [mul_div_cancel₀ _ hc]
    congr 1
    apply Fin.ext
    have := j.2
    simp only
    omega⟩
  exact ⟨Z, x, GlobalTheory.T.curve_z_ne_zero E H ρ Z, hper, hx⟩

end GlobalTheory.CompanionTheory.Ar.Fl
