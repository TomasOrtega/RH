import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarizableComplexRepOfSupercuspidalUnitaryCentralCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealExponentAbsSmoothCharacterLocalField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CuspRealTwist

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem main : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (y : IrrGL k), y.IsCusp →
    ∃ (ρ : IrrGL k) (z : ℝ), ρ.IsCusp ∧ IsUnitarisable ρ.rep ∧ y = ρ.nu z := by
  intro _ k _ _ _ _ _ y hy
  obtain ⟨ω, hωs, hω⟩ := exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr
  obtain ⟨s, hs⟩ := GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow k ω hωs
  have hN : (y.1 : ℝ) ≠ 0 := by exact_mod_cast hy.1.ne'
  refine ⟨y.nu ((-(s / y.1) : ℝ) : ℂ), s / y.1, hy.nu _, ?_, ?_⟩
  · have hρc : (y.nu ((-(s / y.1) : ℝ) : ℂ)).IsCusp := hy.nu _
    have hcc := UnitaryOrder.hasCentralChar_nu y hω ((-(s / y.1) : ℝ) : ℂ)
    have hi := (y.nu ((-(s / y.1) : ℝ) : ℂ)).2.rep.irr
    have hsm := (y.nu ((-(s / y.1) : ℝ) : ℂ)).2.rep.smooth
    haveI := Model.nontrivial_of_isIrreducible hi
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : (y.nu ((-(s / y.1) : ℝ) : ℂ)).2.rep.V)
    obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hsm (GlobalTheory.SqIntUnit.compactOpen_basis k _) hv₀
    refine GlobalTheory.isUnitarisable_of_isSupercuspidal _ _ _ (l : Module.Dual ℂ _) l.2
      (fun e => hl (by rw [e]; rfl)) hi (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k _ _ _ hρc.2) ?_
    intro g hg
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨a, rfl⟩ := hg
    refine ⟨_, ?_, hcc a⟩
    have h1 := UnitaryOrder.log_norm_mul_absPow ω (-(s / y.1)) y.1 a
    have hpos := nabs_pos' k a
    rw [hs a, Real.log_rpow hpos] at h1
    have h2 : Real.log ‖(((ω * absPow k ((-(s / y.1) : ℝ) : ℂ) ^ y.1) a : ℂˣ) : ℂ)‖ = 0 := by
      rw [h1]; field_simp; ring
    exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.2 (Units.ne_zero _)) h2
  · rw [IrrGL.nu_nu, show ((-(s / y.1) : ℝ) : ℂ) + ((s / y.1 : ℝ) : ℂ) = 0 by push_cast; ring, IrrGL.nu_zero]

end GlobalTheory.CuspRealTwist
