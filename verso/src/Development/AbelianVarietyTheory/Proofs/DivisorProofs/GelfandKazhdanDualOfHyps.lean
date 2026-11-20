import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotPairedId
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistCuspidalTrivialOnSplitCentreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRepPairedWithItselfStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.GelfandKazhdanTop

/- English proof (translation)
Introduce `hJS hAF hRD E _ _ _ n π`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `GlobalTheory.Published.InvTransposeModel.rank_zero π`. Take `⟨χ, hχ⟩` from `GlobalTheory.T.exists_twist_cuspidal_trivial_on_splitCentre E n hn π`. Establish `hp` using `GlobalTheory.T.cusp_rep_paired_with_itself hJS.1 (GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay hRD) hAF E n hn (π.twist χ) hχ`.

Establish `h` using `GlobalTheory.Published.InvTransposeModel.twist hp χ⁻¹`. Rewrite `h` using `[← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]`. Then use the resulting hypothesis.
-/
theorem gelfandKazhdanDual_of_rapidDecay : GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL →
    GlobalTheory.Published.CuspRapidDecaySiegelGL → GlobalTheory.Published.GelfandKazhdanDual := by
  intro hJS hAF hRD E _ _ _ n π
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact GlobalTheory.Published.InvTransposeModel.rank_zero π
  · obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_twist_cuspidal_trivial_on_splitCentre E n hn π
    have hp := GlobalTheory.T.cusp_rep_paired_with_itself hJS.1 (GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay hRD) hAF E n hn (π.twist χ) hχ
    have h := GlobalTheory.Published.InvTransposeModel.twist hp χ⁻¹
    rwa [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one] at h

end GlobalTheory.GelfandKazhdanTop
