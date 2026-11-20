import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumFixedAlmostAllPlaces
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PairVac.vac_fixed_cofinite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVacuumFixedAlmostAllPlaces.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.vacuum_fixed_almost_all_places : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ᶠ v in Filter.cofinite, ∀ g ∈ GlobalTheory.InertSph.KAt σ W v, Acts (evFin F v) (om (1, g)) (M.vac v) (M.vac v) := by
  first | exact @GlobalTheory.PairVac.vac_fixed_cofinite | exact GlobalTheory.PairVac.vac_fixed_cofinite | (intros; apply GlobalTheory.PairVac.vac_fixed_cofinite <;> assumption)
