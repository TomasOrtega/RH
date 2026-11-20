import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoverDictionaryAdelicElementComponent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CoverOnto.exists_dict₂_comp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsCoverDictionaryAdelicElementComponent.lean&line=140#L140)
-/
theorem _root_.GlobalTheory.T.exists_coverDictionary_adelic_element_component : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ k₂ : C.U₂.Comp, ∃ h : GA D (T.V j σ), (C.dict₂ h).1 = k₂ := by
  first | exact @GlobalTheory.CoverOnto.exists_dict₂_comp | exact GlobalTheory.CoverOnto.exists_dict₂_comp | (intros; apply GlobalTheory.CoverOnto.exists_dict₂_comp <;> assumption)
