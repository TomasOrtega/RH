import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.LocalRingCardinality.DataParams
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParamsOfRoomy
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HTW

/- English proof (translation)
Introduce `eps A heps`. Take `⟨x0, hx0⟩` from `admissible_params_large eps A heps`. Use `⟨x0, fun D L P h1 h2 h3 => ?_⟩` and prove the remaining obligations. Take `⟨⟨hw, hwb, hbb, hT, ht⟩, hS⟩` from `hx0 D L P h1 h2 h3`. Establish `he` using `L.etaSz_pos`.

Establish `hSc` using `L.Sc_pos`. Establish `htt : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`. Use `⟨⟨by linarith, by linarith, fun tt => by linarith [hT tt], ht⟩, hS⟩` and prove the remaining obligations.
-/
theorem admissibleParameters_of_large_scale : ∀ eps A : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → AdmissibleParameterJ.AdmPar L ∧ EmbeddingTypeJumps.ParametersPolynomiallyBounded L := by
  intro eps A heps
  obtain ⟨x0, hx0⟩ := admissible_params_large eps A heps
  refine ⟨x0, fun D L P h1 h2 h3 => ?_⟩
  obtain ⟨⟨hw, hwb, hbb, hT, ht⟩, hS⟩ := hx0 D L P h1 h2 h3
  have he := L.etaSz_pos
  have hSc := L.Sc_pos
  have htt : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨⟨by linarith, by linarith, fun tt => by linarith [hT tt], ht⟩, hS⟩

end GlobalTheory.HTW
