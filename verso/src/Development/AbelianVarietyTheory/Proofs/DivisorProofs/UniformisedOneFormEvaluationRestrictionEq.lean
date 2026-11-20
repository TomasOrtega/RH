import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRulesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

/- English proof (translation)
Introduce `A _ g L u U V a ξ z hz`. Take `⟨hopen, -, -, -, -, hmono, -, -, hres, -, -, -⟩` from `GlobalTheory.T.uniformisation_preimage_value_rules A g L u`. Establish `hVU : V.1 ≤ U.1` using `leOfHom a.unop`. Establish `hzU : z ∈ pre u.ex U.1` using `hmono _ _ hVU hz`. Establish `evV` using `GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u V.1 z hz`.

Establish `evU` using `GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U.1 z hzU`. Establish `hD : ∀ b : Sec (str A) U.1, fderiv ℂ (val u.ex V.1 (Sec.res (str A) hVU b)) z = fderiv ℂ (val u.ex U.1 b) z`. Introduce `b`. Apply `Filter.EventuallyEq.fderiv_eq` to reduce the goal to its premises. Use `filter_upwards [(hopen V.1).mem_nhds hz] with w hw`.

Conclude with `hres _ _ hVU b w hw`. Establish `hξ : ξ ∈ Submodule.span (Sec (str A) U.1) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U.1)))`. Rewrite using `[KaehlerDifferential.span_range_derivation]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hξ using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨b, rfl⟩` from `hx`. Rewrite using `[p1_D, evV.2.2, evU.2.2]`. Conclude with `hD b`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => simp only [map_add, hx, hy]`. Consider the case `smul b x _ hx`. Rewrite using `[oneFormsMapOfFunctorMorphism_smul, evV.2.1, evU.2.1, hx]`. Use `congr 1`. Conclude with `hres _ _ hVU b z hz`.
-/
theorem uniformisedOneFormEvaluation_restriction_eq : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U V : A.left.affineOpens) (a : Opposite.op U ⟶ Opposite.op V) (ξ : Ω[Sec (str A) U.1⁄ℂ]), ∀ z ∈ pre u.ex V.1, evForm u.ex V.1 z (p1 (OAff (str A)) a ξ) = evForm u.ex U.1 z ξ := by
  intro A _ g L u U V a ξ z hz
  obtain ⟨hopen, -, -, -, -, hmono, -, -, hres, -, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have hVU : V.1 ≤ U.1 := leOfHom a.unop
  have hzU : z ∈ pre u.ex U.1 := hmono _ _ hVU hz
  have evV := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u V.1 z hz
  have evU := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U.1 z hzU
  have hD : ∀ b : Sec (str A) U.1, fderiv ℂ (val u.ex V.1 (Sec.res (str A) hVU b)) z = fderiv ℂ (val u.ex U.1 b) z := by
    intro b
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(hopen V.1).mem_nhds hz] with w hw
    exact hres _ _ hVU b w hw
  have hξ : ξ ∈ Submodule.span (Sec (str A) U.1) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U.1))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [p1_D, evV.2.2, evU.2.2]
    exact hD b
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul b x _ hx =>
    rw [oneFormsMapOfFunctorMorphism_smul, evV.2.1, evU.2.1, hx]
    congr 1
    exact hres _ _ hVU b z hz

end GlobalTheory.CechPer
