import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2.L2

/- English proof (translation)
Unfold `xiR`. Establish `hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖` using `fun σ => by`. Rewrite using `[← norm_pow, ← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast, norm_neg]`. Establish `hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖` using `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)`. Rewrite using `[show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]`.

Simplify using `only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]`.
-/
theorem norm_complexEmbedding_traceElement_const (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = xiR D := by
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, ← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

/- English proof (translation)
Introduce `D H Dw l Xo c r U σ V hr ι Kf χ dict mu x₀ hs hσ hsup P`. Take `⟨g, e, F, ik, φ, th, -, hd, -⟩` from `P.dictLaws`. Establish `hA : AdelAut V dict mu` using `P.adelAut`. Take `⟨hP, hV⟩` from `GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs`. Establish `hL : CuspL2 U σ V dict mu` using `cusp_L2_of_measurable hσ (dict_dom_of hd) P.muUnit (adelMeas_of_aut Xo c hA)`.

Use `⟨hV, fun k τ => ?_, hL, l2Def_of_cusp hσ hsup (aeDom_of hA hV hP P.muUnit hd) hL⟩` and prove the remaining obligations. Conclude with `(congrArg (fun z => ‖τ z‖) (P.modelW k).2).trans (by rw [map_neg, norm_neg]; exact norm_complexEmbedding_traceElement_const D τ)`.
-/
theorem petersson_squareIntegrable_definite_of_laws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (V : HSp D) (hr : V.rank = r) ι Kf χ (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) mu x₀, V.SigOK → GoodEmb c σ → SupDef Xo c U → PkgLaws V hr ι Kf χ (U σ) dict mu x₀ → FinVol V ∧ (∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D) ∧ ∃ h : CuspL2 U σ V dict mu, L2DefiniteCuspForms U σ V dict mu h := by
  intro D H Dw l Xo c r U σ V hr ι Kf χ dict mu x₀ hs hσ hsup P
  obtain ⟨g, e, F, ik, φ, th, -, hd, -⟩ := P.dictLaws
  have hA : AdelAut V dict mu := P.adelAut
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hL : CuspL2 U σ V dict mu :=
    cusp_L2_of_measurable hσ (dict_dom_of hd) P.muUnit (adelMeas_of_aut Xo c hA)
  refine ⟨hV, fun k τ => ?_, hL, l2Def_of_cusp hσ hsup (aeDom_of hA hV hP P.muUnit hd) hL⟩
  exact (congrArg (fun z => ‖τ z‖) (P.modelW k).2).trans
    (by rw [map_neg, norm_neg]; exact norm_complexEmbedding_traceElement_const D τ)

end GlobalTheory.FinalJoin2.L2
