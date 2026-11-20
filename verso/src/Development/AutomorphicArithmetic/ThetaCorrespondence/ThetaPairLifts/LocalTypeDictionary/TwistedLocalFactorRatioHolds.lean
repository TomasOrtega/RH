import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatioOfLocalMatchingTowers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomTripleIntegralEqConstMulLocal

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
noncomputable section
open Finset GlobalTheory.FunObj.SqNum
namespace GlobalTheory.RowClaim
set_option maxHeartbeats 1600000 in
/- English proof (translation)
Introduce `hP hTA hLM hC hLN hTX hTW`. Establish `hBF` using `_root_.GlobalTheory.T.bottom_triple_integral_eq_const_mul_local hP hTA hLM hLN`. Take `⟨c1, h1⟩` from `hC`. Take `⟨c5, h5⟩` from `GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and hLN hTX) (GlobalTheory.SqTop.Model.gBig_and hTW hBF)`. Use `⟨max c1 c5, fun ε CF hCF => ?_⟩` and prove the remaining obligations.

Take `⟨x1, g1⟩` from `h1 ε CF (le_of_max_le_left hCF)`. Take `⟨C0, x5, g5⟩` from `h5 ε CF (le_of_max_le_right hCF)`. Use `⟨max x1 x5, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hs ch hi hsc => ?_⟩` and prove the remaining obligations. Establish `hc` using `g1 D large₂ he (le_of_max_le_left hx) Γ Pl0 T A Ks R F hs ch hi hsc`. Establish `hrec : GlobalTheory.SqTop.Rec large₂` using `(GlobalTheory.SqTop.Model.rec_iff large₂).2 ⟨hs.size, hs.host⟩`.

Establish `hL : R.toLevCh.Is A.μ0` using `hs.core.lev`. Introduce `hfield`. Take `⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩` from `ch`. Express the relevant statement in the definitionally equal form `sc = _ at hsc`. Substitute `hsc` using the available equality.

Take `⟨⟨hLN', hTX'⟩, hTW', hBF'⟩` from `g5 C0 le_rfl D large₂ he (le_of_max_le_right hx) hrec T R.toLevCh A.μ0 hL G`. Establish `hstd : IsStdChar D W.ψ (-1)` using `(hi.weil.ψ : W.ψ = _) ▸ hs.std`. Conclude with `fun i j t => sqRatio_mem_grid G A.μ0 W S.toGridChoice rm c hfield hc hi.const (fun i j => (hLN' i j).1) (hTX' W hstd) (hTW' W S.toGridChoice rm hstd hfield) (hBF' W hstd) i j t`.
-/
theorem twisted_local_factor_ratio_holds : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → ConstK →
    GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.TriEx → GlobalTheory.SqTop.Tower → RatioK := by
  intro hP hTA hLM hC hLN hTX hTW
  have hBF := _root_.GlobalTheory.T.bottom_triple_integral_eq_const_mul_local hP hTA hLM hLN
  obtain ⟨c1, h1⟩ := hC
  obtain ⟨c5, h5⟩ := GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and hLN hTX) (GlobalTheory.SqTop.Model.gBig_and hTW hBF)
  refine ⟨max c1 c5, fun ε CF hCF => ?_⟩
  obtain ⟨x1, g1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C0, x5, g5⟩ := h5 ε CF (le_of_max_le_right hCF)
  refine ⟨max x1 x5, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hs ch hi hsc => ?_⟩
  have hc := g1 D large₂ he (le_of_max_le_left hx) Γ Pl0 T A Ks R F hs ch hi hsc
  have hrec : GlobalTheory.SqTop.Rec large₂ := (GlobalTheory.SqTop.Model.rec_iff large₂).2 ⟨hs.size, hs.host⟩
  have hL : R.toLevCh.Is A.μ0 := hs.core.lev
  intro hfield
  obtain ⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩ := ch
  change sc = _ at hsc
  subst hsc
  obtain ⟨⟨hLN', hTX'⟩, hTW', hBF'⟩ := g5 C0 le_rfl D large₂ he (le_of_max_le_right hx) hrec T R.toLevCh A.μ0 hL G
  have hstd : IsStdChar D W.ψ (-1) := (hi.weil.ψ : W.ψ = _) ▸ hs.std
  exact fun i j t => sqRatio_mem_grid G A.μ0 W S.toGridChoice rm c hfield hc hi.const (fun i j => (hLN' i j).1)
    (hTX' W hstd) (hTW' W S.toGridChoice rm hstd hfield) (hBF' W hstd) i j t
end GlobalTheory.RowClaim
end
end
