import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormChainLemmas

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

namespace GlobalTheory.NGRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hR : PN.RowNGJoint` using `Formalism.FourierDecayAlt.Final.pn_rowNGJoint`. Establish `hC : PN.NGChain` using `Formalism.FourierDecayAlt.P.norm_chain`. Introduce `Cg cb Cw cT CT C0 hcb hcT`. Take `⟨C1, C0n, A, CB, CSt, Cgs, CTs, h1, h2, h3, h4, hA, C'₀, Cl₀, h⟩` from `hc Cg cb Cw cT CT C0 hcb hcT`. Take `⟨Cn, hCn, hK⟩` from `Formalism.L2.SG.RowsOther.rowNG_of_cut hR hC C1 C0n A CB CSt Cgs CTs h1 h2 h3 h4 hA`.

Use `⟨Cn, hCn, C'₀, Cl₀, fun C' Cl a b D large₂ X Y u u' hTi h0 hs hT ha => ?_⟩` and prove the remaining obligations. Take `⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, _, _, hG, hdd, hN, hF, hS, hFin, hRe⟩` from `h C' Cl a b D large₂ X Y u u' hTi h0 hs hT`. Establish `hcard` using `Formalism.MainNotions.LatticeGluingRadicals.d_card D`. Establish `key` using `hK D.host.E (TauC Y u u') _ _ _ _ (Y.tO u u') D.R.rS D.R.k (Set (TauC Y u u')) (NuC D) (NOf2 Y u u' νL νB ng) P B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) cSt e1 Irat Ire`. Rewrite `key` using `[hcard]`.

Establish `r` using `key ha hG hN hF hS hFin hRe`. Rewrite `r` using `[hdd]`. Conclude with `r`.
-/
theorem rowNG_of_cut2P (hc : NGCut2P) : RowNGP := by
  have hR : PN.RowNGJoint := Formalism.FourierDecayAlt.Final.pn_rowNGJoint
  have hC : PN.NGChain := Formalism.FourierDecayAlt.P.norm_chain
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, A, CB, CSt, Cgs, CTs, h1, h2, h3, h4, hA, C'₀, Cl₀, h⟩ := hc Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨Cn, hCn, hK⟩ := Formalism.L2.SG.RowsOther.rowNG_of_cut hR hC C1 C0n A CB CSt Cgs CTs h1 h2 h3 h4 hA
  refine ⟨Cn, hCn, C'₀, Cl₀, fun C' Cl a b D large₂ X Y u u' hTi h0 hs hT ha => ?_⟩
  obtain ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, _, _, hG, hdd, hN, hF, hS, hFin, hRe⟩ :=
    h C' Cl a b D large₂ X Y u u' hTi h0 hs hT
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u') _ _ _ _ (Y.tO u u') D.R.rS D.R.k (Set (TauC Y u u')) (NuC D)
    (NOf2 Y u u' νL νB ng) P B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ))
    cSt e1 Irat Ire
  rw [hcard] at key
  have r := key ha hG hN hF hS hFin hRe
  rw [hdd] at r
  exact r

/- English proof (translation)
The claim follows from `rowNG_of_cut2P`.
-/
example : NGCut2P → RowNGP := rowNG_of_cut2P

end GlobalTheory.NGRow
