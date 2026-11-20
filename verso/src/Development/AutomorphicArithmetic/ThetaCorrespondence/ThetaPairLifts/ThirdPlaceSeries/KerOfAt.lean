import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRationalityAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadComparisonAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRows

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
/- English proof (translation)
Use `⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨0, fun x hx _ i p hR hM w hw j => ?_⟩⟩⟩` and prove the remaining obligations. Introduce `ρ hρ hpin`. Establish `hL` using `_root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hR hM.1`. Establish `hC : GlobalTheory.Hk3.Core (R2 p) (F2 p)` using `⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩`. Establish `hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))`.

Establish `h0` using `baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)`. Conclude with `{ h0 with }`. Establish `hpl` using `placesAt (j := j) hw hρ hpin`. Establish `hl : (Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w) = Formalism.EigenvalueLevelCeiling.plc ((Fm.D x i).plEq w)`. Rewrite using `[(Fm.ex x hx i).nch.twI_l, Formalism.L2.G.ServJoint.plc_plEq]`.

Establish `hpD : ∀ P, P ∈ (Fm.D x i).ntw.pD ((Fm.ex x hx i).nch.twI w) ↔ ((ownAt (Fm.D x i) ((Fm.D x i).plEq w) : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal` using `fun P => by`. Rewrite using `[← Finset.mem_coe, (Fm.D x i).ntw.pD_eq, ownAt, ← hl]`. Both sides reduce to the same expression. Establish `hQ : (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).de.Q = plW p w`. Use extensionality with `P`.

Rewrite using `[hpl.1 P, hpD P]`. Unfold `plW GlobalTheory.OnTies.placesOver`. Rewrite using `[Finset.mem_filter]`. Both sides reduce to the same expression. Establish `hwt : (Fm.D x i).plEq w ∈ (R2 p).twPl` using `hw`.

Take `⟨ω, φ, hK⟩` from `GlobalTheory.OnCmp.exists_baseKernel _ _ _ _ _ _ (R2 p) (F2 p) hC j _ hwt hL.1.tup.mu_on`. Take `⟨χ, ξR, hD⟩` from `GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel _ _ _ _ _ _ (R2 p) (F2 p) hC j _ hwt hL.1.tup.mu_on ω φ hK`. Establish `hχ : χ = (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).de.chi` using `GlobalTheory.ChrEqUnique.idc_unique _ _ _ _ hD.chr (hl ▸ hpin.delta _ j _)`. Substitute `hχ` using the available equality. Establish `hω` using `hρ.weil_base ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)`.

Rewrite `hω` using `[Base.IsWeil, mul_one, Base.mu, hpin.psi, hpin.mu0, hpin.eta]`. Use `⟨hBo, hQ, ξR, φ, { hD with weil := hω }⟩` and prove the remaining obligations.
-/
theorem kerOfAt_alt : _root_.GlobalTheory.BigOn.Exp.SerBase.KerOfAtAlt := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨0, fun x hx _ i p hR hM w hw j => ?_⟩⟩⟩
  intro ρ hρ hpin
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) := by
    have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
    exact { h0 with }
  have hpl := placesAt (j := j) hw hρ hpin
  have hl : (Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w) = Formalism.EigenvalueLevelCeiling.plc ((Fm.D x i).plEq w) := by
    rw [(Fm.ex x hx i).nch.twI_l, Formalism.L2.G.ServJoint.plc_plEq]
  have hpD : ∀ P, P ∈ (Fm.D x i).ntw.pD ((Fm.ex x hx i).nch.twI w) ↔
      ((ownAt (Fm.D x i) ((Fm.D x i).plEq w) : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal := fun P => by
    rw [← Finset.mem_coe, (Fm.D x i).ntw.pD_eq, ownAt, ← hl]
    rfl
  have hQ : (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).de.Q = plW p w := by
    ext P
    rw [hpl.1 P, hpD P]
    unfold plW GlobalTheory.OnTies.placesOver
    classical
    rw [Finset.mem_filter]
    rfl
  have hwt : (Fm.D x i).plEq w ∈ (R2 p).twPl := hw
  obtain ⟨ω, φ, hK⟩ := GlobalTheory.OnCmp.exists_baseKernel _ _ _ _ _ _ (R2 p) (F2 p) hC j _ hwt hL.1.tup.mu_on
  obtain ⟨χ, ξR, hD⟩ := GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel _ _ _ _ _ _ (R2 p) (F2 p) hC j _ hwt hL.1.tup.mu_on ω φ hK
  have hχ : χ = (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).de.chi :=
    GlobalTheory.ChrEqUnique.idc_unique _ _ _ _ hD.chr (hl ▸ hpin.delta _ j _)
  subst hχ
  have hω := hρ.weil_base ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  rw [Base.IsWeil, mul_one, Base.mu, hpin.psi, hpin.mu0, hpin.eta] at hω
  refine ⟨hBo, hQ, ξR, φ, { hD with weil := hω }⟩
end GlobalTheory.BigOn.Exp.SerBase
end
end
