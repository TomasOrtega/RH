import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePartIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open Matrix NumberField
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace GlobalTheory.QuotientNormCoisometry
section Bound
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef.Tree
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Bound
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize in
/- English proof (translation)
Introduce `hB hS hI`. Take `⟨CF0, hI⟩` from `hI`. Use `⟨CF0, fun CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C0, hI⟩` from `hI CF hCF`. Take `⟨e1, he1, hS⟩` from `hS`.

Use `⟨e1, he1, fun eps h1 h2 => ?_⟩` and prove the remaining obligations. Take `⟨K, hK⟩` from `hS eps h1 h2`. Use `⟨K, fun Fm CH hc hL _ => ?_⟩` and prove the remaining obligations. Take `⟨x1, hx1⟩` from `hK Fm CH hc hL`. Use `⟨max C0 (max CF 0), fun C hC => ?_⟩` and prove the remaining obligations.

Establish `hCF' : CF ≤ C` using `((le_max_left _ _).trans (le_max_right _ _)).trans hC`. Establish `hC0 : 0 ≤ C` using `((le_max_right _ _).trans (le_max_right _ _)).trans hC`. Take `⟨x0, hx0⟩` from `hI eps C (le_of_max_le_left hC)`. Use `⟨max x0 x1, fun x hx hle i p hp d hd vb hvb => ?_⟩` and prove the remaining obligations. Take `⟨-, a, ha⟩` from `hd`.

Establish `hset` using `hx1 x hx (le_of_max_le_right hle) i p hp ha.ok.eser`. Establish `key` using `hx0 _ (Fm.L x i) (Fm.L_eps x i) ((le_of_max_le_left hle).trans (Fm.L_x x i hx).ge) _ _ _ _ _ _ _ hset a.ch ha.ok.is a.atScale ha.ok.field`. Establish `hWF` using `(hB p hp).1`. Establish `hX : ∀ v : NumberField.InfinitePlace (Fm.D x i).what₂.LL, IsUnit (Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding)).det ∧ ((Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding))⁻¹)ᴴ * (Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.f …` using `fun v => Formalism.L2.DIV.frameOfSpec _ _ (hWF.HV_pos _ v)`. Establish `k3` using `key d.X' d.M ha.test _ hX (d.V p.P.A3.fam3.base3.μ0) (fun x' a' => ha.sums _ (Or.inl rfl) x' a')`.

Rewrite using `[htMap_quot _ _ _ _ _ (hWF.XQ_quot _) hX vb, hvb]`. Conclude with `k3.trans (bound_le d hC0 hCF')`.
-/
theorem leafHeightMapBound_tie_of_infK : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → InfK → _root_.GlobalTheory.BigTop.Fun.LeafHeightMapBound @Comparison₂ := by
  intro hB hS hI
  obtain ⟨CF0, hI⟩ := hI
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, hI⟩ := hI CF hCF
  obtain ⟨e1, he1, hS⟩ := hS
  refine ⟨e1, he1, fun eps h1 h2 => ?_⟩
  obtain ⟨K, hK⟩ := hS eps h1 h2
  refine ⟨K, fun Fm CH hc hL _ => ?_⟩
  obtain ⟨x1, hx1⟩ := hK Fm CH hc hL
  refine ⟨max C0 (max CF 0), fun C hC => ?_⟩
  have hCF' : CF ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans hC
  have hC0 : 0 ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans hC
  obtain ⟨x0, hx0⟩ := hI eps C (le_of_max_le_left hC)
  refine ⟨max x0 x1, fun x hx hle i p hp d hd vb hvb => ?_⟩
  obtain ⟨-, a, ha⟩ := hd
  have hset := hx1 x hx (le_of_max_le_right hle) i p hp ha.ok.eser
  have key := hx0 _ (Fm.L x i) (Fm.L_eps x i) ((le_of_max_le_left hle).trans (Fm.L_x x i hx).ge) _ _ _ _ _ _ _ hset
    a.ch ha.ok.is a.atScale ha.ok.field
  have hWF := (hB p hp).1
  have hX : ∀ v : NumberField.InfinitePlace (Fm.D x i).what₂.LL,
      IsUnit (Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding)).det ∧
      ((Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding))⁻¹)ᴴ *
        (Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding))⁻¹ =
        ((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding := fun v =>
    Formalism.L2.DIV.frameOfSpec _ _ (hWF.HV_pos _ v)
  have k3 := key d.X' d.M ha.test _ hX (d.V p.P.A3.fam3.base3.μ0) (fun x' a' => ha.sums _ (Or.inl rfl) x' a')
  rw [htMap_quot _ _ _ _ _ (hWF.XQ_quot _) hX vb, hvb]
  exact k3.trans (bound_le d hC0 hCF')
end GlobalTheory.QuotientNormCoisometry
end
end
