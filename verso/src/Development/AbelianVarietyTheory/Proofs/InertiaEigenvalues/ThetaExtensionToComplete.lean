import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisK

/- English proof (translation)
Introduce `l _ K`. Take `⟨C⟩` from `GlobalTheory.MemLoc.nonempty_core l`. Set `v : ↥K.1 →+* ℂ_[l]` to `(algebraMap (Om l) ℂ_[l]).comp K.1.val.toRingHom`. Establish `h : ∀ w : W0 K, ((Per.θD l).comp C.j) (aC l (wA l (fK K) w)) = v (oK K (thetaW (fK K) K w))`. Introduce `w`.

Rewrite using `[RingHom.comp_apply, GlobalTheory.MemLoc.FundOnto.theta_j_alg]`. Express the relevant statement in the definitionally equal form `_ = ((intToOC K (thetaW (fK K) K w) : OC l) : ℂ_[l])`. Rewrite using `[intToOC_thetaW]`. Use `⟨liftB ((Per.θD l).comp C.j) v h, fun x => ?_⟩` and prove the remaining obligations. Establish `e` using `AinfK.ringHom_ext (u := ((liftB ((Per.θD l).comp C.j) v h).comp (toB K)).comp (ofA K)) (v := (Subring.subtype _).comp (thetaK K)) (fun a => by`.

Simplify using `only [RingHom.comp_apply]`. Rewrite using `[ofA_inA, liftB_inC, RingHom.comp_apply, GlobalTheory.MemLoc.FundOnto.theta_j_alg, thetaK_inA]`. Use the proof step `rfl) (fun c => by`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[ofA_inO, ← inK_oK, liftB_inK, thetaK_inO]`.

Use the proof step `rfl)`. Conclude with `RingHom.congr_fun e x`.
-/
theorem exists_thetaB : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ ψ : GlobalTheory.AcrisK.BK K →+* ℂ_[l],
    ∀ x : AK K, ψ (toB K (ofA K x)) = ((thetaK K x : OC l) : ℂ_[l]) := by
  intro l _ K
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  let v : ↥K.1 →+* ℂ_[l] := (algebraMap (Om l) ℂ_[l]).comp K.1.val.toRingHom
  have h : ∀ w : W0 K, ((Per.θD l).comp C.j) (aC l (wA l (fK K) w)) = v (oK K (thetaW (fK K) K w)) := by
    intro w
    rw [RingHom.comp_apply, GlobalTheory.MemLoc.FundOnto.theta_j_alg]
    change _ = ((intToOC K (thetaW (fK K) K w) : OC l) : ℂ_[l])
    rw [intToOC_thetaW]
  refine ⟨liftB ((Per.θD l).comp C.j) v h, fun x => ?_⟩
  have e := AinfK.ringHom_ext (u := ((liftB ((Per.θD l).comp C.j) v h).comp (toB K)).comp (ofA K))
    (v := (Subring.subtype _).comp (thetaK K)) (fun a => by
      simp only [RingHom.comp_apply]
      rw [ofA_inA, liftB_inC, RingHom.comp_apply, GlobalTheory.MemLoc.FundOnto.theta_j_alg, thetaK_inA]
      rfl) (fun c => by
      simp only [RingHom.comp_apply]
      rw [ofA_inO, ← inK_oK, liftB_inK, thetaK_inO]
      rfl)
  exact RingHom.congr_fun e x

end GlobalTheory.AcrisK
