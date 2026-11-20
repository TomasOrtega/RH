import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

open ChangeOfRings in

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(1 : ULift.{1} (ZMod q)) ⊗ₜ[ULift.{1} (ZMod Q), uliftHom (ZMod.castHom hq (ZMod q))] y = 0 at h`. Set `K : AddSubgroup N` to `(DistribMulAction.toAddMonoidHom N q).range`. Set `gZ : ℤ →+ (N →+ N ⧸ K)` to `zmultiplesHom _ (QuotientAddGroup.mk' K)`. Establish `hgZ : gZ q = 0`. Use extensionality with `m`.

Simplify using `only [gZ, zmultiplesHom_apply, AddMonoidHom.zero_apply, AddMonoidHom.coe_smul, Pi.smul_apply, QuotientAddGroup.mk'_apply]`. Rewrite using `[natCast_zsmul, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]`. Conclude with `⟨m, rfl⟩`. Set `g : ZMod q →+ (N →+ N ⧸ K)` to `ZMod.lift q ⟨gZ, hgZ⟩`. Set `f : ((ModuleCat.restrictScalars (uliftHom (ZMod.castHom hq (ZMod q)))).obj (ModuleCat.of _ (ULift.{1} (ZMod q)))) →+ (N →+ N ⧸ K)` to `g.comp (AddEquiv.ulift : ULift.{1} (ZMod q) ≃+ ZMod q).toAddMonoidHom`.

Establish `hf : ∀ (r : ULift.{1} (ZMod Q)) s (n : N), f (r • s) n = f s (r • n)`. Introduce `r s n`. Take `⟨a, ha⟩` from `ZMod.intCast_surjective (ULift.down r)`. Take `⟨b, hb⟩` from `ZMod.intCast_surjective (ULift.down (s : ULift.{1} (ZMod q)))`. Establish `hr : r • n = a • n`.

Rewrite using `[show r = ((a : ℤ) : ULift.{1} (ZMod Q)) from ULift.ext _ _ (by simp [ha]), Int.cast_smul_eq_zsmul]`. Express the relevant statement in the definitionally equal form `g (ZMod.castHom hq (ZMod q) (ULift.down r) * ULift.down (s : ULift.{1} (ZMod q))) n = g (ULift.down (s : ULift.{1} (ZMod q))) (r • n)`. Rewrite using `[hr, ← ha, ← hb, map_intCast, ← Int.cast_mul, ZMod.lift_coe, ZMod.lift_coe]`. Simplify using `only [gZ, zmultiplesHom_apply, AddMonoidHom.coe_smul, Pi.smul_apply, QuotientAddGroup.mk'_apply, map_zsmul, mul_comm a b, mul_zsmul]`. Conclude with `smul_comm b a _`.

Set `one : ((ModuleCat.restrictScalars (uliftHom (ZMod.castHom hq (ZMod q)))).obj (ModuleCat.of _ (ULift.{1} (ZMod q))))` to `(1 : ULift.{1} (ZMod q))`. Establish `e : f one y = 0` using `(TensorProduct.liftAddHom_tmul f hf one y).symm.trans ((congrArg (TensorProduct.liftAddHom f hf) h).trans (map_zero _))`. Establish `e1 : f one = QuotientAddGroup.mk' K`. Express the relevant statement in the definitionally equal form `g ((1 : ZMod q)) = _`. Rewrite using `[← Int.cast_one, ZMod.lift_coe]`.

Simplify using `[gZ]`. Rewrite `e` using `[e1, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]`. Take `⟨z, hz⟩` from `e`. Conclude with `⟨z, hz.symm⟩`.
-/
theorem unit_eq_zero_dvd {Q q : ℕ} [NeZero Q] (hq : q ∣ Q) (N : ModuleCat.{1} (ULift.{1} (ZMod Q))) (y : N)
    (h : ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q)))).unit.app N).hom y = 0) :
    ∃ z : N, y = q • z := by
  change (1 : ULift.{1} (ZMod q)) ⊗ₜ[ULift.{1} (ZMod Q), uliftHom (ZMod.castHom hq (ZMod q))] y = 0 at h
  let K : AddSubgroup N := (DistribMulAction.toAddMonoidHom N q).range
  let gZ : ℤ →+ (N →+ N ⧸ K) := zmultiplesHom _ (QuotientAddGroup.mk' K)
  have hgZ : gZ q = 0 := by
    ext m
    simp only [gZ, zmultiplesHom_apply, AddMonoidHom.zero_apply, AddMonoidHom.coe_smul, Pi.smul_apply,
      QuotientAddGroup.mk'_apply]
    rw [natCast_zsmul, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨m, rfl⟩
  let g : ZMod q →+ (N →+ N ⧸ K) := ZMod.lift q ⟨gZ, hgZ⟩
  let f : ((ModuleCat.restrictScalars (uliftHom (ZMod.castHom hq (ZMod q)))).obj (ModuleCat.of _ (ULift.{1} (ZMod q))))
      →+ (N →+ N ⧸ K) := g.comp (AddEquiv.ulift : ULift.{1} (ZMod q) ≃+ ZMod q).toAddMonoidHom
  have hf : ∀ (r : ULift.{1} (ZMod Q)) s (n : N), f (r • s) n = f s (r • n) := by
    intro r s n
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (ULift.down r)
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective (ULift.down (s : ULift.{1} (ZMod q)))
    have hr : r • n = a • n := by
      rw [show r = ((a : ℤ) : ULift.{1} (ZMod Q)) from ULift.ext _ _ (by simp [ha]), Int.cast_smul_eq_zsmul]
    change g (ZMod.castHom hq (ZMod q) (ULift.down r) * ULift.down (s : ULift.{1} (ZMod q))) n =
      g (ULift.down (s : ULift.{1} (ZMod q))) (r • n)
    rw [hr, ← ha, ← hb, map_intCast, ← Int.cast_mul, ZMod.lift_coe, ZMod.lift_coe]
    simp only [gZ, zmultiplesHom_apply, AddMonoidHom.coe_smul, Pi.smul_apply, QuotientAddGroup.mk'_apply,
      map_zsmul, mul_comm a b, mul_zsmul]
    exact smul_comm b a _
  let one : ((ModuleCat.restrictScalars (uliftHom (ZMod.castHom hq (ZMod q)))).obj (ModuleCat.of _ (ULift.{1} (ZMod q)))) :=
    (1 : ULift.{1} (ZMod q))
  have e : f one y = 0 :=
    (TensorProduct.liftAddHom_tmul f hf one y).symm.trans ((congrArg (TensorProduct.liftAddHom f hf) h).trans (map_zero _))
  have e1 : f one = QuotientAddGroup.mk' K := by
    change g ((1 : ZMod q)) = _
    rw [← Int.cast_one, ZMod.lift_coe]
    simp [gZ]
  rw [e1, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at e
  obtain ⟨z, hz⟩ := e
  exact ⟨z, hz.symm⟩

/- English proof (translation)
Introduce `Q q _ hq M U x hx`. Establish `hloc` using `(GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod q) (M.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q))))).2.1 U (((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q)))).unit.app (M.obj.obj (op U))).hom x) …`. Use `GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U _ _ hloc ?_` and prove the remaining obligations. Introduce `V g hg`. Establish `e2` using `(ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q)))).unit.naturality (M.obj.map g.op)`.

Establish `h2` using `LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e2) x`. Conclude with `unit_eq_zero_dvd hq (M.obj.obj (op V)) (Sec.res g x) (h2.trans hg)`.
-/
theorem extSh_sec_eq_zero_loc : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0}) (x : Sec M U),
    extSh.sec (ZMod.castHom hq (ZMod q)) M U x = 0 → Loc U fun V g => ∃ y : Sec M V, Sec.res g x = q • y := by
  intro Q q _ hq M U x hx
  have hloc := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod q) (M.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q))))).2.1 U
    (((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q)))).unit.app (M.obj.obj (op U))).hom x) hx
  refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U _ _ hloc ?_
  intro V g hg
  have e2 := (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q)))).unit.naturality (M.obj.map g.op)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e2) x
  exact unit_eq_zero_dvd hq (M.obj.obj (op V)) (Sec.res g x) (h2.trans hg)

end GlobalTheory.EtC
