import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFullFaithfulnessLatticeMorphism
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEqMulKisinInfTameSemidirectStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.UnitDatum

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in

/- English proof (translation)
Introduce `BS l _ a e _ _ ϖ LL _ _ η H Pk`. Establish `hx : ((1 : ↥LL.1) : (unitLat (Gl l) : QLat LL).V) ∈ (unitLat (Gl l) : QLat LL).L.T` using `⟨1, by simp⟩`. Set `x : ↥(unitLat (Gl l) : QLat LL).L.T` to `⟨(1 : ↥LL.1), hx⟩`. Set `x' : ↥(resF (unitLat (Gl l) : QLat LL) (ϖ.field a)).L.T` to `⟨(1 : ↥LL.1), hx⟩`. Establish `hTriv : IsTriv (resF (unitLat (Gl l) : QLat LL) (ϖ.field a))` using `fun _ _ => rfl`.

Set `b : Module.Basis Unit ↥(OL LL) ↥(resF (unitLat (Gl l) : QLat LL) (ϖ.field a)).L.T` to `⟨(LinearEquiv.ofInjective (Algebra.linearMap ↥(OL LL) ↥LL.1) IsUnitBall.inj).symm.trans (Finsupp.LinearEquiv.finsuppUnique _ _ _).symm⟩`. Establish `hb : b () = x'`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Algebra.linearMap ↥(OL LL) ↥LL.1 ((Finsupp.LinearEquiv.finsuppUnique ↥(OL LL) ↥(OL LL) Unit) (Finsupp.single () 1)) = 1`. Rewrite using `[show (Finsupp.LinearEquiv.finsuppUnique ↥(OL LL) ↥(OL LL) Unit) (Finsupp.single () 1) = 1 from Finsupp.single_eq_same]`.

Simplify using the standard rewrite rules. Establish `hBK` using `isBK_unitIdent (thetaW a LL) ϖ hTriv b`. Establish `hBK'` using `Pk.isBK`. Establish `h1` using `GlobalTheory.BKReal.Full.main BS l a e (↥(OL LL)) (↥LL.1) (thetaW a LL) ϖ Unit (Fin Pk.n) (unitMod l a e ↥(OL LL) ↥LL.1 Unit) Pk.D.toPhiMod`. Establish `h2` using `h1 (resF (unitLat (Gl l) : QLat LL) (ϖ.field a)) (resF (unitLat (Gl l) : QLat LL) (ϖ.field a)) (unitIdent (thetaW a LL) ϖ _ b)`.

Establish `h3` using `h2 (Pk.R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _))`. Establish `h4` using `h3 hBK`. Establish `h5` using `h4 hBK' (latId _)`. Take `⟨F, hF⟩` from `h5`. Establish `hev : (fun _ _ => (1 : (↥LL.1)⟦X⟧) : Vec (↥LL.1) a Unit) ∈ (unitMod l a e ↥(OL LL) ↥LL.1 Unit).M` using `mem_tot.2 fun _ _ => one_mem _`.

Establish `huM : F.app (fun _ _ => (1 : (↥LL.1)⟦X⟧) : Vec (↥LL.1) a Unit) ∈ Pk.D.M` using `F.app_mem_M hev`. Set `u : ME Pk.D.toPhiMod` to `⟨_, mem_ME_of_mem_M huM⟩`. Establish `h0 : toW (thetaW a LL) ϖ (unitMod l a e ↥(OL LL) ↥LL.1 Unit) ⟨_, mem_ME_of_mem_M hev⟩ = (unitIdent (thetaW a LL) ϖ _ b).ofT x'`. Apply `(unitIdent (thetaW a LL) ϖ _ b).j.injective` to reduce the goal to its premises. Use `Eq.trans ?_ ((unitIdent (thetaW a LL) ϖ _ b).j_ofT x').symm` and prove the remaining obligations.

Rewrite using `[unitIdent_j, Fintype.sum_unique, hb]`. Use `congr 1`. Rewrite using `[toW_apply, ← map_one (ϖ.iW (thetaW a LL) ↥LL.1)]`. Conclude with `congrArg _ (funext fun _ => Subtype.ext rfl)`. Establish `h6` using `homW_toW (thetaW a LL) ϖ F ⟨_, mem_ME_of_mem_M hev⟩`.

Establish `key : toW (thetaW a LL) ϖ Pk.D.toPhiMod u = Pk.R.I.ofT x` using `h6.symm.trans ((congrArg (homW (thetaW a LL) ϖ F) h0).trans (IsMapOf.homW_ofT hF x'))`. Use `⟨u, x, rfl, (Descent.mem_invOf _).2 ⟨huM, fun γ => ?_⟩, ?_, key⟩` and prove the remaining obligations. Take `⟨k, -, hk⟩` from `(GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL).2.2.1 γ`. Establish `hkG : k ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l)`. Introduce `y`.

Take `⟨y, hy⟩` from `y`. Take `⟨c, rfl⟩` from `IntermediateField.mem_bot.mp hy`. Conclude with `k.commutes c`. Establish `hv' : Pk.D.desc.act γ u.1 ∈ ME Pk.D.toPhiMod` using `mem_ME_of_mem_M (Pk.D.desc.act_mem_M γ _ huM)`. Establish `h` using `Pk.R.desc ⟨k, hkG⟩ γ hk u ⟨_, hv'⟩ rfl`.

Establish `hx' : (unitLat (Gl l) : QLat LL).actT ⟨k, hkG⟩ x = x` using `Subtype.ext rfl`. Establish `h10 : toW (thetaW a LL) ϖ Pk.D.toPhiMod ⟨_, hv'⟩ = toW (thetaW a LL) ϖ Pk.D.toPhiMod u` using `h.symm.trans ((congrArg (Pk.R.I.act (sQ l ⟨k, hkG⟩) ⟨k, hkG⟩) key).trans ((Pk.R.I.act_ofT (sQ l ⟨k, hkG⟩) ⟨k, hkG⟩ x).trans ((congrArg Pk.R.I.ofT hx').trans key.symm)))`. Conclude with `congrArg Subtype.val (toW_injective (thetaW a LL) ϖ Pk.D.toPhiMod h10)`. Establish `h7` using `toW_phi (thetaW a LL) ϖ Pk.D.toPhiMod huM`. Establish `h8 : phiW (thetaW a LL) ϖ Pk.D.toPhiMod (Pk.R.I.ofT x) = Pk.R.I.ofT x`.

Rewrite using `[← mem_Treal, ← Pk.R.I.range_ofT]`. Conclude with `LinearMap.mem_range_self Pk.R.I.ofT x`. Establish `h9 : toW (thetaW a LL) ϖ Pk.D.toPhiMod ⟨Pk.D.phi u.1, mem_ME_of_mem_L (Pk.D.phi_mem_L huM)⟩ = toW (thetaW a LL) ϖ Pk.D.toPhiMod u` using `h7.trans ((congrArg (phiW (thetaW a LL) ϖ Pk.D.toPhiMod) key).trans (h8.trans key.symm))`. Conclude with `congrArg Subtype.val (toW_injective (thetaW a LL) ϖ Pk.D.toPhiMod h9)`.
-/
theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (Pk : Pack a ϖ η H (unitLat (Gl l) : QLat LL)), ∃ (u : ME Pk.D.toPhiMod) (x : ↥(unitLat (Gl l) : QLat LL).L.T), x.1 = (1 : ↥LL.1) ∧ u.1 ∈ Pk.D.Minv ∧ Pk.D.phi u.1 = u.1 ∧ toW (thetaW a LL) ϖ Pk.D.toPhiMod u = Pk.R.I.ofT x := by
  intro BS l _ a e _ _ ϖ LL _ _ η H Pk
  have hx : ((1 : ↥LL.1) : (unitLat (Gl l) : QLat LL).V) ∈ (unitLat (Gl l) : QLat LL).L.T := ⟨1, by simp⟩
  let x : ↥(unitLat (Gl l) : QLat LL).L.T := ⟨(1 : ↥LL.1), hx⟩
  let x' : ↥(resF (unitLat (Gl l) : QLat LL) (ϖ.field a)).L.T := ⟨(1 : ↥LL.1), hx⟩
  have hTriv : IsTriv (resF (unitLat (Gl l) : QLat LL) (ϖ.field a)) := fun _ _ => rfl
  let b : Module.Basis Unit ↥(OL LL) ↥(resF (unitLat (Gl l) : QLat LL) (ϖ.field a)).L.T :=
    ⟨(LinearEquiv.ofInjective (Algebra.linearMap ↥(OL LL) ↥LL.1) IsUnitBall.inj).symm.trans
      (Finsupp.LinearEquiv.finsuppUnique _ _ _).symm⟩
  have hb : b () = x' := by
    apply Subtype.ext
    change Algebra.linearMap ↥(OL LL) ↥LL.1 ((Finsupp.LinearEquiv.finsuppUnique ↥(OL LL) ↥(OL LL) Unit) (Finsupp.single () 1)) = 1
    rw [show (Finsupp.LinearEquiv.finsuppUnique ↥(OL LL) ↥(OL LL) Unit) (Finsupp.single () 1) = 1 from Finsupp.single_eq_same]
    simp
  have hBK := isBK_unitIdent (thetaW a LL) ϖ hTriv b
  have hBK' := Pk.isBK
  have h1 := GlobalTheory.BKReal.Full.main BS l a e (↥(OL LL)) (↥LL.1) (thetaW a LL) ϖ Unit (Fin Pk.n)
    (unitMod l a e ↥(OL LL) ↥LL.1 Unit) Pk.D.toPhiMod
  have h2 := h1 (resF (unitLat (Gl l) : QLat LL) (ϖ.field a)) (resF (unitLat (Gl l) : QLat LL) (ϖ.field a))
    (unitIdent (thetaW a LL) ϖ _ b)
  have h3 := h2 (Pk.R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _))
  have h4 := h3 hBK
  have h5 := h4 hBK' (latId _)
  obtain ⟨F, hF⟩ := h5
  have hev : (fun _ _ => (1 : (↥LL.1)⟦X⟧) : Vec (↥LL.1) a Unit) ∈ (unitMod l a e ↥(OL LL) ↥LL.1 Unit).M :=
    mem_tot.2 fun _ _ => one_mem _
  have huM : F.app (fun _ _ => (1 : (↥LL.1)⟦X⟧) : Vec (↥LL.1) a Unit) ∈ Pk.D.M := F.app_mem_M hev
  let u : ME Pk.D.toPhiMod := ⟨_, mem_ME_of_mem_M huM⟩
  have h0 : toW (thetaW a LL) ϖ (unitMod l a e ↥(OL LL) ↥LL.1 Unit) ⟨_, mem_ME_of_mem_M hev⟩ =
      (unitIdent (thetaW a LL) ϖ _ b).ofT x' := by
    apply (unitIdent (thetaW a LL) ϖ _ b).j.injective
    refine Eq.trans ?_ ((unitIdent (thetaW a LL) ϖ _ b).j_ofT x').symm
    rw [unitIdent_j, Fintype.sum_unique, hb]
    congr 1
    rw [toW_apply, ← map_one (ϖ.iW (thetaW a LL) ↥LL.1)]
    exact congrArg _ (funext fun _ => Subtype.ext rfl)
  have h6 := homW_toW (thetaW a LL) ϖ F ⟨_, mem_ME_of_mem_M hev⟩
  have key : toW (thetaW a LL) ϖ Pk.D.toPhiMod u = Pk.R.I.ofT x :=
    h6.symm.trans ((congrArg (homW (thetaW a LL) ϖ F) h0).trans (IsMapOf.homW_ofT hF x'))
  refine ⟨u, x, rfl, (Descent.mem_invOf _).2 ⟨huM, fun γ => ?_⟩, ?_, key⟩
  · obtain ⟨k, -, hk⟩ := (GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL).2.2.1 γ
    have hkG : k ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
      intro y
      obtain ⟨y, hy⟩ := y
      obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hy
      exact k.commutes c
    have hv' : Pk.D.desc.act γ u.1 ∈ ME Pk.D.toPhiMod := mem_ME_of_mem_M (Pk.D.desc.act_mem_M γ _ huM)
    have h := Pk.R.desc ⟨k, hkG⟩ γ hk u ⟨_, hv'⟩ rfl
    have hx' : (unitLat (Gl l) : QLat LL).actT ⟨k, hkG⟩ x = x := Subtype.ext rfl
    have h10 : toW (thetaW a LL) ϖ Pk.D.toPhiMod ⟨_, hv'⟩ = toW (thetaW a LL) ϖ Pk.D.toPhiMod u :=
      h.symm.trans ((congrArg (Pk.R.I.act (sQ l ⟨k, hkG⟩) ⟨k, hkG⟩) key).trans
        ((Pk.R.I.act_ofT (sQ l ⟨k, hkG⟩) ⟨k, hkG⟩ x).trans ((congrArg Pk.R.I.ofT hx').trans key.symm)))
    exact congrArg Subtype.val (toW_injective (thetaW a LL) ϖ Pk.D.toPhiMod h10)
  · have h7 := toW_phi (thetaW a LL) ϖ Pk.D.toPhiMod huM
    have h8 : phiW (thetaW a LL) ϖ Pk.D.toPhiMod (Pk.R.I.ofT x) = Pk.R.I.ofT x := by
      rw [← mem_Treal, ← Pk.R.I.range_ofT]
      exact LinearMap.mem_range_self Pk.R.I.ofT x
    have h9 : toW (thetaW a LL) ϖ Pk.D.toPhiMod ⟨Pk.D.phi u.1, mem_ME_of_mem_L (Pk.D.phi_mem_L huM)⟩ =
        toW (thetaW a LL) ϖ Pk.D.toPhiMod u :=
      h7.trans ((congrArg (phiW (thetaW a LL) ϖ Pk.D.toPhiMod) key).trans (h8.trans key.symm))
    exact congrArg Subtype.val (toW_injective (thetaW a LL) ϖ Pk.D.toPhiMod h9)

end GlobalTheory.BKGal.UnitDatum
