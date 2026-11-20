import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndicesPairingLengthsVanishOffTwistedPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodRationalEigenformHittingCarriedPart
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.RecTie Formalism.IndefR.Lev

noncomputable section
open scoped TensorProduct InnerProductSpace
open Formalism.L2.Rows GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.ThetaRead3

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i t x`. Establish `hE : R.toRealDat.IsThP` using `RealDat.thP_of_weak hP.char.base.thP hH.aux.ex`. Establish `hM` using `hP.char.base.models`. Establish `hμ : Used0 D (Y.tup t)`. Break down `hP.char.tup.mu_used t with h | ⟨w, hw⟩` into its components or cases.

Use `left`. Rewrite using `[h, Y.tup0]`. Use `right`. Use `⟨D.plEq.symm w, ?_⟩` and prove the remaining obligations. Rewrite using `[Y.muAt, Equiv.apply_symm_apply, hw]`.

Use `set xM := D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x) with hxM`. Use `set zt := R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x) with hzt`. Take `⟨w, hwM, hwK, hwW⟩` from `GlobalTheory.T.thetaAdjoint_at_lift_eq_lowestKType_restriction R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hP.char.base.lev hP.char.base.grp hM hE R.hv0 Y.IL (Y.tup t) hμ i xM`. Establish `hth` using `Y.tied.lift.theta (Y.tup t) hμ i xM w (GlobalTheory.ThetaPRead.isThetaP_toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hE.thF (Y.tup t) i) hwM hwK hwW`. Use `set u := Y.tupT (Y.tup t) with hu`.

Use `set a := Y.IL.jMt (Y.tup t) hμ i xM with ha`. Use `set z' : (R.HV i u).H := (LinearEquiv.ofInjective (R.extV i u) (Y.hinj i u)).symm (Submodule.inclusion inf_le_left a) with hz'`. Establish `hz'1 : R.extV i u z' = R.extV i t zt`. Rewrite using `[hz', ofInjective_symm_eq]`. Conclude with `Y.mtRead i t hμ x`.

Establish `hzz : R.thF i u z' = R.thF i t zt` using `thF_congr R.toRealDat Y.hinj i t u (Y.tupT_tup t) zt z' hz'1`. Set `w' : (⨂[ℂ] τ, (R.MW i (sg0 D A3.A)).sm τ) →ₗ[ℂ] (GA D (Wc D i) → ℂ)` to `w`. Set `U : MMap (R.MW i (sg0 D A3.A))` to `PiTensorProduct.lift.symm w'`. Establish `hU : U ∈ R.Wall i (sg0 D A3.A)` using `GlobalTheory.HeckeParts.mult_le_triv _ ((Mult.mem_multT _ _ _ _ w').1 hwM)`. Establish `hlow : ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A3.A)) ρ, U (fun ρ => v ρ) = R.thF i u z' (fun ρ => v ρ)`.

Introduce `v`. Establish `e` using `LinearMap.congr_fun hwK (PiTensorProduct.tprod ℂ v)`. Establish `e2 : w' (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) = PiTensorProduct.lift (R.thF i u z') (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (PiTensorProduct.tprod ℂ v))` using `e`. Rewrite `e2` using `[PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod]`. Conclude with `e2`.

Establish `hw0 : U - R.thF i t zt = 0` using `GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A3.A)) R.θ hM.inf (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ _ (Submodule.sub_mem _ hU (hE.thF_mem i t zt)) (fun v => by show U (fun ρ => v ρ) - R.thF i t zt (fun ρ => v ρ) = 0`. Rewrite using `[hlow v, hzz, sub_self])`. Establish `hUw : PiTensorProduct.lift U = w'` using `LinearEquiv.apply_symm_apply _ w'`. Establish `h1` using `(Y.mjRead i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) xM)).symm.trans hth`. Express the relevant statement in the definitionally equal form `PiTensorProduct.lift _ = R.eWf i (sg0 D A3.A) ∘ₗ w' at h1`.

Rewrite `h1` using `[← hUw, sub_eq_zero.1 hw0, ← lift_postOn, ← hE.thG i t zt]`. Conclude with `(hM.HW i (sg0 D A3.A)).1 (PiTensorProduct.lift.injective h1)`.
-/
theorem thetaP_read_plain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) x, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))) = R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i t x
  have hE : R.toRealDat.IsThP := RealDat.thP_of_weak hP.char.base.thP hH.aux.ex
  have hM := hP.char.base.models
  have hμ : Used0 D (Y.tup t) := by
    rcases hP.char.tup.mu_used t with h | ⟨w, hw⟩
    · left
      rw [h, Y.tup0]
    · right
      refine ⟨D.plEq.symm w, ?_⟩
      rw [Y.muAt, Equiv.apply_symm_apply, hw]
  set xM := D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x) with hxM
  set zt := R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x) with hzt
  obtain ⟨w, hwM, hwK, hwW⟩ := GlobalTheory.T.thetaAdjoint_at_lift_eq_lowestKType_restriction R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hP.char.base.lev
    hP.char.base.grp hM hE R.hv0 Y.IL (Y.tup t) hμ i xM
  have hth := Y.tied.lift.theta (Y.tup t) hμ i xM w
    (GlobalTheory.ThetaPRead.isThetaP_toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hE.thF (Y.tup t) i) hwM hwK hwW
  set u := Y.tupT (Y.tup t) with hu
  set a := Y.IL.jMt (Y.tup t) hμ i xM with ha
  set z' : (R.HV i u).H := (LinearEquiv.ofInjective (R.extV i u) (Y.hinj i u)).symm
    (Submodule.inclusion inf_le_left a) with hz'
  have hz'1 : R.extV i u z' = R.extV i t zt := by
    rw [hz', ofInjective_symm_eq]
    exact Y.mtRead i t hμ x
  have hzz : R.thF i u z' = R.thF i t zt := thF_congr R.toRealDat Y.hinj i t u (Y.tupT_tup t) zt z' hz'1
  let w' : (⨂[ℂ] τ, (R.MW i (sg0 D A3.A)).sm τ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) := w
  let U : MMap (R.MW i (sg0 D A3.A)) := PiTensorProduct.lift.symm w'
  have hU : U ∈ R.Wall i (sg0 D A3.A) :=
    GlobalTheory.HeckeParts.mult_le_triv _ ((Mult.mem_multT _ _ _ _ w').1 hwM)
  have hlow : ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A3.A)) ρ, U (fun ρ => v ρ) = R.thF i u z' (fun ρ => v ρ) := by
    intro v
    have e := LinearMap.congr_fun hwK (PiTensorProduct.tprod ℂ v)
    have e2 : w' (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) =
        PiTensorProduct.lift (R.thF i u z')
          (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) := e
    rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod] at e2
    exact e2
  have hw0 : U - R.thF i t zt = 0 :=
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A3.A)) R.θ hM.inf
      (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ _ (Submodule.sub_mem _ hU (hE.thF_mem i t zt)) (fun v => by
        show U (fun ρ => v ρ) - R.thF i t zt (fun ρ => v ρ) = 0
        rw [hlow v, hzz, sub_self])
  have hUw : PiTensorProduct.lift U = w' := LinearEquiv.apply_symm_apply _ w'
  have h1 := (Y.mjRead i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) xM)).symm.trans hth
  change PiTensorProduct.lift _ = R.eWf i (sg0 D A3.A) ∘ₗ w' at h1
  rw [← hUw, sub_eq_zero.1 hw0, ← lift_postOn, ← hE.thG i t zt] at h1
  exact (hM.HW i (sg0 D A3.A)).1 (PiTensorProduct.lift.injective h1)

end GlobalTheory.Mem.ThetaRead3

namespace GlobalTheory.Mem.AdjLevel

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i σ y _hy hT`. Establish `hread` using `GlobalTheory.Mem.ThetaRead3.thetaP_read_plain D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH i A3.A.μ0`. Establish `hT' : D.what₂.thetaT (Y.tup A3.A.μ0) ((i : ℕ) + 1) y = 0` using `by rw [Y.tup0]; exact hT`. Establish `hw : (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) ∈ R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))`. Establish `h0 : Y.mj.eW i y ∈ LinearMap.range (Y.mj.eW i)` using `⟨y, rfl⟩`.

Rewrite `h0` using `[Y.mj.eW_range]`. Conclude with `h0`. Establish `ha` using `GlobalTheory.CarriedPart.adjoint_mem_span R F hH.ok hP.char hH.prim.unif hH.prim.gUnit hH.prim.gEquiv hH.prim.levW i _ hw`. Establish `horth : ∀ f ∈ BlockGood.goodR (A3.A.fam.L i A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0), ⟪Y.mj.eW i y, R.thG i A3.A.μ0 (R.jV i A3.A.μ0 f)⟫_ℂ = 0`. Introduce `f hf`.

Rewrite `hf` using `[Formalism.IndefR.CxPass.LevelOperators.goodR_eq]`. Establish `hfl : f ∈ lvlForms (A3.A.fam.L i A3.A.μ0).S (A3.A.fam.L i A3.A.μ0).r (A3.A.fam.lvlA F.P0 F.ψ0).P (A3.A.fam.lvlA F.P0 F.ψ0).ψ` using `fun h => Formalism.IndefR.CxPass.LevelOperators.opF_goodAt_type _ _ hH.ok.ok2.irr _ _ h f hf`. Rewrite `hfl` using `[← GlobalTheory.Mem.LiftForms.range_lvlForm]`. Take `⟨x, rfl⟩` from `hfl`. Establish `hx : GlobalTheory.Mem.LiftForms.lvlForm (A3.A.fam.L i A3.A.μ0).S (A3.A.fam.L i A3.A.μ0).r (A3.A.fam.lvlA F.P0 F.ψ0).P (A3.A.fam.lvlA F.P0 F.ψ0).ψ x = liftForm A3.A F.P0 F.ψ0 i A3.A.μ0 x` using `rfl`.

Rewrite using `[hx, ← hread x, GlobalTheory.Mem.LiftForms.inner_of_norm_sq (Y.mj.eW i) (RealDat.nP_pos (F := F.lv2) false) (Y.mj.eW_norm i), ← LinearMap.adjoint_inner_left]`. Use `show _ * ⟪D.what₂.thetaT (Y.tup A3.A.μ0) ((i : ℕ) + 1) y, _⟫_ℂ = 0`. Rewrite using `[hT', inner_zero_left, mul_zero]`. Establish `hall : ∀ v ∈ Submodule.span ℂ (R.jV i A3.A.μ0 '' (BlockGood.goodR (A3.A.fam.L i A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) : Set (A3.A.fam.L i A3.A.μ0).S.Forms)), ⟪Y.mj.eW i y, R.thG i A3.A.μ0 v⟫_ℂ = 0`. Introduce `v hv`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨f, hf, rfl⟩` from `hz`. Conclude with `horth f hf`. Consider the case `zero => rw [map_zero, inner_zero_right]`.

Consider the case `add a b _ _ ha hb => rw [map_add, inner_add_right, ha, hb, add_zero]`. Consider the case `smul c a _ ha => rw [map_smul, inner_smul_right, ha, mul_zero]`. Establish `h0 : ⟪LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y), LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y)⟫_ℂ = 0`. Rewrite using `[LinearMap.adjoint_inner_left]`. Conclude with `hall _ ha`.

Conclude with `inner_self_eq_zero.1 h0`.
-/
theorem adjoint_eW_eq_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → ∀ (i : Fin D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, D.what₂.thetaT D.what₂.mu0 ((i : ℕ) + 1) y = 0 → LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y) = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i σ y _hy hT
  have hread := GlobalTheory.Mem.ThetaRead3.thetaP_read_plain D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH i A3.A.μ0
  have hT' : D.what₂.thetaT (Y.tup A3.A.μ0) ((i : ℕ) + 1) y = 0 := by rw [Y.tup0]; exact hT
  have hw : (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) ∈
      R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) := by
    have h0 : Y.mj.eW i y ∈ LinearMap.range (Y.mj.eW i) := ⟨y, rfl⟩
    rw [Y.mj.eW_range] at h0
    exact h0
  have ha := GlobalTheory.CarriedPart.adjoint_mem_span R F hH.ok hP.char hH.prim.unif hH.prim.gUnit hH.prim.gEquiv hH.prim.levW i _ hw
  have horth : ∀ f ∈ BlockGood.goodR (A3.A.fam.L i A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0),
      ⟪Y.mj.eW i y, R.thG i A3.A.μ0 (R.jV i A3.A.μ0 f)⟫_ℂ = 0 := by
    intro f hf
    rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq] at hf
    have hfl : f ∈ lvlForms (A3.A.fam.L i A3.A.μ0).S (A3.A.fam.L i A3.A.μ0).r (A3.A.fam.lvlA F.P0 F.ψ0).P
        (A3.A.fam.lvlA F.P0 F.ψ0).ψ := fun h =>
      Formalism.IndefR.CxPass.LevelOperators.opF_goodAt_type _ _ hH.ok.ok2.irr _ _ h f hf
    rw [← GlobalTheory.Mem.LiftForms.range_lvlForm] at hfl
    obtain ⟨x, rfl⟩ := hfl
    have hx : GlobalTheory.Mem.LiftForms.lvlForm (A3.A.fam.L i A3.A.μ0).S (A3.A.fam.L i A3.A.μ0).r (A3.A.fam.lvlA F.P0 F.ψ0).P
        (A3.A.fam.lvlA F.P0 F.ψ0).ψ x = liftForm A3.A F.P0 F.ψ0 i A3.A.μ0 x := rfl
    rw [hx, ← hread x, GlobalTheory.Mem.LiftForms.inner_of_norm_sq (Y.mj.eW i) (RealDat.nP_pos (F := F.lv2) false) (Y.mj.eW_norm i),
      ← LinearMap.adjoint_inner_left]
    show _ * ⟪D.what₂.thetaT (Y.tup A3.A.μ0) ((i : ℕ) + 1) y, _⟫_ℂ = 0
    rw [hT', inner_zero_left, mul_zero]
  have hall : ∀ v ∈ Submodule.span ℂ (R.jV i A3.A.μ0 '' (BlockGood.goodR (A3.A.fam.L i A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) :
      Set (A3.A.fam.L i A3.A.μ0).S.Forms)), ⟪Y.mj.eW i y, R.thG i A3.A.μ0 v⟫_ℂ = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨f, hf, rfl⟩ := hz
      exact horth f hf
    | zero => rw [map_zero, inner_zero_right]
    | add a b _ _ ha hb => rw [map_add, inner_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, inner_smul_right, ha, mul_zero]
  have h0 : ⟪LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y), LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y)⟫_ℂ = 0 := by
    rw [LinearMap.adjoint_inner_left]
    exact hall _ ha
  exact inner_self_eq_zero.1 h0

end GlobalTheory.Mem.AdjLevel

end
