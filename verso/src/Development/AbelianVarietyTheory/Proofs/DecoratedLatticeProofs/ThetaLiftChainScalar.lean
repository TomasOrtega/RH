import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainProjectionLevelCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLevelElementsStepVectorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.LiftVol

/- English proof (translation)
Simplify using `only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]`.
-/
theorem thetaKO_sum_translates {D : D7} {S T : HSp D} {ι : Type} (s : Finset ι) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (g : GA D S) (h : GA D T) (c : ι → ℂ) (κ : ι → GA D S) (f : WO S T → ℂ) :
    thetaKO om g h (∑ p ∈ s, c p • om (κ p, 1) f) = ∑ p ∈ s, c p * thetaKO om (g * κ p) h f := by
  simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Yd cX ex W hW t j hj F hF v hv Q x`. Establish `hio : Lift.IsIo ((pk W).νY t (j + 1)) ((pk W).fdY t (j + 1)) (thetaKO ((pk W).ωY t j)) ((pk W).ptY t j) ((pk W).ItY j) ((pk W).CC t (j + 1)) ((pk W).CC t j) ((pk W).ioY t j)` using `hW.bot.hyp.2.2.2.1.chain.ioY t j (by omega)`. Establish `hfin : ∀ PP : (pk W).Pg, Finite (kP PP.1)` using `fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot`. Use `haveI : Fintype (lvP W).H := Fintype.ofFinite _`. Take `⟨κ, hκ, hsum⟩` from `_root_.GlobalTheory.T.exists_level_elements_step_vector W hW t j hj`.

Use function extensionality and compare the values at `g`. Unfold `liftS Lift.liftInt`. Rewrite using `[hsum v hv Q]`. Repeatedly rewrite using `[thetaKO_sum_translates]`. Establish `hint : ∀ p ∈ (Finset.univ : Finset (lvP W).H), IntegrableOn (fun h => (levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p))⁻¹ * thetaKO ((pk W).ωY t j) (g * κ p) h ((pk W).ptY t j Q) * F.1 x h) ((pk W).fdY t (j + 1)) ((pk W).νY t (j + 1))`.

Introduce `p _`. Repeatedly rewrite using `[mul_assoc]`. Conclude with `(hio.integ ⟨F.1, hF⟩ Q x (g * κ p)).const_mul _`. Repeatedly rewrite using `[Finset.sum_mul]`. Rewrite using `[integral_finsetSum _ hint]`.

Establish `e : ∀ p ∈ (Finset.univ : Finset (lvP W).H), ∫ h in (pk W).fdY t (j + 1), (levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p))⁻¹ * thetaKO ((pk W).ωY t j) (g * κ p) h ((pk W).ptY t j Q) * F.1 x h ∂(pk W).νY t (j + 1) = ((pk W).ioY t j ⟨F.1, hF⟩).1 ((pk W).ItY j Q x) g`. Introduce `p _`. Repeatedly rewrite using `[mul_assoc]`. Rewrite using `[integral_const_mul]`. Establish `h1` using `hio.eq ⟨F.1, hF⟩ Q x (g * κ p)`.

Simplify using `only [Lift.liftInt] at h1`. Rewrite using `[h1, _root_.GlobalTheory.T.chain_projection_level_character W hW t j hj ⟨F.1, hF⟩ F.2 (κ p) (hκ p) Q x g]`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ (Lev.levChi_ne_zero (V := Yc D j) (β := (pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p)), one_mul]`. Rewrite using `[Finset.sum_congr rfl e, Finset.sum_const, Finset.card_univ]`. Simplify using `only [Nat.card_eq_fintype_card, nsmul_eq_mul, Pi.smul_apply, smul_eq_mul]`.
-/
theorem lift_levelP : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ t j, j + 1 < D.R.m → ∀ (F : CP (pk W) (lvP W) t (j + 1)) (hF : F.1 ∈ (pk W).CC t (j + 1)), ∀ v, IsStepVecOf (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) ((pk W).ΛY j) ((pk W).ΛY (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) ((pk W).datYt t j (lvP W)) ((pk W).chi (j + 1)) ((pk W).Q t) ((pk W).xiR t) ((pk W).vac j) v → ∀ Q x, liftS ((pk W).ωY t j) ((pk W).νY t (j + 1)) ((pk W).fdY t (j + 1)) (F.1 x) (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) v Q) = (Nat.card (lvP W).H : ℂ) • ((pk W).ioY t j ⟨F.1, hF⟩).1 ((pk W).ItY j Q x) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW t j hj F hF v hv Q x
  have hio : Lift.IsIo ((pk W).νY t (j + 1)) ((pk W).fdY t (j + 1)) (thetaKO ((pk W).ωY t j)) ((pk W).ptY t j)
      ((pk W).ItY j) ((pk W).CC t (j + 1)) ((pk W).CC t j) ((pk W).ioY t j) :=
    hW.bot.hyp.2.2.2.1.chain.ioY t j (by omega)
  have hfin : ∀ PP : (pk W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  haveI : Fintype (lvP W).H := Fintype.ofFinite _
  obtain ⟨κ, hκ, hsum⟩ := _root_.GlobalTheory.T.exists_level_elements_step_vector W hW t j hj
  funext g
  unfold liftS Lift.liftInt
  rw [hsum v hv Q]
  simp_rw [thetaKO_sum_translates]
  have hint : ∀ p ∈ (Finset.univ : Finset (lvP W).H), IntegrableOn (fun h => (levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p))⁻¹ * thetaKO ((pk W).ωY t j) (g * κ p) h ((pk W).ptY t j Q) * F.1 x h) ((pk W).fdY t (j + 1)) ((pk W).νY t (j + 1)) := by
    intro p _
    simp_rw [mul_assoc]
    exact (hio.integ ⟨F.1, hF⟩ Q x (g * κ p)).const_mul _
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ hint]
  have e : ∀ p ∈ (Finset.univ : Finset (lvP W).H), ∫ h in (pk W).fdY t (j + 1), (levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p))⁻¹ * thetaKO ((pk W).ωY t j) (g * κ p) h ((pk W).ptY t j Q) * F.1 x h ∂(pk W).νY t (j + 1) =
      ((pk W).ioY t j ⟨F.1, hF⟩).1 ((pk W).ItY j Q x) g := by
    intro p _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    have h1 := hio.eq ⟨F.1, hF⟩ Q x (g * κ p)
    simp only [Lift.liftInt] at h1
    rw [h1, _root_.GlobalTheory.T.chain_projection_level_character W hW t j hj ⟨F.1, hF⟩ F.2 (κ p) (hκ p) Q x g]
    rw [← mul_assoc, inv_mul_cancel₀ (Lev.levChi_ne_zero (V := Yc D j) (β := (pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p)), one_mul]
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_univ]
  simp only [Nat.card_eq_fintype_card, nsmul_eq_mul, Pi.smul_apply, smul_eq_mul]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Yd cX ex W u hP f hR t j hj G P v`. Establish `h3` using `hP.bot.hyp.2.2.2.1`. Establish `hch : (pk W).IsChain` using `h3.chain`. Establish `hmod : (pk W).IsModels` using `h3.models`. Take `⟨h, hio⟩` from `(hR.row t).io j hj G`.

Establish `hstep` using `(hR.row t).vP j hj`. Establish `hk` using `lift_levelP W hP t j hj G h`. Establish `hk'` using `hk _ hstep P v`. Establish `hω` using `hch.ωY t j hj`. Establish `hθ : IsInfFam (pk W).θ` using `hmod.inf`.

Establish `hpt` using `GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (cart ((pk W).MY j)) (onb ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY (j + 1))) (GlobalTheory.VecTheta.isThetaFunO_stepVec hstep) P`. Establish `hvol` using `hR.meas.vol t j hj`. Establish `hκ` using `hR.meas.κ (j + 1)`. Establish `hHF : ((pk W).νY t (j + 1)).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D (j + 1))) ((pk W).fdY t (j + 1)) ((pk W).νY t (j + 1))`. Distinguish the cases in `h2 : j + 1 + 1 < D.R.m`.

Establish `h4` using `hmod.νY t (j + 1) h2`. Conclude with `⟨h4.1.1, h4.2⟩`. Establish `h4` using `hmod.νY' t`. Establish `e : D.R.m - 1 = j + 1` using `by omega`. Rewrite `h4` using `[e]`.

Conclude with `⟨h4.1.1, h4.2⟩`. Establish `hm` using `(GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 G.2)`. Establish `hleft : ∀ (w : SmT ((pk W).MY (j + 1))), ∀ γ ∈ GQ (Yc D (j + 1)), ∀ x, G.1 w (γ * x) = G.1 w x`. Introduce `w γ hγ x`. Proceed by induction on `w using PiTensorProduct.induction_on with`.

Consider the case `smul_tprod r w`. Use `(hm.aut w).left γ hγ x` as an intermediate fact. Simplify using `only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at this`. Simplify using `only [map_smul, Pi.smul_apply, smul_eq_mul, this]`. Consider the case `add a a' ha ha'`.

Simplify using `only [map_add, Pi.add_apply, ha, ha']`. Establish `hthL : ∀ g, ∀ γ ∈ GQ (Yc D (j + 1)), ∀ x, (pk W).ωY t j (g, γ * x) ((f.t t).pt j P) 0 = (pk W).ωY t j (g, x) ((f.t t).pt j P) 0`. Introduce `g γ hγ x`. Establish `e : ((g, γ * x) : GA D (Yc D j) × GA D (Yc D (j + 1))) = (1, γ) * (g, x)`. Apply the tactic sequence `ext <;> simp`.

Rewrite using `[e, map_mul, Module.End.mul_apply]`. Conclude with `hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ hpt)`. Establish `: IsTopologicalGroup (GA D (Yc D (j + 1)))` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _`. Establish `: BorelSpace (GA D (Yc D (j + 1)))` using `⟨rfl⟩`. Establish `: Countable (GQ (Yc D (j + 1)))` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Yc D (j + 1)).gram`.

Establish `hvol' : (f.c.vol (j + 1)).μ = ENNReal.ofReal (f.g.κ (j + 1) * GlobalTheory.Fam.volLev (pk W) f.g t j) • (pk W).νY t (j + 1)` using `hvol`. Establish `: (f.c.vol (j + 1)).μ.IsHaarMeasure` using `(f.c.vol (j + 1)).haar`. Establish `hF₁` using `(f.c.vol (j + 1)).fund`. Establish `hF₂ : IsFundamentalDomain (GQ (Yc D (j + 1))) ((pk W).fdY t (j + 1)) (f.c.vol (j + 1)).μ` using `hHF.2.mono (by rw [hvol']; exact Measure.smul_absolutelyContinuous)`. Use function extensionality and compare the values at `g`.

Rewrite using `[liftS_apply, hF₁.setIntegral_eq hF₂ (fun γ x => by show (pk W).ωY t j (g, (γ : GA D (Yc D (j + 1))) * x) ((f.t t).pt j P) 0 * G.1 v ((γ : GA D (Yc D (j + 1))) * x) = _`. Rewrite using `[hthL g γ γ.2 x, hleft v γ γ.2 x])]`. Rewrite using `[hvol', Measure.restrict_smul, integral_smul_measure]`. Establish `hk2` using `congrFun hk' g`. Rewrite `hk2` using `[liftS_apply]`.

Establish `hv0 : 0 ≤ GlobalTheory.Fam.volLev (pk W) f.g t j`. Apply the tactic sequence `unfold GlobalTheory.Fam.volLev; split_ifs <;> exact ENNReal.toReal_nonneg`. Establish `hc0 : 0 ≤ f.g.κ (j + 1) * GlobalTheory.Fam.volLev (pk W) f.g t j` using `mul_nonneg hκ.le hv0`. Rewrite using `[ENNReal.toReal_ofReal hc0]`. Use `erw [hk2]`.

Use `show _ = (cIOf (pk W) (lvP W) f.g t j • ((f.row t).io j G).1 ((pk W).ItY j P v)) g`. Rewrite using `[hio]`. Simplify using `only [Pi.smul_apply, cIOf, Complex.real_smul, smul_eq_mul, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lift_eq_cI_io : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ f : FamCh W u, f.RowOK → ∀ t j, j + 1 < D.R.m → ∀ (G : (f.t t).CC (j + 1)) P v, liftS ((f.t t).om j) (f.c.vol (j + 1)).μ (f.c.vol (j + 1)).𝓕 (G.1 v) ((f.t t).pt j P) = (f.t t).cI j • ((f.t t).io j G).1 (f.c.It j P v) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f hR t j hj G P v
  have h3 := hP.bot.hyp.2.2.2.1
  have hch : (pk W).IsChain := h3.chain
  have hmod : (pk W).IsModels := h3.models
  obtain ⟨h, hio⟩ := (hR.row t).io j hj G
  have hstep := (hR.row t).vP j hj
  have hk := lift_levelP W hP t j hj G h
  have hk' := hk _ hstep P v
  have hω := hch.ωY t j hj
  have hθ : IsInfFam (pk W).θ := hmod.inf
  have hpt := GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (cart ((pk W).MY j)) (onb ((pk W).MY j))
    (cart ((pk W).MY (j + 1))) (onb ((pk W).MY (j + 1)))
    (GlobalTheory.VecTheta.isThetaFunO_stepVec hstep) P

  have hvol := hR.meas.vol t j hj
  have hκ := hR.meas.κ (j + 1)
  have hHF : ((pk W).νY t (j + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (j + 1))) ((pk W).fdY t (j + 1)) ((pk W).νY t (j + 1)) := by
    by_cases h2 : j + 1 + 1 < D.R.m
    · have h4 := hmod.νY t (j + 1) h2
      exact ⟨h4.1.1, h4.2⟩
    · have h4 := hmod.νY' t
      have e : D.R.m - 1 = j + 1 := by omega
      rw [e] at h4
      exact ⟨h4.1.1, h4.2⟩

  have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 G.2)
  have hleft : ∀ (w : SmT ((pk W).MY (j + 1))), ∀ γ ∈ GQ (Yc D (j + 1)), ∀ x, G.1 w (γ * x) = G.1 w x := by
    intro w γ hγ x
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r w =>
      have := (hm.aut w).left γ hγ x
      simp only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at this
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, this]
    | add a a' ha ha' =>
      simp only [map_add, Pi.add_apply, ha, ha']
  have hthL : ∀ g, ∀ γ ∈ GQ (Yc D (j + 1)), ∀ x, (pk W).ωY t j (g, γ * x) ((f.t t).pt j P) 0 =
      (pk W).ωY t j (g, x) ((f.t t).pt j P) 0 := by
    intro g γ hγ x
    have e : ((g, γ * x) : GA D (Yc D j) × GA D (Yc D (j + 1))) = (1, γ) * (g, x) := by
      ext <;> simp
    rw [e, map_mul, Module.End.mul_apply]
    exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ hpt)
  have : IsTopologicalGroup (GA D (Yc D (j + 1))) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D (Yc D (j + 1))) := ⟨rfl⟩
  have : Countable (GQ (Yc D (j + 1))) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Yc D (j + 1)).gram
  have hvol' : (f.c.vol (j + 1)).μ = ENNReal.ofReal (f.g.κ (j + 1) * GlobalTheory.Fam.volLev (pk W) f.g t j) • (pk W).νY t (j + 1) := hvol
  have : (f.c.vol (j + 1)).μ.IsHaarMeasure := (f.c.vol (j + 1)).haar
  have hF₁ := (f.c.vol (j + 1)).fund
  have hF₂ : IsFundamentalDomain (GQ (Yc D (j + 1))) ((pk W).fdY t (j + 1)) (f.c.vol (j + 1)).μ :=
    hHF.2.mono (by rw [hvol']; exact Measure.smul_absolutelyContinuous)
  funext g
  rw [liftS_apply, hF₁.setIntegral_eq hF₂ (fun γ x => by
    show (pk W).ωY t j (g, (γ : GA D (Yc D (j + 1))) * x) ((f.t t).pt j P) 0 * G.1 v ((γ : GA D (Yc D (j + 1))) * x) = _
    rw [hthL g γ γ.2 x, hleft v γ γ.2 x])]
  rw [hvol', Measure.restrict_smul, integral_smul_measure]
  have hk2 := congrFun hk' g
  rw [liftS_apply] at hk2

  have hv0 : 0 ≤ GlobalTheory.Fam.volLev (pk W) f.g t j := by
    unfold GlobalTheory.Fam.volLev; split_ifs <;> exact ENNReal.toReal_nonneg
  have hc0 : 0 ≤ f.g.κ (j + 1) * GlobalTheory.Fam.volLev (pk W) f.g t j := mul_nonneg hκ.le hv0
  rw [ENNReal.toReal_ofReal hc0]
  erw [hk2]
  show _ = (cIOf (pk W) (lvP W) f.g t j • ((f.row t).io j G).1 ((pk W).ItY j P v)) g
  rw [hio]
  simp only [Pi.smul_apply, cIOf, Complex.real_smul, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.Fam.LiftVol
