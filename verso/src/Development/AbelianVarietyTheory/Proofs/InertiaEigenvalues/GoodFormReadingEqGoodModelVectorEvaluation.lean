import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlockTriangularTwoBlockSizesOfLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.SeriesTie.ModelGood

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)

def jH (j : Fin D.R.m) : S.WL ((j : ℕ) + 1) →+ (Rl.HW j (sg0 D A3.A)).H where
  toFun x := (Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e x)
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add, map_add]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e (c • x)) = _`. Rewrite using `[map_smul, map_smulₛₗ, show sg0 D A3.A c = D.what₂.embLL c from congrArg (fun f : D.what₂.LL →+* ℂ => f c) (sgAt_mk _ Rl.hv0)]`. Both sides reduce to the same expression.
-/
theorem jH_smul (j : Fin D.R.m) (c : D.what₂.LL) (x : S.WL ((j : ℕ) + 1)) :
    jH YS j (c • x) = D.what₂.embLL c • jH YS j x := by
  change (Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e (c • x)) = _
  rw [map_smul, map_smulₛₗ, show sg0 D A3.A c = D.what₂.embLL c from
    congrArg (fun f : D.what₂.LL →+* ℂ => f c) (sgAt_mk _ Rl.hv0)]
  rfl

section Read

variable {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

def evH : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1) →+ (Rl.HW j (sg0 D A3.A)).H :=
  TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ρ.e i b a)).comp
        ((jH YS j).comp (S.A ((j : ℕ) + 1)).WK.subtype.toAddMonoidHom)
      map_zero' := by ext; simp [show ρ.e i b (0 : NX.KB S i b) = 0 from map_zero _]
      map_add' := fun x y => by
        ext; simp [show ρ.e i b (x + y : NX.KB S i b) = ρ.e i b x + ρ.e i b y from map_add _ _ _, add_smul] }
    fun c a f => by
      change ρ.e i b (sideEmb D.ntw i b (S.kKs c) * (show FractionRing (D.ntw.O i) from a)) • jH YS j (Subtype.val f) =
        ρ.e i b a • jH YS j (c • Subtype.val f)
      rw [← algebraMap_smul D.what₂.LL c, jH_smul, map_mul, hρ.e_LL0, smul_smul, mul_comm, ← S.kKs_spec]
      rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evH_tmul (a : NX.KB S i b) (f : NX.FmK S ((j : ℕ) + 1)) :
    evH YS hρ i j b (a ⊗ₜ f) = ρ.e i b a • jH YS j (Subtype.val f) := rfl

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero, map_zero]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [map_add, map_add, map_add, hx, hy]`. Both sides reduce to the same expression.

Consider the case `tmul a f => rw [evK_tmul, evH_tmul, map_smul]`. Both sides reduce to the same expression.
-/
theorem evK_eq (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (t : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evK YS v₀ hρ i j b t = (Rl.HW j (sg0 D A3.A)).e (evH YS hρ i j b t) (v₀ j _) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; rfl
  | tmul a f => rw [evK_tmul, evH_tmul, map_smul]; rfl

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => rw [smul_zero, map_zero, smul_zero]`. Consider the case `add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]`. Consider the case `tmul a f`. Rewrite using `[TensorProduct.smul_tmul', evH_tmul, evH_tmul, smul_smul]`.

Conclude with `congrArg (· • _) (map_mul (ρ.e i b) c a)`.
-/
theorem evH_smul (c : NX.KB S i b) (t : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evH YS hρ i j b (c • t) = ρ.e i b c • evH YS hρ i j b t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul a f =>
    rw [TensorProduct.smul_tmul', evH_tmul, evH_tmul, smul_smul]
    exact congrArg (· • _) (map_mul (ρ.e i b) c a)

def mv (y : D.nexp.Fm i ((j : ℕ) + 1) b) : (Rl.HW j (sg0 D A3.A)).H :=
  evH YS hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 y)

/- English proof (translation)
Unfold `mv`. Rewrite using `[YS.act]`. Generalize the expression as in `YS.eF i _ b (Nat.le_add_left _ _) j.2 y = t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => erw [LinearEquiv.map_zero]`.

Simplify using `only [map_zero]`. Conclude with `(congrArg (Rl.HW j (sg0 D A3.A)).e ((evH YS hρ i j b).map_zero)).trans (map_zero _)`. Consider the case `add y z hy hz => erw [LinearEquiv.map_add, map_add, map_add, hy, hz, map_add, map_add, map_add]`. Consider the case `tmul a f0`. Establish `e1 : (NX.actG S i ((j : ℕ) + 1) b (YS.rho _ (Nat.le_add_left _ _) j.2) (YS.chi _ (Nat.le_add_left _ _) j.2) g) (a ⊗ₜ f0) = ((NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g)))⁻¹ * a) ⊗ₜ (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm …`.

Express the relevant statement in the definitionally equal form `(NX.readLL0 S i b (NX.chiL S _ _ (S.eG.symm g)))⁻¹ • (a ⊗ₜ[S.Ks] (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0)) = _`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul]`. Use `erw [e1]`. Rewrite using `[evH_tmul, evH_tmul]`. Establish `hgeq : Rl.eG ((YS.fi j).eG (S.eG.symm g)) = cG.symm g`.

Establish `h0` using `YS.geq j (S.eG.symm g)`. Rewrite `h0` using `[MulEquiv.apply_symm_apply]`. Conclude with `((MulEquiv.symm_apply_eq cG).2 h0.symm).symm`. Establish `he : ρ.e i b (NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g))) = D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL)` using `hρ.e_LL0 i b _`. Establish `hne : D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) ≠ 0` using `(map_ne_zero _).2 (Units.ne_zero _)`.

Establish `hs : sg0 D A3.A = D.what₂.embLL` using `GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL Rl`. Express the relevant statement in the definitionally equal form `(Rl.HW j (sg0 D A3.A)).e (ρ.e i b _ • (Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e ((S.A ((j : ℕ) + 1)).ρ (S.eG.symm g) (Subtype.val f0)))) = _`. Rewrite using `[map_smul, map_smul, map_smul, (YS.fi j).rho, (hU j _).2.2, (YS.fi j).chi, hgeq, smul_smul]`. Use `congr 1`. Use `erw [map_mul, map_inv₀, he, hs]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem mv_act (hU : Rl.toRealDat.LUnif) (g : G0g D.nd) (y : D.nexp.Fm i ((j : ℕ) + 1) b) :
    (Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b (D.nexp.actG i _ b g y)) =
      postOn _ (actL (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (cG.symm g))
        ((Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b y)) := by
  unfold mv
  rw [YS.act]
  generalize YS.eF i _ b (Nat.le_add_left _ _) j.2 y = t
  induction t using TensorProduct.induction_on with
  | zero =>
    erw [LinearEquiv.map_zero]
    simp only [map_zero]
    exact (congrArg (Rl.HW j (sg0 D A3.A)).e ((evH YS hρ i j b).map_zero)).trans (map_zero _)
  | add y z hy hz => erw [LinearEquiv.map_add, map_add, map_add, hy, hz, map_add, map_add, map_add]
  | tmul a f0 =>
    have e1 : (NX.actG S i ((j : ℕ) + 1) b (YS.rho _ (Nat.le_add_left _ _) j.2) (YS.chi _ (Nat.le_add_left _ _) j.2) g)
        (a ⊗ₜ f0) = ((NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g)))⁻¹ * a) ⊗ₜ
          (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0) := by
      change (NX.readLL0 S i b (NX.chiL S _ _ (S.eG.symm g)))⁻¹ •
        (a ⊗ₜ[S.Ks] (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0)) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul]
    erw [e1]
    rw [evH_tmul, evH_tmul]
    have hgeq : Rl.eG ((YS.fi j).eG (S.eG.symm g)) = cG.symm g := by
      have h0 := YS.geq j (S.eG.symm g)
      rw [MulEquiv.apply_symm_apply] at h0
      exact ((MulEquiv.symm_apply_eq cG).2 h0.symm).symm
    have he : ρ.e i b (NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g))) =
        D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) :=
      hρ.e_LL0 i b _
    have hne : D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) ≠ 0 :=
      (map_ne_zero _).2 (Units.ne_zero _)
    have hs : sg0 D A3.A = D.what₂.embLL := GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL Rl
    change (Rl.HW j (sg0 D A3.A)).e (ρ.e i b _ • (Rl.FW j).j (sg0 D A3.A)
      ((YS.fi j).e ((S.A ((j : ℕ) + 1)).ρ (S.eG.symm g) (Subtype.val f0)))) = _
    rw [map_smul, map_smul, map_smul, (YS.fi j).rho, (hU j _).2.2, (YS.fi j).chi, hgeq, smul_smul]
    congr 1
    erw [map_mul, map_inv₀, he, hs]
    field_simp

/- English proof (translation)
Unfold `mv`. Rewrite using `[map_smul]`. Conclude with `evH_smul YS hρ i j b c _`.
-/
theorem mv_smul (c : FractionRing (D.ntw.O i)) (y : D.nexp.Fm i ((j : ℕ) + 1) b) :
    mv YS hρ i j b (c • y) = ρ.e i b c • mv YS hρ i j b y := by
  unfold mv
  rw [map_smul]
  exact evH_smul YS hρ i j b c _

/- English proof (translation)
Unfold `mv`. Rewrite using `[map_sum]`. Conclude with `map_sum (evH YS hρ i j b) _ _`.
-/
theorem mv_sum {ι : Type} (s : Finset ι) (y : ι → D.nexp.Fm i ((j : ℕ) + 1) b) :
    mv YS hρ i j b (∑ k ∈ s, y k) = ∑ k ∈ s, mv YS hρ i j b (y k) := by
  unfold mv
  rw [map_sum]
  exact map_sum (evH YS hρ i j b) _ _

/- English proof (translation)
Use `MultilinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [RealDat.eWf, gaL, postOn, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.compMultilinearMap_apply, LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply, MultilinearMap.smul_apply]`. Both sides reduce to the same expression.
-/
theorem postOn_eWf_sum (σ : D.what₂.LL →+* ℂ) (M : MMap (Rl.MW j σ)) :
    postOn (Rl.MW j σ) (Rl.toRealDat.eWf j σ) M = ∑ γ : Γ, RealDat.eC (A := A3.A) σ γ •
      postOn (Rl.MW j σ) (actL (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG γ)) M := by
  refine MultilinearMap.ext fun v => ?_
  simp only [RealDat.eWf, gaL, postOn, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.compMultilinearMap_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply, MultilinearMap.smul_apply]
  rfl

/- English proof (translation)
Use `letI : Fintype (G0g D.nd) := Fintype.ofEquiv Γ (Rl.eG.trans cG).toEquiv`. Establish `h1 : Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b y = ∑ g, (D.nexp.eAlg i b).coeff g • D.nexp.actG i _ b g y`. Unfold `Formalism.MainNotions.IntegralHeckeForms.eG`. Rewrite using `[MonoidAlgebra.lift_apply, Finsupp.sum_fintype]`. Rewrite using `[LinearMap.sum_apply]`.

Both sides reduce to the same expression. Use `intro`. Conclude with `zero_smul _ _`. Establish `hc : ∀ g, ρ.e i b ((D.nexp.eAlg i b).coeff g) = D.ntypes.e0.coeff g` using `fun g => by`. Establish `h : (D.nexp.eAlg i b).coeff g = NX.readLL0 S i b (D.nexp.eLL0 g)` using `by rw [D.nexp.eAlg_def]; rfl`.

Rewrite using `[h]`. Conclude with `(hρ.e_LL0 i b _).trans (D.nStage_trivialCharacter_coeff_eq g)`. Establish `hs : sg0 D A3.A = D.what₂.embLL` using `GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL Rl`. Rewrite using `[h1, mv_sum, map_sum, postOn_eWf_sum]`. Use `(Fintype.sum_equiv (Rl.eG.trans cG).toEquiv _ _ fun γ => ?_).symm` and prove the remaining obligations.

Rewrite using `[mv_smul, map_smul, mv_act YS hρ i j b hU, hc]`. Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]`. Use `congr 1`. Conclude with `(congrArg (fun f : D.what₂.LL →+* ℂ => f ((idemOf A3.A.X).coeff γ)) hs).trans (hid γ)`.
-/
theorem mv_eG (hU : Rl.toRealDat.LUnif)
    (hid : ∀ γ : Γ, D.what₂.embLL ((idemOf A3.A.X).coeff γ) = D.ntypes.e0.coeff ((Rl.eG.trans cG) γ))
    (y : D.nexp.Fm i ((j : ℕ) + 1) b) :
    (Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b y)) =
      postOn _ (Rl.toRealDat.eWf j (sg0 D A3.A)) ((Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b y)) := by
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv Γ (Rl.eG.trans cG).toEquiv
  have h1 : Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b y = ∑ g, (D.nexp.eAlg i b).coeff g • D.nexp.actG i _ b g y := by
    unfold Formalism.MainNotions.IntegralHeckeForms.eG
    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype]
    · rw [LinearMap.sum_apply]; rfl
    · intro; exact zero_smul _ _
  have hc : ∀ g, ρ.e i b ((D.nexp.eAlg i b).coeff g) = D.ntypes.e0.coeff g := fun g => by
    have h : (D.nexp.eAlg i b).coeff g = NX.readLL0 S i b (D.nexp.eLL0 g) := by rw [D.nexp.eAlg_def]; rfl
    rw [h]
    exact (hρ.e_LL0 i b _).trans (D.nStage_trivialCharacter_coeff_eq g)
  have hs : sg0 D A3.A = D.what₂.embLL := GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL Rl
  rw [h1, mv_sum, map_sum, postOn_eWf_sum]
  refine (Fintype.sum_equiv (Rl.eG.trans cG).toEquiv _ _ fun γ => ?_).symm
  rw [mv_smul, map_smul, mv_act YS hρ i j b hU, hc]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  congr 1
  exact (congrArg (fun f : D.what₂.LL →+* ℂ => f ((idemOf A3.A.X).coeff γ)) hs).trans (hid γ)

end Read
end GlobalTheory.SeriesTie.ModelGood

open GlobalTheory.SeriesTie.ModelGood in
/- English proof (translation)
Introduce `D X E Y i j b x hx`. Take `⟨f, -, rfl⟩` from `hx`. Establish `hidem : ∀ z, Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b z) = Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i ((j : ℕ) + 1) b z` using `fun z => by rw [← Module.End.mul_apply, Formalism.MainNotions.IntegralHeckeForms.eG, ← map_mul, D.nexp.eAlg_idem]`. Use `⟨mv Y.YS Y.Z.good i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b f), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h` using `LinearMap.mem_range_self (X.R.HW j (sg0 D X.A3.A)).e (mv Y.YS Y.Z.good i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b f))`.

Rewrite `h` using `[(X.char.models.HW j _).2.1]`. Conclude with `h`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply]`. Rewrite using `[← mv_eG Y.YS Y.Z.good i j b X.unif X.idem, hidem]`. Express the relevant statement in the definitionally equal form `(Y.Z.ν i j b)⁻¹ • evK Y.YS X.geo.v₀ Y.Z.good i j b _ = _`.

Conclude with `congrArg _ (evK_eq Y.YS Y.Z.good i j b X.geo.v₀ _)`.
-/
theorem GlobalTheory.SeriesTie.rd_good_model : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∃ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.goodModel X.R.toRealDat j,
      Y.Z.rd i j b x = (Y.Z.ν i j b)⁻¹ • (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) := by
  intro D X E Y i j b x hx
  obtain ⟨f, -, rfl⟩ := hx
  have hidem : ∀ z, Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b z) = Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i ((j : ℕ) + 1) b z :=
    fun z => by rw [← Module.End.mul_apply, Formalism.MainNotions.IntegralHeckeForms.eG, ← map_mul, D.nexp.eAlg_idem]
  refine ⟨mv Y.YS Y.Z.good i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b f), ⟨?_, ?_⟩, ?_⟩
  · have h := LinearMap.mem_range_self (X.R.HW j (sg0 D X.A3.A)).e
      (mv Y.YS Y.Z.good i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b f))
    rw [(X.char.models.HW j _).2.1] at h
    exact h
  · rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply]
    rw [← mv_eG Y.YS Y.Z.good i j b X.unif X.idem, hidem]
  · change (Y.Z.ν i j b)⁻¹ • evK Y.YS X.geo.v₀ Y.Z.good i j b _ = _
    exact congrArg _ (evK_eq Y.YS Y.Z.good i j b X.geo.v₀ _)
