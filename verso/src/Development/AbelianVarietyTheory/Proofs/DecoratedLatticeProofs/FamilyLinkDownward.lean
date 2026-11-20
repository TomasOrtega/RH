import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopVectorMemExtraProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EZeroThetaDescentEvalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowDescent

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

abbrev xOf (W : RealPack ex) (t : W.P.T) (F : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL) : ((pk W).HX t).H :=
  (pk W).jX t (W.Q.F.eV (cxW W).zs t F)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem topOf_eq (W : RealPack ex) (t : W.P.T) (F : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL) :
    topOf W t F = (pk W).cX.toMap (pk W).prX (((pk W).HX t).e (xOf W t F)) := rfl

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _ F F' e`. Conclude with `e`. Consider the case `succ k ih`.

Introduce `hk F F' e`. Take `⟨h1, h2⟩` from `hr.io k (by omega) F`. Establish `e2 : (⟨F.1, h1⟩ : (pk W).CC t (k + 1)) = F'` using `Subtype.ext e`. Use `show ((f.t t).dn k ((f.row t).io k F)).1 = (Lift.dnFrom ((pk W).CC t) ((pk W).ioY t) k ((pk W).ioY t k F')).1`. Rewrite using `[← e2]`.

Conclude with `ih (by omega) _ _ h2`.
-/
theorem dn_eq {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u) (t : W.P.T) (hr : (f.row t).Is) :
    ∀ k, k + 1 ≤ D.R.m → ∀ (F : (f.t t).CC k) (F' : (pk W).CC t k), F.1 = F'.1 →
      ((f.t t).dn k F).1 = (Lift.dnFrom ((pk W).CC t) ((pk W).ioY t) k F').1 := by
  intro k
  induction k with
  | zero => intro _ F F' e; exact e
  | succ k ih =>
    intro hk F F' e
    obtain ⟨h1, h2⟩ := hr.io k (by omega) F
    have e2 : (⟨F.1, h1⟩ : (pk W).CC t (k + 1)) = F' := Subtype.ext e
    show ((f.t t).dn k ((f.row t).io k F)).1 = (Lift.dnFrom ((pk W).CC t) ((pk W).ioY t) k ((pk W).ioY t k F')).1
    rw [← e2]
    exact ih (by omega) _ _ h2

/- English proof (translation)
Substitute `hk` using the available equality. Rewrite using `[eq_of_heq e]`.
-/
theorem dnFrom_heq (W : RealPack ex) (t : W.P.T) {k : ℕ} (hk : D.R.m - 1 = k) (X : (pk W).CC t k) (X' : (pk W).CC t (D.R.m - 1))
    (e : HEq X X') : (Lift.dnFrom ((pk W).CC t) ((pk W).ioY t) k X).1 = (Lift.dnFrom ((pk W).CC t) ((pk W).ioY t) (D.R.m - 1) X').1 := by
  subst hk
  rw [eq_of_heq e]

/- English proof (translation)
Substitute `p` using the available equality. Both sides reduce to the same expression.
-/
theorem app_heq (W : RealPack ex) (t : W.P.T) {M : Type} [AddCommGroup M] [Module ℂ M] {k k' : ℕ} (p : k = k')
    (g : M →ₗ[ℂ] (pk W).CC t k) (z : M) :
    HEq ((Eq.rec (motive := fun n _ => M →ₗ[ℂ] (pk W).CC t n) g p) z) (g z) := by
  subst p
  rfl

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `H` using `hr.ioT (2 * n) h G`. Establish `h'` using `H.choose`. Establish `e : (((f.row t).ioT (2 * n) h G).1 : SmT ((pk W).MY (2 * n + 1)) →ₗ[ℂ] (GA D (Yc D (2 * n + 1)) → ℂ)) = (ioXT (pk W) t (2 * n) h ⟨G.1, h'⟩).1` using `H.choose_spec`. Establish `e1` using `dn_eq f t hr (2 * n + 1) (by omega) ((f.t t).ioT (2 * n) h G) (ioXT (pk W) t (2 * n) h ⟨G.1, h'⟩) e`. Establish `hy : (⟨G.1, h'⟩ : LinearMap.range ((pk W).cX.toMap (pk W).prX ∘ₗ ((pk W).HX t).e)) = ((pk W).cX.toMap (pk W).prX ∘ₗ ((pk W).HX t).e).rangeRestrict y` using `Subtype.ext hG`.

Establish `e2` using `dnFrom_heq W t (idx_top h) (ioXT (pk W) t (2 * n) h ⟨G.1, h'⟩) ((pk W).ioX t ⟨G.1, h'⟩) (app_heq W t (idx_top h) ((pk W).ioX t) _)`. Establish `e3 : (Lift.dnFrom ((pk W).CC t) ((pk W).ioY t) (D.R.m - 1) ((pk W).ioX t ⟨G.1, h'⟩)).1 = (pk W).thDn t y` using `(congrArg (fun z => (Lift.dnFrom ((pk W).CC t) ((pk W).ioY t) (D.R.m - 1) ((pk W).ioX t z)).1) hy).trans (GlobalTheory.ChainEquiv.thDn_eq t y).symm`. Establish `key : ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)).1 = (pk W).thDn t y` using `e1.trans (e2.trans e3)`. Unfold `GlobalTheory.MiTop.down`. Conclude with `key`.
-/
theorem down_eq {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u) (t : W.P.T) (hr : (f.row t).Is) (n : ℕ)
    (h : 2 * n + 2 * 0 + 2 = D.R.m) (G : (f.t t).CT) (y : ((pk W).HX t).H)
    (hG : G.1 = (pk W).cX.toMap (pk W).prX (((pk W).HX t).e y)) : down f n h t G = (pk W).thDn t y := by
  have H := hr.ioT (2 * n) h G
  have h' := H.choose
  have e : (((f.row t).ioT (2 * n) h G).1 : SmT ((pk W).MY (2 * n + 1)) →ₗ[ℂ] (GA D (Yc D (2 * n + 1)) → ℂ)) =
      (ioXT (pk W) t (2 * n) h ⟨G.1, h'⟩).1 := H.choose_spec
  have e1 := dn_eq f t hr (2 * n + 1) (by omega) ((f.t t).ioT (2 * n) h G) (ioXT (pk W) t (2 * n) h ⟨G.1, h'⟩) e
  have hy : (⟨G.1, h'⟩ : LinearMap.range ((pk W).cX.toMap (pk W).prX ∘ₗ ((pk W).HX t).e)) =
      ((pk W).cX.toMap (pk W).prX ∘ₗ ((pk W).HX t).e).rangeRestrict y := Subtype.ext hG
  have e2 := dnFrom_heq W t (idx_top h) (ioXT (pk W) t (2 * n) h ⟨G.1, h'⟩) ((pk W).ioX t ⟨G.1, h'⟩)
    (app_heq W t (idx_top h) ((pk W).ioX t) _)
  have e3 : (Lift.dnFrom ((pk W).CC t) ((pk W).ioY t) (D.R.m - 1) ((pk W).ioX t ⟨G.1, h'⟩)).1 = (pk W).thDn t y :=
    (congrArg (fun z => (Lift.dnFrom ((pk W).CC t) ((pk W).ioY t) (D.R.m - 1) ((pk W).ioX t z)).1) hy).trans
      (GlobalTheory.ChainEquiv.thDn_eq t y).symm
  have key : ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)).1 = (pk W).thDn t y := e1.trans (e2.trans e3)
  unfold GlobalTheory.MiTop.down
  exact key

/- English proof (translation)
Use `PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, postOn_apply]`. Rewrite using `[show (PiTensorProduct.lift.symm T) v = T (PiTensorProduct.tprod ℂ v) from rfl, hT v]`.
-/
theorem lift_postOn_fixed (W : RealPack ex) (T : SmT ((pk W).MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ))
    (hT : ∀ v : ((pk W).MY 0).Vec, (pk W).e0 (T (PiTensorProduct.tprod ℂ v)) = T (PiTensorProduct.tprod ℂ v)) :
    PiTensorProduct.lift (postOn ((pk W).MY 0) (pk W).e0 (PiTensorProduct.lift.symm T)) = T := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, postOn_apply]
  rw [show (PiTensorProduct.lift.symm T) v = T (PiTensorProduct.tprod ℂ v) from rfl, hT v]

end GlobalTheory.RowDescent

end

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Yd cX ex W u hP f hR n h t F`. Use `⟨⟨topOf W t F, GlobalTheory.T.top_vector_mem_extra_projection W hP t F⟩, rfl, ?_⟩` and prove the remaining obligations. Establish `e1` using `GlobalTheory.RowDescent.down_eq f t (hR.row t) n h ⟨topOf W t F, GlobalTheory.T.top_vector_mem_extra_projection W hP t F⟩ (GlobalTheory.RowDescent.xOf W t F) (GlobalTheory.RowDescent.topOf_eq W t F)`. Establish `hC : (pk W).IsChain` using `RealDat.chain_of_weak W.Q.charW.base.chain hP.ex`. Establish `e2 : rowAt W t F = PiTensorProduct.lift ((pk W).HE.e ((pk W).Th t (GlobalTheory.RowDescent.xOf W t F)))` using `rfl`.

Establish `e3` using `congrArg PiTensorProduct.lift (hC.Th t (GlobalTheory.RowDescent.xOf W t F))`. Establish `e4` using `GlobalTheory.RowDescent.lift_postOn_fixed W _ (GlobalTheory.T.e0_thDn_tprod_eq W hP t F)`. Conclude with `e1.trans (e4.symm.trans (e3.symm.trans e2.symm))`.
-/
theorem GlobalTheory.MiTop.linkDown_of_rowOK : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ f : FamCh W u, f.RowOK → LinkDown f := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f hR n h t F
  refine ⟨⟨topOf W t F, GlobalTheory.T.top_vector_mem_extra_projection W hP t F⟩, rfl, ?_⟩
  have e1 := GlobalTheory.RowDescent.down_eq f t (hR.row t) n h ⟨topOf W t F, GlobalTheory.T.top_vector_mem_extra_projection W hP t F⟩
    (GlobalTheory.RowDescent.xOf W t F) (GlobalTheory.RowDescent.topOf_eq W t F)
  have hC : (pk W).IsChain := RealDat.chain_of_weak W.Q.charW.base.chain hP.ex
  have e2 : rowAt W t F = PiTensorProduct.lift ((pk W).HE.e ((pk W).Th t (GlobalTheory.RowDescent.xOf W t F))) := rfl
  have e3 := congrArg PiTensorProduct.lift (hC.Th t (GlobalTheory.RowDescent.xOf W t F))
  have e4 := GlobalTheory.RowDescent.lift_postOn_fixed W _ (GlobalTheory.T.e0_thDn_tprod_eq W hP t F)
  exact e1.trans (e4.symm.trans (e3.symm.trans e2.symm))
