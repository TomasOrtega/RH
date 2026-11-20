import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLinkDownward
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NotMemQBase
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopOfMemCXPStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EZeroThetaDescentEvalAltBisStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowDescent
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
abbrev geometricDatumOfFamily (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) : ((_root_.GlobalTheory.Fam.pk_z W).HX t).H :=
  (_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem apex_eq_toMap_geometricDatum (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) :
    _root_.GlobalTheory.Fam.leadingLinearMap W t F = (_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F)) := rfl
/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _ F F' e`. Conclude with `e`. Consider the case `succ k ih`.

Introduce `hk F F' e`. Take `⟨h1, h2⟩` from `hr.io k (by omega) F`. Establish `e2 : (⟨F.1, h1⟩ : (_root_.GlobalTheory.Fam.pk_z W).CC t (k + 1)) = F'` using `Subtype.ext e`. Use `show ((f.t t).dn k ((f.row t).io k F)).1 = (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) k ((_root_.GlobalTheory.Fam.pk_z W).ioY t k F')).1`. Rewrite using `[← e2]`.

Conclude with `ih (by omega) _ _ h2`.
-/
theorem dn_fst_eq_dnFrom_fst {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (t : W.P.T) (hr : (f.row t).Is) :
    ∀ k, k + 1 ≤ D.R.m → ∀ (F : (f.t t).CC k) (F' : (_root_.GlobalTheory.Fam.pk_z W).CC t k), F.1 = F'.1 →
      ((f.t t).dn k F).1 = (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) k F').1 := by
  intro k
  induction k with
  | zero => intro _ F F' e; exact e
  | succ k ih =>
    intro hk F F' e
    obtain ⟨h1, h2⟩ := hr.io k (by omega) F
    have e2 : (⟨F.1, h1⟩ : (_root_.GlobalTheory.Fam.pk_z W).CC t (k + 1)) = F' := Subtype.ext e
    show ((f.t t).dn k ((f.row t).io k F)).1 = (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) k ((_root_.GlobalTheory.Fam.pk_z W).ioY t k F')).1
    rw [← e2]
    exact ih (by omega) _ _ h2
/- English proof (translation)
Substitute `hk` using the available equality. Rewrite using `[eq_of_heq e]`.
-/
theorem dnFrom_fst_eq_of_heq (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) {k : ℕ} (hk : D.R.m - 1 = k) (X : (_root_.GlobalTheory.Fam.pk_z W).CC t k) (X' : (_root_.GlobalTheory.Fam.pk_z W).CC t (D.R.m - 1))
    (e : HEq X X') : (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) k X).1 = (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) (D.R.m - 1) X').1 := by
  subst hk
  rw [eq_of_heq e]
/- English proof (translation)
Substitute `p` using the available equality. Both sides reduce to the same expression.
-/
theorem heq_eq_rec_apply (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) {M : Type} [AddCommGroup M] [Module ℂ M] {k k' : ℕ} (p : k = k')
    (g : M →ₗ[ℂ] (_root_.GlobalTheory.Fam.pk_z W).CC t k) (z : M) :
    HEq ((Eq.rec (motive := fun n _ => M →ₗ[ℂ] (_root_.GlobalTheory.Fam.pk_z W).CC t n) g p) z) (g z) := by
  subst p
  rfl
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `H` using `hr.ioT (2 * n) h G`. Establish `h'` using `H.choose`. Establish `e : (((f.row t).ioT (2 * n) h G).1 : SmT ((_root_.GlobalTheory.Fam.pk_z W).MY (2 * n + 1)) →ₗ[ℂ] (GA D (Yc D (2 * n + 1)) → ℂ)) = (ioXT (_root_.GlobalTheory.Fam.pk_z W) t (2 * n) h ⟨G.1, h'⟩).1` using `H.choose_spec`. Establish `e1` using `_root_.GlobalTheory.RowDescent.dn_fst_eq_dnFrom_fst f t hr (2 * n + 1) (by omega) ((f.t t).ioT (2 * n) h G) (ioXT (_root_.GlobalTheory.Fam.pk_z W) t (2 * n) h ⟨G.1, h'⟩) e`. Establish `hy : (⟨G.1, h'⟩ : LinearMap.range ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e)) = ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W). …` using `Subtype.ext hG`.

Establish `e2` using `_root_.GlobalTheory.RowDescent.dnFrom_fst_eq_of_heq W t (idx_top h) (ioXT (_root_.GlobalTheory.Fam.pk_z W) t (2 * n) h ⟨G.1, h'⟩) ((_root_.GlobalTheory.Fam.pk_z W).ioX t ⟨G.1, h'⟩) (_root_.GlobalTheory.RowDescent.heq_eq_rec_apply W t (idx_top h) ((_root_.GlobalTheory.Fam.pk_z W). …`. Establish `e3 : (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) (D.R.m - 1) ((_root_.GlobalTheory.Fam.pk_z W).ioX t ⟨G.1, h'⟩)).1 = (_root_.GlobalTheory.Fam.pk_z W).thDn t y` using `(congrArg (fun z => (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) (D.R.m - 1) ((_root_.GlobalTheory.Fam.pk_z W).ioX t z)).1) hy).trans (GlobalTheory.ChainEquiv.thDn_eq t y).symm`. Establish `key : ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)).1 = (_root_.GlobalTheory.Fam.pk_z W).thDn t y` using `e1.trans (e2.trans e3)`. Unfold `_root_.GlobalTheory.MiTop.descentToLevelZero`. Conclude with `key`.
-/
theorem down_eq_thDn {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (t : W.P.T) (hr : (f.row t).Is) (n : ℕ)
    (h : 2 * n + 2 * 0 + 2 = D.R.m) (G : (f.t t).CT) (y : ((_root_.GlobalTheory.Fam.pk_z W).HX t).H)
    (hG : G.1 = (_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e y)) : _root_.GlobalTheory.MiTop.descentToLevelZero f n h t G = (_root_.GlobalTheory.Fam.pk_z W).thDn t y := by
  have H := hr.ioT (2 * n) h G
  have h' := H.choose
  have e : (((f.row t).ioT (2 * n) h G).1 : SmT ((_root_.GlobalTheory.Fam.pk_z W).MY (2 * n + 1)) →ₗ[ℂ] (GA D (Yc D (2 * n + 1)) → ℂ)) =
      (ioXT (_root_.GlobalTheory.Fam.pk_z W) t (2 * n) h ⟨G.1, h'⟩).1 := H.choose_spec
  have e1 := _root_.GlobalTheory.RowDescent.dn_fst_eq_dnFrom_fst f t hr (2 * n + 1) (by omega) ((f.t t).ioT (2 * n) h G) (ioXT (_root_.GlobalTheory.Fam.pk_z W) t (2 * n) h ⟨G.1, h'⟩) e
  have hy : (⟨G.1, h'⟩ : LinearMap.range ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e)) =
      ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e).rangeRestrict y := Subtype.ext hG
  have e2 := _root_.GlobalTheory.RowDescent.dnFrom_fst_eq_of_heq W t (idx_top h) (ioXT (_root_.GlobalTheory.Fam.pk_z W) t (2 * n) h ⟨G.1, h'⟩) ((_root_.GlobalTheory.Fam.pk_z W).ioX t ⟨G.1, h'⟩)
    (_root_.GlobalTheory.RowDescent.heq_eq_rec_apply W t (idx_top h) ((_root_.GlobalTheory.Fam.pk_z W).ioX t) _)
  have e3 : (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) (D.R.m - 1) ((_root_.GlobalTheory.Fam.pk_z W).ioX t ⟨G.1, h'⟩)).1 = (_root_.GlobalTheory.Fam.pk_z W).thDn t y :=
    (congrArg (fun z => (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) (D.R.m - 1) ((_root_.GlobalTheory.Fam.pk_z W).ioX t z)).1) hy).trans
      (GlobalTheory.ChainEquiv.thDn_eq t y).symm
  have key : ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)).1 = (_root_.GlobalTheory.Fam.pk_z W).thDn t y := e1.trans (e2.trans e3)
  unfold _root_.GlobalTheory.MiTop.descentToLevelZero
  exact key
/- English proof (translation)
Use `PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, postOn_apply]`. Rewrite using `[show (PiTensorProduct.lift.symm T) v = T (PiTensorProduct.tprod ℂ v) from rfl, hT v]`.
-/
theorem piTensorProduct_lift_postOn_eq_of_fixed (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (T : SmT ((_root_.GlobalTheory.Fam.pk_z W).MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ))
    (hT : ∀ v : ((_root_.GlobalTheory.Fam.pk_z W).MY 0).Vec, (_root_.GlobalTheory.Fam.pk_z W).e0 (T (PiTensorProduct.tprod ℂ v)) = T (PiTensorProduct.tprod ℂ v)) :
    PiTensorProduct.lift (postOn ((_root_.GlobalTheory.Fam.pk_z W).MY 0) (_root_.GlobalTheory.Fam.pk_z W).e0 (PiTensorProduct.lift.symm T)) = T := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, postOn_apply]
  rw [show (PiTensorProduct.lift.symm T) v = T (PiTensorProduct.tprod ℂ v) from rfl, hT v]
end GlobalTheory.RowDescent
end
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `D L hT Gi Gl Kc Yd cX ex W u hP f hR n h t F`. Use `⟨⟨_root_.GlobalTheory.Fam.leadingLinearMap W t F, _root_.GlobalTheory.T.vector_of_mem_extra_projection W hP t F⟩, rfl, ?_⟩` and prove the remaining obligations. Establish `e1` using `_root_.GlobalTheory.RowDescent.down_eq_thDn f t (hR.row t) n h ⟨_root_.GlobalTheory.Fam.leadingLinearMap W t F, _root_.GlobalTheory.T.vector_of_mem_extra_projection W hP t F⟩ (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F) (_root_.GlobalTheory.RowDescent.apex_eq_toM …`. Establish `hC : (_root_.GlobalTheory.Fam.pk_z W).IsChain` using `RealDat.chain_of_weak W.Q.charW.base.chain hP.ex`. Establish `e2 : _root_.GlobalTheory.MiTop.rowFormOfTuple W t F = PiTensorProduct.lift ((_root_.GlobalTheory.Fam.pk_z W).HE.e ((_root_.GlobalTheory.Fam.pk_z W).Th t (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F)))` using `rfl`.

Establish `e3` using `congrArg PiTensorProduct.lift (hC.Th t (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F))`. Establish `e4` using `_root_.GlobalTheory.RowDescent.piTensorProduct_lift_postOn_eq_of_fixed W _ (_root_.GlobalTheory.T.e_zero_theta_descent_eval_alt_alt W hP t F)`. Conclude with `e1.trans (e4.symm.trans (e3.symm.trans e2.symm))`.
-/
theorem GlobalTheory.MiTop.linkDown_of_ok : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → _root_.GlobalTheory.MiTop.LinkDescends f := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f hR n h t F
  refine ⟨⟨_root_.GlobalTheory.Fam.leadingLinearMap W t F, _root_.GlobalTheory.T.vector_of_mem_extra_projection W hP t F⟩, rfl, ?_⟩
  have e1 := _root_.GlobalTheory.RowDescent.down_eq_thDn f t (hR.row t) n h ⟨_root_.GlobalTheory.Fam.leadingLinearMap W t F, _root_.GlobalTheory.T.vector_of_mem_extra_projection W hP t F⟩
    (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F) (_root_.GlobalTheory.RowDescent.apex_eq_toMap_geometricDatum W t F)
  have hC : (_root_.GlobalTheory.Fam.pk_z W).IsChain := RealDat.chain_of_weak W.Q.charW.base.chain hP.ex
  have e2 : _root_.GlobalTheory.MiTop.rowFormOfTuple W t F = PiTensorProduct.lift ((_root_.GlobalTheory.Fam.pk_z W).HE.e ((_root_.GlobalTheory.Fam.pk_z W).Th t (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F))) := rfl
  have e3 := congrArg PiTensorProduct.lift (hC.Th t (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F))
  have e4 := _root_.GlobalTheory.RowDescent.piTensorProduct_lift_postOn_eq_of_fixed W _ (_root_.GlobalTheory.T.e_zero_theta_descent_eval_alt_alt W hP t F)
  exact e1.trans (e4.symm.trans (e3.symm.trans e2.symm))
end
