import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.LieMet
  GlobalTheory.LocM
open GlobalTheory.Conormal
open GlobalTheory.Twist (resM resM_self)
open GlobalTheory.QCoh (pullbackSections)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap LieG dualScale)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.TanPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {R : Type} [CommRing R] {x : Sp R ⟶ X} {G' : Over (Sp R)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}
  (h' : IsGrpPullback G' t.G x φ)

/- English proof (translation)
Rewrite using `[Over.toUnit_left]`. Conclude with `Spec.map_id _`.
-/
theorem toUnit_specO_left : (toUnit (specO R R)).left = 𝟙 (Sp R) := by
  rw [Over.toUnit_left]
  exact Spec.map_id _

include h'

/- English proof (translation)
Set `p : specO R (DualNumber R) ⟶ G'` to `Over.homMk (h'.1.lift v (specO R (DualNumber R)).hom hv.1) (h'.1.lift_snd _ _ _)`. Establish `hp : p.left ≫ φ = v` using `h'.1.lift_fst _ _ _`. Use `⟨⟨p, Over.OverMorphism.ext (h'.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩, hp⟩` and prove the remaining obligations. Rewrite using `[Over.comp_left, Over.comp_left, toUnit_specO_left, Category.assoc, hp, Category.assoc]`. Conclude with `(epsZero_comp_of_isTanAtG t hv).trans ((unitSec_comp h').symm.trans (Category.id_comp _).symm)`.
-/
theorem exists_lieG {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    ∃ p : LieG G', p.1.left ≫ φ = v := by
  let p : specO R (DualNumber R) ⟶ G' :=
    Over.homMk (h'.1.lift v (specO R (DualNumber R)).hom hv.1) (h'.1.lift_snd _ _ _)
  have hp : p.left ≫ φ = v := h'.1.lift_fst _ _ _
  refine ⟨⟨p, Over.OverMorphism.ext (h'.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩, hp⟩
  rw [Over.comp_left, Over.comp_left, toUnit_specO_left, Category.assoc, hp, Category.assoc]
  exact (epsZero_comp_of_isTanAtG t hv).trans ((unitSec_comp h').symm.trans (Category.id_comp _).symm)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[Category.assoc, h'.1.w, ← Category.assoc]`. Conclude with `congrArg (· ≫ x) (Over.w p.1)`. Rewrite using `[← Category.assoc, Hom.one_def, Over.comp_left, Over.toUnit_left]`. Conclude with `(congrArg (· ≫ φ) (sec_epsZero_comp p)).trans (unitSec_comp h')`.
-/
theorem isTanAtG_lieG (p : LieG G') : IsTanAtG t x (p.1.left ≫ φ) := by
  constructor
  · rw [Category.assoc, h'.1.w, ← Category.assoc]
    exact congrArg (· ≫ x) (Over.w p.1)
  · rw [← Category.assoc, Hom.one_def, Over.comp_left, Over.toUnit_left]
    exact (congrArg (· ≫ φ) (sec_epsZero_comp p)).trans (unitSec_comp h')

/- English proof (translation)
Use `Eq.trans (congrArg (· ≫ (epsIso R).hom) ?_) (Category.assoc _ _ _)` and prove the remaining obligations. Use `pullback_hom_ext (sec_hom η[t.G]) fun W a => ?_` and prove the remaining obligations. Establish `k₁ : x ⁻¹ᵁ unitSec t.G ⁻¹ᵁ W ≤ unitSec G' ⁻¹ᵁ φ ⁻¹ᵁ W` using `(le_preimage_of_comp (unitSec_comp h')).2 le_rfl`. Establish `k₂ : x ⁻¹ᵁ unitSec t.G ⁻¹ᵁ W ≤ sec (epsZero R) ⁻¹ᵁ v ⁻¹ᵁ W` using `(le_preimage_of_comp (epsZero_comp_of_isTanAtG t hv)).2 le_rfl`. Establish `k₃ : v ⁻¹ᵁ W ≤ p.1.left ⁻¹ᵁ φ ⁻¹ᵁ W` using `(le_preimage_of_comp hp).2 le_rfl`.

Use `(baseMap_d (sec_hom η[t.G]) (sec_hom (epsZero R)) hv.1 (epsZero_comp_of_isTanAtG t hv) le_rfl le_rfl k₂ le_rfl a).trans ?_` and prove the remaining obligations. Use `Eq.symm ((congrArg ((cotMap p.1 (epsZero_comp p)).app _) (omegaBase_dUnit h' le_rfl le_rfl k₁ le_rfl a)).trans ?_)` and prove the remaining obligations. Conclude with `(cotMap_d p.1 (epsZero_comp p) k₁ k₂ k₃ _).trans (congrArg _ (appLE_appLE hp _ _ _ a))`.
-/
theorem tanForm_eq (p : LieG G') {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) (hp : p.1.left ≫ φ = v) :
    tanForm t hv = omegaBase h' ≫ cotMap p.1 (epsZero_comp p) ≫ (epsIso R).hom := by
  refine Eq.trans (congrArg (· ≫ (epsIso R).hom) ?_) (Category.assoc _ _ _)
  refine pullback_hom_ext (sec_hom η[t.G]) fun W a => ?_
  have k₁ : x ⁻¹ᵁ unitSec t.G ⁻¹ᵁ W ≤ unitSec G' ⁻¹ᵁ φ ⁻¹ᵁ W :=
    (le_preimage_of_comp (unitSec_comp h')).2 le_rfl
  have k₂ : x ⁻¹ᵁ unitSec t.G ⁻¹ᵁ W ≤ sec (epsZero R) ⁻¹ᵁ v ⁻¹ᵁ W :=
    (le_preimage_of_comp (epsZero_comp_of_isTanAtG t hv)).2 le_rfl
  have k₃ : v ⁻¹ᵁ W ≤ p.1.left ⁻¹ᵁ φ ⁻¹ᵁ W := (le_preimage_of_comp hp).2 le_rfl
  refine (baseMap_d (sec_hom η[t.G]) (sec_hom (epsZero R)) hv.1 (epsZero_comp_of_isTanAtG t hv) le_rfl le_rfl k₂
    le_rfl a).trans ?_
  refine Eq.symm ((congrArg ((cotMap p.1 (epsZero_comp p)).app _)
    (omegaBase_dUnit h' le_rfl le_rfl k₁ le_rfl a)).trans ?_)
  exact (cotMap_d p.1 (epsZero_comp p) k₁ k₂ k₃ _).trans (congrArg _ (appLE_appLE hp _ _ _ a))

/- English proof (translation)
Rewrite using `[tanEv, tanForm_eq h' p hv hp]`. Both sides reduce to the same expression.
-/
theorem tanEv_eq (p : LieG G') {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) (hp : p.1.left ≫ φ = v)
    {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(omega t.G, V)) :
    tanEv t hv h s = (Scheme.ΓSpecIso (.of R)).hom
      (dualApp (tangent p) le_top ((omegaBase h').app ⊤ (pullbackSections x (omega t.G) h s))) := by
  rw [tanEv, tanForm_eq h' p hv hp]
  rfl

/- English proof (translation)
Use `t.semi` as an intermediate fact. Establish `: QuasiSeparated G'.hom` using `MorphismProperty.of_isPullback h'.1 inferInstance`. Set `e : Fin n → Γ(omega G', ⊤)` to `fun b => (omegaBase h').app ⊤ (pullbackSections x (omega t.G) h (s b))`. Establish `he : VB.IsFrame e`. Establish `h₁` using `((hs.pullback x).res h).map_iso (omegaBase h')`.

Establish `h₂ (b : Fin n) : resM _ h (pullbackSections x (omega t.G) le_rfl (s b)) = pullbackSections x (omega t.G) h (s b)` using `QCoh.res_pullbackSections x _ _ _ _`. Simplify `h₁` using `only [h₂]`. Establish `hc` using `ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom`. Set `Φ : TanM x t.G →ₗ[R] (Fin n → R)` to `{ toFun := fun v b => tanEv t (isTan_tv v) h (s b) map_add' := fun v w => funext fun b => by`. Take `⟨p, hp⟩` from `exists_lieG h' (isTan_tv v)`.

Take `⟨q, hq⟩` from `exists_lieG h' (isTan_tv w)`. Establish `hpq : (p.1 * q.1).left ≫ φ = (tv (v + w)).left` using `(h'.2 _ p.1 q.1 (tv v) (tv w) hp.symm hq.symm).symm`. Rewrite using `[Pi.add_apply, tanEv_eq h' p _ hp, tanEv_eq h' q _ hq, tanEv_eq h' ⟨_, OmegaGlobal.fst_mul p q⟩ _ hpq, tangent_mul, dualApp_add, LinearMap.add_apply, map_add]`. Use the proof step `map_smul' := fun a v => funext fun b => by`. Take `⟨p, hp⟩` from `exists_lieG h' (isTan_tv v)`.

Establish `ha : (dualScale a).toRingHom = epsScaleR a`. Apply the tactic sequence `ext y <;> simp [dualScale, epsScaleR]`. Establish `hpq : (ptMap (dualScale a) ≫ p.1).left ≫ φ = (tv (a • v)).left`. Rewrite using `[Over.comp_left, Category.assoc, hp]`. Conclude with `congrArg (fun r => spMap r ≫ (tv v).left) ha`.

Rewrite using `[Pi.smul_apply, tanEv_eq h' p _ hp, tanEv_eq h' ⟨_, OmegaGlobal.fst_scale a p⟩ _ hpq, tangent_scale]`. Simplify using `only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, GlobalTheory.LB.resG_self, Iso.inv_hom_id_apply, RingHom.id_apply] }`. Use `⟨LinearEquiv.ofBijective Φ ⟨fun v w hvw => ?_, fun c => ?_⟩, fun _ _ => rfl⟩` and prove the remaining obligations. Take `⟨p, hp⟩` from `exists_lieG h' (isTan_tv v)`. Take `⟨q, hq⟩` from `exists_lieG h' (isTan_tv w)`.

Take `rfl : p = q` from `tangent_injective R G' (he.dual_ext le_rfl fun b => by`. Rewrite using `[resM_self]`. Conclude with `hc.1 ((tanEv_eq h' p _ hp h (s b)).symm.trans ((congrFun hvw b).trans (tanEv_eq h' q _ hq h (s b)))))`. Conclude with `tan_ext (hp.symm.trans hq)`. Take `⟨p, hp⟩` from `TangentSurj.tangent_surjective R G' ((he.dual.basis le_rfl).equivFun.symm fun b => cst R (c b))`.

Use `⟨tanOf (isTanAtG_lieG h' p), funext fun b => (tanEv_eq h' p _ rfl h (s b)).trans ?_⟩` and prove the remaining obligations. Establish `k` using `he.dual_basis_repr le_rfl (tangent p) b`. Rewrite `k` using `[resM_self, hp, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, ← hp]`. Conclude with `(congrArg _ k.symm).trans (Iso.inv_hom_id_apply _ _)`.
-/
theorem exists_equiv_of_isGrpPullback {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} {s : Fin n → Γ(omega t.G, V)}
    (hs : VB.IsFrame s) : ∃ Φ : TanM x t.G ≃ₗ[R] (Fin n → R), ∀ v b, Φ v b = tanEv t (isTan_tv v) h (s b) := by
  have := t.semi
  have : QuasiSeparated G'.hom := MorphismProperty.of_isPullback h'.1 inferInstance
  let e : Fin n → Γ(omega G', ⊤) := fun b => (omegaBase h').app ⊤ (pullbackSections x (omega t.G) h (s b))
  have he : VB.IsFrame e := by
    have h₁ := ((hs.pullback x).res h).map_iso (omegaBase h')
    have h₂ (b : Fin n) : resM _ h (pullbackSections x (omega t.G) le_rfl (s b)) =
        pullbackSections x (omega t.G) h (s b) := QCoh.res_pullbackSections x _ _ _ _
    simpa only [h₂] using h₁
  have hc := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom
  let Φ : TanM x t.G →ₗ[R] (Fin n → R) :=
    { toFun := fun v b => tanEv t (isTan_tv v) h (s b)
      map_add' := fun v w => funext fun b => by
        obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
        obtain ⟨q, hq⟩ := exists_lieG h' (isTan_tv w)
        have hpq : (p.1 * q.1).left ≫ φ = (tv (v + w)).left :=
          (h'.2 _ p.1 q.1 (tv v) (tv w) hp.symm hq.symm).symm
        rw [Pi.add_apply, tanEv_eq h' p _ hp, tanEv_eq h' q _ hq,
          tanEv_eq h' ⟨_, OmegaGlobal.fst_mul p q⟩ _ hpq, tangent_mul, dualApp_add, LinearMap.add_apply, map_add]
      map_smul' := fun a v => funext fun b => by
        obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
        have ha : (dualScale a).toRingHom = epsScaleR a := by
          ext y <;> simp [dualScale, epsScaleR]
        have hpq : (ptMap (dualScale a) ≫ p.1).left ≫ φ = (tv (a • v)).left := by
          rw [Over.comp_left, Category.assoc, hp]
          exact congrArg (fun r => spMap r ≫ (tv v).left) ha
        rw [Pi.smul_apply, tanEv_eq h' p _ hp, tanEv_eq h' ⟨_, OmegaGlobal.fst_scale a p⟩ _ hpq, tangent_scale]
        simp only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, GlobalTheory.LB.resG_self,
          Iso.inv_hom_id_apply, RingHom.id_apply] }
  refine ⟨LinearEquiv.ofBijective Φ ⟨fun v w hvw => ?_, fun c => ?_⟩, fun _ _ => rfl⟩
  · obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
    obtain ⟨q, hq⟩ := exists_lieG h' (isTan_tv w)
    obtain rfl : p = q := tangent_injective R G' (he.dual_ext le_rfl fun b => by
      rw [resM_self]
      exact hc.1 ((tanEv_eq h' p _ hp h (s b)).symm.trans
        ((congrFun hvw b).trans (tanEv_eq h' q _ hq h (s b)))))
    exact tan_ext (hp.symm.trans hq)
  · obtain ⟨p, hp⟩ := TangentSurj.tangent_surjective R G'
      ((he.dual.basis le_rfl).equivFun.symm fun b => cst R (c b))
    refine ⟨tanOf (isTanAtG_lieG h' p), funext fun b => (tanEv_eq h' p _ rfl h (s b)).trans ?_⟩
    have k := he.dual_basis_repr le_rfl (tangent p) b
    rw [resM_self, hp, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, ← hp] at k
    exact (congrArg _ k.symm).trans (Iso.inv_hom_id_apply _ _)

omit h'

/- English proof (translation)
The claim follows from `exists_equiv_of_isGrpPullback (isGrpPullback_pullback t.G x) h hs`.
-/
theorem exists_tanM_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (n : ℕ)
    (s : Fin n → Γ(omega t.G, V)) (hs : VB.IsFrame s) :
    ∃ Φ : TanM x t.G ≃ₗ[R] (Fin n → R), ∀ v b, Φ v b = tanEv t (isTan_tv v) h (s b) :=
  exists_equiv_of_isGrpPullback (isGrpPullback_pullback t.G x) h hs

end GlobalTheory.LocM.TanPair
