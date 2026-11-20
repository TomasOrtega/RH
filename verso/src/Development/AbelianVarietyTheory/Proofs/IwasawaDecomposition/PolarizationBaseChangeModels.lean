import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFrames

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFin

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.FlagMod GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)

attribute [local instance] Over.cartesianMonoidalCategory

section Push

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {π : X' ⟶ X} {F : G'.left ⟶ G.left} {S S' : Type} [CommRing S] [CommRing S']

def tanPush (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') : TanM x G' →ₗ[S] TanM (x ≫ π) G where
  toFun v := mkT (pushHom h (overAt x (DualNumber S)) (tv v)) (by
    have e : smT (x ≫ π) 0 (pushHom h (overAt x (DualNumber S)) (tv v)) =
        pushHom h (overAt x (DualNumber S)) (smT x 0 (tv v)) := Over.OverMorphism.ext (Category.assoc _ _ _).symm
    rw [e, tv_mem]
    exact map_one _)
  map_add' u v := tanM_ext (map_mul (pushHom h (overAt x (DualNumber S))) _ _)
  map_smul' a v := tanM_ext (Over.OverMorphism.ext (Category.assoc _ _ _))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tanPush_left (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') (v : TanM x G') :
    (tv (tanPush h x v)).left = (tv v).left ≫ F := rfl

/- English proof (translation)
Establish `inj : Function.Injective (pushHom h (overAt x (DualNumber S)))` using `fun p q hpq => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun V => V.left) hpq) ((Over.w p).trans (Over.w q).symm))`. Use `⟨fun u v e => tanM_ext (inj (congrArg tv e)), fun V => ?_⟩` and prove the remaining obligations. Set `p : overAt x (DualNumber S) ⟶ G'` to `Over.homMk (h.1.lift (tv V).left (overAt x (DualNumber S)).hom (Over.w (tv V))) (h.1.lift_snd _ _ _)`. Establish `hp : pushHom h (overAt x (DualNumber S)) p = tv V` using `Over.OverMorphism.ext (h.1.lift_fst _ _ _)`. Use `⟨mkT p (inj ?_), tanM_ext hp⟩` and prove the remaining obligations.

Establish `e : smT (x ≫ π) 0 (pushHom h (overAt x (DualNumber S)) p) = pushHom h (overAt x (DualNumber S)) (smT x 0 p)` using `Over.OverMorphism.ext (Category.assoc _ _ _).symm`. Rewrite using `[← e, hp, map_one]`. Conclude with `tv_mem V`.
-/
theorem tanPush_bijective (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') : Function.Bijective (tanPush h x) := by
  have inj : Function.Injective (pushHom h (overAt x (DualNumber S))) := fun p q hpq =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun V => V.left) hpq) ((Over.w p).trans (Over.w q).symm))
  refine ⟨fun u v e => tanM_ext (inj (congrArg tv e)), fun V => ?_⟩
  let p : overAt x (DualNumber S) ⟶ G' :=
    Over.homMk (h.1.lift (tv V).left (overAt x (DualNumber S)).hom (Over.w (tv V))) (h.1.lift_snd _ _ _)
  have hp : pushHom h (overAt x (DualNumber S)) p = tv V := Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  refine ⟨mkT p (inj ?_), tanM_ext hp⟩
  have e : smT (x ≫ π) 0 (pushHom h (overAt x (DualNumber S)) p) =
      pushHom h (overAt x (DualNumber S)) (smT x 0 p) := Over.OverMorphism.ext (Category.assoc _ _ _).symm
  rw [← e, hp, map_one]
  exact tv_mem V

def tanEquiv (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') : TanM x G' ≃ₗ[S] TanM (x ≫ π) G :=
  LinearEquiv.ofBijective _ (tanPush_bijective h x)

/- English proof (translation)
The claim follows from `tan_ext_left (Category.assoc _ _ _).symm`.
-/
theorem tanPull_tanEquiv (h : IsGrpPullback G' G π F) (φ : S →+* S') {x : Sp S ⟶ X'} {x' : Sp S' ⟶ X'}
    (e : spMap φ ≫ x = x') (e' : spMap φ ≫ x ≫ π = x' ≫ π) (v : TanM x G') :
    tanPull φ e' (tanEquiv h x v) = tanEquiv h x' (tanPull φ e v) :=
  tan_ext_left (Category.assoc _ _ _).symm

end Push

/- English proof (translation)
Establish `: IsAffineHom ((hU'.fromSpec ≫ π) ≫ s)` using `isAffineHom_of_isAffine _`. Establish `: IsAffineHom (hU'.fromSpec ≫ π)` using `IsAffineHom.of_comp _ s`. Establish `h` using `(hU.preimage (hU'.fromSpec ≫ π)).image_of_isOpenImmersion hU'.fromSpec`. Rewrite `h` using `[Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, hU'.opensRange_fromSpec]`. Then use the resulting hypothesis.
-/
theorem isAffineOpen_inf_preimage {X X' T : Scheme.{0}} [IsAffine T] (s : X ⟶ T) [IsSeparated s] (π : X' ⟶ X)
    {U : X.Opens} {U' : X'.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') : IsAffineOpen (U' ⊓ π ⁻¹ᵁ U) := by
  have : IsAffineHom ((hU'.fromSpec ≫ π) ≫ s) := isAffineHom_of_isAffine _
  have : IsAffineHom (hU'.fromSpec ≫ π) := IsAffineHom.of_comp _ s
  have h := (hU.preimage (hU'.fromSpec ≫ π)).image_of_isOpenImmersion hU'.fromSpec
  rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, hU'.opensRange_fromSpec] at h

/- English proof (translation)
Establish `le : (L.pull π).U J ⊓ (L.pull π).U J' ≤ π ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit))` using `le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => π) J PUnit.unit)) (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => π) J' PUnit.unit))`. Establish `e : (L.pull π).g J J' = res le (pullU π _ (L.g (J PUnit.unit) (J' PUnit.unit)))` using `by show ∏ _k : PUnit, res le (pullU π _ (L.g (J _k) (J' _k))) ^ (1 : ℤ) = _`. Rewrite using `[Fintype.prod_unique, zpow_one]`. Rewrite using `[e, ← ev_appLE z π le h]`. Both sides reduce to the same expression.
-/
theorem ev_pull_g {X X' : Scheme.{0}} {S : Type} [CommRing S] (L : LB X) (π : X' ⟶ X) (z : Sp S ⟶ X')
    (J J' : PUnit → L.ι) (h : ⊤ ≤ z ⁻¹ᵁ ((L.pull π).U J ⊓ (L.pull π).U J'))
    (h' : ⊤ ≤ (z ≫ π) ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit))) :
    ev z _ h ((L.pull π).g J J').val = ev (z ≫ π) _ h' (L.g (J PUnit.unit) (J' PUnit.unit)).val := by
  have le : (L.pull π).U J ⊓ (L.pull π).U J' ≤ π ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => π) J PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => π) J' PUnit.unit))
  have e : (L.pull π).g J J' = res le (pullU π _ (L.g (J PUnit.unit) (J' PUnit.unit))) := by
    show ∏ _k : PUnit, res le (pullU π _ (L.g (J _k) (J' _k))) ^ (1 : ℤ) = _
    rw [Fintype.prod_unique, zpow_one]
  rw [e, ← ev_appLE z π le h]
  rfl

section Det

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l' : Level H}
  {Xo : Moduli D l} {Xo' : Moduli D l'} {c : Coeff l} {c' : Coeff l'} {O O' : Type} [CommRing O] [CommRing O']
  {β : O →+* c.F} {β' : O' →+* c'.F} {Z : Model Xo c β} {Z' : Model Xo' c' β'} {π : Z'.X ⟶ Z.X}
  {F : Z'.t.G.left ⟶ Z.t.G.left} (h : IsGrpPullback Z'.t.G Z.t.G π F) {S : Type} [CommRing S]

/- English proof (translation)
Use `GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj` as an intermediate fact. Conclude with `isAffineOpen_inf_preimage Z.s π M.hU M'.hU`.
-/
theorem isAffineOpen_mix (π : Z'.X ⟶ Z.X) (M' : MChart Z') (M : MChart Z) : IsAffineOpen (M'.U ⊓ π ⁻¹ᵁ M.U) := by
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
  exact isAffineOpen_inf_preimage Z.s π M.hU M'.hU

def mixChg (M' : MChart Z') (M : MChart Z) : Matrix (Fin M'.n) (Fin M.n) Γ(Z'.X, M'.U ⊓ π ⁻¹ᵁ M.U) :=
  ((lieBasis M' (tau (isAffineOpen_mix π M' M)) (tau_le _ inf_le_left)).map (tanEquiv h _)).toMatrix
    (lieBasis M (tau (isAffineOpen_mix π M' M) ≫ π) (le_preimage_map π inf_le_right (tau_le _ le_rfl)))

/- English proof (translation)
Establish `e : spMap (ev x _ hh) ≫ tau (isAffineOpen_mix π M' M) = x` using `spMap_ev x _ hh`. Establish `e' : spMap (ev x _ hh) ≫ tau (isAffineOpen_mix π M' M) ≫ π = x ≫ π` using `by rw [← Category.assoc, e]`. Use extensionality with `i j`. Establish `h1` using `((lieBasis M' (tau (isAffineOpen_mix π M' M)) (tau_le _ inf_le_left)).map (tanEquiv h _)).sum_toMatrix_smul_self (lieBasis M (tau (isAffineOpen_mix π M' M) ≫ π) (le_preimage_map π inf_le_right (tau_le _ le_rfl))) j`. Establish `h2` using `congrArg (tanPull (G := Z.t.G) _ e') h1`.

Rewrite `h2` using `[map_sum, tanPull_lieBasis M _ e' _ h₀]`. Simplify using `only [map_smulₛₗ, Module.Basis.map_apply, tanPull_tanEquiv h _ e e', tanPull_lieBasis M' _ e _ h'] at h2`. Rewrite using `[Module.Basis.toMatrix_apply, ← h2]`. Simplify using `only [← Module.Basis.map_apply]`. Rewrite using `[Module.Basis.repr_sum_self]`.

Both sides reduce to the same expression.
-/
theorem mixChg_map (M' : MChart Z') (M : MChart Z) (x : Sp S ⟶ Z'.X) (h' : ⊤ ≤ x ⁻¹ᵁ M'.U)
    (h₀ : ⊤ ≤ (x ≫ π) ⁻¹ᵁ M.U) (hh : ⊤ ≤ x ⁻¹ᵁ (M'.U ⊓ π ⁻¹ᵁ M.U)) :
    (mixChg h M' M).map (ev x _ hh) = ((lieBasis M' x h').map (tanEquiv h x)).toMatrix (lieBasis M (x ≫ π) h₀) := by
  have e : spMap (ev x _ hh) ≫ tau (isAffineOpen_mix π M' M) = x := spMap_ev x _ hh
  have e' : spMap (ev x _ hh) ≫ tau (isAffineOpen_mix π M' M) ≫ π = x ≫ π := by rw [← Category.assoc, e]
  ext i j
  have h1 := ((lieBasis M' (tau (isAffineOpen_mix π M' M)) (tau_le _ inf_le_left)).map
    (tanEquiv h _)).sum_toMatrix_smul_self
    (lieBasis M (tau (isAffineOpen_mix π M' M) ≫ π) (le_preimage_map π inf_le_right (tau_le _ le_rfl))) j
  have h2 := congrArg (tanPull (G := Z.t.G) _ e') h1
  rw [map_sum, tanPull_lieBasis M _ e' _ h₀] at h2
  simp only [map_smulₛₗ, Module.Basis.map_apply, tanPull_tanEquiv h _ e e', tanPull_lieBasis M' _ e _ h'] at h2
  rw [Module.Basis.toMatrix_apply, ← h2]
  simp only [← Module.Basis.map_apply]
  rw [Module.Basis.repr_sum_self]
  rfl

def mixDet (M' : MChart Z') (M : MChart Z) : Γ(Z'.X, M'.U ⊓ π ⁻¹ᵁ M.U)ˣ :=
  (show IsUnit (rdet (mixChg h M' M)) from isUnit_rdet_toMatrix _ _).unit

/- English proof (translation)
Rewrite using `[← mixChg_map h M' M x h' h₀ hh, ← map_rdet]`. Both sides reduce to the same expression.
-/
theorem ev_mixDet (M' : MChart Z') (M : MChart Z) (x : Sp S ⟶ Z'.X) (h' : ⊤ ≤ x ⁻¹ᵁ M'.U)
    (h₀ : ⊤ ≤ (x ≫ π) ⁻¹ᵁ M.U) (hh : ⊤ ≤ x ⁻¹ᵁ (M'.U ⊓ π ⁻¹ᵁ M.U)) :
    ev x _ hh (mixDet h M' M).val =
      rdet (((lieBasis M' x h').map (tanEquiv h x)).toMatrix (lieBasis M (x ≫ π) h₀)) := by
  rw [← mixChg_map h M' M x h' h₀ hh, ← map_rdet]
  rfl

include h in

/- English proof (translation)
Establish `le : ∀ J : ((detLie Z).pull π).ι, ((detLie Z).pull π).U J ≤ π ⁻¹ᵁ (J PUnit.unit).U` using `fun J => LB.wchart_le (detLie Z) (fun _ : PUnit => π) J PUnit.unit`. Use `⟨⟨fun p => res (inf_le_inf_left _ (le p.2)) (mixDet h p.1 (p.2 PUnit.unit))⟩, fun p q => ?_⟩` and prove the remaining obligations. Use `Eq.trans ?_ (mul_right_comm _ _ _)` and prove the remaining obligations. Use `eq_mul_inv_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))` and prove the remaining obligations. Establish `hp` using `le_preimage_mono inf_le_left hz`.

Establish `hq` using `le_preimage_mono inf_le_right hz`. Establish `hp1 : ⊤ ≤ z ⁻¹ᵁ (p.1 : MChart Z').U` using `le_preimage_mono inf_le_left hp`. Establish `hq1 : ⊤ ≤ z ⁻¹ᵁ (q.1 : MChart Z').U` using `le_preimage_mono inf_le_left hq`. Establish `hp2 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z).pull π).U p.2` using `le_preimage_mono inf_le_right hp`. Establish `hq2 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z).pull π).U q.2` using `le_preimage_mono inf_le_right hq`.

Establish `hp3` using `le_preimage_map π (le p.2) hp2`. Establish `hq3` using `le_preimage_map π (le q.2) hq2`. Establish `hp4` using `le_preimage_mono (inf_le_inf_left _ (le p.2)) hp`. Establish `hq4` using `le_preimage_mono (inf_le_inf_left _ (le q.2)) hq`. Establish `g` using `ev_pull_g (detLie Z) π z p.2 q.2 (le_preimage_inf hp2 hq2) (le_preimage_inf hp3 hq3)`.

Use `(map_mul (ev z _ hz) _ _).trans (Eq.trans ?_ (map_mul (ev z _ hz) _ _).symm)` and prove the remaining obligations. Use `(congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans ((ev_res z _ hp hp4 _).trans (ev_mixDet h _ _ z hp1 hp3 hp4))) ((ev_res z _ hz _ _).trans (g.trans (ev_detChg _ _ _ hp3 hq3 _)))).trans (Eq.trans ?_ (congrArg₂ (· * ·) ((ev_res z _ hz (le_preimage_inf hp1 hq1) _).trans (ev_detChg _ _ …` and prove the remaining obligations. Rewrite using `[rdet_toMatrix_mul, ← rdet_toMatrix_mul _ ((lieBasis q.1 z hq1).map (tanEquiv h z))]`. Use `congr 2`. Use extensionality with `i j`.

Simplify using `[Module.Basis.toMatrix_apply]`.
-/
theorem lbIso_detLie : LBIso ((detLie Z).pull π) (detLie Z') := by
  have le : ∀ J : ((detLie Z).pull π).ι, ((detLie Z).pull π).U J ≤ π ⁻¹ᵁ (J PUnit.unit).U := fun J =>
    LB.wchart_le (detLie Z) (fun _ : PUnit => π) J PUnit.unit
  refine ⟨⟨fun p => res (inf_le_inf_left _ (le p.2)) (mixDet h p.1 (p.2 PUnit.unit))⟩, fun p q => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ (p.1 : MChart Z').U := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ (q.1 : MChart Z').U := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z).pull π).U p.2 := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z).pull π).U q.2 := le_preimage_mono inf_le_right hq
  have hp3 := le_preimage_map π (le p.2) hp2
  have hq3 := le_preimage_map π (le q.2) hq2
  have hp4 := le_preimage_mono (inf_le_inf_left _ (le p.2)) hp
  have hq4 := le_preimage_mono (inf_le_inf_left _ (le q.2)) hq
  have g := ev_pull_g (detLie Z) π z p.2 q.2 (le_preimage_inf hp2 hq2) (le_preimage_inf hp3 hq3)
  refine (map_mul (ev z _ hz) _ _).trans (Eq.trans ?_ (map_mul (ev z _ hz) _ _).symm)
  refine (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans ((ev_res z _ hp hp4 _).trans (ev_mixDet h _ _ z hp1 hp3 hp4)))
    ((ev_res z _ hz _ _).trans (g.trans (ev_detChg _ _ _ hp3 hq3 _)))).trans (Eq.trans ?_
    (congrArg₂ (· * ·) ((ev_res z _ hz (le_preimage_inf hp1 hq1) _).trans (ev_detChg _ _ z hp1 hq1 _))
      ((ev_res z _ hz hq _).trans ((ev_res z _ hq hq4 _).trans (ev_mixDet h _ _ z hq1 hq3 hq4)))).symm)
  rw [rdet_toMatrix_mul, ← rdet_toMatrix_mul _ ((lieBasis q.1 z hq1).map (tanEquiv h z))]
  congr 2
  ext i j
  simp [Module.Basis.toMatrix_apply]

end Det

/- English proof (translation)
Use `isLB_of_ev _ (eq_top_iff.2 fun x _ => ?_) fun i j k _ _ z => ev_detChg_mul i j k z` and prove the remaining obligations. Take `⟨i, hi⟩` from `Opens.mem_iSup.1 (h.cover.ge (Set.mem_univ x))`. Conclude with `Opens.mem_iSup.2 ⟨i.1 PUnit.unit, LB.wchart_le _ _ _ PUnit.unit hi.1⟩`.
-/
theorem isLB_detLie_of_polOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {m : ℕ}
    {BD : EffCartierData Z.X} (h : (polOf Z m BD).IsLB) : (detLie Z).IsLB := by
  refine isLB_of_ev _ (eq_top_iff.2 fun x _ => ?_) fun i j k _ _ z => ev_detChg_mul i j k z
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (h.cover.ge (Set.mem_univ x))
  exact Opens.mem_iSup.2 ⟨i.1 PUnit.unit, LB.wchart_le _ _ _ PUnit.unit hi.1⟩

/- English proof (translation)
Take `⟨n, hn, s, hy, hs⟩` from `h.exists_affine y`. Establish `e : LBIso (lbPow A n) (LB.LinComb A (K` using `Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ))) := CechPic.iso_of_chart (LB.isLB_linComb h.isLB _ _) (AmpUniq.chartPullPowSingle A n)`. Take `⟨t, ht⟩` from `exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_linComb h.isLB _ _) (isLB_lbPow h.isLB n) e.symm s`. Conclude with `⟨n, t, hn, ht ▸ hy, ht ▸ hs⟩`.
-/
theorem exists_H0_of_isAmpleLB {X : Scheme.{0}} {A : LB X} (h : GlobalTheory.IsAmpleLB A) (y : X) :
    ∃ (d : ℕ) (s : Out.H0 A d), 1 ≤ d ∧ y ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s) := by
  obtain ⟨n, hn, s, hy, hs⟩ := h.exists_affine y
  have e : LBIso (lbPow A n) (LB.LinComb A (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ))) :=
    CechPic.iso_of_chart (LB.isLB_linComb h.isLB _ _) (AmpUniq.chartPullPowSingle A n)
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_linComb h.isLB _ _) (isLB_lbPow h.isLB n) e.symm s
  exact ⟨n, t, hn, ht ▸ hy, ht ▸ hs⟩

/- English proof (translation)
Introduce `E _ _ _ H D l l' Xo Xo' c c' O O' _ _ β β' Z Z' BD BD' m b σ π hπ mu hA hA' hI`. Establish `hL` using `isLB_detLie_of_polOf hA.isLB`. Establish `hL'` using `isLB_detLie_of_polOf hA'.isLB`. Establish `e₁ : CechPic.pull π (CechPic.cls _ hL) = CechPic.cls _ hL'` using `(CechPic.cls_eq_iff (pull_isLB hL π) hL').2 (lbIso_detLie mu.cart)`. Establish `hk : BD.KeepsRegular π` using `(BD.keepsRegular_iff_effCartier π).2 (hI ▸ BD'.effCartier_idealSheaf)`.

Establish `e₂ : CechPic.pull π (CechPic.cls _ BD.isLB_lb) = CechPic.cls _ BD'.isLB_lb` using `((CechPic.cls_eq_iff (BD.pull π hk).isLB_lb (pull_isLB BD.isLB_lb π)).2 (BD.lbIso_pull π hk)).symm.trans ((CechPic.cls_eq_iff _ _).2 (EffCartierData.lbIso_of_idealSheaf_eq _ _ ((BD.idealSheaf_pull π hk).trans hI.symm)))`. Establish `cl : ∀ {X : Scheme.{0}} {L B : LB X} (hL : L.IsLB) (hB : B.IsLB) (h : (CechPic.tens (lbPow (CechPic.dual L) m) (CechPic.dual B)).IsLB), CechPic.cls _ h = m • -CechPic.cls L hL + -CechPic.cls B hB` using `fun hL hB h => by`. Rewrite using `[CechPic.cls_tens (isLB_lbPow (CechPic.isLB_dual hL) m) (CechPic.isLB_dual hB), CechPic.cls_lbPow (CechPic.isLB_dual hL), CechPic.cls_dual hL, CechPic.cls_dual hB]`. Establish `e : CechPic.pull π (CechPic.cls _ hA.isLB) = CechPic.cls _ hA'.isLB` using `(congrArg _ (cl hL BD.isLB_lb hA.isLB)).trans (Eq.trans (by rw [map_add, map_nsmul, map_neg, map_neg, e₁, e₂]) (cl hL' BD'.isLB_lb hA'.isLB).symm)`. Use `GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj` as an intermediate fact.

Use `GlobalTheory.ThetaDescent.isProper_of_isProjOver Z'.proj` as an intermediate fact. Set `f` to `pullback.lift π Z'.s hπ`. Set `s₁` to `pullback.snd Z.s (spMap b)`. Establish `hf : f ≫ s₁ = 𝟙 _ ≫ Z'.s` using `(pullback.lift_snd _ _ _).trans (Category.id_comp _).symm`. Set `ν : Z'.X ⟶ pullback s₁ Z'.s` to `pullback.lift f (𝟙 _) hf`.

Establish `h₁ : ν ≫ pullback.fst s₁ Z'.s = f` using `pullback.lift_fst _ _ _`. Establish `h₂ : ν ≫ pullback.snd s₁ Z'.s = 𝟙 _` using `pullback.lift_snd _ _ _`. Establish `: IsClosedImmersion (ν ≫ pullback.snd s₁ Z'.s)` using `h₂ ▸ inferInstance`. Establish `: IsClosedImmersion ν` using `IsClosedImmersion.of_comp ν (pullback.snd s₁ Z'.s)`. Establish `hB` using `pull_isLB hA.isLB (pullback.fst Z.s (spMap b))`.

Establish `key` using `AmpUniq.isFinite_fst s₁ Z'.s ν hB hA'.isLB (exists_H0_of_isAmpleLB hA') (by`. Use `(CechPic.cls_eq_iff (pull_isLB hB _) (pull_isLB hA'.isLB _)).1 ?_` and prove the remaining obligations. Rewrite using `[CechPic.cls_pull hB, CechPic.cls_pull hA.isLB, CechPic.cls_pull hA'.isLB, ← CechPic.pull_comp, h₁, h₂, CechPic.pull_id, pullback.lift_fst, e])`. Rewrite `key` using `[h₁]`. Then use the resulting hypothesis.
-/
theorem isFinite_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F)
    (β' : O' →+* c'.F) (Z : Model Xo c β) (Z' : Model Xo' c' β') (BD : EffCartierData Z.X) (BD' : EffCartierData Z'.X)
    (m : ℕ) (b : O →+* O') (σ : 𝓞 E ≃+* 𝓞 E) (π : Z'.X ⟶ Z.X) (hπ : π ≫ Z.s = Z'.s ≫ spMap b)
    (mu : TwMap σ Z'.t Z.t π), GlobalTheory.IsAmpleLB (polOf Z m BD) → GlobalTheory.IsAmpleLB (polOf Z' m BD') →
    BD'.idealSheaf = BD.idealSheaf.comap π → IsFinite (pullback.lift π Z'.s hπ) := by
  intro E _ _ _ H D l l' Xo Xo' c c' O O' _ _ β β' Z Z' BD BD' m b σ π hπ mu hA hA' hI
  have hL := isLB_detLie_of_polOf hA.isLB
  have hL' := isLB_detLie_of_polOf hA'.isLB
  have e₁ : CechPic.pull π (CechPic.cls _ hL) = CechPic.cls _ hL' :=
    (CechPic.cls_eq_iff (pull_isLB hL π) hL').2 (lbIso_detLie mu.cart)
  have hk : BD.KeepsRegular π := (BD.keepsRegular_iff_effCartier π).2 (hI ▸ BD'.effCartier_idealSheaf)
  have e₂ : CechPic.pull π (CechPic.cls _ BD.isLB_lb) = CechPic.cls _ BD'.isLB_lb :=
    ((CechPic.cls_eq_iff (BD.pull π hk).isLB_lb (pull_isLB BD.isLB_lb π)).2 (BD.lbIso_pull π hk)).symm.trans
      ((CechPic.cls_eq_iff _ _).2 (EffCartierData.lbIso_of_idealSheaf_eq _ _
        ((BD.idealSheaf_pull π hk).trans hI.symm)))
  have cl : ∀ {X : Scheme.{0}} {L B : LB X} (hL : L.IsLB) (hB : B.IsLB)
      (h : (CechPic.tens (lbPow (CechPic.dual L) m) (CechPic.dual B)).IsLB),
      CechPic.cls _ h = m • -CechPic.cls L hL + -CechPic.cls B hB := fun hL hB h => by
    rw [CechPic.cls_tens (isLB_lbPow (CechPic.isLB_dual hL) m) (CechPic.isLB_dual hB),
      CechPic.cls_lbPow (CechPic.isLB_dual hL), CechPic.cls_dual hL, CechPic.cls_dual hB]
  have e : CechPic.pull π (CechPic.cls _ hA.isLB) = CechPic.cls _ hA'.isLB :=
    (congrArg _ (cl hL BD.isLB_lb hA.isLB)).trans (Eq.trans
      (by rw [map_add, map_nsmul, map_neg, map_neg, e₁, e₂]) (cl hL' BD'.isLB_lb hA'.isLB).symm)
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z'.proj
  let f := pullback.lift π Z'.s hπ
  let s₁ := pullback.snd Z.s (spMap b)
  have hf : f ≫ s₁ = 𝟙 _ ≫ Z'.s := (pullback.lift_snd _ _ _).trans (Category.id_comp _).symm
  let ν : Z'.X ⟶ pullback s₁ Z'.s := pullback.lift f (𝟙 _) hf
  have h₁ : ν ≫ pullback.fst s₁ Z'.s = f := pullback.lift_fst _ _ _
  have h₂ : ν ≫ pullback.snd s₁ Z'.s = 𝟙 _ := pullback.lift_snd _ _ _
  have : IsClosedImmersion (ν ≫ pullback.snd s₁ Z'.s) := h₂ ▸ inferInstance
  have : IsClosedImmersion ν := IsClosedImmersion.of_comp ν (pullback.snd s₁ Z'.s)
  have hB := pull_isLB hA.isLB (pullback.fst Z.s (spMap b))
  have key := AmpUniq.isFinite_fst s₁ Z'.s ν hB hA'.isLB (exists_H0_of_isAmpleLB hA') (by
    refine (CechPic.cls_eq_iff (pull_isLB hB _) (pull_isLB hA'.isLB _)).1 ?_
    rw [CechPic.cls_pull hB, CechPic.cls_pull hA.isLB, CechPic.cls_pull hA'.isLB, ← CechPic.pull_comp, h₁, h₂,
      CechPic.pull_id, pullback.lift_fst, e])
  rwa [h₁] at key

end GlobalTheory.PolFin
