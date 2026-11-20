import Mathlib
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.FewAtTest

open GlobalTheory.CechPic

/- English proof (translation)
Take `⟨M, hM, rfl⟩` from `cls_surj c`. Set `eK : Sp (FractionRing V) ⟶ pullback p (Out.jK V)` to `pullback.lift (Out.jK V ≫ e) (𝟙 _) (by`. Rewrite using `[Category.assoc, he, Category.id_comp]`. Conclude with `Category.comp_id _)`. Establish `heK : eK ≫ pullback.fst p (Out.jK V) = Out.jK V ≫ e` using `pullback.lift_fst _ _ _`.

Take `⟨t, ht⟩` from `(cls_eq_zero_iff (pull_isLB hM (pullback.fst p (Out.jK V) ≫ 𝟙 H))).1 (by`. Rewrite using `[cls_pull hM, pull_comp, pull_id, h₁])`. Take `⟨ρ, hρ⟩` from `(cls_eq_zero_iff (pull_isLB hM (e ≫ 𝟙 H))).1 (by`. Rewrite using `[cls_pull hM, pull_comp, pull_id, h₂])`. Take `⟨u, hu, cu⟩` from `DVR.exists_normalized_to hM _ _ t ht (pullback.snd p (Out.jK V)) eK (pullback.lift_snd _ _ _) _ _ (LB.pullGen M _ _ ρ (Out.jK V)) (DVR.pullGen_isGen _ _ _ _ hρ _) (by`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[← Category.assoc, heK, Category.assoc])`. Take `⟨s, ⟨hs₁, -⟩, -⟩` from `GenExtend.existsUnique_gen_extend V (FractionRing V) H H p e hs hi he eK heK M hM PUnit (fun _ => 𝟙 H) (fun _ => 1) u ρ hu hρ cu`. Use `(cls_eq_zero_iff (pull_isLB hM (𝟙 H))).2 ⟨s, hs₁⟩` as an intermediate fact.

Rewrite `this` using `[cls_pull hM, pull_id]`. Then use the resulting hypothesis.
-/
theorem pic_eq_zero_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {H : Scheme.{0}}
    (p : H ⟶ Sp V) (e : Sp V ⟶ H) (hs : Smooth p) (hi : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (c : Pic H)
    (h₁ : pull (pullback.fst p (Out.jK V)) c = 0) (h₂ : pull e c = 0) : c = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  let eK : Sp (FractionRing V) ⟶ pullback p (Out.jK V) := pullback.lift (Out.jK V ≫ e) (𝟙 _) (by
    rw [Category.assoc, he, Category.id_comp]; exact Category.comp_id _)
  have heK : eK ≫ pullback.fst p (Out.jK V) = Out.jK V ≫ e := pullback.lift_fst _ _ _
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (pull_isLB hM (pullback.fst p (Out.jK V) ≫ 𝟙 H))).1 (by
    rw [cls_pull hM, pull_comp, pull_id, h₁])
  obtain ⟨ρ, hρ⟩ := (cls_eq_zero_iff (pull_isLB hM (e ≫ 𝟙 H))).1 (by
    rw [cls_pull hM, pull_comp, pull_id, h₂])
  obtain ⟨u, hu, cu⟩ := DVR.exists_normalized_to hM _ _ t ht (pullback.snd p (Out.jK V)) eK
    (pullback.lift_snd _ _ _) _ _ (LB.pullGen M _ _ ρ (Out.jK V)) (DVR.pullGen_isGen _ _ _ _ hρ _) (by
      congr 1
      funext k
      rw [← Category.assoc, heK, Category.assoc])
  obtain ⟨s, ⟨hs₁, -⟩, -⟩ := GenExtend.existsUnique_gen_extend V (FractionRing V) H H p e hs hi he eK heK M hM
    PUnit (fun _ => 𝟙 H) (fun _ => 1) u ρ hu hρ cu
  have := (cls_eq_zero_iff (pull_isLB hM (𝟙 H))).2 ⟨s, hs₁⟩
  rwa [cls_pull hM, pull_id] at this

/- English proof (translation)
Use `(cls_eq_iff L.isLB M.isLB).1 (sub_eq_zero.1 (pic_eq_zero_of_generic G.hom (eSec G) hG.smooth (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hG.smooth hG.geomConnected) (Over.w η[G]) _ ?_ ?_))` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `(cls_eq_iff (pull_isLB L.isLB _) (pull_isLB M.isLB _)).2 h`. Establish `a` using `(cls_eq_zero_iff (pull_isLB L.isLB (eSec G))).2 ⟨L.rig, L.rigGen⟩`. Establish `b` using `(cls_eq_zero_iff (pull_isLB M.isLB (eSec G))).2 ⟨M.rig, M.rigGen⟩`.

Rewrite `a` using `[cls_pull L.isLB]`. Rewrite `b` using `[cls_pull M.isLB]`. Conclude with `(map_sub _ _ _).trans (sub_eq_zero.2 (a.trans b.symm))`.
-/
theorem lbIso_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {G : Over (Sp V)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (L M : RigLB G)
    (h : LBIso (L.L.pull (pullback.fst G.hom (Out.jK V))) (M.L.pull (pullback.fst G.hom (Out.jK V)))) :
    LBIso L.L M.L := by
  refine (cls_eq_iff L.isLB M.isLB).1 (sub_eq_zero.1 (pic_eq_zero_of_generic G.hom (eSec G) hG.smooth
    (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hG.smooth hG.geomConnected)
    (Over.w η[G]) _ ?_ ?_))
  · rw [map_sub, sub_eq_zero]
    exact (cls_eq_iff (pull_isLB L.isLB _) (pull_isLB M.isLB _)).2 h
  · have a := (cls_eq_zero_iff (pull_isLB L.isLB (eSec G))).2 ⟨L.rig, L.rigGen⟩
    have b := (cls_eq_zero_iff (pull_isLB M.isLB (eSec G))).2 ⟨M.rig, M.rigGen⟩
    rw [cls_pull L.isLB] at a
    rw [cls_pull M.isLB] at b
    exact (map_sub _ _ _).trans (sub_eq_zero.2 (a.trans b.symm))

/- English proof (translation)
Use `(h.map x.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom` as an intermediate fact. Rewrite `this` using `[map_natCast, map_natCast]`. Conclude with `this.ne_zero`.
-/
theorem natCast_ne_zero_of_isUnit {Z : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ Z) {n : ℕ}
    (h : IsUnit (n : Γ(Z, ⊤))) : (n : K) ≠ 0 := by
  have := (h.map x.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  rw [map_natCast, map_natCast] at this
  exact this.ne_zero

/- English proof (translation)
Establish `key : ∀ x : Sp (kb p), (rPt p ≫ spMap j : Sp (kb p) ⟶ Sp V) x = IsLocalRing.closedPoint V` using `fun x => by`. Establish `hx : x = IsLocalRing.closedPoint (kb p)` using `Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _`. Substitute `hx` using the available equality. Conclude with `(congrArg (PrimeSpectrum.comap j) (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans (IsLocalRing.comap_closedPoint j)`. Use extensionality with `x`.

Conclude with `⟨fun ⟨a, ha⟩ => ha ▸ key a, fun h => ⟨IsLocalRing.closedPoint (kb p), (key _).trans h.symm⟩⟩`.
-/
theorem range_rPt {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsLocalRing V] (j : V →+* OO p) [IsLocalHom j] :
    Set.range (rPt p ≫ spMap j : Sp (kb p) ⟶ Sp V) = {IsLocalRing.closedPoint V} := by
  have key : ∀ x : Sp (kb p), (rPt p ≫ spMap j : Sp (kb p) ⟶ Sp V) x = IsLocalRing.closedPoint V := fun x => by
    have hx : x = IsLocalRing.closedPoint (kb p) := Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _
    subst hx
    exact (congrArg (PrimeSpectrum.comap j) (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans
      (IsLocalRing.comap_closedPoint j)
  ext x
  exact ⟨fun ⟨a, ha⟩ => ha ▸ key a, fun h => ⟨IsLocalRing.closedPoint (kb p), (key _).trans h.symm⟩⟩

end GlobalTheory.FewAtTest

namespace GlobalTheory.ZJ

open GlobalTheory.FewAtTest

/- English proof (translation)
Introduce `hU laws laws₂ C T hA hK hs hS N n hN hn hlt p _ y τ E c`. Take `⟨-, h0, hG⟩` from `(core_basic C).2.2.2.2.2.2.2.2.2.2.2.2 p y τ`. Establish `hL` using `pull_isLB T.L.isLB τ.φ`. Establish `hi` using `PolBaseChange.lbIso_refl hL`. Take `⟨hab, hamp, hkt⟩` from `pol_pull _ _ C.A ((Over.pullback (Out.jK τ.V)).obj τ.H) τ.yK τ.φ T.L.L (T.L.L.pull τ.φ) T.L.isLB hL C.ab τ.φ_cart hi`.

Set `A : Out.PolAV (Sp (FractionRing τ.V))` to `{ A := (Over.pullback (Out.jK τ.V)).obj τ.H isAb := hab g := C.g smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback τ.φ_cart.1 C.dim L := T.L.L.pull τ.φ isLB := hL rigid := PolBaseChange.rigidified_pull τ.φ_cart ⟨T.L.rig, T.L.rigGen⟩ sym := PolBaseCh …`. Use `hab.comm` as an intermediate fact. Establish `hS'` using `SymBaseChange.hypS_baseChange _ _ C.A ((Over.pullback (Out.jK τ.V)).obj τ.H) τ.yK τ.φ T.L.L (T.L.L.pull τ.φ) T.L.isLB hL τ.φ_cart hi hS`. Take `⟨D, U, hgen⟩` from `hU τ.V τ.complete A τ.H hG τ.split hS' (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 ((Over.pullback (Out.jK τ.V)).obj τ.H))))`. Establish `e₁ : LBIso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst τ.H.hom (Out.jK τ.V)))` using `U.ext`.

Rewrite `e₁` using `[hgen]`. Establish `e₂ : LBIso (E.L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) (A.L.pull (𝟙 _))` using `LBIso.trans (pull_isLB E.L.isLB _) hL (pull_isLB hL _) (LBIso.symm ⟨E.w, E.w_gen⟩) (CechPic.iso_of_chart hL (Geo.Tor.chartPullPull _ _ _ rfl)).symm`. Establish `e` using `lbIso_of_generic hG E.L U.LG (LBIso.trans (pull_isLB E.L.isLB _) (pull_isLB hL _) (pull_isLB U.LG.isLB _) e₂ e₁)`. Use `isAlgClosed_kb (p := p)` as an intermediate fact. Use `τ.j_loc` as an intermediate fact.

Conclude with `GlobalTheory.FewZeros.card_torsion_translate_zeros_lt laws laws₂ τ.V τ.complete D A τ.H U E.L.L E.θ E.L.isLB e E.θ_ne (kb p) (rPt p ≫ spMap τ.j) N n (range_rPt τ.j) hN (natCast_ne_zero_of_isUnit (rPt p ≫ y) hn) hlt c`.
-/
theorem theta_few : GlobalTheory.ZH.ThmUSt → Out.Laws → Out.Laws2 → ∀ (C : Core) (T : C.Theta), Out.RelAmple C.A T.L.L → Out.KTriv C.A T.L.L → T.L.IsSymmetric → GlobalTheory.ZH.HypS C.A T.L.L → ∀ N n : ℕ, 4 ≤ N → IsUnit (n : Γ(C.Z, ⊤)) → 6 * (N ^ C.g * C.g.factorial) < n ^ 2 → T.Few n := by
  intro hU laws laws₂ C T hA hK hs hS N n hN hn hlt p _ y τ E c
  obtain ⟨-, h0, hG⟩ := (core_basic C).2.2.2.2.2.2.2.2.2.2.2.2 p y τ
  have hL := pull_isLB T.L.isLB τ.φ
  have hi := PolBaseChange.lbIso_refl hL
  obtain ⟨hab, hamp, hkt⟩ := pol_pull _ _ C.A ((Over.pullback (Out.jK τ.V)).obj τ.H) τ.yK τ.φ T.L.L (T.L.L.pull τ.φ)
    T.L.isLB hL C.ab τ.φ_cart hi
  let A : Out.PolAV (Sp (FractionRing τ.V)) :=
    { A := (Over.pullback (Out.jK τ.V)).obj τ.H
      isAb := hab
      g := C.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback τ.φ_cart.1 C.dim
      L := T.L.L.pull τ.φ
      isLB := hL
      rigid := PolBaseChange.rigidified_pull τ.φ_cart ⟨T.L.rig, T.L.rigGen⟩
      sym := PolBaseChange.sym_pull τ.φ_cart (CechPic.sym_of_isSymmetric T.L hs)
      ample := hamp hA
      ktriv := hkt hK }
  have := hab.comm
  have hS' := SymBaseChange.hypS_baseChange _ _ C.A ((Over.pullback (Out.jK τ.V)).obj τ.H) τ.yK τ.φ T.L.L
    (T.L.L.pull τ.φ) T.L.isLB hL τ.φ_cart hi hS
  obtain ⟨D, U, hgen⟩ := hU τ.V τ.complete A τ.H hG τ.split hS' (Iso.refl _)
    (inferInstanceAs (IsMonHom (𝟙 ((Over.pullback (Out.jK τ.V)).obj τ.H))))
  have e₁ : LBIso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) := U.ext
  rw [hgen] at e₁
  have e₂ : LBIso (E.L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) (A.L.pull (𝟙 _)) :=
    LBIso.trans (pull_isLB E.L.isLB _) hL (pull_isLB hL _) (LBIso.symm ⟨E.w, E.w_gen⟩)
      (CechPic.iso_of_chart hL (Geo.Tor.chartPullPull _ _ _ rfl)).symm
  have e := lbIso_of_generic hG E.L U.LG
    (LBIso.trans (pull_isLB E.L.isLB _) (pull_isLB hL _) (pull_isLB U.LG.isLB _) e₂ e₁)
  have := isAlgClosed_kb (p := p)
  have := τ.j_loc
  exact GlobalTheory.FewZeros.card_torsion_translate_zeros_lt laws laws₂ τ.V τ.complete D A τ.H U E.L.L E.θ E.L.isLB e E.θ_ne (kb p) (rPt p ≫ spMap τ.j) N n
    (range_rPt τ.j) hN (natCast_ne_zero_of_isUnit (rPt p ≫ y) hn) hlt c

end GlobalTheory.ZJ
