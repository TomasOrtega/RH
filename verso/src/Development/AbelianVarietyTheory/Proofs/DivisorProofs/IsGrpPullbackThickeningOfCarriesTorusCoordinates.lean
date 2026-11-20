import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FormalModel

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel GlobalTheory.ConstLin

section Thru

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {D : DegPre R}
  {D' : DegPre R'} {F : D'.P.A.left ⟶ D.P.A.left} {w : LB.Iso D'.P.L (D.P.L.pull F)} {ε : D'.X → D.X}

/- English proof (translation)
Establish `hb : k ≫ g.b = g₀.b` using `Over.OverMorphism.ext hk.1.symm`. Use `forall_congr' fun y => and_congr (forall_congr' fun j => ?_) (forall_congr' fun Z => forall_congr' fun r => forall_congr' fun z => forall_congr' fun J => forall_congr' fun J' => forall_congr' fun hJ => ?_)` and prove the remaining obligations. Rewrite using `[Category.assoc, ConstTanRed.comp_gtφT D k g.b g₀.b hb]`. Rewrite using `[(val_corr hJ (hk.2 (ε y)) (r ≫ h)).trans (val_pull hJ _ _ _), Category.assoc]`.
-/
theorem thru_pull_iff {T T₀ : Over (Sp R)} {T' : Over (Sp R')} (k : T₀ ⟶ T) {g : GtPt D T} {g₀ : GtPt D T₀}
    (hk : GtPt.IsPull k.left g g₀) (h : T'.left ⟶ T₀.left) (ξ : GtPt D' T') :
    Thru w ε h g₀ ξ ↔ Thru w ε (h ≫ k.left) g ξ := by
  have hb : k ≫ g.b = g₀.b := Over.OverMorphism.ext hk.1.symm
  refine forall_congr' fun y => and_congr (forall_congr' fun j => ?_) (forall_congr' fun Z => forall_congr' fun r =>
    forall_congr' fun z => forall_congr' fun J => forall_congr' fun J' => forall_congr' fun hJ => ?_)
  · rw [Category.assoc, ConstTanRed.comp_gtφT D k g.b g₀.b hb]
  · rw [(val_corr hJ (hk.2 (ε y)) (r ≫ h)).trans (val_pull hJ _ _ _), Category.assoc]

/- English proof (translation)
Use `hom_ext hΦ (((h 0).1 2).symm.trans ((h' 0).1 2)) fun χ z J hJ => ?_` and prove the remaining obligations. Take `⟨χ, rfl⟩` from `hε χ`. Take `⟨J', hJ'⟩` from `TorusCoord.exists_good' D'.P.isLB z`. Establish `a` using `((h χ).2 _ (𝟙 _) z J J' hJ hJ').trans ((h' χ).2 _ (𝟙 _) z J J' hJ hJ').symm`. Rewrite `a` using `[Category.id_comp, Category.id_comp]`. Then use the resulting hypothesis.
-/
theorem eq_of_thru {Y : Over (Sp R)} [GrpObj Y] {Φ : ∀ T, (T ⟶ Y) ≃ GtPt D T} (hΦ : Represents Φ)
    (hε : Function.Surjective ε) {T' : Over (Sp R')} {r r' : T'.left ⟶ Y.left} {ξ : GtPt D' T'}
    (h : Thru w ε r (Φ Y (𝟙 Y)) ξ) (h' : Thru w ε r' (Φ Y (𝟙 Y)) ξ) : r = r' := by
  refine hom_ext hΦ (((h 0).1 2).symm.trans ((h' 0).1 2)) fun χ z J hJ => ?_
  obtain ⟨χ, rfl⟩ := hε χ
  obtain ⟨J', hJ'⟩ := TorusCoord.exists_good' D'.P.isLB z
  have a := ((h χ).2 _ (𝟙 _) z J J' hJ hJ').trans ((h' χ).2 _ (𝟙 _) z J J' hJ hJ').symm
  rwa [Category.id_comp, Category.id_comp] at a

end Thru

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R}
  {I : Ideal R'} {E : DegData R' I} {hE : IsPullDeg ρ D E.toPre} {A' : PolAV (Sp (FractionRing R'))}
  {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] {Y : Over (Sp R)}

/- English proof (translation)
Establish `hx` using `TorusCoord.isPointOf_toGtPt c x`. Introduce `y`. Use `⟨fun k => ?_, fun Z r z J J' hJ hJ' => ?_⟩` and prove the remaining obligations. Rewrite using `[TorusCoord.gtφT_eq, TorusCoord.gtφT_eq]`. Use `TorusCoordPull.Oφ_pull hE g.b (TorusCoord.toGtPt c x).b (x.left ≫ φ) ?_ y k` and prove the remaining obligations.

Rewrite using `[hx.1, Category.assoc, h.1, Category.assoc]`. Establish `o` using `(TorusCoord.comp_eq_of_left (TorusCoord.toGtPt c x).b c.pG r (r ≫ x.left) (by rw [hx.1, Category.assoc])).1 y`. Use `(congrArg (fun q => val (g.s (hE.xe y)) q z J) (Category.assoc _ _ _).symm).trans ((h.2 y Z (r ≫ x.left) z J J' hJ hJ').trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (fun q => TorusCoordPull.om hE.w z J J' q ^ Oinvε k) (o k).symm) ?_))` and prove the remaining obligations. Conclude with `((val_corr hJ' (hx.2 y) r).trans (val_pull hJ' _ _ _)).symm`.
-/
theorem Carries.thru {e : ℕ} {c : GtCoord I E.toPre e G'} {g : GtPt D Y} {φ} (h : Carries hE c g φ)
    {T : Over (Sp (R' ⧸ I ^ (e + 1)))} (x : T ⟶ thickObj R' I e G') :
    Thru hE.w hE.xe (T' := (Over.map (thick R' I e)).obj T) (x.left ≫ φ) g (TorusCoord.toGtPt c x) := by
  have hx := TorusCoord.isPointOf_toGtPt c x
  intro y
  refine ⟨fun k => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · rw [TorusCoord.gtφT_eq, TorusCoord.gtφT_eq]
    refine TorusCoordPull.Oφ_pull hE g.b (TorusCoord.toGtPt c x).b (x.left ≫ φ) ?_ y k
    rw [hx.1, Category.assoc, h.1, Category.assoc]
  · have o := (TorusCoord.comp_eq_of_left (TorusCoord.toGtPt c x).b c.pG r (r ≫ x.left)
      (by rw [hx.1, Category.assoc])).1 y
    refine (congrArg (fun q => val (g.s (hE.xe y)) q z J) (Category.assoc _ _ _).symm).trans
      ((h.2 y Z (r ≫ x.left) z J J' hJ hJ').trans (congrArg₂ (· * ·)
        (Finset.prod_congr rfl fun k _ => congrArg (fun q => TorusCoordPull.om hE.w z J J' q ^ Oinvε k) (o k).symm) ?_))
    exact ((val_corr hJ' (hx.2 y) r).trans (val_pull hJ' _ _ _)).symm

/- English proof (translation)
Use `⟨h.isPullback hΦ U, fun T x y x₀ y₀ hx hy => ?_⟩` and prove the remaining obligations. Set `Tw` to `(Over.map (thick R' I e)).obj T`. Set `T₀ : Over (Sp R)` to `Over.mk (T.hom ≫ thick R' I e ≫ spMap ρ)`. Set `i : Tw.left ⟶ T₀.left` to `𝟙 T.left`. Establish `hi : i ≫ T₀.hom = Tw.hom ≫ spMap ρ` using `(Category.id_comp _).trans (Category.assoc _ _ _).symm`.

Establish `pl : ∀ k : T₀ ⟶ Y, GtPt.IsPull k.left (Φ Y (𝟙 Y)) (Φ T₀ k)` using `fun k => by`. Use `hΦ.1 _ _ k (𝟙 Y)` as an intermediate fact. Rewrite `this` using `[Category.comp_id]`. Then use the resulting hypothesis. Establish `key : ∀ (x : T ⟶ thickObj R' I e G') (x₀ : T₀ ⟶ Y), x₀.left = x.left ≫ φ → Thru hE.w hE.xe i (Φ T₀ x₀) (TorusCoord.toGtPt (U.gt e) x)` using `fun x x₀ hx => by`. Use `(thru_pull_iff x₀ (pl x₀) i _).2 ?_` and prove the remaining obligations.

Establish `e₁ : i ≫ x₀.left = x.left ≫ φ` using `(Category.id_comp _).trans hx`. Rewrite using `[e₁]`. Conclude with `h.thru x`. Take `⟨ξ, hξ⟩` from `ConstPoint.exists_gtPt_through globalFns_holds (pull_grp hE) hE.w_gen hE.xe.toAddMonoidHom hE.c_pr (T := T₀) (T' := Tw) i hi (Φ T₀ (x₀ * y₀))`. Establish `hξ' : Thru hE.w hE.xe i (Φ T₀ (x₀ * y₀)) ξ` using `hξ`.

Establish `ad` using `Thru.isAdd (pull_grp hE) globalFns_holds hE.w_gen hi (key x x₀ hx) (key y y₀ hy) hξ' (hΦ.2 T₀ x₀ y₀)`. Take `rfl : ξ = TorusCoord.toGtPt (U.gt e) (x * y)` from `isAdd_unique ad (TorusCoord.isAdd_pointsEquiv (U.gt e) globalFns_holds x y)`. Conclude with `(Category.id_comp _).symm.trans (eq_of_thru hΦ hE.xe.surjective ((thru_pull_iff _ (pl _) i _).1 hξ') (h.thru (x * y)))`.
-/
theorem Carries.isGrpPullback' [GrpObj Y] {Φ : ∀ T, (T ⟶ Y) ≃ GtPt D T} (hΦ : Represents Φ) (U : UnifPre I E A' G')
    {e : ℕ} {φ} (h : Carries hE (U.gt e) (Φ Y (𝟙 Y)) φ) :
    IsGrpPullback (thickObj R' I e G') Y (thick R' I e ≫ spMap ρ) φ := by
  refine ⟨h.isPullback hΦ U, fun T x y x₀ y₀ hx hy => ?_⟩
  let Tw := (Over.map (thick R' I e)).obj T
  let T₀ : Over (Sp R) := Over.mk (T.hom ≫ thick R' I e ≫ spMap ρ)
  let i : Tw.left ⟶ T₀.left := 𝟙 T.left
  have hi : i ≫ T₀.hom = Tw.hom ≫ spMap ρ := (Category.id_comp _).trans (Category.assoc _ _ _).symm
  have pl : ∀ k : T₀ ⟶ Y, GtPt.IsPull k.left (Φ Y (𝟙 Y)) (Φ T₀ k) := fun k => by
    have := hΦ.1 _ _ k (𝟙 Y)
    rwa [Category.comp_id] at this
  have key : ∀ (x : T ⟶ thickObj R' I e G') (x₀ : T₀ ⟶ Y), x₀.left = x.left ≫ φ →
      Thru hE.w hE.xe i (Φ T₀ x₀) (TorusCoord.toGtPt (U.gt e) x) := fun x x₀ hx => by
    refine (thru_pull_iff x₀ (pl x₀) i _).2 ?_
    have e₁ : i ≫ x₀.left = x.left ≫ φ := (Category.id_comp _).trans hx
    rw [e₁]
    exact h.thru x
  obtain ⟨ξ, hξ⟩ := ConstPoint.exists_gtPt_through globalFns_holds (pull_grp hE) hE.w_gen hE.xe.toAddMonoidHom hE.c_pr
    (T := T₀) (T' := Tw) i hi (Φ T₀ (x₀ * y₀))
  have hξ' : Thru hE.w hE.xe i (Φ T₀ (x₀ * y₀)) ξ := hξ
  have ad := Thru.isAdd (pull_grp hE) globalFns_holds hE.w_gen hi (key x x₀ hx) (key y y₀ hy) hξ' (hΦ.2 T₀ x₀ y₀)
  obtain rfl : ξ = TorusCoord.toGtPt (U.gt e) (x * y) :=
    isAdd_unique ad (TorusCoord.isAdd_pointsEquiv (U.gt e) globalFns_holds x y)
  exact (Category.id_comp _).symm.trans
    (eq_of_thru hΦ hE.xe.surjective ((thru_pull_iff _ (pl _) i _).1 hξ') (h.thru (x * y)))

/- English proof (translation)
Introduce `_ _ _ _ _ U Y _ _ h` and use `h.isGrpPullback' Y.rep U`.
-/
theorem isGrpPullback_of_carries : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → IsGrpPullback (thickObj R' I e G') Y.H (thick R' I e ≫ spMap ρ) φ :=
  fun _ _ _ _ _ U Y _ _ h => h.isGrpPullback' Y.rep U

end GlobalTheory.FormalModel
