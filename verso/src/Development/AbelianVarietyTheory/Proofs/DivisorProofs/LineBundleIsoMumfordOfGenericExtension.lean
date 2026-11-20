import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `R _ _ _ _ _ G _ _ hG L' N PP hL' hN hNL hE`. Establish `hsm : Smooth G.hom` using `hG.smooth`. Establish `hgc : GeometricallyConnected G.hom` using `hG.geomConnected`. Establish `hsm₂ : Smooth (G ⊗ G).hom` using `by show Smooth (pullback.fst G.hom G.hom ≫ G.hom) infer_instance`. Establish `hgc₂ : GeometricallyConnected (G ⊗ G).hom` using `by show GeometricallyConnected (pullback.fst G.hom G.hom ≫ G.hom)`.

Conclude with `GeometricallyConnected.comp _ _`. Establish `hgi₂ : GeometricallyIntegral (G2 G).hom` using `GlobalTheory.geometricallyIntegral_of_smooth _`. Establish `hLam : (abelian₂ G L').IsLB` using `DVR.linComb_isLB _ hL' _ _`. Establish `hPP : PP.IsLB` using `hE.1`. Establish `hpb` using `isGrpPullback_pullback G (jK R)`.

Take `⟨β₂, hsq, hβ⟩` from `GlobalTheory.T.exists_mumfordBundle_pullback_grpPullback _ _ (jK R) G ((Over.pullback (jK R)).obj G) (pullback.fst G.hom (jK R)) hpb`. Establish `h1 : LBIso (abelian₂ G L') ((abelian₂ G L').pull (𝟙 _))` using `LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hLam)`. Establish `h2` using `hβ L' N _ (abelian₂ G L') (𝟙 _) hL' hN hLam hNL h1`. Rewrite `h2` using `[Category.comp_id]`. Establish `h3` using `hE.2 β₂ hsq`.

Establish `hgen : LBIso ((abelian₂ G L').pull β₂) (PP.pull β₂)` using `LBIso.trans (pull_isLB hLam _) (DVR.linComb_isLB _ hN _ _) (pull_isLB hPP _) (LBIso.symm h2) h3`. Set `p1` to `pullback.fst (G2 G).hom (jK R)`. Set `p2` to `pullback.snd (G2 G).hom (jK R)`. Set `T : Over (Spec (CommRingCat.of (FractionRing R)))` to `Over.mk p2`. Establish `wx : (p1 ≫ (fst G G).left) ≫ G.hom = p2 ≫ jK R`.

Rewrite using `[Category.assoc, Over.w (fst G G)]`. Conclude with `pullback.condition`. Establish `wy : (p1 ≫ (snd G G).left) ≫ G.hom = p2 ≫ jK R`. Rewrite using `[Category.assoc, Over.w (snd G G)]`. Conclude with `pullback.condition`.

Set `x : T ⟶ (Over.pullback (jK R)).obj G` to `Over.homMk (hpb.1.lift _ _ wx) (hpb.1.lift_snd _ _ _)`. Set `y : T ⟶ (Over.pullback (jK R)).obj G` to `Over.homMk (hpb.1.lift _ _ wy) (hpb.1.lift_snd _ _ _)`. Set `i : pullback (G2 G).hom (jK R) ⟶ (G2 ((Over.pullback (jK R)).obj G)).left` to `(lift x y).left`. Establish `hi : i ≫ β₂ = p1`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Use `show i ≫ β₂ ≫ (fst G G).left = p1 ≫ (fst G G).left`. Rewrite using `[hsq.1, ← Category.assoc]`. Use `show (lift x y ≫ fst _ _).left ≫ _ = _`. Rewrite using `[lift_fst]`. Conclude with `hpb.1.lift_fst _ _ _`.

Use `show i ≫ β₂ ≫ (snd G G).left = p1 ≫ (snd G G).left`. Rewrite using `[hsq.2, ← Category.assoc]`. Use `show (lift x y ≫ snd _ _).left ≫ _ = _`. Rewrite using `[lift_snd]`. Conclude with `hpb.1.lift_fst _ _ _`.

Establish `hK : LBIso ((abelian₂ G L').pull p1) (PP.pull p1)` using `LBIso.chartPull (chartPullSame (abelian₂ G L') (fun _ => p1) (fun _ => β₂) (fun _ => 1) i (fun _ => hi.symm)) (chartPullSame PP (fun _ => p1) (fun _ => β₂) (fun _ => 1) i (fun _ => hi.symm)) hgen`. Conclude with `GlobalTheory.T.lineBundleIso_of_generic_normal_local_base R (G2 G) (lift η[G] η[G]).left (Over.w (lift η[G] η[G])) (abelian₂ G L') PP hLam hPP hK`.
-/
theorem lbIso_lam_of_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L' : LB G.left) (N : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left), L'.IsLB → N.IsLB → LBIso N (L'.pull (pullback.fst G.hom (jK R))) → ExtLam G N PP → LBIso (abelian₂ G L') PP := by
  intro R _ _ _ _ _ G _ _ hG L' N PP hL' hN hNL hE
  have hsm : Smooth G.hom := hG.smooth
  have hgc : GeometricallyConnected G.hom := hG.geomConnected
  have hsm₂ : Smooth (G ⊗ G).hom := by
    show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have hgc₂ : GeometricallyConnected (G ⊗ G).hom := by
    show GeometricallyConnected (pullback.fst G.hom G.hom ≫ G.hom)
    exact GeometricallyConnected.comp _ _
  have hgi₂ : GeometricallyIntegral (G2 G).hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have hLam : (abelian₂ G L').IsLB := DVR.linComb_isLB _ hL' _ _
  have hPP : PP.IsLB := hE.1

  have hpb := isGrpPullback_pullback G (jK R)
  obtain ⟨β₂, hsq, hβ⟩ := GlobalTheory.T.exists_mumfordBundle_pullback_grpPullback _ _ (jK R) G ((Over.pullback (jK R)).obj G) (pullback.fst G.hom (jK R)) hpb
  have h1 : LBIso (abelian₂ G L') ((abelian₂ G L').pull (𝟙 _)) :=
    LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hLam)
  have h2 := hβ L' N _ (abelian₂ G L') (𝟙 _) hL' hN hLam hNL h1
  rw [Category.comp_id] at h2
  have h3 := hE.2 β₂ hsq
  have hgen : LBIso ((abelian₂ G L').pull β₂) (PP.pull β₂) :=
    LBIso.trans (pull_isLB hLam _) (DVR.linComb_isLB _ hN _ _) (pull_isLB hPP _) (LBIso.symm h2) h3

  let p1 := pullback.fst (G2 G).hom (jK R)
  let p2 := pullback.snd (G2 G).hom (jK R)
  let T : Over (Spec (CommRingCat.of (FractionRing R))) := Over.mk p2
  have wx : (p1 ≫ (fst G G).left) ≫ G.hom = p2 ≫ jK R := by
    rw [Category.assoc, Over.w (fst G G)]; exact pullback.condition
  have wy : (p1 ≫ (snd G G).left) ≫ G.hom = p2 ≫ jK R := by
    rw [Category.assoc, Over.w (snd G G)]; exact pullback.condition
  let x : T ⟶ (Over.pullback (jK R)).obj G := Over.homMk (hpb.1.lift _ _ wx) (hpb.1.lift_snd _ _ _)
  let y : T ⟶ (Over.pullback (jK R)).obj G := Over.homMk (hpb.1.lift _ _ wy) (hpb.1.lift_snd _ _ _)
  let i : pullback (G2 G).hom (jK R) ⟶ (G2 ((Over.pullback (jK R)).obj G)).left := (lift x y).left
  have hi : i ≫ β₂ = p1 := by
    apply pullback.hom_ext
    · show i ≫ β₂ ≫ (fst G G).left = p1 ≫ (fst G G).left
      rw [hsq.1, ← Category.assoc]
      show (lift x y ≫ fst _ _).left ≫ _ = _
      rw [lift_fst]
      exact hpb.1.lift_fst _ _ _
    · show i ≫ β₂ ≫ (snd G G).left = p1 ≫ (snd G G).left
      rw [hsq.2, ← Category.assoc]
      show (lift x y ≫ snd _ _).left ≫ _ = _
      rw [lift_snd]
      exact hpb.1.lift_fst _ _ _
  have hK : LBIso ((abelian₂ G L').pull p1) (PP.pull p1) :=
    LBIso.chartPull (chartPullSame (abelian₂ G L') (fun _ => p1) (fun _ => β₂) (fun _ => 1) i (fun _ => hi.symm))
      (chartPullSame PP (fun _ => p1) (fun _ => β₂) (fun _ => 1) i (fun _ => hi.symm)) hgen
  exact GlobalTheory.T.lineBundleIso_of_generic_normal_local_base R (G2 G) (lift η[G] η[G]).left (Over.w (lift η[G] η[G])) (abelian₂ G L') PP hLam hPP hK

end GlobalTheory.Mum
