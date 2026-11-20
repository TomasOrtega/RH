import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitPeriodFormValuationSumRefinedChart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
open Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.TraitExt

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear in

/- English proof (translation)
Establish `hP : PolBaseChangeSt` using `polBaseChange_holds`. Establish `hU : UnifBaseChangeSt` using `GlobalTheory.UnifPullGuards.unifBaseChange_holds`. Establish `hψ : PsiOnExistsSt` using `psiOnExists`. Establish `sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g` using `(fracMap_sq hg).symm.trans (Category.id_comp _)`. Take `⟨A', gA, pA, dA, mA, tA⟩` from `hP _ _ (spMap (fracMap hg)) A`.

Establish `gpA : IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA` using `⟨pA, fun T x y x₀ y₀ hx hy => by`. Establish `e₁ : x₀ = Out.toBase pA.w x` using `Over.OverMorphism.ext hx`. Establish `e₂ : y₀ = Out.toBase pA.w y` using `Over.OverMorphism.ext hy`. Rewrite using `[e₁, e₂, ← mA]`. Use the proof step `rfl⟩`.

Establish `gpG` using `ThetaBaseChange.grp_generic U.toUnifPre`. Establish `gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap (fracMap hg) ≫ jK R) (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g))` using `((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl`. Take `⟨eA, mE, heA⟩` from `grpPullback_iso gp' (gpA.comp gpG)`. Establish `hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _`. Rewrite using `[← Over.comp_left, Iso.inv_hom_id, Over.id_left]`.

Establish `hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = pullback.fst G.hom (spMap g)` using `Category.id_comp _`. Establish `wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)))`. Use `LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left) (pull_isLB U.LG.isLB _) ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ …` and prove the remaining obligations. Use `LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left) (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_) (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hgi, Category.comp_id]`.

Rewrite using `[hbc, ← heA]`. Simplify using `only [Category.assoc]`. Establish `he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = specOf g ≫ eSec G`. Rewrite using `[hbc]`. Conclude with `(cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm`.

Establish `hr : (rigPullOf (G` using `G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen := LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec ((Over.pullback (specOf g)).obj G)) (fun _ => he) U.LG.rig U.LG.rigGen`. Set `L' : RigLB ((Over.pullback (specOf g)).obj G)` to `⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)), rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _, hr⟩`. Take `⟨Wo, hWo, hψ⟩` from `hψ R I hR D`. Establish `hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo`. Establish `: (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R))`.

Rewrite using `[genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]`. Conclude with `PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)`. Rewrite using `[this]`. Conclude with `hWo`. Establish `mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom` using `by show IsMonHom (𝟙 _); infer_instance`.

Take `⟨D', hD, U', -, hU', -⟩` from `hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G) (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)`. Use `⟨D', hD, A', U', gA, eA.hom.left ≫ gA ≫ U.gen.inv.left, gpA, LBIso.symm tA, ?_, ?_⟩` and prove the remaining obligations. Simplify `heA` using `only [Category.assoc]`. Rewrite using `[hU']`. Simplify using `only [Category.assoc, hgi, Category.comp_id]`.
-/
theorem exists_pull_gen {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I')
    {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    ∃ (D' : DegData R' I') (_ : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
      (U' : Unif I' D' A' ((Over.pullback (spMap g)).obj G)) (gA : A'.A.left ⟶ A.A.left)
      (πK : pullback ((Over.pullback (spMap g)).obj G).hom (jK R') ⟶ pullback G.hom (jK R)),
      IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA ∧ LBIso A'.L (A.L.pull gA) ∧
      πK ≫ pullback.fst G.hom (jK R) =
        pullback.fst ((Over.pullback (spMap g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g) ∧
      U'.gen.hom.left ≫ gA = πK ≫ U.gen.hom.left := by
  have hP : PolBaseChangeSt := polBaseChange_holds
  have hU : UnifBaseChangeSt := GlobalTheory.UnifPullGuards.unifBaseChange_holds
  have hψ : PsiOnExistsSt := psiOnExists
  have sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g := (fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hg)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap (fracMap hg) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) =
      pullback.fst G.hom (spMap g) := Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫
      pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec ((Over.pullback (specOf g)).obj G)) (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) :=
    ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
      rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig,
      pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, hU', -⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  refine ⟨D', hD, A', U', gA, eA.hom.left ≫ gA ≫ U.gen.inv.left, gpA, LBIso.symm tA, ?_, ?_⟩
  · simpa only [Category.assoc] using heA
  · rw [hU']; simp only [Category.assoc, hgi, Category.comp_id]

end GlobalTheory.TraitExt

namespace GlobalTheory.TraitExt

end GlobalTheory.TraitExt
