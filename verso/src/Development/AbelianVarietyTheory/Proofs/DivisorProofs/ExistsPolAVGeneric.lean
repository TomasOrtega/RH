import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNormalisedPolarisation
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RosatiAdjIffLamEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.GenPol

/- English proof (translation)
Introduce `R _ _ _ hB D A G _ _ hG U O _ _ _ o oA oG hlin w hw hpsi P hP`. Establish `laws : Out.Laws` using `GlobalTheory.lawsAndExpansions.1.1`. Establish `: IsCommMonObj A.A` using `A.isAb.comm`. Establish `hwA : IsMonHom (oA.act w)` using `oA.hom w`. Establish `hwA' : IsMonHom (oA.act (star w))` using `oA.hom (star w)`.

Establish `hs : oA.act w * oA.act (star w) = 𝟙 A.A`. Rewrite using `[Hom.mul_def]`. Express the relevant statement in the definitionally equal form `padd A.A (oA.act w) (oA.act (star w)) = 𝟙 A.A`. Rewrite using `[← oA.map_add, hw, oA.map_one]`. Establish `ha` using `(GlobalTheory.RosLam.rosatiAdj_iff_lamEq laws.globalFns _ A _ _ hwA hwA').1 (oA.rosati w)`.

Take `⟨L', h1, h2, h3, h4, h5, h6, h7⟩` from `GlobalTheory.CM.exists_normalised_polarisation laws (FractionRing R) A _ _ hwA hwA' hs ha`. Set `A' : PolAV (Sp (FractionRing R))` to `{ A := A.A, isAb := A.isAb, g := A.g, smoothDim := A.smoothDim, L := L', isLB := h1, rigid := h2, sym := h3, ample := h4, ktriv := h5 }`. Use `⟨A', U.gen, U.gen_hom, ?_⟩` and prove the remaining obligations. Use `haveI := U.gen_hom`. Establish `hLG` using `U.LG.isLB`.

Establish `hAL` using `A.isLB`. Set `φ` to `pullback.fst G.hom (jK R)`. Set `GK` to `(Over.pullback (jK R)).obj G`. Set `wGK` to `(Over.pullback (jK R)).map (oG.act w)`. Establish `lbc : ∀ {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ B)) {L : LB B.left}, L.IsLB → (cubeLB B x L).IsLB` using `fun x L hL => DVR.linComb_isLB _ hL _ _`.

Establish `s1 : LBIso L' (cubeLB A.A ![𝟙 A.A, oA.act w] A.L)`. Establish `e` using `GlobalTheory.LamCalc.lbIso_of_lamEq h6 (𝟙 A.A) (oA.act w)`. Simplify using `only [Category.comp_id] at e`. Conclude with `LBIso.trans h1 (lbc _ h1) (lbc _ hAL) h7 e`. Establish `s2` using `GlobalTheory.RigidBundleGlue.LBIso.pull s1 U.gen.hom.left`.

Establish `hext : LBIso (U.LG.L.pull φ) (A.L.pull U.gen.hom.left)`. Take `⟨v, hv⟩` from `U.ext`. Conclude with `LBIso.symm ⟨v, hv⟩`. Establish `hgp` using `isGrpPullback_of_iso U.gen`. Establish `s3` using `GlobalTheory.ShapePull.iso_cubeLB_pull hgp (pushPt hgp.1.w (𝟙 GK)) hext (a' := 𝟙 GK) (b' := wGK) (a := 𝟙 A.A) (b := oA.act w) (Category.comp_id _).symm (by`.

Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Establish `e` using `congrArg (fun q => q.left) (hlin.ext w)`. Simplify using `only [Over.comp_left] at e`. Simplify using `only [pushPt, Over.homMk_left, Over.comp_left, Over.id_left, Category.id_comp]`. Conclude with `e)`.

Establish `hpb` using `isGrpPullback_pullback G (jK R)`. Establish `s4` using `GlobalTheory.ShapePull.iso_cubeLB_pull hpb (pushPt hpb.1.w (𝟙 GK)) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hLG φ)) (a' := 𝟙 GK) (b' := wGK) (a := 𝟙 G) (b := oG.act w) (Category.comp_id _).symm (by`. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Use `show wGK.left ≫ φ = (𝟙 GK.left ≫ φ) ≫ (oG.act w).left`. Rewrite using `[Category.id_comp]`.

Simplify using `only [wGK, φ, Over.pullback_map_left]`. Conclude with `pullback.lift_fst _ _ _)`. Establish `s5` using `GlobalTheory.RigidBundleGlue.LBIso.pull hP φ`. Establish `e3 : (pushPt hgp.1.w (𝟙 GK)).left = U.gen.hom.left` using `by simp [pushPt]`. Establish `e4 : (pushPt hpb.1.w (𝟙 GK)).left = φ` using `Category.id_comp _`.

Rewrite `s3` using `[e3]`. Rewrite `s4` using `[e4]`. Establish `i1` using `pull_isLB h1 U.gen.hom.left`. Establish `i2` using `pull_isLB (lbc ![𝟙 A.A, oA.act w] hAL) U.gen.hom.left`. Establish `i3` using `lbc ![𝟙 GK, wGK] (pull_isLB hLG φ)`.

Establish `i4` using `pull_isLB (lbc ![𝟙 G, oG.act w] hLG) φ`. Establish `i5` using `pull_isLB P.L.isLB φ`. Conclude with `LBIso.trans i1 i2 i5 s2 (LBIso.trans i2 i3 i5 s3.symm (LBIso.trans i3 i4 i5 s4 s5.symm))`.
-/
theorem exists_polAV_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → TraceFormTwistIso D.toPre o w → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → ∃ (A' : PolAV (Sp (FractionRing R))) (gen' : (Over.pullback (jK R)).obj G ≅ A'.A), IsMonHom gen'.hom ∧ LBIso (A'.L.pull gen'.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ hB D A G _ _ hG U O _ _ _ o oA oG hlin w hw hpsi P hP
  have laws : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  have : IsCommMonObj A.A := A.isAb.comm
  have hwA : IsMonHom (oA.act w) := oA.hom w
  have hwA' : IsMonHom (oA.act (star w)) := oA.hom (star w)
  have hs : oA.act w * oA.act (star w) = 𝟙 A.A := by
    rw [Hom.mul_def]
    change padd A.A (oA.act w) (oA.act (star w)) = 𝟙 A.A
    rw [← oA.map_add, hw, oA.map_one]
  have ha := (GlobalTheory.RosLam.rosatiAdj_iff_lamEq laws.globalFns _ A _ _ hwA hwA').1 (oA.rosati w)
  obtain ⟨L', h1, h2, h3, h4, h5, h6, h7⟩ :=
    GlobalTheory.CM.exists_normalised_polarisation laws (FractionRing R) A _ _ hwA hwA' hs ha
  let A' : PolAV (Sp (FractionRing R)) :=
    { A := A.A, isAb := A.isAb, g := A.g, smoothDim := A.smoothDim, L := L', isLB := h1, rigid := h2, sym := h3,
      ample := h4, ktriv := h5 }
  refine ⟨A', U.gen, U.gen_hom, ?_⟩
  haveI := U.gen_hom
  have hLG := U.LG.isLB
  have hAL := A.isLB
  let φ := pullback.fst G.hom (jK R)
  let GK := (Over.pullback (jK R)).obj G
  let wGK := (Over.pullback (jK R)).map (oG.act w)
  have lbc : ∀ {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ B))
      {L : LB B.left}, L.IsLB → (cubeLB B x L).IsLB := fun x L hL => DVR.linComb_isLB _ hL _ _
  have s1 : LBIso L' (cubeLB A.A ![𝟙 A.A, oA.act w] A.L) := by
    have e := GlobalTheory.LamCalc.lbIso_of_lamEq h6 (𝟙 A.A) (oA.act w)
    simp only [Category.comp_id] at e
    exact LBIso.trans h1 (lbc _ h1) (lbc _ hAL) h7 e
  have s2 := GlobalTheory.RigidBundleGlue.LBIso.pull s1 U.gen.hom.left
  have hext : LBIso (U.LG.L.pull φ) (A.L.pull U.gen.hom.left) := by
    obtain ⟨v, hv⟩ := U.ext
    exact LBIso.symm ⟨v, hv⟩
  have hgp := isGrpPullback_of_iso U.gen
  have s3 := GlobalTheory.ShapePull.iso_cubeLB_pull hgp (pushPt hgp.1.w (𝟙 GK)) hext
    (a' := 𝟙 GK) (b' := wGK) (a := 𝟙 A.A) (b := oA.act w) (Category.comp_id _).symm (by
      refine Over.OverMorphism.ext ?_
      have e := congrArg (fun q => q.left) (hlin.ext w)
      simp only [Over.comp_left] at e
      simp only [pushPt, Over.homMk_left, Over.comp_left, Over.id_left, Category.id_comp]
      exact e)
  have hpb := isGrpPullback_pullback G (jK R)
  have s4 := GlobalTheory.ShapePull.iso_cubeLB_pull hpb (pushPt hpb.1.w (𝟙 GK)) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hLG φ))
    (a' := 𝟙 GK) (b' := wGK) (a := 𝟙 G) (b := oG.act w) (Category.comp_id _).symm (by
      refine Over.OverMorphism.ext ?_
      show wGK.left ≫ φ = (𝟙 GK.left ≫ φ) ≫ (oG.act w).left
      rw [Category.id_comp]
      simp only [wGK, φ, Over.pullback_map_left]
      exact pullback.lift_fst _ _ _)
  have s5 := GlobalTheory.RigidBundleGlue.LBIso.pull hP φ
  have e3 : (pushPt hgp.1.w (𝟙 GK)).left = U.gen.hom.left := by simp [pushPt]
  have e4 : (pushPt hpb.1.w (𝟙 GK)).left = φ := Category.id_comp _
  rw [e3] at s3
  rw [e4] at s4
  have i1 := pull_isLB h1 U.gen.hom.left
  have i2 := pull_isLB (lbc ![𝟙 A.A, oA.act w] hAL) U.gen.hom.left
  have i3 := lbc ![𝟙 GK, wGK] (pull_isLB hLG φ)
  have i4 := pull_isLB (lbc ![𝟙 G, oG.act w] hLG) φ
  have i5 := pull_isLB P.L.isLB φ
  exact LBIso.trans i1 i2 i5 s2 (LBIso.trans i2 i3 i5 s3.symm (LBIso.trans i3 i4 i5 s4 s5.symm))

end GlobalTheory.Mum.GenPol
