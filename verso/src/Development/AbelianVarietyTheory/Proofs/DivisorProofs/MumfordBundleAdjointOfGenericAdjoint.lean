import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoGenericFibreExtendsUniformisedGr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.PoincAdj

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend GlobalTheory.UT GlobalTheory.Mum.Two

/- English proof (translation)
Introduce `R _ _ _ hB G _ _ hS D A U E E' hA`. Establish `hR : AdmBase R (maximalIdeal R)` using `hB.1`. Use `haveI : IsNoetherianRing R := hR.1`. Use `haveI : IsIntegrallyClosed R := hR.2.2.1`. Use `haveI := hS.smooth`.

Use `haveI := hS.geomConnected`. Use `haveI := GlobalTheory.smooth_tensorObj_hom G G`. Use `haveI := GlobalTheory.geometricallyIntegral_tensorObj_hom G G`. Set `U₁` to `U.toUnifPre`. Set `δ` to `CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G G`.

Set `u` to `lift (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U₁.gen.hom) (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U₁.gen.hom)`. Establish `hL` using `U₁.LG.isLB`. Establish `hAL` using `A.isLB`. Establish `hgen` using `U₁.gen_hom`. Establish `hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U₁.LG.L hL) = CechPic.pull U₁.gen.hom.left (cls A.L hAL)`.

Take `⟨w, hw⟩` from `U₁.ext`. Rewrite using `[← cls_pull hL _ (pull_isLB hL _), ← cls_pull hAL _ (pull_isLB hAL _)]`. Conclude with `((cls_eq_iff _ _).2 ⟨w, hw⟩).symm`. Establish `Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z), ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left` using `fun q => pullback.lift_fst _ _ _`. Establish `hu : u.left ≫ (A.A ⊗ A.A).hom = ((Over.pullback (jK R)).obj G ⊗ (Over.pullback (jK R)).obj G).hom ≫ 𝟙 _`.

Rewrite using `[Category.comp_id]`. Conclude with `Over.w u`. Establish `key : ∀ (x y : G ⟶ G) (cx cy : A.A ⟶ A.A), Gen₀ U₁ U₁ x cx → Gen₀ U₁ U₁ y cy → CechPic.pull (pullback.fst (G ⊗ G).hom (jK R)) (cubeCls G ![fst G G ≫ x, snd G G ≫ y] (cls U₁.LG.L hL)) = CechPic.pull δ.left (CechPic.pull u.left (cubeCls A.A ![fst A.A A.A ≫ cx, snd A.A A.A ≫ cy] (cl …`. Introduce `x y cx cy hx hy`. Establish `e'` using `push_cubeCls (isGrpPullback_pullback G (jK R)) (T' := (Over.pullback (jK R)).obj (G ⊗ G)) (T := G ⊗ G) (fun i => (Over.pullback (jK R)).map (![fst G G ≫ x, snd G G ≫ y] i)) ![fst G G ≫ x, snd G G ≫ y] (pullback.fst (G ⊗ G).hom (jK R)) pullback.condition (fun i => Aw _) (cls U₁.LG …`.

Use `e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x, snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> simp [δ]`. Rewrite using `[hc']`. Use `congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U₁.gen) _ _ u.left hu (fun i => ?_) _).symm` and prove the remaining obligations. Use `fin_cases i`.

Use `show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U₁.gen.hom).left = (u ≫ fst A.A A.A ≫ cx).left`. Use `congr 1`. Simplify using `only [u, Category.assoc, lift_fst_assoc]`. Rewrite using `[hx]`. Use `show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U₁.gen.hom).left = (u ≫ snd A.A A.A ≫ cy).left`.

Use `congr 1`. Simplify using `only [u, Category.assoc, lift_snd_assoc]`. Rewrite using `[hy]`. Establish `g₁ : Gen₀ U₁ U₁ (𝟙 G) (𝟙 A.A)`. Unfold `Gen₀`.

Rewrite using `[CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]`. Establish `k₁` using `key E.aG (𝟙 G) E.aA (𝟙 A.A) E.ext g₁`. Establish `k₂` using `key (𝟙 G) E'.aG (𝟙 A.A) E'.aA g₁ E'.ext`. Simplify using `only [Category.comp_id] at k₁ k₂`. Establish `eA : cubeCls A.A ![fst A.A A.A ≫ E.aA, snd A.A A.A] (cls _ hAL) = cubeCls A.A ![fst A.A A.A, snd A.A A.A ≫ E'.aA] (cls _ hAL)` using `(cls_cubeLB A.A _ hAL).symm.trans (((cls_eq_iff _ _).2 hA).trans (cls_cubeLB A.A _ hAL))`.

Use `GlobalTheory.Mum.lbIso_of_generic_local R (G ⊗ G) (η[G ⊗ G]).left (Over.w _) _ _ (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _) ?_` and prove the remaining obligations. Use `(cls_eq_iff (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB (LB.isLB_linComb hL _ _) _)).1 ?_` and prove the remaining obligations. Rewrite using `[cls_pull (LB.isLB_linComb hL _ _) _ (pull_isLB (LB.isLB_linComb hL _ _) _), cls_pull (LB.isLB_linComb hL _ _) _ (pull_isLB (LB.isLB_linComb hL _ _) _),`. Use the proof step `]`. Use `(congrArg (CechPic.pull _) (cls_cubeLB G ![fst G G ≫ E.aG, snd G G] hL)).trans ?_` and prove the remaining obligations.

Use `Eq.trans ?_ (congrArg (CechPic.pull _) (cls_cubeLB G ![fst G G, snd G G ≫ E'.aG] hL)).symm` and prove the remaining obligations. Rewrite using `[k₁, k₂, eA]`.
-/
theorem lbIso_adj_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB A.A ![fst A.A A.A ≫ E.aA, snd A.A A.A] A.L) (cubeLB A.A ![fst A.A A.A, snd A.A A.A ≫ E'.aA] A.L) → LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) := by
  intro R _ _ _ hB G _ _ hS D A U E E' hA
  have hR : AdmBase R (maximalIdeal R) := hB.1
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  haveI := hS.smooth
  haveI := hS.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom G G
  haveI := GlobalTheory.geometricallyIntegral_tensorObj_hom G G
  let U₁ := U.toUnifPre
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G G
  let u := lift (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U₁.gen.hom)
  have hL := U₁.LG.isLB
  have hAL := A.isLB
  have hgen := U₁.gen_hom
  have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U₁.LG.L hL) =
      CechPic.pull U₁.gen.hom.left (cls A.L hAL) := by
    obtain ⟨w, hw⟩ := U₁.ext
    rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hAL _ (pull_isLB hAL _)]
    exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
  have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
      ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
    fun q => pullback.lift_fst _ _ _
  have hu : u.left ≫ (A.A ⊗ A.A).hom =
      ((Over.pullback (jK R)).obj G ⊗ (Over.pullback (jK R)).obj G).hom ≫ 𝟙 _ := by
    rw [Category.comp_id]; exact Over.w u
  have key : ∀ (x y : G ⟶ G) (cx cy : A.A ⟶ A.A), Gen₀ U₁ U₁ x cx → Gen₀ U₁ U₁ y cy →
      CechPic.pull (pullback.fst (G ⊗ G).hom (jK R)) (cubeCls G ![fst G G ≫ x, snd G G ≫ y] (cls U₁.LG.L hL)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A.A ![fst A.A A.A ≫ cx, snd A.A A.A ≫ cy] (cls A.L hAL))) := by
    intro x y cx cy hx hy
    have e' := push_cubeCls (isGrpPullback_pullback G (jK R)) (T' := (Over.pullback (jK R)).obj (G ⊗ G))
      (T := G ⊗ G) (fun i => (Over.pullback (jK R)).map (![fst G G ≫ x, snd G G ≫ y] i))
      ![fst G G ≫ x, snd G G ≫ y] (pullback.fst (G ⊗ G).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U₁.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U₁.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U₁.gen.hom).left = (u ≫ fst A.A A.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U₁.gen.hom).left = (u ≫ snd A.A A.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have g₁ : Gen₀ U₁ U₁ (𝟙 G) (𝟙 A.A) := by
    unfold Gen₀; rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have k₁ := key E.aG (𝟙 G) E.aA (𝟙 A.A) E.ext g₁
  have k₂ := key (𝟙 G) E'.aG (𝟙 A.A) E'.aA g₁ E'.ext
  simp only [Category.comp_id] at k₁ k₂
  have eA : cubeCls A.A ![fst A.A A.A ≫ E.aA, snd A.A A.A] (cls _ hAL) =
      cubeCls A.A ![fst A.A A.A, snd A.A A.A ≫ E'.aA] (cls _ hAL) :=
    (cls_cubeLB A.A _ hAL).symm.trans (((cls_eq_iff _ _).2 hA).trans (cls_cubeLB A.A _ hAL))
  refine GlobalTheory.Mum.lbIso_of_generic_local R (G ⊗ G) (η[G ⊗ G]).left (Over.w _) _ _ (LB.isLB_linComb hL _ _)
    (LB.isLB_linComb hL _ _) ?_
  refine (cls_eq_iff (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB (LB.isLB_linComb hL _ _) _)).1 ?_
  rw [cls_pull (LB.isLB_linComb hL _ _) _ (pull_isLB (LB.isLB_linComb hL _ _) _),
    cls_pull (LB.isLB_linComb hL _ _) _ (pull_isLB (LB.isLB_linComb hL _ _) _),
]
  refine (congrArg (CechPic.pull _) (cls_cubeLB G ![fst G G ≫ E.aG, snd G G] hL)).trans ?_
  refine Eq.trans ?_ (congrArg (CechPic.pull _) (cls_cubeLB G ![fst G G, snd G G ≫ E'.aG] hL)).symm
  rw [k₁, k₂, eA]

end GlobalTheory.PoincAdj
