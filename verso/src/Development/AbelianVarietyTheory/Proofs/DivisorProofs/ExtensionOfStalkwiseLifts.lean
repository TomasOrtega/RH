import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls

/- English proof (translation)
Use `⟨q.isOpenEmbedding.isInducing.dense_iff.2 fun w => ?_⟩` and prove the remaining obligations. Establish `e : q '' Set.range r = Set.range (GlobalTheory.FlagCov.genPt G)`. Rewrite using `[← hr, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Establish `hm : genericPoint G ∈ Set.range (GlobalTheory.FlagCov.genPt G)` using `⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩`. Establish `hd : q w ∈ closure ({genericPoint G} : Set G)`. Rewrite using `[(genericPoint_spec G).def]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `closure_mono (Set.singleton_subset_iff.2 hm) hd`.
-/
theorem isDominant_of_comp_eq_genPt {G W : Scheme.{0}} [IsIntegral G] (q : W ⟶ G) [IsOpenImmersion q]
    (r : Sp G.functionField ⟶ W) (hr : r ≫ q = GlobalTheory.FlagCov.genPt G) : IsDominant r := by
  refine ⟨q.isOpenEmbedding.isInducing.dense_iff.2 fun w => ?_⟩
  have e : q '' Set.range r = Set.range (GlobalTheory.FlagCov.genPt G) := by
    rw [← hr, ← Set.range_comp]
    rfl
  rw [e]
  have hm : genericPoint G ∈ Set.range (GlobalTheory.FlagCov.genPt G) :=
    ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
  have hd : q w ∈ closure ({genericPoint G} : Set G) := by
    rw [(genericPoint_spec G).def]; trivial
  exact closure_mono (Set.singleton_subset_iff.2 hm) hd

/- English proof (translation)
Establish `h' : ∀ z : G, ∃ (U : G.Opens) (_ : z ∈ U) (g : U.toScheme ⟶ Y) (r : Sp G.functionField ⟶ U.toScheme), r ≫ U.ι = GlobalTheory.FlagCov.genPt G ∧ r ≫ g = p ∧ g ≫ t = U.ι ≫ s` using `fun z => by`. Take `⟨q, h1, h2⟩` from `h z`. Take `⟨U, hU, g, h3, h4⟩` from `spread_out_of_isGermInjective' s t (x := z) q h2`. Use `⟨U, hU, g, spMap (algebraMap (G.presheaf.stalk z) G.functionField) ≫ U.fromSpecStalkOfMem z hU, ?_, ?_, h4⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]`.

Conclude with `Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes z)`. Rewrite using `[Category.assoc, ← h1, h3]`. Use `choose U hU g r hr hg hs using h'`. Set `𝒰 : G.OpenCover` to `Scheme.Cover.mkOfCovers G (fun z => (U z).toScheme) (fun z => (U z).ι) fun z => ⟨z, ⟨z, hU z⟩, rfl⟩`. Establish `hc : ∀ z w, Limits.pullback.fst (U z).ι (U w).ι ≫ g z = Limits.pullback.snd (U z).ι (U w).ι ≫ g w` using `fun z w => by`.

Establish `: IsReduced (Limits.pullback (U z).ι (U w).ι)` using `isReduced_of_isOpenImmersion (Limits.pullback.fst (U z).ι (U w).ι ≫ (U z).ι)`. Use `isDominant_of_comp_eq_genPt (Limits.pullback.fst (U z).ι (U w).ι ≫ (U z).ι) (Limits.pullback.lift (r z) (r w) ((hr z).trans (hr w).symm)) (by rw [Limits.pullback.lift_fst_assoc, hr])` as an intermediate fact. Use `ext_of_isDominant_of_isSeparated t ?_ (Limits.pullback.lift (r z) (r w) ((hr z).trans (hr w).symm)) ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hs, hs, Limits.pullback.condition_assoc]`. Rewrite using `[Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd_assoc, hg, hg]`.

Establish `e : ∀ z, (U z).ι ≫ 𝒰.glueMorphisms g hc = g z` using `fun z => 𝒰.ι_glueMorphisms g hc z`. Use `⟨𝒰.glueMorphisms g hc, ?_, 𝒰.hom_ext _ _ fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[← hr (genericPoint G), Category.assoc, e, hg]`. Conclude with `((Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) (e z))).trans (hs z)`.
-/
theorem exists_hom_of_forall_stalk (G Y S : Scheme.{0}) [IsIntegral G] (s : G ⟶ S) (t : Y ⟶ S) [IsSeparated t]
    [LocallyOfFiniteType t] (p : Sp G.functionField ⟶ Y) (_hp : p ≫ t = GlobalTheory.FlagCov.genPt G ≫ s)
    (h : ∀ z : G, ∃ q : Sp (G.presheaf.stalk z) ⟶ Y,
      spMap (algebraMap (G.presheaf.stalk z) G.functionField) ≫ q = p ∧ q ≫ t = G.fromSpecStalk z ≫ s) :
    ∃ f : G ⟶ Y, GlobalTheory.FlagCov.genPt G ≫ f = p ∧ f ≫ t = s := by
  have h' : ∀ z : G, ∃ (U : G.Opens) (_ : z ∈ U) (g : U.toScheme ⟶ Y) (r : Sp G.functionField ⟶ U.toScheme),
      r ≫ U.ι = GlobalTheory.FlagCov.genPt G ∧ r ≫ g = p ∧ g ≫ t = U.ι ≫ s := fun z => by
    obtain ⟨q, h1, h2⟩ := h z
    obtain ⟨U, hU, g, h3, h4⟩ := spread_out_of_isGermInjective' s t (x := z) q h2
    refine ⟨U, hU, g, spMap (algebraMap (G.presheaf.stalk z) G.functionField) ≫ U.fromSpecStalkOfMem z hU, ?_, ?_, h4⟩
    · rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
      exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes z)
    · rw [Category.assoc, ← h1, h3]
  choose U hU g r hr hg hs using h'
  let 𝒰 : G.OpenCover := Scheme.Cover.mkOfCovers G (fun z => (U z).toScheme) (fun z => (U z).ι)
    fun z => ⟨z, ⟨z, hU z⟩, rfl⟩
  have hc : ∀ z w, Limits.pullback.fst (U z).ι (U w).ι ≫ g z = Limits.pullback.snd (U z).ι (U w).ι ≫ g w := fun z w => by
    have : IsReduced (Limits.pullback (U z).ι (U w).ι) :=
      isReduced_of_isOpenImmersion (Limits.pullback.fst (U z).ι (U w).ι ≫ (U z).ι)
    have := isDominant_of_comp_eq_genPt (Limits.pullback.fst (U z).ι (U w).ι ≫ (U z).ι)
      (Limits.pullback.lift (r z) (r w) ((hr z).trans (hr w).symm)) (by rw [Limits.pullback.lift_fst_assoc, hr])
    refine ext_of_isDominant_of_isSeparated t ?_ (Limits.pullback.lift (r z) (r w) ((hr z).trans (hr w).symm)) ?_
    · rw [Category.assoc, Category.assoc, hs, hs, Limits.pullback.condition_assoc]
    · rw [Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd_assoc, hg, hg]
  have e : ∀ z, (U z).ι ≫ 𝒰.glueMorphisms g hc = g z := fun z => 𝒰.ι_glueMorphisms g hc z
  refine ⟨𝒰.glueMorphisms g hc, ?_, 𝒰.hom_ext _ _ fun z => ?_⟩
  · rw [← hr (genericPoint G), Category.assoc, e, hg]
  · exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) (e z))).trans (hs z)

end GlobalTheory.FlagCls
