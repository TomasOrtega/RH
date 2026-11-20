import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamComparisonBijectiveCupSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLieSequenceExactAbelianSchemeStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianHodge

/- English proof (translation)
Take `⟨g, hg⟩` from `Module.projective_lifting_property f LinearMap.id hf`. Establish `hfg : ∀ y, f (g y) = y` using `fun y ↦ LinearMap.congr_fun hg y`. Use `⟨LinearMap.range g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.disjoint_def]`. Introduce and unpack `x hx ⟨y, rfl⟩`.

Establish `: y = 0` using `(hfg y).symm.trans hx`. Rewrite using `[this, map_zero]`. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `x _`. Establish `e : x = (x - g (f x)) + g (f x)` using `by abel`.

Rewrite using `[e]`. Use `Submodule.add_mem_sup ?_ (LinearMap.mem_range_self g _)` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, map_sub, hfg, sub_self]`.
-/
theorem exists_isCompl_ker {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module.Projective R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    ∃ C : Submodule R M, IsCompl (LinearMap.ker f) C := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfg : ∀ y, f (g y) = y := fun y ↦ LinearMap.congr_fun hg y
  refine ⟨LinearMap.range g, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨y, rfl⟩
    have : y = 0 := (hfg y).symm.trans hx
    rw [this, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have e : x = (x - g (f x)) + g (f x) := by abel
    rw [e]
    refine Submodule.add_mem_sup ?_ (LinearMap.mem_range_self g _)
    rw [LinearMap.mem_ker, map_sub, hfg, sub_self]

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `toH1O s c = 0 ↔ toHO1 s (cmp1 s c) = 0`. Rewrite using `[structureSheaf_comparison_comm]`. Conclude with `⟨fun h ↦ h ▸ map_zero _, fun h ↦ hO (h.trans (map_zero _).symm)⟩`.
-/
theorem mem_F1_iff_supported (hO : Function.Injective (cmpO s)) (c : FirstDeRham s) :
    c ∈ F1 s ↔ cmp1 s c ∈ CechHodgeFiltration s := by
  change toH1O s c = 0 ↔ toHO1 s (cmp1 s c) = 0
  rw [structureSheaf_comparison_comm]
  exact ⟨fun h ↦ h ▸ map_zero _, fun h ↦ hO (h.trans (map_zero _).symm)⟩

/- English proof (translation)
Substitute `hst` using the available equality. Set `E : P ≃ₗ[R] HH1 s` to `(LinearEquiv.ofTop P hP).trans (LinearEquiv.ofBijective (cmp1 s) hb)`. Establish `hE : ∀ x : P, E x = cmp1 s x.1` using `fun _ ↦ rfl`. Establish `hc : (F1 s).comap P.subtype = (CechHodgeFiltration s).comap (E : P →ₗ[R] HH1 s)`. Use extensionality with `x`.

Rewrite using `[Submodule.mem_comap, Submodule.mem_comap, Submodule.coe_subtype, LinearEquiv.coe_coe, hE]`. Conclude with `mem_F1_iff_supported s hO x.1`. Take `⟨N', hN'⟩` from `exists_isCompl_ker (toHO1 s) hsurj`. Use `⟨⟨N'.comap (E : P →ₗ[R] HH1 s), ?_⟩, ⟨?_⟩⟩` and prove the remaining obligations. Rewrite using `[hc, Submodule.comap_equiv_eq_map_symm, Submodule.comap_equiv_eq_map_symm]`.

Conclude with `(Submodule.orderIsoMapComap E.symm).isCompl hN'`. Set `e1 : ((F1 s).comap P.subtype) ≃ₗ[R] ((CechHodgeFiltration s).comap (E : P →ₗ[R] HH1 s))` to `LinearEquiv.ofEq _ _ hc`. Set `e2 : ((CechHodgeFiltration s).comap (E : P →ₗ[R] HH1 s)) ≃ₗ[R] CechHodgeFiltration s` to `E.ofSubmodules _ (CechHodgeFiltration s) (Submodule.map_comap_eq_of_surjective E.surjective _)`. Set `e3 : CechHodgeFiltration s ≃ₗ[R] LinearMap.range (clForm s)` to `LinearEquiv.ofEq _ _ (cechHodgeFiltration_eq_range s)`. Set `e4 : LinearMap.range (clForm s) ≃ₗ[R] ClosedForm s` to `(LinearEquiv.ofInjective (clForm s) hinj).symm`.

Set `e5 : ClosedForm s ≃ₗ[R] GlobForm s` to `LinearEquiv.ofTop _ hcl`. Conclude with `e1.trans (e2.trans (e3.trans (e4.trans e5)))`.
-/
theorem hodge_of_cmp (P : Submodule R (FirstDeRham s)) (hP : P = ⊤)
    (hb : Function.Bijective (cmp1 s)) (hO : Function.Injective (cmpO s)) (t : X ⟶ Sp R) (hst : s = t)
    (hcl : ClosedForm t = ⊤) (hinj : Function.Injective (clForm t))
    (hsurj : Function.Surjective (toHO1 t)) (hproj : Module.Projective R (HO1 t)) :
    (∃ N : Submodule R P, IsCompl ((F1 s).comap P.subtype) N) ∧
      Nonempty (((F1 s).comap P.subtype) ≃ₗ[R] GlobForm t) := by
  subst hst
  let E : P ≃ₗ[R] HH1 s := (LinearEquiv.ofTop P hP).trans (LinearEquiv.ofBijective (cmp1 s) hb)
  have hE : ∀ x : P, E x = cmp1 s x.1 := fun _ ↦ rfl
  have hc : (F1 s).comap P.subtype = (CechHodgeFiltration s).comap (E : P →ₗ[R] HH1 s) := by
    ext x
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.coe_subtype, LinearEquiv.coe_coe, hE]
    exact mem_F1_iff_supported s hO x.1
  obtain ⟨N', hN'⟩ := exists_isCompl_ker (toHO1 s) hsurj
  refine ⟨⟨N'.comap (E : P →ₗ[R] HH1 s), ?_⟩, ⟨?_⟩⟩
  · rw [hc, Submodule.comap_equiv_eq_map_symm, Submodule.comap_equiv_eq_map_symm]
    exact (Submodule.orderIsoMapComap E.symm).isCompl hN'
  · let e1 : ((F1 s).comap P.subtype) ≃ₗ[R] ((CechHodgeFiltration s).comap (E : P →ₗ[R] HH1 s)) :=
      LinearEquiv.ofEq _ _ hc
    let e2 : ((CechHodgeFiltration s).comap (E : P →ₗ[R] HH1 s)) ≃ₗ[R] CechHodgeFiltration s :=
      E.ofSubmodules _ (CechHodgeFiltration s) (Submodule.map_comap_eq_of_surjective E.surjective _)
    let e3 : CechHodgeFiltration s ≃ₗ[R] LinearMap.range (clForm s) := LinearEquiv.ofEq _ _ (cechHodgeFiltration_eq_range s)
    let e4 : LinearMap.range (clForm s) ≃ₗ[R] ClosedForm s := (LinearEquiv.ofInjective (clForm s) hinj).symm
    let e5 : ClosedForm s ≃ₗ[R] GlobForm s := LinearEquiv.ofTop _ hcl
    exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

end GlobalTheory.AbelianHodge

namespace GlobalTheory.AbelianHodge

/- English proof (translation)
Introduce `R _ A _ g hA hg`. Take `⟨h0, -⟩` from `GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison P1 P2) R A g hA hg`. Take `⟨-, -, ⟨hGf, hGp, hGr⟩, ⟨-, hOp, -⟩, ⟨hcl, hinj, hsurj⟩, -⟩` from `P2 R A g hA hg`. Use `hA.smooth` as an intermediate fact. Use `hA.proper` as an intermediate fact.

Take `⟨hb, -⟩` from `cechDeRham_comparison_bijective_cup_smooth P1 R A.left (A.hom ≫ 𝟙 _) inferInstance inferInstance inferInstance`. Establish `hO` using `GlobalTheory.T.structure_sheaf_comparison_injective R A.left (A.hom ≫ 𝟙 _)`. Take `⟨⟨N, hN⟩, ⟨e⟩⟩` from `hodge_of_cmp (A.hom ≫ 𝟙 _) (primDR A) h0 hb hO A.hom (Category.comp_id _) hcl hinj hsurj hOp`. Conclude with `⟨GlobalTheory.T.hodgeLieSequence_exact_abelianScheme P1 P2 R A g hA hg, ⟨N, hN⟩, Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, fun p ↦ by`. Express the relevant statement in the definitionally equal form `Module.rankAtStalk ((F1 (A.hom ≫ 𝟙 _)).comap (primDR A).subtype) p = g`.

Rewrite using `[Module.rankAtStalk_eq_of_equiv e, hGr]⟩`.
-/
theorem abelianDeRham_hodge (P1 : GlobalTheory.Published.CrystallineSmoothLift) (P2 : GlobalTheory.Published.AbelianHodgeDeRham) :
    GlobalTheory.Published.AbelianDeRham.Hodge := by
  intro R _ A _ g hA hg
  obtain ⟨h0, -⟩ := GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison P1 P2) R A g hA hg
  obtain ⟨-, -, ⟨hGf, hGp, hGr⟩, ⟨-, hOp, -⟩, ⟨hcl, hinj, hsurj⟩, -⟩ := P2 R A g hA hg
  have := hA.smooth
  have := hA.proper
  obtain ⟨hb, -⟩ := cechDeRham_comparison_bijective_cup_smooth P1 R A.left (A.hom ≫ 𝟙 _) inferInstance inferInstance
    inferInstance
  have hO := GlobalTheory.T.structure_sheaf_comparison_injective R A.left (A.hom ≫ 𝟙 _)
  obtain ⟨⟨N, hN⟩, ⟨e⟩⟩ := hodge_of_cmp (A.hom ≫ 𝟙 _) (primDR A) h0 hb hO A.hom
    (Category.comp_id _) hcl hinj hsurj hOp
  exact ⟨GlobalTheory.T.hodgeLieSequence_exact_abelianScheme P1 P2 R A g hA hg, ⟨N, hN⟩, Module.Finite.equiv e.symm,
    Module.Projective.of_equiv e.symm, fun p ↦ by
      change Module.rankAtStalk ((F1 (A.hom ≫ 𝟙 _)).comap (primDR A).subtype) p = g
      rw [Module.rankAtStalk_eq_of_equiv e, hGr]⟩

end GlobalTheory.AbelianHodge
