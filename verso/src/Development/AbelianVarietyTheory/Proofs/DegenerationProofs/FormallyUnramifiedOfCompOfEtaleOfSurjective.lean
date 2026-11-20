import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))

namespace GlobalTheory

universe u

open TensorProduct in

/- English proof (translation)
Use `algebraize [φ, β, β.comp φ]`. Establish `: Algebra.FormallyEtale B C` using `Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩`. Establish `h1 : Subsingleton (C ⊗[B] Ω[B⁄A])` using `(KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A B C).subsingleton`. Conclude with `⟨(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right B C).mp h1⟩`.
-/
theorem ringHom_formallyUnramified_of_comp_faithfullyFlat {A B C : Type*} [CommRing A]
    [CommRing B] [CommRing C] {φ : A →+* B} {β : B →+* C} (hβ : β.FaithfullyFlat)
    (hs : β.FormallySmooth) (hu : β.FormallyUnramified) (h : (β.comp φ).FormallyUnramified) :
    φ.FormallyUnramified := by
  algebraize [φ, β, β.comp φ]
  have : Algebra.FormallyEtale B C :=
    Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  have h1 : Subsingleton (C ⊗[B] Ω[B⁄A]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A B C).subsingleton
  exact ⟨(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right B C).mp h1⟩

/- English proof (translation)
Establish `h` using `Flat.stalkMap g w`. Use `algebraize [(g.stalkMap w).hom]`. Establish `: IsLocalHom (algebraMap (X.presheaf.stalk (g w)) (W.presheaf.stalk w))` using `inferInstanceAs <| IsLocalHom (g.stalkMap w).hom`. Conclude with `Module.FaithfullyFlat.of_flat_of_isLocalHom`.
-/
theorem faithfullyFlat_stalkMap_of_flat {W X : Scheme.{u}} (g : W ⟶ X) [Flat g] (w : W) :
    (g.stalkMap w).hom.FaithfullyFlat := by
  have h := Flat.stalkMap g w
  algebraize [(g.stalkMap w).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk (g w)) (W.presheaf.stalk w)) :=
    inferInstanceAs <| IsLocalHom (g.stalkMap w).hom
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/- English proof (translation)
Use `Flat.of_stalkMap u fun x => ?_` and prove the remaining obligations. Take `⟨w, rfl⟩` from `g.surjective x`. Establish `h` using `Flat.stalkMap (g ≫ u) w`. Rewrite `h` using `[Scheme.Hom.stalkMap_comp]`. Conclude with `ringHom_flat_of_comp_faithfullyFlat (faithfullyFlat_stalkMap_of_flat g w) h`.
-/
theorem flat_of_comp_of_flat_of_surjective {W X Y : Scheme.{u}} (g : W ⟶ X) (u : X ⟶ Y)
    [Flat g] [Surjective g] [Flat (g ≫ u)] : Flat u := by
  refine Flat.of_stalkMap u fun x => ?_
  obtain ⟨w, rfl⟩ := g.surjective x
  have h := Flat.stalkMap (g ≫ u) w
  rw [Scheme.Hom.stalkMap_comp] at h
  exact ringHom_flat_of_comp_faithfullyFlat (faithfullyFlat_stalkMap_of_flat g w) h

/- English proof (translation)
Establish `: Flat g` using `(Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1`. Use `HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime fun x => ?_` and prove the remaining obligations. Take `⟨w, rfl⟩` from `g.surjective x`. Establish `h` using `FormallyUnramified.stalkMap (g ≫ u) w`. Rewrite `h` using `[Scheme.Hom.stalkMap_comp]`.

Establish `hs : (g.stalkMap w).hom.FormallySmooth` using `Scheme.Hom.mem_smoothLocus.mp (g.smoothLocus_eq_top.ge (Set.mem_univ w))`. Conclude with `ringHom_formallyUnramified_of_comp_faithfullyFlat (faithfullyFlat_stalkMap_of_flat g w) hs (FormallyUnramified.stalkMap g w) h`.
-/
theorem formallyUnramified_of_comp_of_etale_of_surjective {W X Y : Scheme.{u}} (g : W ⟶ X)
    (u : X ⟶ Y) [Etale g] [Surjective g] [FormallyUnramified (g ≫ u)] :
    FormallyUnramified u := by
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  refine HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime fun x => ?_
  obtain ⟨w, rfl⟩ := g.surjective x
  have h := FormallyUnramified.stalkMap (g ≫ u) w
  rw [Scheme.Hom.stalkMap_comp] at h
  have hs : (g.stalkMap w).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (g.smoothLocus_eq_top.ge (Set.mem_univ w))
  exact ringHom_formallyUnramified_of_comp_faithfullyFlat (faithfullyFlat_stalkMap_of_flat g w)
    hs (FormallyUnramified.stalkMap g w) h

/- English proof (translation)
Establish `: Flat g` using `(Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1`. Establish `: Flat (g ≫ u)` using `(Etale.iff_flat_and_formallyUnramified.mp ‹Etale (g ≫ u)›).1`. Use `flat_of_comp_of_flat_of_surjective g u` as an intermediate fact. Use `formallyUnramified_of_comp_of_etale_of_surjective g u` as an intermediate fact. Conclude with `Etale.of_formallyUnramified_of_flat u`.
-/
theorem etale_of_comp_of_etale_of_surjective {W X Y : Scheme.{u}} (g : W ⟶ X)
    (u : X ⟶ Y) [Etale g] [Surjective g] [Etale (g ≫ u)] [LocallyOfFinitePresentation u] :
    Etale u := by
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  have : Flat (g ≫ u) := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale (g ≫ u)›).1
  have := flat_of_comp_of_flat_of_surjective g u
  have := formallyUnramified_of_comp_of_etale_of_surjective g u
  exact Etale.of_formallyUnramified_of_flat u

/- English proof (translation)
Introduce `W X Y g u _ _ _`. Establish `: Flat g` using `(Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1`. Set `V : X.Opens` to `⟨Set.range g, g.isOpenMap.isOpen_range⟩`. Use `⟨V, rfl, ?_⟩` and prove the remaining obligations. Establish `hr : Set.range g ⊆ Set.range V.ι`.

Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `subset_rfl`. Set `g' : W ⟶ V` to `IsOpenImmersion.lift V.ι g hr`. Establish `hg' : g' ≫ V.ι = g` using `IsOpenImmersion.lift_fac _ _ _`. Establish `: Etale (g' ≫ V.ι)` using `by rw [hg']; infer_instance`.

Establish `: Etale g'` using `Etale.of_comp g' V.ι`. Establish `: Surjective g'`. Use `⟨fun v => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩ : V.ι v ∈ Set.range g` from `v.2`. Use `⟨w, V.ι.isOpenEmbedding.injective ?_⟩` and prove the remaining obligations.

Rewrite using `[← Scheme.Hom.comp_apply, hg', hw]`. Establish `: Etale (g' ≫ V.ι ≫ u)` using `by rw [← Category.assoc, hg']; infer_instance`. Conclude with `etale_of_comp_of_etale_of_surjective g' (V.ι ≫ u)`.
-/
theorem exists_opens_range_etale_of_comp :
    ∀ (W X Y : Scheme.{0}) (g : W ⟶ X) (u : X ⟶ Y) [Etale g] [Etale (g ≫ u)]
      [LocallyOfFinitePresentation u],
      ∃ V : X.Opens, (V : Set X) = Set.range g ∧ Etale (V.ι ≫ u) := by
  intro W X Y g u _ _ _
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  let V : X.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  refine ⟨V, rfl, ?_⟩
  have hr : Set.range g ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]; exact subset_rfl
  let g' : W ⟶ V := IsOpenImmersion.lift V.ι g hr
  have hg' : g' ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  have : Etale (g' ≫ V.ι) := by rw [hg']; infer_instance
  have : Etale g' := Etale.of_comp g' V.ι
  have : Surjective g' := by
    refine ⟨fun v => ?_⟩
    obtain ⟨w, hw⟩ : V.ι v ∈ Set.range g := v.2
    refine ⟨w, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hg', hw]
  have : Etale (g' ≫ V.ι ≫ u) := by rw [← Category.assoc, hg']; infer_instance
  exact etale_of_comp_of_etale_of_surjective g' (V.ι ≫ u)

end GlobalTheory
