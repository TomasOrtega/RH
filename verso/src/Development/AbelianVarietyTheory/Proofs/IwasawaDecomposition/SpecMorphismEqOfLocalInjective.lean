import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecMapFromSpecOfRangeSubset
open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.ExtLocal

/- English proof (translation)
Introduce `A R _ _ _ _ φ hφ hloc S f g h`. Establish `hcl : (spMap φ) (closedPoint R) = closedPoint A` using `by haveI := hloc`. Conclude with `IsLocalRing.comap_closedPoint φ`. Establish `hfg : f (closedPoint A) = g (closedPoint A)`. Establish `hall : ∀ r : Sp R, f (spMap φ r) = g (spMap φ r)` using `fun r => by`.

Establish `e : (spMap φ ≫ f) r = (spMap φ ≫ g) r` using `by rw [h]`. Rewrite `e` using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]`. Then use the resulting hypothesis. Establish `e` using `hall (closedPoint R)`. Conclude with `hcl ▸ e`. Take `⟨U, hU, hxU, -⟩` from `exists_isAffineOpen_mem_and_subset (X := S) (x := f (closedPoint A)) (U := ⊤) trivial`.

Establish `h1 : ∀ x, f x ∈ U` using `fun x => ((IsLocalRing.specializes_closedPoint (R := A) x).map f.continuous).mem_open U.2 hxU`. Establish `h2 : ∀ x, g x ∈ U` using `fun x => ((IsLocalRing.specializes_closedPoint (R := A) x).map g.continuous).mem_open U.2 (hfg ▸ hxU)`. Take `⟨a, rfl⟩` from `exists_specMap_fromSpec_of_range_subset f hU h1`. Take `⟨b, rfl⟩` from `exists_specMap_fromSpec_of_range_subset g hU h2`. Establish `h' : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map a = Spec.map (CommRingCat.ofHom φ) ≫ Spec.map b`.

Establish `h3 : (Spec.map (CommRingCat.ofHom φ) ≫ Spec.map a) ≫ hU.fromSpec = (Spec.map (CommRingCat.ofHom φ) ≫ Spec.map b) ≫ hU.fromSpec`. Simplify `h` using `[Category.assoc]`. Conclude with `(cancel_mono hU.fromSpec).1 h3`. Establish `h4 : a ≫ CommRingCat.ofHom φ = b ≫ CommRingCat.ofHom φ`. Apply `Spec.map_injective` to reduce the goal to its premises.

Simplify `h'` using `[Spec.map_comp]`. Establish `h5 : a = b`. Use extensionality with `x`. Apply `hφ` to reduce the goal to its premises. Conclude with `congrArg (fun k => k.hom x) h4`.

Rewrite using `[h5]`.
-/
theorem eq_of_spMap_comp_eq : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] (φ : A →+* R),
    Function.Injective φ → IsLocalHom φ → ∀ (S : Scheme.{0}) (f g : Sp A ⟶ S), spMap φ ≫ f = spMap φ ≫ g → f = g := by
  intro A R _ _ _ _ φ hφ hloc S f g h
  have hcl : (spMap φ) (closedPoint R) = closedPoint A := by
    haveI := hloc
    exact IsLocalRing.comap_closedPoint φ
  have hfg : f (closedPoint A) = g (closedPoint A) := by
    have hall : ∀ r : Sp R, f (spMap φ r) = g (spMap φ r) := fun r => by
      have e : (spMap φ ≫ f) r = (spMap φ ≫ g) r := by rw [h]
      rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e
    have e := hall (closedPoint R)
    exact hcl ▸ e
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := S)
    (x := f (closedPoint A)) (U := ⊤) trivial
  have h1 : ∀ x, f x ∈ U := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := A) x).map f.continuous).mem_open U.2 hxU
  have h2 : ∀ x, g x ∈ U := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := A) x).map g.continuous).mem_open U.2 (hfg ▸ hxU)
  obtain ⟨a, rfl⟩ := exists_specMap_fromSpec_of_range_subset f hU h1
  obtain ⟨b, rfl⟩ := exists_specMap_fromSpec_of_range_subset g hU h2
  have h' : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map a = Spec.map (CommRingCat.ofHom φ) ≫ Spec.map b := by
    have h3 : (Spec.map (CommRingCat.ofHom φ) ≫ Spec.map a) ≫ hU.fromSpec =
        (Spec.map (CommRingCat.ofHom φ) ≫ Spec.map b) ≫ hU.fromSpec := by
      simpa [Category.assoc] using h
    exact (cancel_mono hU.fromSpec).1 h3
  have h4 : a ≫ CommRingCat.ofHom φ = b ≫ CommRingCat.ofHom φ := by
    apply Spec.map_injective
    simpa [Spec.map_comp] using h'
  have h5 : a = b := by
    ext x
    apply hφ
    exact congrArg (fun k => k.hom x) h4
  rw [h5]

end GlobalTheory.ExtLocal
