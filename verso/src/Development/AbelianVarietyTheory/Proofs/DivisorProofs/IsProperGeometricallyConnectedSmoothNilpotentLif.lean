import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperAndGeometricallyConnectedOfIsNilpotent

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilLift

/- English proof (translation)
Use `⟨fun (x : PrimeSpectrum R) ↦ ?_⟩` and prove the remaining obligations. Establish `: x ∈ Set.range (PrimeSpectrum.comap π)`. Rewrite using `[range_comap_of_surjective _ _ hπ]`. Take `⟨n, hn⟩` from `hn`. Introduce `a ha`.

Apply `x.isPrime.mem_of_pow_mem n` to reduce the goal to its premises. Establish `: a ^ n ∈ RingHom.ker π ^ n` using `Ideal.pow_mem_pow ha n`. Rewrite `this` using `[hn]`. Rewrite using `[show a ^ n = 0 from this]`. Conclude with `zero_mem _`.

Conclude with `this`.
-/
theorem surjective_spMap_of_isNilpotent_ker {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) : Surjective (spMap π) := by
  refine ⟨fun (x : PrimeSpectrum R) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ _ hπ]
    obtain ⟨n, hn⟩ := hn
    intro a ha
    apply x.isPrime.mem_of_pow_mem n
    have : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    rw [show a ^ n = 0 from this]
    exact zero_mem _
  exact this

/- English proof (translation)
Introduce `R R₀ _ _ π hπ hn X X₀ i hsq hsm hp hgc`. Establish `hs : Surjective (spMap π)` using `surjective_spMap_of_isNilpotent_ker π hπ hn`. Establish `hc : IsClosedImmersion (spMap π)` using `.spec_of_surjective _ hπ`. Establish `: Surjective i` using `MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hs`. Establish `: IsClosedImmersion i` using `MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hc`.

Establish `: IsProper (i ≫ X.hom)` using `by rw [hsq.w]; infer_instance`. Establish `: UniversallyClosed X.hom` using `UniversallyClosed.of_comp_surjective i X.hom`. Establish `: IsSeparated X.hom` using `GlobalTheory.NilProper.isSeparated_of_comp_surjective i X.hom`. Establish `: LocallyOfFiniteType X.hom` using `inferInstance`. Use `⟨{}, ⟨fun K _ y Z fst snd hz ↦ ?_⟩⟩` and prove the remaining obligations.

Take `⟨φ, rfl⟩` from `Spec.map_surjective y`. Establish `hφ : RingHom.ker π ≤ RingHom.ker φ.hom`. Introduce `a ha`. Take `⟨n, hn⟩` from `hn`. Establish `: a ^ n ∈ RingHom.ker π ^ n` using `Ideal.pow_mem_pow ha n`.

Rewrite `this` using `[hn]`. Establish `h0 : IsNilpotent a` using `⟨n, this⟩`. Conclude with `(h0.map φ.hom).eq_zero`. Set `ψ : R₀ →+* K` to `RingHom.liftOfSurjective π hπ ⟨φ.hom, hφ⟩`. Establish `hψ : ∀ a, ψ (π a) = φ.hom a` using `fun a ↦ RingHom.liftOfRightInverse_comp_apply π _ _ ⟨φ.hom, hφ⟩ a`.

Set `y' : Spec (CommRingCat.of K) ⟶ Sp R₀` to `Spec.map (CommRingCat.ofHom ψ)`. Establish `hy : y' ≫ spMap π = Spec.map φ`. Simplify using `only [y', spMap, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `a`.

Conclude with `hψ a`. Rewrite `hz` using `[← hy]`. Set `p : Z ⟶ X₀.left` to `hsq.lift fst (snd ≫ y') (by rw [hz.w, Category.assoc])`. Use `hgc.geometrically_connectedSpace y' p snd ?_` and prove the remaining obligations. Conclude with `IsPullback.of_right (by rw [hsq.lift_fst]; exact hz) (hsq.lift_snd _ _ _) hsq`.
-/
theorem isProper_and_geometricallyConnected_of_smooth_lift :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    IsProper X₀.hom → GeometricallyConnected X₀.hom → IsProper X.hom ∧ GeometricallyConnected X.hom := by
  intro R R₀ _ _ π hπ hn X X₀ i hsq hsm hp hgc
  have hs : Surjective (spMap π) := surjective_spMap_of_isNilpotent_ker π hπ hn
  have hc : IsClosedImmersion (spMap π) := .spec_of_surjective _ hπ
  have : Surjective i := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hs
  have : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hc
  have : IsProper (i ≫ X.hom) := by rw [hsq.w]; infer_instance
  have : UniversallyClosed X.hom := UniversallyClosed.of_comp_surjective i X.hom
  have : IsSeparated X.hom := GlobalTheory.NilProper.isSeparated_of_comp_surjective i X.hom
  have : LocallyOfFiniteType X.hom := inferInstance
  refine ⟨{}, ⟨fun K _ y Z fst snd hz ↦ ?_⟩⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  have hφ : RingHom.ker π ≤ RingHom.ker φ.hom := by
    intro a ha
    obtain ⟨n, hn⟩ := hn
    have : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    have h0 : IsNilpotent a := ⟨n, this⟩
    exact (h0.map φ.hom).eq_zero
  let ψ : R₀ →+* K := RingHom.liftOfSurjective π hπ ⟨φ.hom, hφ⟩
  have hψ : ∀ a, ψ (π a) = φ.hom a := fun a ↦
    RingHom.liftOfRightInverse_comp_apply π _ _ ⟨φ.hom, hφ⟩ a
  let y' : Spec (CommRingCat.of K) ⟶ Sp R₀ := Spec.map (CommRingCat.ofHom ψ)
  have hy : y' ≫ spMap π = Spec.map φ := by
    simp only [y', spMap, ← Spec.map_comp]
    congr 1
    ext a
    exact hψ a
  rw [← hy] at hz
  let p : Z ⟶ X₀.left := hsq.lift fst (snd ≫ y') (by rw [hz.w, Category.assoc])
  refine hgc.geometrically_connectedSpace y' p snd ?_
  exact IsPullback.of_right (by rw [hsq.lift_fst]; exact hz) (hsq.lift_snd _ _ _) hsq

end GlobalTheory.NilLift
