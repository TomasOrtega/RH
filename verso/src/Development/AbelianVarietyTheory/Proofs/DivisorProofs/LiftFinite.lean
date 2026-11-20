import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.RetractionLiftSection

/- English proof (translation)
Establish `inj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Establish `key : ∀ a : A, ∃ r : R, algebraMap R K r = ψ a`. Introduce `a`. Take `⟨f, hf, hfa⟩` from `hφ a`. Establish `hi : IsIntegral R (ψ a)`.

Use `⟨f, hf, ?_⟩` and prove the remaining obligations. Rewrite using `[← h, ← Polynomial.hom_eval₂, hfa, map_zero]`. Conclude with `IsIntegrallyClosed.algebraMap_eq_of_integral hi`. Use `choose s hs using key`. Set `σ : A →+* R` to `{ toFun := s map_one' := inj (by rw [hs, map_one, map_one]) map_mul' := fun a b => inj (by rw [map_mul, hs, hs, hs, map_mul]) map_zero' := inj (by rw [hs, map_zero, map_zero]) map_add' := fun a b => inj (by rw [map_add, hs, hs, hs, map_add]) }`.

Use `⟨σ, RingHom.ext hs, RingHom.ext fun r => inj ?_⟩` and prove the remaining obligations. Conclude with `(hs (φ r)).trans (RingHom.congr_fun h r)`.
-/
theorem exists_retraction {R K A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] (φ : R →+* A) (hφ : φ.IsIntegral) (ψ : A →+* K)
    (h : ψ.comp φ = algebraMap R K) :
    ∃ σ : A →+* R, (algebraMap R K).comp σ = ψ ∧ σ.comp φ = RingHom.id R := by
  have inj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have key : ∀ a : A, ∃ r : R, algebraMap R K r = ψ a := by
    intro a
    obtain ⟨f, hf, hfa⟩ := hφ a
    have hi : IsIntegral R (ψ a) := by
      refine ⟨f, hf, ?_⟩
      rw [← h, ← Polynomial.hom_eval₂, hfa, map_zero]
    exact IsIntegrallyClosed.algebraMap_eq_of_integral hi
  choose s hs using key
  let σ : A →+* R :=
    { toFun := s
      map_one' := inj (by rw [hs, map_one, map_one])
      map_mul' := fun a b => inj (by rw [map_mul, hs, hs, hs, map_mul])
      map_zero' := inj (by rw [hs, map_zero, map_zero])
      map_add' := fun a b => inj (by rw [map_add, hs, hs, hs, map_add]) }
  refine ⟨σ, RingHom.ext hs, RingHom.ext fun r => inj ?_⟩
  exact (hs (φ r)).trans (RingHom.congr_fun h r)

/- English proof (translation)
Use `haveI : IsAffine W := isAffine_of_isAffineHom q`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (W.isoSpec.inv ≫ q)`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (y ≫ W.isoSpec.hom)`. Establish `hfin : IsFinite (Spec.map φ)` using `by rw [hφ]; infer_instance`. Establish `hint : φ.hom.IsIntegral` using `((IsFinite.SpecMap_iff φ).1 hfin).to_isIntegral`.

Establish `hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, h]`. Take `⟨σ, h₁, h₂⟩` from `exists_retraction (R := R) (K := K) φ.hom hint ψ.hom (congrArg CommRingCat.Hom.hom hc)`. Use `⟨Spec.map (CommRingCat.ofHom σ) ≫ W.isoSpec.inv, ?_, ?_⟩` and prove the remaining obligations.

Establish `e : CommRingCat.ofHom σ ≫ CommRingCat.ofHom (algebraMap R K) = ψ` using `CommRingCat.hom_ext h₁`. Rewrite using `[← Category.assoc, ← Spec.map_comp]`. Use `erw [e]`. Rewrite using `[hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Establish `e : φ ≫ CommRingCat.ofHom σ = 𝟙 _` using `CommRingCat.hom_ext h₂`.

Rewrite using `[Category.assoc, ← hφ, ← Spec.map_comp]`. Use `erw [e]`. Rewrite using `[Spec.map_id]`.
-/
theorem exists_section {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {W : Scheme.{0}} (q : W ⟶ Spec (CommRingCat.of R)) [IsFinite q]
    (y : Spec (CommRingCat.of K) ⟶ W) (h : y ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ W, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = y ∧ s ≫ q = 𝟙 _ := by
  haveI : IsAffine W := isAffine_of_isAffineHom q
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (W.isoSpec.inv ≫ q)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (y ≫ W.isoSpec.hom)
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hint : φ.hom.IsIntegral := ((IsFinite.SpecMap_iff φ).1 hfin).to_isIntegral
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, h]
  obtain ⟨σ, h₁, h₂⟩ := exists_retraction (R := R) (K := K) φ.hom hint ψ.hom (congrArg CommRingCat.Hom.hom hc)
  refine ⟨Spec.map (CommRingCat.ofHom σ) ≫ W.isoSpec.inv, ?_, ?_⟩
  · have e : CommRingCat.ofHom σ ≫ CommRingCat.ofHom (algebraMap R K) = ψ := CommRingCat.hom_ext h₁
    rw [← Category.assoc, ← Spec.map_comp]
    erw [e]
    rw [hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · have e : φ ≫ CommRingCat.ofHom σ = 𝟙 _ := CommRingCat.hom_ext h₂
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    erw [e]
    rw [Spec.map_id]

/- English proof (translation)
Take `⟨s, h₁, h₂⟩` from `exists_section (K := K) (pullback.snd p x) (pullback.lift y _ h) (pullback.lift_snd _ _ _)`. Use `⟨s ≫ pullback.fst p x, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, h₁, pullback.lift_fst]`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, h₂, Category.id_comp]`.
-/
theorem exists_lift {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {Z P : Scheme.{0}} (p : Z ⟶ P) [IsFinite p] (x : Spec (CommRingCat.of R) ⟶ P)
    (y : Spec (CommRingCat.of K) ⟶ Z) (h : y ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ x) :
    ∃ ξ : Spec (CommRingCat.of R) ⟶ Z, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ ξ = y ∧ ξ ≫ p = x := by
  obtain ⟨s, h₁, h₂⟩ := exists_section (K := K) (pullback.snd p x) (pullback.lift y _ h) (pullback.lift_snd _ _ _)
  refine ⟨s ≫ pullback.fst p x, ?_, ?_⟩
  · rw [← Category.assoc, h₁, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, h₂, Category.id_comp]

/- English proof (translation)
Introduce `R _ _ _ _ _ p x y _ h` and use `exists_lift (R := R) (K := FractionRing R) p x y h`.
-/
theorem lift_finite : ∀ (R : Type) [inst : CommRing R] [IsDomain R] [IsIntegrallyClosed R] (Z P : AlgebraicGeometry.Scheme) (p : Z ⟶ P) (ξ₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ P) (y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (FractionRing R) ⟶ Z), AlgebraicGeometry.IsFinite p → CategoryTheory.CategoryStruct.comp y p = CategoryTheory.CategoryStruct.comp (ReciprocityTheory.ChartRestriction.G.Out.jK R) ξ₀ → ∃ (ξ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Z), CategoryTheory.CategoryStruct.comp (ReciprocityTheory.ChartRestriction.G.Out.jK R) ξ = y ∧ CategoryTheory.CategoryStruct.comp ξ p = ξ₀ :=
  fun R _ _ _ _ _ p x y _ h => exists_lift (R := R) (K := FractionRing R) p x y h

end GlobalTheory.RetractionLiftSection
