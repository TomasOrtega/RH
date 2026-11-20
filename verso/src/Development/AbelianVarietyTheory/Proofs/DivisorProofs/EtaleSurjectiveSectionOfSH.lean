import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIff
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `A _ hA Y f hf hs`. Take `⟨hH, hsep⟩` from `hA`. Use `haveI := hH`. Take `⟨y, hy⟩` from `f.surjective (IsLocalRing.closedPoint A)`. Set `𝒰` to `Y.affineOpenCover`.

Set `i` to `𝒰.idx y`. Take `⟨z, hz⟩` from `𝒰.covers y`. Set `g : Spec (𝒰.X i) ⟶ Spec (CommRingCat.of A)` to `𝒰.f i ≫ f`. Use `haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i`. Use `haveI : Etale g := inferInstance`.

Set `φ : CommRingCat.of A ⟶ 𝒰.X i` to `Spec.preimage g`. Establish `hφ : Spec.map φ = g` using `Spec.map_preimage g`. Establish `hEt : φ.hom.Etale`. Rewrite using `[← HasRingHomProperty.Spec_iff (P := @Etale), hφ]`. Use `infer_instance`.

Use `letI : Algebra A (𝒰.X i) := φ.hom.toAlgebra`. Use `haveI : Algebra.Etale A (𝒰.X i) := hEt`. Establish `hq : z.asIdeal.comap (algebraMap A (𝒰.X i)) = IsLocalRing.maximalIdeal A`. Establish `h1 : (Spec.map φ).base z = IsLocalRing.closedPoint A`. Rewrite using `[hφ]`.

Use `show f.base ((𝒰.f i).base z) = _`. Rewrite using `[hz, hy]`. Establish `h2` using `congrArg PrimeSpectrum.asIdeal h1`. Conclude with `h2`. Use `haveI : z.asIdeal.IsPrime := PrimeSpectrum.isPrime z`.

Take `⟨s, -⟩` from `(GlobalTheory.StrictHensel.strictlyHenselian_iff A).2 ⟨hH, hsep⟩ (𝒰.X i) z.asIdeal hq`. Use `⟨Spec.map (CommRingCat.ofHom s.toRingHom) ≫ 𝒰.f i, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc]`. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom s.toRingHom) ≫ g = _`. Rewrite using `[← hφ, ← Spec.map_comp]`.

Establish `: φ ≫ CommRingCat.ofHom s.toRingHom = 𝟙 _`. Use extensionality with `a`. Conclude with `s.commutes a`. Conclude with `(congrArg Spec.map this).trans (Spec.map_id _)`.
-/
theorem etale_surjective_section_of_SH : ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of A)), Etale f → Surjective f →
      ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _ := by
  intro A _ hA Y f hf hs
  obtain ⟨hH, hsep⟩ := hA
  haveI := hH
  obtain ⟨y, hy⟩ := f.surjective (IsLocalRing.closedPoint A)
  let 𝒰 := Y.affineOpenCover
  let i := 𝒰.idx y
  obtain ⟨z, hz⟩ := 𝒰.covers y
  let g : Spec (𝒰.X i) ⟶ Spec (CommRingCat.of A) := 𝒰.f i ≫ f
  haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  haveI : Etale g := inferInstance
  let φ : CommRingCat.of A ⟶ 𝒰.X i := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hEt : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hφ]; infer_instance
  letI : Algebra A (𝒰.X i) := φ.hom.toAlgebra
  haveI : Algebra.Etale A (𝒰.X i) := hEt
  have hq : z.asIdeal.comap (algebraMap A (𝒰.X i)) = IsLocalRing.maximalIdeal A := by
    have h1 : (Spec.map φ).base z = IsLocalRing.closedPoint A := by
      rw [hφ]; show f.base ((𝒰.f i).base z) = _; rw [hz, hy]
    have h2 := congrArg PrimeSpectrum.asIdeal h1
    exact h2
  haveI : z.asIdeal.IsPrime := PrimeSpectrum.isPrime z
  obtain ⟨s, -⟩ := (GlobalTheory.StrictHensel.strictlyHenselian_iff A).2 ⟨hH, hsep⟩ (𝒰.X i) z.asIdeal hq
  refine ⟨Spec.map (CommRingCat.ofHom s.toRingHom) ≫ 𝒰.f i, ?_⟩
  rw [Category.assoc]
  change Spec.map (CommRingCat.ofHom s.toRingHom) ≫ g = _
  rw [← hφ, ← Spec.map_comp]
  have : φ ≫ CommRingCat.ofHom s.toRingHom = 𝟙 _ := by
    ext a
    exact s.commutes a
  exact (congrArg Spec.map this).trans (Spec.map_id _)

end GlobalTheory.EtC
