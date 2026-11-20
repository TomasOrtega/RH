import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIffStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

/- English proof (translation)
Take `⟨y, hy⟩` from `(Surjective.surj (f := f)) (⟨IsLocalRing.maximalIdeal O, inferInstance⟩ : PrimeSpectrum O)`. Set `U` to `Y.affineOpenCover`. Take `⟨x, hx⟩` from `U.covers y`. Establish `hi : IsOpenImmersion (U.f (U.idx y))` using `U.map_prop _`. Set `φ : CommRingCat.of O ⟶ U.X (U.idx y)` to `Spec.preimage (U.f (U.idx y) ≫ f)`.

Establish `hφ : Spec.map φ = U.f (U.idx y) ≫ f` using `Spec.map_preimage _`. Establish `he : Etale (Spec.map φ)` using `by rw [hφ]; infer_instance`. Establish `hE : φ.hom.Etale` using `HasRingHomProperty.Spec_iff.mp he`. Use `letI : Algebra O (U.X (U.idx y)) := φ.hom.toAlgebra`. Use `haveI : Algebra.Etale O (U.X (U.idx y)) := hE`.

Establish `h1 : (Spec.map φ).base x = (⟨IsLocalRing.maximalIdeal O, inferInstance⟩ : PrimeSpectrum O)`. Rewrite using `[hφ]`. Express the relevant statement in the definitionally equal form `f (U.f (U.idx y) x) = _`. Rewrite using `[hx, hy]`. Set `p : PrimeSpectrum (U.X (U.idx y))` to `x`.

Take `⟨s, hs⟩` from `(GlobalTheory.T.exists_etale_section_iff_henselian_and_isSepClosed O).mpr ⟨inferInstance, inferInstance⟩ (U.X (U.idx y)) p.asIdeal (congrArg PrimeSpectrum.asIdeal h1)`. Use `⟨Spec.map (CommRingCat.ofHom s.toRingHom) ≫ U.f (U.idx y), ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`. Use extensionality with `a`.

Conclude with `s.commutes a`.
-/
private theorem exists_section_of_etale (O : Type) [CommRing O] [HenselianLocalRing O]
    [IsSepClosed (IsLocalRing.ResidueField O)] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of O))
    [Etale f] [Surjective f] : ∃ s : Spec (CommRingCat.of O) ⟶ Y, s ≫ f = 𝟙 _ := by
  obtain ⟨y, hy⟩ := (Surjective.surj (f := f)) (⟨IsLocalRing.maximalIdeal O, inferInstance⟩ : PrimeSpectrum O)
  let U := Y.affineOpenCover
  obtain ⟨x, hx⟩ := U.covers y
  have hi : IsOpenImmersion (U.f (U.idx y)) := U.map_prop _
  let φ : CommRingCat.of O ⟶ U.X (U.idx y) := Spec.preimage (U.f (U.idx y) ≫ f)
  have hφ : Spec.map φ = U.f (U.idx y) ≫ f := Spec.map_preimage _
  have he : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hE : φ.hom.Etale := HasRingHomProperty.Spec_iff.mp he
  letI : Algebra O (U.X (U.idx y)) := φ.hom.toAlgebra
  haveI : Algebra.Etale O (U.X (U.idx y)) := hE
  have h1 : (Spec.map φ).base x = (⟨IsLocalRing.maximalIdeal O, inferInstance⟩ : PrimeSpectrum O) := by
    rw [hφ]
    change f (U.f (U.idx y) x) = _
    rw [hx, hy]
  let p : PrimeSpectrum (U.X (U.idx y)) := x
  obtain ⟨s, hs⟩ := (GlobalTheory.T.exists_etale_section_iff_henselian_and_isSepClosed O).mpr ⟨inferInstance, inferInstance⟩ (U.X (U.idx y)) p.asIdeal
    (congrArg PrimeSpectrum.asIdeal h1)
  refine ⟨Spec.map (CommRingCat.ofHom s.toRingHom) ≫ U.f (U.idx y), ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  exact s.commutes a

/- English proof (translation)
Introduce `R _ O _ hO F n hn`. Take `⟨_, _⟩` from `hO`. Use `subsingleton_of_forall_eq 0 fun x => ?_` and prove the remaining obligations. Take `⟨Y, f, hf, hsurj, hx⟩` from `GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover R _ F n hn x`. Take `⟨s, hs⟩` from `exists_section_of_etale O f`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hs, sch.map_id, pull_id]`. Use `_ = 0 := by`. Rewrite using `[sch.map_comp, pull_comp, hx, map_zero]`.
-/
theorem UpperTheory.cohomology_subsingleton_pos_of_strictly_henselian :
    ∀ (R : Type) [CommRing R] (O : Type) [CommRing O], SH O → ∀ (F : Shv R) (n : ℤ), 0 < n → Subsingleton (H R (sp O) F n) := by
  intro R _ O _ hO F n hn
  obtain ⟨_, _⟩ := hO
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨Y, f, hf, hsurj, hx⟩ := GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover R _ F n hn x
  obtain ⟨s, hs⟩ := exists_section_of_etale O f
  calc x = pull R (sch.map (s ≫ f)) F n x := by
        rw [hs, sch.map_id, pull_id]
    _ = 0 := by
        rw [sch.map_comp, pull_comp, hx, map_zero]
