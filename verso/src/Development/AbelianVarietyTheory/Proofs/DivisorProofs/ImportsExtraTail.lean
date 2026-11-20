import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FactorAndSection

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Establish `hmem : ∀ a : A, ψ a ∈ (algebraMap R K).range`. Introduce `a`. Establish `h1 : (ψ.comp φ).IsIntegralElem (ψ a)` using `(hφ a).map ψ`. Rewrite `h1` using `[h]`.

Conclude with `(IsIntegrallyClosed.isIntegral_iff (R := R) (K := K)).1 h1`. Set `e : R ≃+* (algebraMap R K).range` to `RingEquiv.ofBijective (algebraMap R K).rangeRestrict ⟨fun a b hab => hinj (congrArg Subtype.val hab), (algebraMap R K).rangeRestrict_surjective⟩`. Establish `he : ∀ z : (algebraMap R K).range, algebraMap R K (e.symm z) = z.1` using `fun z => congrArg Subtype.val (e.apply_symm_apply z)`. Establish `h1 : (algebraMap R K).comp (e.symm.toRingHom.comp (ψ.codRestrict _ hmem)) = ψ`. Use extensionality with `a`.

Conclude with `he _`. Use `⟨e.symm.toRingHom.comp (ψ.codRestrict _ hmem), h1, ?_⟩` and prove the remaining obligations. Use extensionality with `r`. Apply `hinj` to reduce the goal to its premises. Establish `h2` using `congrArg (fun f : A →+* K => f (φ r)) h1`.

Establish `h3` using `congrArg (fun f : R →+* K => f r) h`. Conclude with `h2.trans h3`.
-/
theorem exists_factor {R K A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] (φ : R →+* A) (hφ : φ.IsIntegral) (ψ : A →+* K)
    (h : ψ.comp φ = algebraMap R K) : ∃ χ : A →+* R, (algebraMap R K).comp χ = ψ ∧ χ.comp φ = RingHom.id R := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmem : ∀ a : A, ψ a ∈ (algebraMap R K).range := by
    intro a
    have h1 : (ψ.comp φ).IsIntegralElem (ψ a) := (hφ a).map ψ
    rw [h] at h1
    exact (IsIntegrallyClosed.isIntegral_iff (R := R) (K := K)).1 h1
  let e : R ≃+* (algebraMap R K).range := RingEquiv.ofBijective (algebraMap R K).rangeRestrict
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), (algebraMap R K).rangeRestrict_surjective⟩
  have he : ∀ z : (algebraMap R K).range, algebraMap R K (e.symm z) = z.1 := fun z =>
    congrArg Subtype.val (e.apply_symm_apply z)
  have h1 : (algebraMap R K).comp (e.symm.toRingHom.comp (ψ.codRestrict _ hmem)) = ψ := by
    ext a
    exact he _
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict _ hmem), h1, ?_⟩
  ext r
  apply hinj
  have h2 := congrArg (fun f : A →+* K => f (φ r)) h1
  have h3 := congrArg (fun f : R →+* K => f r) h
  exact h2.trans h3

/- English proof (translation)
Use `haveI : IsAffine Z := isAffine_of_isAffineHom p`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (Z.isoSpec.inv ≫ p)`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (y ≫ Z.isoSpec.hom)`. Establish `hfin : IsFinite (Spec.map φ)` using `by rw [hφ]; infer_instance`. Establish `hint : φ.hom.IsIntegral` using `((IsFinite.SpecMap_iff φ).1 hfin).to_isIntegral`.

Establish `hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hy]`. Take `⟨χ, h1, h2⟩` from `exists_factor (R := R) (K := K) φ.hom hint ψ.hom (congrArg CommRingCat.Hom.hom hc)`. Establish `h1' : CommRingCat.ofHom χ ≫ CommRingCat.ofHom (algebraMap R K) = ψ` using `CommRingCat.hom_ext h1`.

Establish `h2' : φ ≫ CommRingCat.ofHom χ = 𝟙 _` using `CommRingCat.hom_ext h2`. Use `⟨Spec.map (CommRingCat.ofHom χ) ≫ Z.isoSpec.inv, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Spec.map_comp, h1', hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Rewrite using `[Category.assoc, ← hφ, ← Spec.map_comp, h2', Spec.map_id]`.
-/
theorem exists_section {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {Z : Scheme.{0}} (p : Z ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) [IsFinite p]
    (y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ Z) (hy : y ≫ p = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) :
    ∃ x : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Z,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K) ≫ x = y ∧ x ≫ p = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) := by
  haveI : IsAffine Z := isAffine_of_isAffineHom p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ p)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (y ≫ Z.isoSpec.hom)
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hint : φ.hom.IsIntegral := ((IsFinite.SpecMap_iff φ).1 hfin).to_isIntegral
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hy]
  obtain ⟨χ, h1, h2⟩ := exists_factor (R := R) (K := K) φ.hom hint ψ.hom (congrArg CommRingCat.Hom.hom hc)
  have h1' : CommRingCat.ofHom χ ≫ CommRingCat.ofHom (algebraMap R K) = ψ := CommRingCat.hom_ext h1
  have h2' : φ ≫ CommRingCat.ofHom χ = 𝟙 _ := CommRingCat.hom_ext h2
  refine ⟨Spec.map (CommRingCat.ofHom χ) ≫ Z.isoSpec.inv, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, h1', hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, h2', Spec.map_id]

end GlobalTheory.FactorAndSection
