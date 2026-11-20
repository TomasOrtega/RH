import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.CohomologicalPurity.Thom

namespace HtpyOnePf

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pull_bij_of_iso {R : Type} [CommRing R] (F : Shv R) {E E' : Spc} (a : E ⟶ E') [IsIso a] (n : ℤ) :
    Function.Bijective (pull R a F n) :=
  Function.bijective_iff_has_inverse.2 ⟨pull R (inv a) F n,
    fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id],
    fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eqv_of_sq {R : Type} [CommRing R] (F : Shv R) {E1 E2 E3 E4 : Spc} (f : E1 ⟶ E2) (g : E3 ⟶ E4)
    (a : E3 ⟶ E1) (b : E4 ⟶ E2) [IsIso a] [IsIso b] (w : a ≫ f = g ≫ b) (hg : Eqv R g F) : Eqv R f F := by
  intro n
  have h1 : (pull R a F n) ∘ (pull R f F n) = (pull R g F n) ∘ (pull R b F n) := by
    funext x; simp only [Function.comp_apply]; rw [← pull_comp, ← pull_comp, w]
  have h2 : Function.Bijective ((pull R a F n) ∘ (pull R f F n)) := by
    rw [h1]; exact (hg n).comp (pull_bij_of_iso F b n)
  exact (Function.Bijective.of_comp_iff' (pull_bij_of_iso F a n) _).1 h2

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem off_span (A : Type) [CommRing A] (x : A) :
    off A (Ideal.span {x}) = PrimeSpectrum.basicOpen x := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus ((Ideal.span {x} : Ideal A) : Set A))ᶜ = _
  rw [PrimeSpectrum.zeroLocus_span]; exact (PrimeSpectrum.basicOpen_eq_zeroLocus_compl x).symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem off_span_C (A : Type) [CommRing A] (x : A) :
    off (Polynomial A) ((Ideal.span {x}).map Polynomial.C) = PrimeSpectrum.basicOpen (C x) := by
  rw [Ideal.map_span, Set.image_singleton]; exact off_span _ _

attribute [local instance] Polynomial.algebra in
/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem away_poly (A : Type) [CommRing A] (x : A) :
    IsLocalization.Away (C x) (Polynomial (Localization.Away x)) := by
  have := Polynomial.isLocalization (Submonoid.powers x) (Localization.Away x)
  rw [Submonoid.map_powers] at this
  exact this

/- English proof (translation)
Equip the data with the indicated structure. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem sq (A : Type) [CommRing A] (x : A)
    (h : off (Polynomial A) ((Ideal.span {x}).map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A (Ideal.span {x})) :
    ∃ (eT : Spec (CommRingCat.of (Polynomial (Localization.Away x))) ≅
        (off (Polynomial A) ((Ideal.span {x}).map Polynomial.C)).toScheme)
      (eB : Spec (CommRingCat.of (Localization.Away x)) ≅ (off A (Ideal.span {x})).toScheme),
      eT.hom ≫ (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h =
        Spec.map (CommRingCat.ofHom (Polynomial.C : Localization.Away x →+* _)) ≫ eB.hom := by
  letI : Algebra (Polynomial A) (Polynomial (Localization.Away x)) := Polynomial.algebra A (Localization.Away x)
  have := away_poly A x
  let jB := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))
  let jT := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial A) (Polynomial (Localization.Away x))))
  have : IsOpenImmersion jT := IsOpenImmersion.of_isLocalization (C x)
  have rB : Set.range jB = Set.range (off A (Ideal.span {x})).ι := by
    rw [Scheme.Opens.range_ι, off_span]
    exact PrimeSpectrum.localization_away_comap_range _ x
  have rT : Set.range jT = Set.range (off (Polynomial A) ((Ideal.span {x}).map Polynomial.C)).ι := by
    rw [Scheme.Opens.range_ι, off_span_C]
    exact PrimeSpectrum.localization_away_comap_range _ (C x)
  refine ⟨IsOpenImmersion.isoOfRangeEq jT _ rT, IsOpenImmersion.isoOfRangeEq jB _ rB, ?_⟩
  rw [← cancel_mono (off A (Ideal.span {x})).ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
  simp only [jT, jB, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a : 2
  simp [Polynomial.algebraMap_def]

end HtpyOnePf

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities.
-/
theorem LeafHtpyOne_of : LeafHtpyOne := by
  intro _ c4 q _ A _ x hq h i
  obtain ⟨eT, eB, w⟩ := HtpyOnePf.sq A x h
  have hqB : IsUnit ((q : ℕ) : Localization.Away x) := by
    simpa using hq.map (algebraMap A (Localization.Away x))
  refine HtpyOnePf.eqv_of_sq _ _ (sch.map (Spec.map (CommRingCat.ofHom (Polynomial.C : Localization.Away x →+* _))))
    (sch.map eT.hom) (sch.map eB.hom) ?_ (c4 q (Localization.Away x) hqB i)
  rw [← Functor.map_comp, ← Functor.map_comp, w]

end LateralTheory.CohomologicalPurity.Thom
