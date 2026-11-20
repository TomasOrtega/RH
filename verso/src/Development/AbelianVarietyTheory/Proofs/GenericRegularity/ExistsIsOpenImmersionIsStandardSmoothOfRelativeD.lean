import Mathlib

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

/- English proof (translation)
Take `⟨g, hg⟩` from `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d K B`. Use `letI : Algebra (MvPolynomial (Fin d) K) B := g.toRingHom.toAlgebra`. Use `haveI : Algebra.Etale (MvPolynomial (Fin d) K) B := hg`. Use `haveI : IsScalarTower K (MvPolynomial (Fin d) K) B := IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm`. Use `haveI : Algebra.FiniteType K B := .trans (S := MvPolynomial (Fin d) K) inferInstance inferInstance`.

Use `⟨.comp K B _, ?_⟩` and prove the remaining obligations. Take `⟨q, hqp, hq, hqo⟩` from `Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal (MvPolynomial (Fin d) K))) (q := p.under (MvPolynomial (Fin d) K)) p bot_le`. Take `rfl` from `hp q hq hqp`. Use `haveI : FaithfulSMul (MvPolynomial (Fin d) K) q.ResidueField := by`. Rewrite using `[faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]`.

Introduce `a ha`. Rewrite `ha` using `[IsScalarTower.algebraMap_apply _ B, Ideal.algebraMap_residueField_eq_zero]`. Establish `: a ∈ q.under (MvPolynomial (Fin d) K)` using `ha`. Rewrite `this` using `[← hqo.over]`. Then use the resulting hypothesis. Use `haveI : Algebra.IsAlgebraic (MvPolynomial (Fin d) K) q.ResidueField := by`.

Set `` to `Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal (MvPolynomial (Fin d) K)) q`. Establish `: Module.Finite (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField q.ResidueField` using `inferInstance`. Establish `: Algebra.IsAlgebraic (MvPolynomial (Fin d) K) (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField` using `IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (Fin d) K))`. Conclude with `Algebra.IsAlgebraic.trans _ (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField _`. Rewrite using `[← trdeg_add_eq K (MvPolynomial (Fin d) K), MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero]`.

Simplify using the standard rewrite rules.
-/
theorem residueField_fg_trdeg_of_isStandardSmoothOfRelativeDimension {K B : Type} [Field K]
    [CommRing B] [Algebra K B] (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d K B]
    (p : Ideal B) [p.IsPrime] (hp : ∀ q : Ideal B, q.IsPrime → q ≤ p → q = p) :
    Algebra.EssFiniteType K p.ResidueField ∧ Algebra.trdeg K p.ResidueField = d := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d K B
  letI : Algebra (MvPolynomial (Fin d) K) B := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) K) B := hg
  haveI : IsScalarTower K (MvPolynomial (Fin d) K) B :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  haveI : Algebra.FiniteType K B := .trans (S := MvPolynomial (Fin d) K) inferInstance inferInstance
  refine ⟨.comp K B _, ?_⟩
  obtain ⟨q, hqp, hq, hqo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := (⊥ : Ideal (MvPolynomial (Fin d) K))) (q := p.under (MvPolynomial (Fin d) K)) p bot_le
  obtain rfl := hp q hq hqp
  haveI : FaithfulSMul (MvPolynomial (Fin d) K) q.ResidueField := by
    rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
    intro a ha
    rw [IsScalarTower.algebraMap_apply _ B, Ideal.algebraMap_residueField_eq_zero] at ha
    have : a ∈ q.under (MvPolynomial (Fin d) K) := ha
    rwa [← hqo.over] at this
  haveI : Algebra.IsAlgebraic (MvPolynomial (Fin d) K) q.ResidueField := by
    let := Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal (MvPolynomial (Fin d) K)) q
    have : Module.Finite (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField q.ResidueField :=
      inferInstance
    have : Algebra.IsAlgebraic (MvPolynomial (Fin d) K)
        (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField :=
      IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (Fin d) K))
    exact Algebra.IsAlgebraic.trans _ (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField _
  rw [← trdeg_add_eq K (MvPolynomial (Fin d) K), MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero]
  simp

/- English proof (translation)
Take `⟨A, j, hj, ⟨y, rfl⟩, -⟩` from `Scheme.exists_affine_mem_range_and_range_subset (x := x) (U := ⊤) trivial`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (j ≫ f)`. Establish `h : SmoothOfRelativeDimension (0 + d) (j ≫ f)` using `inferInstance`. Rewrite `h` using `[zero_add, ← hφ]`. Take `⟨s, hs, h'⟩` from `(HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).1 h`.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht, hty⟩ : ∃ t ∈ s, t ∉ y.asIdeal := by`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Conclude with `y.isPrime.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hne))`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : y ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away t))) := by`.

Rewrite using `[PrimeSpectrum.localization_away_comap_range _ t]`. Conclude with `hty`. Use `⟨.of (Localization.Away t), φ ≫ CommRingCat.ofHom (algebraMap A (Localization.Away t)), Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away t))) ≫ j, inferInstance, z, ?_, ?_, h' t ht⟩` and prove the remaining obligations. Rewrite using `[← hz]`. Both sides reduce to the same expression.

Rewrite using `[Category.assoc, ← hφ, Spec.map_comp]`.
-/
theorem exists_isOpenImmersion_isStandardSmoothOfRelativeDimension {K : Type} [Field K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (hf : SmoothOfRelativeDimension d f) (x : X) :
    ∃ (B : CommRingCat.{0}) (φ : CommRingCat.of K ⟶ B) (j : Spec B ⟶ X) (_ : IsOpenImmersion j)
      (y : Spec B), j y = x ∧ j ≫ f = Spec.map φ ∧
        φ.hom.IsStandardSmoothOfRelativeDimension d := by
  obtain ⟨A, j, hj, ⟨y, rfl⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x) (U := ⊤) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ f)
  have h : SmoothOfRelativeDimension (0 + d) (j ≫ f) := inferInstance
  rw [zero_add, ← hφ] at h
  obtain ⟨s, hs, h'⟩ := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).1 h
  obtain ⟨t, ht, hty⟩ : ∃ t ∈ s, t ∉ y.asIdeal := by
    by_contra hne
    push Not at hne
    exact y.isPrime.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hne))
  obtain ⟨z, hz⟩ : y ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away t))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ t]
    exact hty
  refine ⟨.of (Localization.Away t), φ ≫ CommRingCat.ofHom (algebraMap A (Localization.Away t)),
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away t))) ≫ j, inferInstance, z,
    ?_, ?_, h' t ht⟩
  · rw [← hz]; rfl
  · rw [Category.assoc, ← hφ, Spec.map_comp]

/- English proof (translation)
Take `⟨B, φ, j, hj, y, rfl, hjf, hφ⟩` from `exists_isOpenImmersion_isStandardSmoothOfRelativeDimension f d hf x`. Use `letI : Algebra K (X.residueField (j y)) := (Spec.preimage (X.fromSpecResidueField (j y) ≫ f)).hom.toAlgebra`. Use `letI : Algebra K B := φ.hom.toAlgebra`. Use `haveI : y.asIdeal.IsPrime := y.isPrime`. Use `haveI : Algebra.IsStandardSmoothOfRelativeDimension d K B := hφ`.

Take `⟨h1, h2⟩` from `residueField_fg_trdeg_of_isStandardSmoothOfRelativeDimension (K := K) d y.asIdeal (fun q hq hqy => by`. Establish `hs : (⟨q, hq⟩ : PrimeSpectrum B) ⤳ y` using `(PrimeSpectrum.le_iff_specializes _ _).mp hqy`. Use `j.isOpenEmbedding.injective (hx _ (hs.map j.continuous))` as an intermediate fact. Conclude with `congrArg PrimeSpectrum.asIdeal this)`. Set `e : X.residueField (j y) ≅ CommRingCat.of y.asIdeal.ResidueField` to `asIso (j.residueFieldMap y) ≪≫ Scheme.Spec.residueFieldIso B y`.

Establish `he : Spec.preimage (X.fromSpecResidueField (j y) ≫ f) ≫ e.hom = φ ≫ CommRingCat.ofHom (algebraMap B y.asIdeal.ResidueField)`. Rewrite using `[← Spec.map_inj, ← cancel_epi (Spec.map (Scheme.Spec.residueFieldIso B y).inv)]`. Simplify using `only [e, Iso.trans_hom, asIso_hom, Spec.map_comp, Spec.map_preimage, Category.assoc, Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField_assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, hjf]`. Rewrite using `[← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]`. Set `e' : X.residueField (j y) ≃ₐ[K] y.asIdeal.ResidueField` to `{ e.commRingCatIsoToRingEquiv with commutes' := fun a => congr($(he).hom a) }`.

Use `⟨IntermediateField.fg_top_iff.mpr ?_, ?_⟩` and prove the remaining obligations. Conclude with `Algebra.EssFiniteType.of_surjective e'.symm.toAlgHom e'.symm.surjective`. Rewrite using `[e'.trdeg_eq, h2]`.
-/
theorem residueField_fg_trdeg_of_smoothOfRelativeDimension {K : Type} [Field K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (hf : SmoothOfRelativeDimension d f) (x : X) (hx : ∀ y : X, y ⤳ x → y = x) :
    letI : Algebra K (X.residueField x) :=
      (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
    (⊤ : IntermediateField K (X.residueField x)).FG ∧ Algebra.trdeg K (X.residueField x) = d := by
  obtain ⟨B, φ, j, hj, y, rfl, hjf, hφ⟩ :=
    exists_isOpenImmersion_isStandardSmoothOfRelativeDimension f d hf x
  letI : Algebra K (X.residueField (j y)) :=
    (Spec.preimage (X.fromSpecResidueField (j y) ≫ f)).hom.toAlgebra
  letI : Algebra K B := φ.hom.toAlgebra
  haveI : y.asIdeal.IsPrime := y.isPrime
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d K B := hφ
  obtain ⟨h1, h2⟩ := residueField_fg_trdeg_of_isStandardSmoothOfRelativeDimension (K := K) d
    y.asIdeal (fun q hq hqy => by
      have hs : (⟨q, hq⟩ : PrimeSpectrum B) ⤳ y := (PrimeSpectrum.le_iff_specializes _ _).mp hqy
      have := j.isOpenEmbedding.injective (hx _ (hs.map j.continuous))
      exact congrArg PrimeSpectrum.asIdeal this)
  let e : X.residueField (j y) ≅ CommRingCat.of y.asIdeal.ResidueField :=
    asIso (j.residueFieldMap y) ≪≫ Scheme.Spec.residueFieldIso B y
  have he : Spec.preimage (X.fromSpecResidueField (j y) ≫ f) ≫ e.hom =
      φ ≫ CommRingCat.ofHom (algebraMap B y.asIdeal.ResidueField) := by
    rw [← Spec.map_inj, ← cancel_epi (Spec.map (Scheme.Spec.residueFieldIso B y).inv)]
    simp only [e, Iso.trans_hom, asIso_hom, Spec.map_comp, Spec.map_preimage, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField_assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, hjf]
    rw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  let e' : X.residueField (j y) ≃ₐ[K] y.asIdeal.ResidueField :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := fun a => congr($(he).hom a) }
  refine ⟨IntermediateField.fg_top_iff.mpr ?_, ?_⟩
  · exact Algebra.EssFiniteType.of_surjective e'.symm.toAlgHom e'.symm.surjective
  · rw [e'.trdeg_eq, h2]

/- English proof (translation)
Introduce `K _ X f d hf Z hZ`. Use `residueField_fg_trdeg_of_smoothOfRelativeDimension f d hf _ fun y hy => ?_` and prove the remaining obligations. Establish `hg` using `(hZ.1 : IsIrreducible Z).isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)`. Establish `h1 : Z ⊆ closure {y}`. Rewrite using `[← hg.def]`.

Conclude with `specializes_iff_closure_subset.mp hy`. Establish `h2 : closure {y} ⊆ Z` using `hZ.2 isIrreducible_singleton.closure h1`. Conclude with `(hy.antisymm (hg.specializes (h2 (subset_closure rfl)))).eq`.
-/
theorem residueField_genericPoint_fg_trdeg_of_smoothOfRelativeDimension :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ), SmoothOfRelativeDimension d f → ∀ (Z : Set X) (hZ : Z ∈ irreducibleComponents X), letI : Algebra K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint) := (Spec.preimage (X.fromSpecResidueField (hZ.1 : IsIrreducible Z).genericPoint ≫ f)).hom.toAlgebra; (⊤ : IntermediateField K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint)).FG ∧ Algebra.trdeg K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint) = d := by
  intro K _ X f d hf Z hZ
  refine residueField_fg_trdeg_of_smoothOfRelativeDimension f d hf _ fun y hy => ?_
  have hg := (hZ.1 : IsIrreducible Z).isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents Z hZ)
  have h1 : Z ⊆ closure {y} := by
    rw [← hg.def]
    exact specializes_iff_closure_subset.mp hy
  have h2 : closure {y} ⊆ Z := hZ.2 isIrreducible_singleton.closure h1
  exact (hy.antisymm (hg.specializes (h2 (subset_closure rfl)))).eq

end GlobalTheory
