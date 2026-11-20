import Development.EtaleCohomology.EtaleSheaves.ChowGraphCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.EmbedPf

def AffClosed : Prop := ∀ (A : Type) [CommRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A))
  [LocallyOfFiniteType p] (V : X.Opens), IsAffineOpen V →
    ∃ (n : ℕ) (e : V.toScheme ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) A))), IsClosedImmersion e ∧
      e ≫ Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A))) = V.ι ≫ p

def Chart : Prop := ∀ (A : Type) [CommRing A] (n : ℕ), ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of A))
  (j : Spec (CommRingCat.of (MvPolynomial (Fin n) A)) ⟶ P), IterLine q ∧ IsOpenImmersion j ∧
    j ≫ q = Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)))

/- English proof (translation)
Introduce `A _ X p _ V hV`. Use `haveI : IsAffine V.toScheme := hV`. Establish `hfT : LocallyOfFiniteType (V.ι ≫ p)` using `inferInstance`. Establish `happ` using `HasRingHomProperty.appTop @LocallyOfFiniteType (V.ι ≫ p) hfT`. Set `g : CommRingCat.of A ⟶ Γ(V.toScheme, ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (V.ι ≫ p).appTop`.

Establish `hg : g.hom.FiniteType`. Establish `h1 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.FiniteType` using `RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2`. Conclude with `RingHom.FiniteType.comp happ h1`. Use `letI : Algebra A Γ(V.toScheme, ⊤) := g.hom.toAlgebra`. Establish `hft : Algebra.FiniteType A Γ(V.toScheme, ⊤)` using `hg`.

Take `⟨n, φ, hφ⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft`. Use `⟨n, V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom), ?_, ?_⟩` and prove the remaining obligations. Establish `hs` using `IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ.toRingHom) hφ`. Establish `hi : IsClosedImmersion V.toScheme.toSpecΓ` using `inferInstance`. Conclude with `@IsClosedImmersion.comp _ _ _ _ _ hi hs`.

Establish `hcomp : CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)) ≫ CommRingCat.ofHom φ.toRingHom = g`. Use extensionality with `a`. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]`. Conclude with `φ.commutes a`. Establish `h2 : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A))) = Spec.map g` using `by rw [← Spec.map_comp, hcomp]`.

Establish `h3 : V.toScheme.toSpecΓ ≫ Spec.map g = V.ι ≫ p`. Establish `hn` using `Scheme.toSpecΓ_naturality (V.ι ≫ p)`. Establish `h4 : Spec.map g = Spec.map (V.ι ≫ p).appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv` using `Spec.map_comp _ _`. Rewrite using `[h4, ← Category.assoc, ← hn, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]`. Use `Eq.trans ?_ h3` and prove the remaining obligations.

Rewrite using `[Category.assoc]`. Conclude with `congrArg (fun t => V.toScheme.toSpecΓ ≫ t) h2`.
-/
theorem affClosed : AffClosed := by
  intro A _ X p _ V hV
  haveI : IsAffine V.toScheme := hV
  have hfT : LocallyOfFiniteType (V.ι ≫ p) := inferInstance
  have happ := HasRingHomProperty.appTop @LocallyOfFiniteType (V.ι ≫ p) hfT
  let g : CommRingCat.of A ⟶ Γ(V.toScheme, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (V.ι ≫ p).appTop
  have hg : g.hom.FiniteType := by
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact RingHom.FiniteType.comp happ h1
  letI : Algebra A Γ(V.toScheme, ⊤) := g.hom.toAlgebra
  have hft : Algebra.FiniteType A Γ(V.toScheme, ⊤) := hg
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  refine ⟨n, V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom), ?_, ?_⟩
  · have hs := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ.toRingHom) hφ
    have hi : IsClosedImmersion V.toScheme.toSpecΓ := inferInstance
    exact @IsClosedImmersion.comp _ _ _ _ _ hi hs
  · have hcomp : CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)) ≫ CommRingCat.ofHom φ.toRingHom = g := by
      ext a
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
      exact φ.commutes a
    have h2 : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A))) =
        Spec.map g := by rw [← Spec.map_comp, hcomp]
    have h3 : V.toScheme.toSpecΓ ≫ Spec.map g = V.ι ≫ p := by
      have hn := Scheme.toSpecΓ_naturality (V.ι ≫ p)
      have h4 : Spec.map g = Spec.map (V.ι ≫ p).appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv :=
        Spec.map_comp _ _
      rw [h4, ← Category.assoc, ← hn, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    refine Eq.trans ?_ h3
    rw [Category.assoc]
    exact congrArg (fun t => V.toScheme.toSpecΓ ≫ t) h2

/- English proof (translation)
Introduce `A _ X p _ V hV`. Take `⟨n, e, he, hep⟩` from `hA A p V hV`. Take `⟨P, q, j, hq, hj, hjq⟩` from `hC A n`. Use `haveI := hj`. Use `haveI := he`.

Use `⟨P, q, j.opensRange, e ≫ j.isoOpensRange.hom, hq, inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, hjq, hep]`.
-/
theorem Embed_of (hA : AffClosed) (hC : Chart) : LateralTheory.E.ChowGraphCut.Embed := by
  intro A _ X p _ V hV
  obtain ⟨n, e, he, hep⟩ := hA A p V hV
  obtain ⟨P, q, j, hq, hj, hjq⟩ := hC A n
  haveI := hj
  haveI := he
  refine ⟨P, q, j.opensRange, e ≫ j.isoOpensRange.hom, hq, inferInstance, ?_⟩
  rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, hjq, hep]

end LateralTheory.E.EmbedPf
