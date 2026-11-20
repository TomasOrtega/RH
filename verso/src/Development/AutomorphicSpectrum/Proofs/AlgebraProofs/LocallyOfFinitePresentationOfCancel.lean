import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FinitePresentationOfFaithfullyFlatStatement

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.LfpDescent

/- English proof (translation)
Rewrite using `[HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]`. Establish `h1 : q.appTop.hom.Finite` using `Scheme.Hom.finite_appTop q`. Establish `h2 : q.appTop.hom.FaithfullyFlat` using `(Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).1 ⟨inferInstance, inferInstance⟩`. Establish `h3 : q.appTop.hom.FinitePresentation` using `(HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).1 inferInstance`. Establish `h4 : (q.appTop.hom.comp f.appTop.hom).FinitePresentation`.

Use `(HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).1 (inferInstance : LocallyOfFinitePresentation (q ≫ f))` as an intermediate fact. Rewrite `this` using `[Scheme.Hom.comp_appTop, CommRingCat.hom_comp]`. Then use the resulting hypothesis. Use `letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra`. Use `letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra`. Use `letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (q.appTop.hom.comp f.appTop.hom).toAlgebra`.

Use `haveI : IsScalarTower Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤) := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := h1`. Use `haveI : Algebra.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) := h3`. Use `haveI : Module.FaithfullyFlat Γ(Y, ⊤) Γ(X, ⊤) := h2`. Use `haveI : Module.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) := Module.FinitePresentation.of_finite_of_finitePresentation _ _`.

Establish `hp : Module.Projective Γ(Y, ⊤) Γ(X, ⊤)` using `Module.Flat.projective_of_finitePresentation`. Conclude with `GlobalTheory.T.finitePresentation_of_faithfully_flat _ _ _ inferInstance hp inferInstance h4`.
-/
lemma affine_case {X Y S : Scheme.{0}} [IsAffine X] [IsAffine Y] [IsAffine S] (q : X ⟶ Y)
    (f : Y ⟶ S) [IsFinite q] [Flat q] [LocallyOfFinitePresentation q] [Surjective q]
    [LocallyOfFinitePresentation (q ≫ f)] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  have h1 : q.appTop.hom.Finite :=
    Scheme.Hom.finite_appTop q
  have h2 : q.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).1 ⟨inferInstance, inferInstance⟩
  have h3 : q.appTop.hom.FinitePresentation :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).1 inferInstance
  have h4 : (q.appTop.hom.comp f.appTop.hom).FinitePresentation := by
    have := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).1
      (inferInstance : LocallyOfFinitePresentation (q ≫ f))
    rwa [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at this
  letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (q.appTop.hom.comp f.appTop.hom).toAlgebra
  haveI : IsScalarTower Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := h1
  haveI : Algebra.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) := h3
  haveI : Module.FaithfullyFlat Γ(Y, ⊤) Γ(X, ⊤) := h2
  haveI : Module.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  have hp : Module.Projective Γ(Y, ⊤) Γ(X, ⊤) := Module.Flat.projective_of_finitePresentation
  exact GlobalTheory.T.finitePresentation_of_faithfully_flat _ _ _ inferInstance hp inferInstance h4

/- English proof (translation)
Introduce `X Y S q f _ _ _ _ _`. Set `I` to `{p : S.affineOpens × Y.affineOpens // (p.2 : Y.Opens) ≤ f ⁻¹ᵁ (p.1 : S.Opens)}`. Use `haveI := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{0})`. Use `IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFinitePresentation.{0}) (fun i : I ↦ (i.1.2 : Y.Opens)) ?_ ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff]`.

Introduce and unpack `y -`. Take `⟨U, hU, hyU, -⟩` from `exists_isAffineOpen_mem_and_subset (x := f y) (U := ⊤) trivial`. Take `⟨V, hV, hyV, hVU⟩` from `exists_isAffineOpen_mem_and_subset (x := y) (U := f ⁻¹ᵁ U) hyU`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hVU⟩, hyV⟩`. Introduce and unpack `⟨⟨⟨U, hU⟩, ⟨V, hV⟩⟩, e⟩ dsimp only at e ⊢ haveI : IsAffine U.toScheme := hU haveI : IsAffine V.toScheme := hV haveI : IsAffine (q ⁻¹ᵁ V).toScheme := (hV.preimage q)`.

Establish `hc : (q ∣_ V) ≫ f.resLE U V e = (q ≫ f).resLE U (q ⁻¹ᵁ V) (by simpa using (Scheme.Hom.preimage_mono q e))`. Rewrite using `[← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]`. Use `haveI : LocallyOfFinitePresentation ((q ∣_ V) ≫ f.resLE U V e) := by`. Rewrite using `[hc]`. Use `delta Scheme.Hom.resLE`.

Use `infer_instance`. Use `haveI : Surjective (q ∣_ V) := IsZariskiLocalAtTarget.restrict ‹Surjective q› V`. Use `haveI : LocallyOfFinitePresentation (f.resLE U V e) := affine_case (q ∣_ V) _`. Rewrite using `[← Scheme.Hom.resLE_comp_ι f e]`. Use `infer_instance`.
-/
theorem descends : ∀ {X Y S : Scheme.{0}} (q : X ⟶ Y) (f : Y ⟶ S), IsFinite q → Flat q →
    LocallyOfFinitePresentation q → Surjective q → LocallyOfFinitePresentation (q ≫ f) →
    LocallyOfFinitePresentation f := by
  intro X Y S q f _ _ _ _ _
  let I := {p : S.affineOpens × Y.affineOpens // (p.2 : Y.Opens) ≤ f ⁻¹ᵁ (p.1 : S.Opens)}
  haveI := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{0})
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFinitePresentation.{0}) (fun i : I ↦ (i.1.2 : Y.Opens)) ?_ ?_
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := f y) (U := ⊤) trivial
    obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := f ⁻¹ᵁ U) hyU
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hVU⟩, hyV⟩
  · rintro ⟨⟨⟨U, hU⟩, ⟨V, hV⟩⟩, e⟩
    dsimp only at e ⊢
    haveI : IsAffine U.toScheme := hU
    haveI : IsAffine V.toScheme := hV
    haveI : IsAffine (q ⁻¹ᵁ V).toScheme := (hV.preimage q)
    have hc : (q ∣_ V) ≫ f.resLE U V e =
        (q ≫ f).resLE U (q ⁻¹ᵁ V) (by simpa using (Scheme.Hom.preimage_mono q e)) := by
      rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
    haveI : LocallyOfFinitePresentation ((q ∣_ V) ≫ f.resLE U V e) := by
      rw [hc]; delta Scheme.Hom.resLE; infer_instance
    haveI : Surjective (q ∣_ V) := IsZariskiLocalAtTarget.restrict ‹Surjective q› V
    haveI : LocallyOfFinitePresentation (f.resLE U V e) := affine_case (q ∣_ V) _
    rw [← Scheme.Hom.resLE_comp_ι f e]
    infer_instance

end GlobalTheory.CompanionTheory.LfpDescent
