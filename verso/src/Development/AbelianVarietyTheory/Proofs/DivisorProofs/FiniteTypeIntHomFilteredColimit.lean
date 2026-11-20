import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

/- English proof (translation)
Introduce `A hA J _ _ D c hc`. Set `R : CommRingCat.{0}` to `CommRingCat.of ℤ`. Set `f : R ⟶ A` to `CommRingCat.ofHom (Int.castRingHom A)`. Set `α : (Functor.const J).obj R ⟶ D` to `{ app := fun i => CommRingCat.ofHom (Int.castRingHom (D.obj i)) naturality := by`. Introduce `i j g`.

Use `ext1`. Conclude with `RingHom.ext_int _ _ }`. Establish `hfp : f.hom.FinitePresentation`. Establish `h1 : Algebra.FinitePresentation ℤ A` using `Algebra.FinitePresentation.of_finiteType.mp hA`. Establish `e : f.hom.toAlgebra = (inferInstance : Algebra ℤ A)` using `Subsingleton.elim _ _`.

Unfold `RingHom.FinitePresentation`. Rewrite using `[e]`. Conclude with `h1`. Establish `hft : f.hom.FiniteType`. Establish `e : f.hom.toAlgebra = (inferInstance : Algebra ℤ A)` using `Subsingleton.elim _ _`.

Unfold `RingHom.FiniteType`. Rewrite using `[e]`. Conclude with `hA`. Establish `hR : ∀ {X : CommRingCat.{0}} (u v : R ⟶ X), u = v`. Introduce `X u v`.

Use `ext1`. Conclude with `RingHom.ext_int _ _`. Use `⟨fun φ => ?_, fun j ψ ψ' h => ?_⟩` and prove the remaining obligations. Take `⟨i, g', -, hg'⟩` from `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R D α f c hc hfp φ (fun i => hR _ _)`. Conclude with `⟨i, g', hg'.symm⟩`.

Take `⟨k, hik, hjk, e⟩` from `RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit R D α f c hc hft.essFiniteType ψ (hR _ _) ψ' (hR _ _) h`. Use `⟨IsFiltered.coeq hik hjk, hik ≫ IsFiltered.coeqHom hik hjk, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[D.map_comp, Category.assoc]`. Use `_ = (ψ' ≫ D.map hjk) ≫ D.map (IsFiltered.coeqHom hik hjk) := by rw [e]`.

Use `_ = ψ' ≫ D.map (hjk ≫ IsFiltered.coeqHom hik hjk) := by`. Rewrite using `[D.map_comp, Category.assoc]`. Use `_ = ψ' ≫ D.map (hik ≫ IsFiltered.coeqHom hik hjk) := by`. Rewrite using `[IsFiltered.coeq_condition]`.
-/
theorem finiteType_int_hom_filteredColimit :
    ∀ (A : CommRingCat.{0}), Algebra.FiniteType ℤ A → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
      (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c →
      (∀ φ : A ⟶ c.pt, ∃ (j : J) (ψ : A ⟶ D.obj j), ψ ≫ c.ι.app j = φ) ∧
      ∀ (j : J) (ψ ψ' : A ⟶ D.obj j), ψ ≫ c.ι.app j = ψ' ≫ c.ι.app j →
        ∃ (k : J) (f : j ⟶ k), ψ ≫ D.map f = ψ' ≫ D.map f := by
  intro A hA J _ _ D c hc
  let R : CommRingCat.{0} := CommRingCat.of ℤ
  let f : R ⟶ A := CommRingCat.ofHom (Int.castRingHom A)
  let α : (Functor.const J).obj R ⟶ D :=
    { app := fun i => CommRingCat.ofHom (Int.castRingHom (D.obj i))
      naturality := by
        intro i j g
        ext1
        exact RingHom.ext_int _ _ }
  have hfp : f.hom.FinitePresentation := by
    have h1 : Algebra.FinitePresentation ℤ A := Algebra.FinitePresentation.of_finiteType.mp hA
    have e : f.hom.toAlgebra = (inferInstance : Algebra ℤ A) := Subsingleton.elim _ _
    unfold RingHom.FinitePresentation
    rw [e]
    exact h1
  have hft : f.hom.FiniteType := by
    have e : f.hom.toAlgebra = (inferInstance : Algebra ℤ A) := Subsingleton.elim _ _
    unfold RingHom.FiniteType
    rw [e]
    exact hA
  have hR : ∀ {X : CommRingCat.{0}} (u v : R ⟶ X), u = v := by
    intro X u v
    ext1
    exact RingHom.ext_int _ _
  refine ⟨fun φ => ?_, fun j ψ ψ' h => ?_⟩
  · obtain ⟨i, g', -, hg'⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R D α f c hc
      hfp φ (fun i => hR _ _)
    exact ⟨i, g', hg'.symm⟩
  · obtain ⟨k, hik, hjk, e⟩ := RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit R D α f c hc
      hft.essFiniteType ψ (hR _ _) ψ' (hR _ _) h
    refine ⟨IsFiltered.coeq hik hjk, hik ≫ IsFiltered.coeqHom hik hjk, ?_⟩
    calc ψ ≫ D.map (hik ≫ IsFiltered.coeqHom hik hjk)
        = (ψ ≫ D.map hik) ≫ D.map (IsFiltered.coeqHom hik hjk) := by
          rw [D.map_comp, Category.assoc]
      _ = (ψ' ≫ D.map hjk) ≫ D.map (IsFiltered.coeqHom hik hjk) := by rw [e]
      _ = ψ' ≫ D.map (hjk ≫ IsFiltered.coeqHom hik hjk) := by
          rw [D.map_comp, Category.assoc]
      _ = ψ' ≫ D.map (hik ≫ IsFiltered.coeqHom hik hjk) := by
          rw [IsFiltered.coeq_condition]

end GlobalTheory
