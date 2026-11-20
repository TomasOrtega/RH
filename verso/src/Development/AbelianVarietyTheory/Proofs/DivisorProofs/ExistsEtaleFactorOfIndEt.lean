import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `A O _ _ _ hO B _ _ _ φ`. Take `⟨J, _, _, D, t, s, hs, hst⟩` from `hO`. Establish `hp : MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0} (CommRingCat.ofHom (algebraMap A B))` using `CommRingCat.isFinitelyPresentable_hom _ (RingHom.finitePresentation_algebraMap.2 inferInstance)`. Take `⟨j, q, hq1, hq2⟩` from `MorphismProperty.exists_hom_of_isFinitelyPresentable hs hp t (CommRingCat.ofHom φ.toRingHom) (fun j => by`. Rewrite using `[(hst j).2]`.

Use extensionality with `a`. Use the proof step `simp)`. Use `letI : Algebra A (D.obj j) := (t.app j).hom.toAlgebra`. Use `haveI : Algebra.Etale A (D.obj j) := (hst j).1`. Establish `h1 : ∀ a : A, q.hom (algebraMap A B a) = algebraMap A (D.obj j) a` using `fun a => congrArg (fun f => f.hom a) hq1`.

Establish `h2 : ∀ a : A, (s.app j).hom (algebraMap A (D.obj j) a) = algebraMap A O a` using `fun a => congrArg (fun f => f.hom a) (hst j).2`. Establish `h3 : ∀ b : B, (s.app j).hom (q.hom b) = φ b` using `fun b => congrArg (fun f => f.hom b) hq2`. Use `⟨D.obj j, inferInstance, inferInstance, inferInstance, ⟨q.hom, h1⟩, ⟨(s.app j).hom, h2⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `b`. Conclude with `h3 b`.
-/
theorem exists_etale_factor_of_indEt : ∀ (A O : Type) [CommRing A] [CommRing O] [Algebra A O], IndEt A O → ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B] (φ : B →ₐ[A] O), ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.Etale A C) (ψ : B →ₐ[A] C) (χ : C →ₐ[A] O), χ.comp ψ = φ := by
  intro A O _ _ _ hO B _ _ _ φ
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := hO
  have hp : MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0}
      (CommRingCat.ofHom (algebraMap A B)) :=
    CommRingCat.isFinitelyPresentable_hom _ (RingHom.finitePresentation_algebraMap.2 inferInstance)
  obtain ⟨j, q, hq1, hq2⟩ := MorphismProperty.exists_hom_of_isFinitelyPresentable hs hp t
    (CommRingCat.ofHom φ.toRingHom) (fun j => by
      rw [(hst j).2]; ext a; simp)
  letI : Algebra A (D.obj j) := (t.app j).hom.toAlgebra
  haveI : Algebra.Etale A (D.obj j) := (hst j).1
  have h1 : ∀ a : A, q.hom (algebraMap A B a) = algebraMap A (D.obj j) a := fun a =>
    congrArg (fun f => f.hom a) hq1
  have h2 : ∀ a : A, (s.app j).hom (algebraMap A (D.obj j) a) = algebraMap A O a := fun a =>
    congrArg (fun f => f.hom a) (hst j).2
  have h3 : ∀ b : B, (s.app j).hom (q.hom b) = φ b := fun b =>
    congrArg (fun f => f.hom b) hq2
  refine ⟨D.obj j, inferInstance, inferInstance, inferInstance, ⟨q.hom, h1⟩, ⟨(s.app j).hom, h2⟩, ?_⟩
  ext b
  exact h3 b

end GlobalTheory.EtC
