import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `k _ _ J J' i θ S h ε hε`. Take `⟨s, c, hs, hc⟩` from `h ε hε`. Use `⟨s.image (fun x => x ∘ i), fun ζ => ∑ η ∈ s with η ∘ i = ζ, c η, ?_, ?_⟩` and prove the remaining obligations. Introduce `ζ hζ`. Simplify using `only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hζ`.

Take `⟨η, hη, rfl⟩` from `hζ`. Conclude with `⟨η, hs hη, rfl⟩`. Introduce `P`. Establish `key : ∀ η : J' → k, MvPolynomial.aeval (η ∘ i) P = MvPolynomial.aeval η (MvPolynomial.rename i P)`. Introduce `η`.

Rewrite using `[MvPolynomial.aeval_rename]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 2`. Conclude with `key θ`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image (fun x => x ∘ i)) (g := fun x => x ∘ i) (fun η hη => Finset.mem_image_of_mem _ hη)]`.

Use `Finset.sum_congr rfl fun ζ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun η hη => ?_` and prove the remaining obligations. Rewrite using `[← (Finset.mem_filter.1 hη).2, key]`. Use `_ ≤ ε := hc _`.
-/
theorem UpperTheory.Gal.Gen.restrict_pf :
    UpperTheory.Gal.Gen.Restrict := by
  classical
  intro k _ _ J J' i θ S h ε hε
  obtain ⟨s, c, hs, hc⟩ := h ε hε
  refine ⟨s.image (fun x => x ∘ i), fun ζ => ∑ η ∈ s with η ∘ i = ζ, c η, ?_, ?_⟩
  · intro ζ hζ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hζ
    obtain ⟨η, hη, rfl⟩ := hζ
    exact ⟨η, hs hη, rfl⟩
  · intro P
    have key : ∀ η : J' → k,
        MvPolynomial.aeval (η ∘ i) P = MvPolynomial.aeval η (MvPolynomial.rename i P) := by
      intro η
      rw [MvPolynomial.aeval_rename]
    calc _ = ‖MvPolynomial.aeval θ (MvPolynomial.rename i P)
          - ∑ η ∈ s, c η * MvPolynomial.aeval η (MvPolynomial.rename i P)‖ := by
          congr 2
          · exact key θ
          · rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image (fun x => x ∘ i))
              (g := fun x => x ∘ i) (fun η hη => Finset.mem_image_of_mem _ hη)]
            refine Finset.sum_congr rfl fun ζ _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun η hη => ?_
            rw [← (Finset.mem_filter.1 hη).2, key]
      _ ≤ ε := hc _
