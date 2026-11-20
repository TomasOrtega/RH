import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `T Z S p π ι σ m hsym`. Use `⟨fun Ω _ _ z => if h : ∃ x : gp Ω ⟶ T, z ≫ p = x ≫ π then ∑ᶠ (j : ι) (_ : j ∈ {j | h.choose ≫ σ j = z}), m j else 0, ?_⟩` and prove the remaining obligations. Introduce `Ω _ _ x z hz`. Establish `hex : ∃ x : gp Ω ⟶ T, z ≫ p = x ≫ π` using `⟨x, hz⟩`. Simplify using `only [dif_pos hex]`.

Use `set x₀ := hex.choose with hx₀`. Establish `h₀ : z ≫ p = x₀ ≫ π` using `hex.choose_spec`. Take `⟨e, he⟩` from `hsym Ω x x₀ (hz.symm.trans h₀)`. Use `symm`. Apply `finsum_mem_eq_of_bijOn e` to reduce the goal to its premises.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j hj`. Simplify using `only [Set.mem_setOf_eq] at hj ⊢`. Rewrite using `[← (he j).1, hj]`. Introduce `a _ b _ hab`.

Conclude with `e.injective hab`. Introduce `k hk`. Simplify using `only [Set.mem_setOf_eq] at hk`. Use `⟨e.symm k, ?_, by simp⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq]`.

Rewrite using `[(he (e.symm k)).1, Equiv.apply_symm_apply, hk]`. Introduce `j _`. Conclude with `((he j).2).symm`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.countEx_of :
    CountEx := by
  classical
  intro T Z S p π ι σ m hsym
  refine ⟨fun Ω _ _ z => if h : ∃ x : gp Ω ⟶ T, z ≫ p = x ≫ π then
      ∑ᶠ (j : ι) (_ : j ∈ {j | h.choose ≫ σ j = z}), m j else 0, ?_⟩
  intro Ω _ _ x z hz
  have hex : ∃ x : gp Ω ⟶ T, z ≫ p = x ≫ π := ⟨x, hz⟩
  simp only [dif_pos hex]
  set x₀ := hex.choose with hx₀
  have h₀ : z ≫ p = x₀ ≫ π := hex.choose_spec
  obtain ⟨e, he⟩ := hsym Ω x x₀ (hz.symm.trans h₀)
  symm
  apply finsum_mem_eq_of_bijOn e
  · refine ⟨?_, ?_, ?_⟩
    · intro j hj
      simp only [Set.mem_setOf_eq] at hj ⊢
      rw [← (he j).1, hj]
    · intro a _ b _ hab
      exact e.injective hab
    · intro k hk
      simp only [Set.mem_setOf_eq] at hk
      refine ⟨e.symm k, ?_, by simp⟩
      simp only [Set.mem_setOf_eq]
      rw [(he (e.symm k)).1, Equiv.apply_symm_apply, hk]
  · intro j _
    exact ((he j).2).symm
