import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
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
