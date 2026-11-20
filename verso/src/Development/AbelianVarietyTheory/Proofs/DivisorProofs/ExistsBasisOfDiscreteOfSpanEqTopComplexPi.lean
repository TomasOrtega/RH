import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `g Λ hd h`. Use `haveI : IsZLattice ℝ Λ := ⟨h⟩`. Use `haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ`. Use `haveI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ`. Establish `hr : Module.finrank ℤ Λ = 2 * g`.

Rewrite using `[ZLattice.rank ℝ Λ, Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex]`. Simplify using `[mul_comm]`. Set `b : Module.Basis (Fin (2 * g)) ℤ Λ` to `Module.finBasisOfFinrankEq ℤ Λ hr`. Establish `e : (fun i => (b i : Fin g → ℂ)) = ⇑(b.ofZLatticeBasis ℝ Λ)`. Use function extensionality and compare the values at `i`.

Conclude with `(Module.Basis.ofZLatticeBasis_apply ℝ Λ b i).symm`. Use `⟨b, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `(b.ofZLatticeBasis ℝ Λ).linearIndependent`. Rewrite using `[e]`.

Conclude with `(b.ofZLatticeBasis ℝ Λ).span_eq`.
-/
theorem exists_basis_of_discrete_of_span_eq_top_complex_pi :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∃ b : Module.Basis (Fin (2 * g)) ℤ Λ,
        LinearIndependent ℝ (fun i => (b i : Fin g → ℂ)) ∧
          Submodule.span ℝ (Set.range fun i => (b i : Fin g → ℂ)) = ⊤ := by
  intro g Λ hd h
  haveI : IsZLattice ℝ Λ := ⟨h⟩
  haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  haveI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  have hr : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex]
    simp [mul_comm]
  let b : Module.Basis (Fin (2 * g)) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ hr
  have e : (fun i => (b i : Fin g → ℂ)) = ⇑(b.ofZLatticeBasis ℝ Λ) := by
    funext i
    exact (Module.Basis.ofZLatticeBasis_apply ℝ Λ b i).symm
  refine ⟨b, ?_, ?_⟩
  · rw [e]; exact (b.ofZLatticeBasis ℝ Λ).linearIndependent
  · rw [e]; exact (b.ofZLatticeBasis ℝ Λ).span_eq

end GlobalTheory
