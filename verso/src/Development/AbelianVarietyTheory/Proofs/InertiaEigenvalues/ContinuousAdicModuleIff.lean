import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open Topology Filter

namespace GlobalTheory

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private lemma mem_span_pow_smul_iff_exists_pow_smul {R : Type} [CommRing R] (a : R) {M : Type} [AddCommGroup M]
    [Module R M] (n : ℕ) (x : M) :
    x ∈ (Ideal.span {a}) ^ n • (⊤ : Submodule R M) ↔ ∃ y : M, x = a ^ n • y := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp [eq_comm]

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_adicModule_iff {R : Type} [CommRing R] (a : R) {M : Type} [AddCommGroup M]
    [Module R M] {G : Type} [TopologicalSpace G] (f : G → M) :
    @Continuous G M _ ((Ideal.span {a}).adicModuleTopology M) f ↔
      ∀ (g : G) (n : ℕ), ∀ᶠ h in 𝓝 g, ∃ y : M, f h - f g = a ^ n • y := by
  let _ : TopologicalSpace R := (Ideal.span {a}).ringFilterBasis.topology
  let _ : TopologicalSpace M := (Ideal.span {a}).adicModuleTopology M
  have hB : ∀ y : M, (𝓝 y).HasBasis
      (fun V : Set M => ∃ n : ℕ, V = ↑((Ideal.span {a}) ^ n • (⊤ : Submodule R M)))
      (fun V => (fun z => y + z) '' V) := fun y =>
    ((Ideal.span {a}).ringFilterBasis.moduleFilterBasis
      ((Ideal.span {a}).adic_module_basis M)).toAddGroupFilterBasis.nhds_hasBasis y
  rw [continuous_iff_continuousAt]
  refine forall_congr' fun g => ?_
  refine ((hB (f g)).tendsto_right_iff).trans ⟨fun H n => ?_, fun H V hV => ?_⟩
  · filter_upwards [H _ ⟨n, rfl⟩] with h hh
    obtain ⟨z, hz, hzh⟩ := hh
    obtain ⟨y, rfl⟩ := (mem_span_pow_smul_iff_exists_pow_smul a n z).1 hz
    beta_reduce at hzh
    exact ⟨y, by rw [← hzh, add_sub_cancel_left]⟩
  · obtain ⟨n, rfl⟩ := hV
    filter_upwards [H n] with h hh
    obtain ⟨y, hy⟩ := hh
    exact ⟨a ^ n • y, (mem_span_pow_smul_iff_exists_pow_smul a n _).2 ⟨y, rfl⟩, by
      show f g + a ^ n • y = f h
      rw [← hy]; abel⟩

end GlobalTheory
