import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDetEqLinearCombinationNatNodes
open NumberField GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.CuspRep

open Finset in

/- English proof (translation)
Introduce `E _ _ _ b`. Use `⟨univ.image (fun p : (E →+* ℂ) × Fin (b + 1) => cap (a := b) p.1 ((p.2 : ℕ) : ℂ)), ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Take `⟨p, -, rfl⟩` from `mem_image.1 ht`. Conclude with `⟨p.1, _, rfl⟩`.

Apply `le_antisymm` to reduce the goal to its premises. Unfold `Zalg`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `z ⟨τ, u, rfl⟩`. Take `⟨w, hw⟩` from `cap_eq_sum_nodes E b τ u`.

Rewrite using `[hw]`. Use `Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _ (Algebra.subset_adjoin ?_) _` and prove the remaining obligations. Simplify using `only [coe_image, coe_univ, Set.image_univ, Set.mem_range]`. Conclude with `⟨(τ, j), rfl⟩`. Unfold `Zalg`.

Apply `Algebra.adjoin_mono` to reduce the goal to its premises. Introduce `t ht`. Simplify using `only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at ht`. Take `⟨p, rfl⟩` from `ht`. Conclude with `⟨p.1, _, rfl⟩`.
-/
theorem zalg_eq_adjoin_finite_caps : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ),
    ∃ T : Finset (Module.End ℂ (Sm E b)), (∀ t ∈ T, ∃ (τ : E →+* ℂ) (u : ℂ), t = cap τ u) ∧
      Zalg E b = Algebra.adjoin ℂ (T : Set (Module.End ℂ (Sm E b))) := by
  intro E _ _ _ b
  classical
  refine ⟨univ.image (fun p : (E →+* ℂ) × Fin (b + 1) => cap (a := b) p.1 ((p.2 : ℕ) : ℂ)), ?_, ?_⟩
  · intro t ht
    obtain ⟨p, -, rfl⟩ := mem_image.1 ht
    exact ⟨p.1, _, rfl⟩
  · apply le_antisymm
    · unfold Zalg
      rw [Algebra.adjoin_le_iff]
      rintro z ⟨τ, u, rfl⟩
      obtain ⟨w, hw⟩ := cap_eq_sum_nodes E b τ u
      rw [hw]
      refine Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _ (Algebra.subset_adjoin ?_) _
      simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨(τ, j), rfl⟩
    · unfold Zalg
      apply Algebra.adjoin_mono
      intro t ht
      simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at ht
      obtain ⟨p, rfl⟩ := ht
      exact ⟨p.1, _, rfl⟩

end GlobalTheory.CuspRep

end
