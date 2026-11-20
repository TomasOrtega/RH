import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockHarmonicRepresentative

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag]`. Use `Finset.sum_eq_zero fun a _ => hZ a a ?_` and prove the remaining obligations. Apply the tactic sequence `rcases a with a | a <;> simp [sameBlock]`.
-/
theorem pcTrace_eq_zero {p q : ℕ} {Z : Mat p q} (hZ : IsPC Z) : Z.trace = 0 := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_eq_zero fun a _ => hZ a a ?_
  rcases a with a | a <;> simp [sameBlock]

/- English proof (translation)
Introduce `P Q R S x`. Use `eq_top_iff.2 fun f _ => ?_` and prove the remaining obligations. Establish `hpr : ∀ Z : Mat P Q, IsPC Z → ∀ g, (coinv P Q R S x).mkQ (fockAct1 P Q R S Z g) = 0`. Introduce `Z hZ g`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Use `Submodule.subset_span ⟨Z, g, ?_⟩` and prove the remaining obligations. Rewrite using `[pcTrace_eq_zero hZ, mul_zero, zero_smul, sub_zero]`. Take `⟨h, hh, he⟩` from `GlobalTheory.FockAlg.HarmLift.exists_harm2_rep P Q R S _ (coinv P Q R S x).mkQ hpr f`. Establish `hd : f - h ∈ coinv P Q R S x`. Rewrite using `[← Submodule.Quotient.eq]`.

Conclude with `he.symm`. Establish `: f = h + (f - h)` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.add_mem_sup (Submodule.subset_span hh) hd`.
-/
theorem span_harm2_sup_coinv_eq_univ : ∀ (P Q R S : ℕ) (x : ℂ),
    Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x = ⊤ := by
  intro P Q R S x
  refine eq_top_iff.2 fun f _ => ?_
  have hpr : ∀ Z : Mat P Q, IsPC Z → ∀ g, (coinv P Q R S x).mkQ (fockAct1 P Q R S Z g) = 0 := by
    intro Z hZ g
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine Submodule.subset_span ⟨Z, g, ?_⟩
    rw [pcTrace_eq_zero hZ, mul_zero, zero_smul, sub_zero]
  obtain ⟨h, hh, he⟩ := GlobalTheory.FockAlg.HarmLift.exists_harm2_rep P Q R S _ (coinv P Q R S x).mkQ hpr f
  have hd : f - h ∈ coinv P Q R S x := by
    rw [← Submodule.Quotient.eq]; exact he.symm
  have : f = h + (f - h) := by abel
  rw [this]
  exact Submodule.add_mem_sup (Submodule.subset_span hh) hd

/- English proof (translation)
The claim follows from `span_harm2_sup_coinv_eq_univ`.
-/
example : ∀ (P Q R S : ℕ) (x : ℂ), Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x = ⊤ := span_harm2_sup_coinv_eq_univ

end GlobalTheory.HoweR
