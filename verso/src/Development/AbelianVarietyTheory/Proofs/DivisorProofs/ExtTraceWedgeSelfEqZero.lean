import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

namespace GlobalTheory.SqZeroLine

/- English proof (translation)
Take `⟨a, ha⟩` from `Fintype.card_eq_one_iff.mp hm`. Take `⟨b, hb⟩` from `Fintype.card_eq_one_iff.mp hl`. Use `⟨a, b, fun A B => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply]`. Rewrite using `[Fintype.sum_eq_single b (fun i hi => (hi (hb i)).elim)]`.

Rewrite using `[Fintype.sum_eq_single a (fun i hi => (hi (ha i)).elim)]`.
-/
theorem trace_mul_eq_of_card_one {m l : Type} [Fintype m] [Fintype l]
    (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) :
    ∃ a : m, ∃ b : l, ∀ (A : Matrix l m ℂ) (B : Matrix m l ℂ), (A * B).trace = A b a * B a b := by
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hm
  obtain ⟨b, hb⟩ := Fintype.card_eq_one_iff.mp hl
  refine ⟨a, b, fun A B => ?_⟩
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Fintype.sum_eq_single b (fun i hi => (hi (hb i)).elim)]
  rw [Fintype.sum_eq_single a (fun i hi => (hi (ha i)).elim)]

/- English proof (translation)
Simplify using `only [wedge, hα]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wedge_self_of_product {V : Type} (α : V → V → ℂ) (g f : V → ℂ) (c : ℂ)
    (hα : ∀ ξ η, α ξ η = c * g ξ * f η) (ξ₁ η₁ ξ₂ η₂ : V) :
    wedge α α ξ₁ η₁ ξ₂ η₂ = 0 := by
  simp only [wedge, hα]; ring

end GlobalTheory.SqZeroLine

/- English proof (translation)
Introduce `V _ _ _ _ m l _ _ _ _ U H z _ _ hm hl ξ₁ η₁ ξ₂ η₂`. Take `⟨a, b, hab⟩` from `GlobalTheory.SqZeroLine.trace_mul_eq_of_card_one hm hl`. Conclude with `GlobalTheory.SqZeroLine.wedge_self_of_product (extTrace H z) (fun ξ => extFormAdj H z ξ b a) (fun η => extForm H z η a b) kappa (fun ξ η => by simp only [extTrace, hab]; ring) ξ₁ η₁ ξ₂ η₂`.
-/
theorem GlobalTheory.extTrace_wedge_self_eq_zero_of_line : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (ξ₁ η₁ ξ₂ η₂ : V), wedge (extTrace H z) (extTrace H z) ξ₁ η₁ ξ₂ η₂ = 0 := by
  intro V _ _ _ _ m l _ _ _ _ U H z _ _ hm hl ξ₁ η₁ ξ₂ η₂
  obtain ⟨a, b, hab⟩ := GlobalTheory.SqZeroLine.trace_mul_eq_of_card_one hm hl
  exact GlobalTheory.SqZeroLine.wedge_self_of_product (extTrace H z)
    (fun ξ => extFormAdj H z ξ b a) (fun η => extForm H z η a b) kappa
    (fun ξ η => by simp only [extTrace, hab]; ring) ξ₁ η₁ ξ₂ η₂
