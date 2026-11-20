import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SpanEvalEqTop

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ThetaAddition

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul`. Consider the case `exact _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul`. Consider the case `(apply _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul ..)`.
-/
theorem exists_sum_mul {X Y : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (L : Submodule ℂ (Y → ℂ)) (F : X → Y → ℂ) (h1 : ∀ y, (fun x => F x y) ∈ V)
    (h2 : ∀ x, F x ∈ L) :
    ∃ (n : ℕ) (h : Fin n → X → ℂ) (k : Fin n → Y → ℂ), (∀ i, h i ∈ V ∧ k i ∈ L) ∧
      ∀ x y, F x y = ∑ i, h i x * k i y := by
  first
  | exact @_root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul
  | exact _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul
  | (apply _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul ..)

/- English proof (translation)
Use `⟨(hf.1.comp (by fun_prop)).mul (hf'.1.comp (by fun_prop)), fun n n' z => ?_⟩` and prove the remaining obligations. Establish `e1 : z + τ *ᵥ ofIntVec n + ofIntVec n' + w = (z + w) + τ *ᵥ ofIntVec n + ofIntVec n'`. Normalize the expressions using the abelian group laws. Establish `e2 : z + τ *ᵥ ofIntVec n + ofIntVec n' - w = (z - w) + τ *ᵥ ofIntVec n + ofIntVec n'`. Normalize the expressions using the abelian group laws.

Use `show f _ * f' _ = _ * (f _ * f' _)`. Rewrite using `[e1, e2, hf.2, hf'.2, mul_mul_mul_comm, ← eC_add]`. Use `congr 2`. Rewrite using `[dotProduct_add, dotProduct_sub]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem left_mem {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) {f f' : (Fin g → ℂ) → ℂ}
    (hf : f ∈ thetaLevel N τ) (hf' : f' ∈ thetaLevel N τ) (w : Fin g → ℂ) :
    (fun z => f (z + w) * f' (z - w)) ∈ thetaLevel (2 * N) τ := by
  refine ⟨(hf.1.comp (by fun_prop)).mul (hf'.1.comp (by fun_prop)), fun n n' z => ?_⟩
  have e1 : z + τ *ᵥ ofIntVec n + ofIntVec n' + w = (z + w) + τ *ᵥ ofIntVec n + ofIntVec n' := by
    abel
  have e2 : z + τ *ᵥ ofIntVec n + ofIntVec n' - w = (z - w) + τ *ᵥ ofIntVec n + ofIntVec n' := by
    abel
  show f _ * f' _ = _ * (f _ * f' _)
  rw [e1, e2, hf.2, hf'.2, mul_mul_mul_comm, ← eC_add]
  congr 2
  rw [dotProduct_add, dotProduct_sub]; push_cast; ring

/- English proof (translation)
Use `⟨(hf.1.comp (by fun_prop)).mul (hf'.1.comp (by fun_prop)), fun n n' w => ?_⟩` and prove the remaining obligations. Establish `e1 : z + (w + τ *ᵥ ofIntVec n + ofIntVec n') = (z + w) + τ *ᵥ ofIntVec n + ofIntVec n'`. Normalize the expressions using the abelian group laws. Establish `e2 : z - (w + τ *ᵥ ofIntVec n + ofIntVec n') = (z - w) + τ *ᵥ ofIntVec (-n) + ofIntVec (-n')`. Rewrite using `[ofIntVec_neg, ofIntVec_neg, mulVec_neg]`.

Normalize the expressions using the abelian group laws. Use `show f _ * f' _ = _ * (f _ * f' _)`. Rewrite using `[e1, e2, hf.2, hf'.2, mul_mul_mul_comm, ← eC_add]`. Use `congr 2`. Rewrite using `[ofIntVec_neg, mulVec_neg, neg_dotProduct_neg, neg_dotProduct, dotProduct_add, dotProduct_sub]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem right_mem {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) {f f' : (Fin g → ℂ) → ℂ}
    (hf : f ∈ thetaLevel N τ) (hf' : f' ∈ thetaLevel N τ) (z : Fin g → ℂ) :
    (fun w => f (z + w) * f' (z - w)) ∈ thetaLevel (2 * N) τ := by
  refine ⟨(hf.1.comp (by fun_prop)).mul (hf'.1.comp (by fun_prop)), fun n n' w => ?_⟩
  have e1 : z + (w + τ *ᵥ ofIntVec n + ofIntVec n') = (z + w) + τ *ᵥ ofIntVec n + ofIntVec n' := by
    abel
  have e2 : z - (w + τ *ᵥ ofIntVec n + ofIntVec n')
      = (z - w) + τ *ᵥ ofIntVec (-n) + ofIntVec (-n') := by
    rw [ofIntVec_neg, ofIntVec_neg, mulVec_neg]; abel
  show f _ * f' _ = _ * (f _ * f' _)
  rw [e1, e2, hf.2, hf'.2, mul_mul_mul_comm, ← eC_add]
  congr 2
  rw [ofIntVec_neg, mulVec_neg, neg_dotProduct_neg, neg_dotProduct, dotProduct_add, dotProduct_sub]
  push_cast; ring

/- English proof (translation)
Introduce `H1 H2 g τ hτ N hN f f' hf hf'`. Establish `hN2 : 1 ≤ 2 * N` using `by omega`. Establish `hle : thetaLevel (2 * N) τ ≤ _` using `fun φ hφ => H2 g τ hτ (2 * N) hN2 φ hφ`. Use `haveI : FiniteDimensional ℂ (thetaLevel (2 * N) τ) := by haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range (fun (c : Fin g → Fin (2 * N)) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / (2 * N : ℕ)) 0 (((2 * N : ℕ) : ℂ) • z) (((2 * N : ℕ) : ℂ) • τ)))`. Conclude with `Submodule.finiteDimensional_of_le hle`.

Conclude with `exists_sum_mul (thetaLevel (2 * N) τ) (thetaLevel (2 * N) τ) (fun z w => f (z + w) * f' (z - w)) (left_mem τ N hf hf') (right_mem τ N hf hf')`.
-/
theorem addition_level_two_mul :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f f' : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → (Differentiable ℂ f' ∧ ∀ (n n' : Fin g → ℤ) z, f' (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f' z) → ∃ (n : ℕ) (h k : Fin n → (Fin g → ℂ) → ℂ), (∀ i, (Differentiable ℂ (h i) ∧ ∀ (n n' : Fin g → ℤ) z, (h i) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((2 * N : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (h i) z) ∧ (Differentiable ℂ (k i) ∧ ∀ (n n' : Fin g → ℤ) z, (k i) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((2 * N : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (k i) z)) ∧ ∀ z w, f (z + w) * f' (z - w) = ∑ i, h i z * k i w) := by
  intro H1 H2 g τ hτ N hN f f' hf hf'
  have hN2 : 1 ≤ 2 * N := by omega
  have hle : thetaLevel (2 * N) τ ≤ _ := fun φ hφ => H2 g τ hτ (2 * N) hN2 φ hφ
  haveI : FiniteDimensional ℂ (thetaLevel (2 * N) τ) := by
    haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range
      (fun (c : Fin g → Fin (2 * N)) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / (2 * N : ℕ)) 0 (((2 * N : ℕ) : ℂ) • z) (((2 * N : ℕ) : ℂ) • τ)))
    exact Submodule.finiteDimensional_of_le hle
  exact exists_sum_mul (thetaLevel (2 * N) τ) (thetaLevel (2 * N) τ)
    (fun z w => f (z + w) * f' (z - w)) (left_mem τ N hf hf') (right_mem τ N hf hf')

end GlobalTheory.ThetaAddition
