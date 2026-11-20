import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.SkewSpan

/- English proof (translation)
Establish `h' : Bᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * B)` using `eq_neg_of_add_eq_zero_left h`. Rewrite using `[Matrix.mul_assoc, h', Matrix.mul_neg, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul]`.
-/
theorem skew_conj {n : ℕ} (ε : Fin n → Bool) {B : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.inG ε B) : Formalism.REAL.Jm ε * Bᴴ * Formalism.REAL.Jm ε = -B := by
  have h' : Bᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * B) := eq_neg_of_add_eq_zero_left h
  rw [Matrix.mul_assoc, h', Matrix.mul_neg, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self,
    Matrix.one_mul]

/- English proof (translation)
Establish `h1 : (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * Bᴴ).trace = (Xᴴ * (Formalism.REAL.Jm ε * Bᴴ * Formalism.REAL.Jm ε)).trace`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`. Establish `h2 : starRingEnd ℂ (X * Bᴴ).trace = (Xᴴ * B).trace`. Rewrite using `[starRingEnd_apply, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]`.

Rewrite using `[h1, h2, skew_conj ε h, Matrix.mul_neg, Matrix.trace_neg]`.
-/
theorem trace_twisted {n : ℕ} (ε : Fin n → Bool) {B : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.inG ε B) (X : Matrix (Fin n) (Fin n) ℂ) :
    (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * Bᴴ).trace = - starRingEnd ℂ (X * Bᴴ).trace := by
  have h1 : (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * Bᴴ).trace
      = (Xᴴ * (Formalism.REAL.Jm ε * Bᴴ * Formalism.REAL.Jm ε)).trace := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : starRingEnd ℂ (X * Bᴴ).trace = (Xᴴ * B).trace := by
    rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  rw [h1, h2, skew_conj ε h, Matrix.mul_neg, Matrix.trace_neg]

/- English proof (translation)
Establish `h2 : ∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0`. Introduce `X hX i hi`. Proceed by induction on `hX using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, hk, rfl⟩` from `hx`.

Rewrite using `[hB, if_neg]`. Introduce and unpack `rfl`. Conclude with `hi hk`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.trace_add, hx, hy, add_zero]`.

Consider the case `smul c x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]`. Establish `hexp : ∀ X ∈ Submodule.span ℂ (B '' s), X = ∑ i, (X * (B i)ᴴ).trace • B i`. Introduce `X hX`. Proceed by induction on `hX using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨k, hk, rfl⟩` from `hx`. Simplify using `[hB]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Simplify using `only [Matrix.add_mul, Matrix.trace_add, add_smul, Finset.sum_add_distrib]`.

Rewrite using `[← hx, ← hy]`. Consider the case `smul c x _ hx`. Simplify using `only [Matrix.smul_mul, Matrix.trace_smul, smul_assoc, ← Finset.smul_sum]`. Rewrite using `[← hx]`. Use `⟨fun X => ⟨?_, ?_⟩, h2, fun X i => trace_twisted ε (hG i) X⟩` and prove the remaining obligations.

Introduce and unpack `⟨hX, hXG⟩`. Rewrite using `[hexp X hX]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i ∈ s`. Establish `h3` using `trace_twisted ε (hG i) X`.

Rewrite `h3` using `[skew_conj ε hXG, Matrix.neg_mul, Matrix.trace_neg, neg_inj]`. Establish `h4 : (X * (B i)ᴴ).trace = (((X * (B i)ᴴ).trace.re : ℝ) : ℂ)` using `(Complex.conj_eq_iff_re.mp h3.symm).symm`. Rewrite using `[h4, Complex.coe_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)`. Rewrite using `[h2 X hX i hi, zero_smul]`.

Conclude with `Submodule.zero_mem _`. Introduce `hX`. Use `⟨Submodule.span_le_restrictScalars ℝ ℂ _ hX, ?_⟩` and prove the remaining obligations. Proceed by induction on `hX using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨k, hk, rfl⟩` from `hx`. Conclude with `hG k`. Consider the case `zero => simp [Formalism.REAL.inG]`. Consider the case `add x y _ _ hx hy`. Unfold `Formalism.REAL.inG at *`.

Rewrite using `[Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hx, hy, add_zero]`. Consider the case `smul c x _ hx`. Unfold `Formalism.REAL.inG at *`. Rewrite using `[Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hx, smul_zero]`.
-/
theorem real_span (n d : ℕ) (ε : Fin n → Bool) (B : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (s : Set (Fin d)) (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hG : ∀ i, Formalism.REAL.inG ε (B i)) :
    (∀ X, (X ∈ Submodule.span ℂ (B '' s) ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (B '' s)) ∧
    (∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0) ∧
    ∀ X i, (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * (B i)ᴴ).trace
      = - starRingEnd ℂ (X * (B i)ᴴ).trace := by
  have h2 : ∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0 := by
    intro X hX i hi
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      rw [hB, if_neg]
      rintro rfl
      exact hi hk
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul c x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  have hexp : ∀ X ∈ Submodule.span ℂ (B '' s), X = ∑ i, (X * (B i)ᴴ).trace • B i := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      simp [hB]
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Matrix.add_mul, Matrix.trace_add, add_smul, Finset.sum_add_distrib]
      rw [← hx, ← hy]
    | smul c x _ hx =>
      simp only [Matrix.smul_mul, Matrix.trace_smul, smul_assoc, ← Finset.smul_sum]
      rw [← hx]
  refine ⟨fun X => ⟨?_, ?_⟩, h2, fun X i => trace_twisted ε (hG i) X⟩
  · rintro ⟨hX, hXG⟩
    rw [hexp X hX]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ s
    · have h3 := trace_twisted ε (hG i) X
      rw [skew_conj ε hXG, Matrix.neg_mul, Matrix.trace_neg, neg_inj] at h3
      have h4 : (X * (B i)ᴴ).trace = (((X * (B i)ᴴ).trace.re : ℝ) : ℂ) :=
        (Complex.conj_eq_iff_re.mp h3.symm).symm
      rw [h4, Complex.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [h2 X hX i hi, zero_smul]
      exact Submodule.zero_mem _
  · intro hX
    refine ⟨Submodule.span_le_restrictScalars ℝ ℂ _ hX, ?_⟩
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hG k
    | zero => simp [Formalism.REAL.inG]
    | add x y _ _ hx hy =>
      unfold Formalism.REAL.inG at *
      rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hx, hy,
        add_zero]
    | smul c x _ hx =>
      unfold Formalism.REAL.inG at *
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
        hx, smul_zero]

end GlobalTheory.SkewSpan
