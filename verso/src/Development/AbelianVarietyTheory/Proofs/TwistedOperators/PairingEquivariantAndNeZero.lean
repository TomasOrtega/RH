import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodOfIsIrreducibleAl
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

noncomputable section

namespace GlobalTheory.GLDuality

def pairLmul {n n' k : ℕ} (x : Matrix (Fin n') (Fin n) ℂ) :
    MvPolynomial (Fin n' × Fin k) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin k) ℂ :=
  aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ))

/- English proof (translation)
Establish `: (pairLmul x).comp (rowAct ℂ (n` using `k) h) = pairLmul (h * x) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, s⟩`. Simplify using `only [pairLmul, rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[← this]`. Both sides reduce to the same expression.
-/
theorem pairLmul_rowAct {n n' k : ℕ} (x : Matrix (Fin n') (Fin n) ℂ) (h : Matrix (Fin n') (Fin n') ℂ)
    (f : MvPolynomial (Fin n' × Fin k) ℂ) : pairLmul x (rowAct ℂ h f) = pairLmul (h * x) f := by
  have : (pairLmul x).comp (rowAct ℂ (n := k) h) = pairLmul (h * x) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp only [pairLmul, rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← this]; rfl

/- English proof (translation)
Establish `: (rowAct ℂ (n` using `k) g).comp (pairLmul x) = pairLmul (x * g) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, s⟩`. Simplify using `only [pairLmul, rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[← this]`. Both sides reduce to the same expression.
-/
theorem rowAct_pairLmul {n n' k : ℕ} (x : Matrix (Fin n') (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (f : MvPolynomial (Fin n' × Fin k) ℂ) : rowAct ℂ g (pairLmul x f) = pairLmul (x * g) f := by
  have : (rowAct ℂ (n := k) g).comp (pairLmul x) = pairLmul (x * g) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp only [pairLmul, rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← this]; rfl

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [rowAct]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp, map_X]`.

Use `congr 1`. Simplify using `[rowAct, map_sum]`.
-/
theorem pair_map_conj_rowAct {n k : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin k) ℂ) :
    map (starRingEnd ℂ) (rowAct ℂ g p) = rowAct ℂ (gᵀ)ᴴ (map (starRingEnd ℂ) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [rowAct, map_sum]

/- English proof (translation)
Simplify using `only [hw, map_prod, map_pow, lpMinor]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[RingHom.map_det]`. Use `congr 1`.

Use extensionality with `p q : 1`. Simplify using the standard rewrite rules.
-/
theorem pair_map_conj_hw {n k : ℕ} (hn : k ≤ n) (ν : Fin k → ℕ) :
    map (starRingEnd ℂ) (hw ℂ hn ν) = hw ℂ hn ν := by
  simp only [hw, map_prod, map_pow, lpMinor]
  refine Finset.prod_congr rfl fun s _ => ?_
  congr 1
  rw [RingHom.map_det]
  congr 1
  ext p q : 1
  simp

/- English proof (translation)
Simplify using `only [hw, map_prod, map_pow, lpMinor]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`.

Use extensionality with `p q : 1`. Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, pairLmul, aeval_X]`. Rewrite using `[Finset.sum_eq_single (Fin.castLE (by have := s.2; omega) p)]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Rewrite using `[if_neg]`. Simplify using the standard rewrite rules. Introduce `e`. Conclude with `hb (Fin.ext (by simpa using e.symm))`. Simplify using the standard rewrite rules.
-/
theorem pairLmul_hw {n n' k : ℕ} (hn : k ≤ n) (hn' : k ≤ n') (ν : Fin k → ℕ) :
    pairLmul (Matrix.of fun (a : Fin n') (t : Fin n) => if a.val = t.val then (1 : ℂ) else 0) (hw ℂ hn' ν) =
      hw ℂ hn ν := by
  simp only [hw, map_prod, map_pow, lpMinor]
  refine Finset.prod_congr rfl fun s _ => ?_
  congr 1
  rw [AlgHom.map_det]
  congr 1
  ext p q : 1
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, pairLmul, aeval_X]
  rw [Finset.sum_eq_single (Fin.castLE (by have := s.2; omega) p)]
  · simp
  · intro b _ hb
    rw [if_neg]
    · simp
    · intro e
      exact hb (Fin.ext (by simpa using e.symm))
  · simp

/- English proof (translation)
Introduce `n n' k T hT`. Establish `hT' : ∀ φ f (x : Matrix (Fin n') (Fin n) ℂ), eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (pairLmul x f))` using `hT`. Use `⟨fun g h φ f => ?_, fun hn hn' ν h0 => ?_⟩` and prove the remaining obligations. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `p`.

Establish `hp : p = fun v => (Matrix.of fun a t => p (a, t)) v.1 v.2` using `rfl`. Rewrite using `[hp, eval_matRep, hT', hT', fockRowAdj, pairLmul_rowAct, ← pair_map_conj_rowAct, rowAct_pairLmul]`. Establish `h1` using `hT' (hw ℂ hn ν) (hw ℂ hn' ν) (Matrix.of fun (a : Fin n') (t : Fin n) => if a.val = t.val then (1 : ℂ) else 0)`. Rewrite `h1` using `[h0, map_zero, pairLmul_hw hn hn', pair_map_conj_hw]`. Establish `h2` using `(fockPos _ _ (hwNe ℂ n k hn ν)).1`.

Rewrite `h2` using `[← h1]`. Simplify using `at h2`.
-/
theorem pairing_equivariant_and_ne_zero : ∀ (n n' k : ℕ) (T : MvPolynomial (Fin n × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n) ℂ), (∀ (φ : MvPolynomial (Fin n × Fin k) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ) (x : Matrix (Fin n') (Fin n) ℂ), eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ)) f))) → (∀ (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) (φ : MvPolynomial (Fin n × Fin k) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ), T (rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ φ) (rowAct ℂ (h : Matrix (Fin n') (Fin n') ℂ)ᵀ f) = matRep n n' (g, h) (T φ f)) ∧ ∀ (hn : k ≤ n) (hn' : k ≤ n') (ν : Fin k → ℕ), T (hw ℂ hn ν) (hw ℂ hn' ν) ≠ 0 := by
  intro n n' k T hT
  have hT' : ∀ φ f (x : Matrix (Fin n') (Fin n) ℂ),
      eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (pairLmul x f)) := hT
  refine ⟨fun g h φ f => ?_, fun hn hn' ν h0 => ?_⟩
  · apply MvPolynomial.funext
    intro p
    have hp : p = fun v => (Matrix.of fun a t => p (a, t)) v.1 v.2 := rfl
    rw [hp, eval_matRep, hT', hT', fockRowAdj, pairLmul_rowAct, ← pair_map_conj_rowAct, rowAct_pairLmul]
  · have h1 := hT' (hw ℂ hn ν) (hw ℂ hn' ν)
      (Matrix.of fun (a : Fin n') (t : Fin n) => if a.val = t.val then (1 : ℂ) else 0)
    rw [h0, map_zero, pairLmul_hw hn hn', pair_map_conj_hw] at h1
    have h2 := (fockPos _ _ (hwNe ℂ n k hn ν)).1
    rw [← h1] at h2
    simp at h2

end GlobalTheory.GLDuality
