import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.Columns.PolyFn
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

/- English proof (translation)
Unfold `lpMinor`. Rewrite using `[AlgHom.map_det, RingHom.map_det, ← Matrix.det_mul]`. Use `congr 1`. Use `ext1 p q`. Simplify using `[rowAct, Matrix.mul_apply]`.
-/
theorem rowAct_genericDet (R : Type) [CommRing R] (n : ℕ) (g : Matrix (Fin n) (Fin n) R) :
    rowAct R (n := n) g (lpMinor R n le_rfl le_rfl) = C g.det * lpMinor R n le_rfl le_rfl := by
  unfold lpMinor
  rw [AlgHom.map_det, RingHom.map_det, ← Matrix.det_mul]
  congr 1
  ext1 p q
  simp [rowAct, Matrix.mul_apply]

/- English proof (translation)
Establish `h` using `bidetMem R n n c (fun _ => n) (fun _ => le_rfl) (fun _ => Fin.castLE le_rfl)`. Establish `e : shapeDeg (n` using `n) (fun _ : Fin c => n) = fun _ => c := by`. Use function extensionality and compare the values at `t`. Simplify using `[shapeDeg]`. Rewrite `h` using `[e]`.

Simplify `h` using `[bideterminant, initMinor, lpMinor]`.
-/
theorem genericDet_pow_mem (R : Type) [CommRing R] (n c : ℕ) :
    lpMinor R n le_rfl le_rfl ^ c ∈ dualWeyl R n n (fun _ => c) := by
  have h := bidetMem R n n c (fun _ => n) (fun _ => le_rfl) (fun _ => Fin.castLE le_rfl)
  have e : shapeDeg (n := n) (fun _ : Fin c => n) = fun _ => c := by
    funext t
    simp [shapeDeg]
  rw [e] at h
  simpa [bideterminant, initMinor, lpMinor] using h

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => simp [hw, lpMinor]`. Consider the case `succ m`. Unfold `hw`. Rewrite using `[Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_left_comm]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `hs : (Fin.castSucc s).val + 1 < m + 1` using `by simp`. Simplify using `only [nuNext, dif_pos hs]`.

Use linear arithmetic over natural numbers and integers. Establish `hs : ¬ (Fin.last m).val + 1 < m + 1` using `by simp`. Simplify using `only [nuNext, dif_neg hs, Nat.sub_zero]`. Rewrite using `[pow_add, mul_comm]`. Both sides reduce to the same expression.
-/
theorem genericDet_pow_mul_hw (R : Type) [CommRing R] (n c : ℕ) (ν : Fin n → ℕ) :
    lpMinor R n le_rfl le_rfl ^ c * hw R le_rfl ν = hw R (le_refl n) (fun i => ν i + c) := by
  cases n with
  | zero => simp [hw, lpMinor]
  | succ m =>
    unfold hw
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_left_comm]
    congr 1
    · refine Finset.prod_congr rfl fun s _ => ?_
      congr 1
      have hs : (Fin.castSucc s).val + 1 < m + 1 := by simp
      simp only [nuNext, dif_pos hs]
      omega
    · have hs : ¬ (Fin.last m).val + 1 < m + 1 := by simp
      simp only [nuNext, dif_neg hs, Nat.sub_zero]
      rw [pow_add, mul_comm]
      rfl

/- English proof (translation)
Introduce `n c ν`. Use `⟨fun f hf => ?_, fun g f => ?_, fun _ => genericDet_pow_mul_hw ℂ n c ν⟩` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `(dualWeylMul ℂ n n ν (fun _ => c) f _).1 hf (genericDet_pow_mem ℂ n c)`. Rewrite using `[map_mul, map_pow, rowAct_genericDet, mul_pow, smul_eq_C_mul, map_pow, mul_assoc]`.
-/
theorem genericDet_pow_mul :
    ∀ (n c : ℕ) (ν : Fin n → ℕ), (∀ f ∈ dualWeyl ℂ n n ν, lpMinor ℂ n le_rfl le_rfl ^ c * f ∈ dualWeyl ℂ n n (fun i => ν i + c)) ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ) (f : MvPolynomial (Fin n × Fin n) ℂ), rowAct ℂ g (lpMinor ℂ n le_rfl le_rfl ^ c * f) = g.det ^ c • (lpMinor ℂ n le_rfl le_rfl ^ c * rowAct ℂ g f)) ∧ (Antitone ν → lpMinor ℂ n le_rfl le_rfl ^ c * hw ℂ le_rfl ν = hw ℂ (le_refl n) (fun i => ν i + c)) := by
  intro n c ν
  refine ⟨fun f hf => ?_, fun g f => ?_, fun _ => genericDet_pow_mul_hw ℂ n c ν⟩
  · rw [mul_comm]
    exact (dualWeylMul ℂ n n ν (fun _ => c) f _).1 hf (genericDet_pow_mem ℂ n c)
  · rw [map_mul, map_pow, rowAct_genericDet, mul_pow, smul_eq_C_mul, map_pow, mul_assoc]

end GlobalTheory.Branching
