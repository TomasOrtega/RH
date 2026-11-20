import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section
namespace GlobalTheory.KSp

section PairAlg

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

/- English proof (translation)
Establish `h : fromCols x (0 : Matrix α ν E) * stdJ ν E * ((fromCols (0 : Matrix α ν E) y).map c)ᵀ = x * (y.map c)ᵀ`. Use extensionality with `i k`. Simplify using `[stdJ, mul_apply, Fintype.sum_sum_type, one_apply]`. Rewrite using `[pr, form, hTens_eq, h]`. Use `congr 2`.

Simplify using `only [Matrix.trace, diag, mul_apply, transpose_apply]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem pr_eq_trace (Q : Matrix α α E) (x y : Matrix α ν E) :
    pr c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  have h : fromCols x (0 : Matrix α ν E) * stdJ ν E * ((fromCols (0 : Matrix α ν E) y).map c)ᵀ = x * (y.map c)ᵀ := by
    ext i k
    simp [stdJ, mul_apply, Fintype.sum_sum_type, one_apply]
  rw [pr, form, hTens_eq, h]
  congr 2
  simp only [Matrix.trace, diag, mul_apply, transpose_apply]
  rw [Finset.sum_comm]

/- English proof (translation)
Simplify using `[Matrix.trace, mul_apply, Matrix.single_apply, Finset.mul_sum, ite_and]`. Use `Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations.
-/
theorem trace_single_pair (Q : Matrix α α E) (y : Matrix α ν E) (i : α) (j : ν) (z : E) :
    Matrix.trace (Qᵀ * (Matrix.single i j z * (y.map c)ᵀ)) = z * (Q * y.map c) i j := by
  simp [Matrix.trace, mul_apply, Matrix.single_apply, Finset.mul_sum, ite_and]
  refine Finset.sum_congr rfl fun _ _ => by ring

def prLin (Q : Matrix α α E) : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))))
    (fun x x' y => by simp [Matrix.add_mul, Matrix.mul_add, mul_add])
    (fun t x y => by simp [Matrix.smul_mul, Matrix.mul_smul, mul_left_comm])
    (fun x y y' => by
      rw [show (y + y').map c = y.map c + y'.map c from Matrix.map_add _ (map_add c) _ _]
      simp [Matrix.add_mul, Matrix.mul_add, mul_add])
    (fun t x y => by
      rw [show (t • y).map c = t • y.map c from by ext i j; simp [map_smul]]
      simp [Matrix.smul_mul, Matrix.mul_smul, mul_left_comm])

end PairAlg

end GlobalTheory.KSp

namespace GlobalTheory.KSp

/- English proof (translation)
Introduce `F _ _ E _ _ c δ hE α _ _ ν _ _ Q hQ`. Establish `hc : ∀ z, c (c z) = z` using `hE.invol`. Establish `ht : ∀ z, Algebra.trace F E (c z) = Algebra.trace F E z` using `fun z => Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z`. Establish `hap : ∀ x y : Matrix α ν E, prLin c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ)))` using `fun _ _ => rfl`. Use `⟨prLin c Q, fun x y => by rw [hap, pr_eq_trace], fun x y => ?_, fun y hy => ?_, fun x y a => ?_, hap⟩` and prove the remaining obligations.

Establish `h : Matrix.trace (Qᵀ * (y * (x.map c)ᵀ)) = c (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ)))`. Simplify using `only [Matrix.trace, diag, mul_apply, transpose_apply, map_apply, map_sum, map_mul, hc, hQ.1]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Conclude with `congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)`.

Rewrite using `[hap, hap, h, ht]`. Take `⟨bE, -, -⟩` from `hE.basis`. Use `haveI : Module.Finite F E := Module.Finite.of_basis bE`. Establish `htr : Algebra.trace F E 1 ≠ 0`. Rewrite using `[← map_one (algebraMap F E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]`.

Conclude with `Nat.cast_ne_zero.mpr Module.finrank_pos.ne'`. Establish `hw : Q * y.map c = 0`. Use extensionality with `i j`. Assume the negation of the conclusion as `hij`. Apply `htr` to reduce the goal to its premises.

Use `hy (Matrix.single i j ((Q * y.map c) i j)⁻¹)` as an intermediate fact. Rewrite `this` using `[hap, trace_single_pair, inv_mul_cancel₀ hij]`. Simplify using `using this`. Establish `hy0 : y.map c = 0`. Use `congrArg (fun m => Q⁻¹ * m) hw` as an intermediate fact.

Simplify `this` using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ.2]`. Use extensionality with `i j`. Conclude with `c.toRingHom.injective (by simpa using congrFun (congrFun hy0 i) j)`. Establish `h : ((y * (a.map c)ᵀ).map c)ᵀ = a * (y.map c)ᵀ`. Use extensionality with `i j`.

Simplify using `[mul_apply, map_sum, hc, mul_comm]`. Rewrite using `[hap, hap, h, Matrix.mul_assoc]`.
-/
theorem pr_alg : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E)
    (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν]
    (Q : Matrix α α E) (_ : IsHerm c Q), ∃ β : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F,
      (∀ x y, β x y = pr c Q x y) ∧ (∀ x y, β x y = β y x) ∧ (∀ y, (∀ x, β x y = 0) → y = 0) ∧
      (∀ (x y : Matrix α ν E) (a : Matrix ν ν E), β (x * a) y = β x (y * (a.map c)ᵀ)) ∧
      ∀ x y, β x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  intro F _ _ E _ _ c δ hE α _ _ ν _ _ Q hQ
  have hc : ∀ z, c (c z) = z := hE.invol
  have ht : ∀ z, Algebra.trace F E (c z) = Algebra.trace F E z := fun z =>
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z
  have hap : ∀ x y : Matrix α ν E, prLin c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) :=
    fun _ _ => rfl
  refine ⟨prLin c Q, fun x y => by rw [hap, pr_eq_trace], fun x y => ?_, fun y hy => ?_, fun x y a => ?_, hap⟩
  ·
    have h : Matrix.trace (Qᵀ * (y * (x.map c)ᵀ)) = c (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
      simp only [Matrix.trace, diag, mul_apply, transpose_apply, map_apply, map_sum, map_mul, hc, hQ.1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      exact congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)
    rw [hap, hap, h, ht]
  ·
    obtain ⟨bE, -, -⟩ := hE.basis
    haveI : Module.Finite F E := Module.Finite.of_basis bE
    have htr : Algebra.trace F E 1 ≠ 0 := by
      rw [← map_one (algebraMap F E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
      exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have hw : Q * y.map c = 0 := by
      ext i j
      by_contra hij
      apply htr
      have := hy (Matrix.single i j ((Q * y.map c) i j)⁻¹)
      rw [hap, trace_single_pair, inv_mul_cancel₀ hij] at this
      simpa using this
    have hy0 : y.map c = 0 := by
      have := congrArg (fun m => Q⁻¹ * m) hw
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ.2] using this
    ext i j
    exact c.toRingHom.injective (by simpa using congrFun (congrFun hy0 i) j)
  ·
    have h : ((y * (a.map c)ᵀ).map c)ᵀ = a * (y.map c)ᵀ := by
      ext i j
      simp [mul_apply, map_sum, hc, mul_comm]
    rw [hap, hap, h, Matrix.mul_assoc]

end GlobalTheory.KSp
