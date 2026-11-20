import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

/- English proof (translation)
Simplify using `only [h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmLatticeHermitianForm_add_left (d : ℕ) (x y z : ℂ) : h1 d (x + y) z = h1 d x z + h1 d y z := by
  simp only [h1]; ring

/- English proof (translation)
Simplify using `only [h1, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmLatticeHermitianForm_add_right (d : ℕ) (x y z : ℂ) : h1 d x (y + z) = h1 d x y + h1 d x z := by
  simp only [h1, map_add]; ring

/- English proof (translation)
Establish `h : h1 d y x = conj (h1 d x y)`. Simplify using `only [h1, map_mul, Complex.conj_ofReal, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmLatticeHermitianForm_swap (d : ℕ) (x y : ℂ) :
    h1 d y x = h1 d x y - 2 * Complex.I * (((h1 d x y).im : ℝ) : ℂ) := by
  have h : h1 d y x = conj (h1 d x y) := by
    simp only [h1, map_mul, Complex.conj_ofReal, Complex.conj_conj]; ring
  rw [h]
  apply Complex.ext
  · simp
  · simp; ring

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [U1]`. Rewrite using `[mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc z x y]`. Use `congr 2`. Simplify using `only [cmLatticeHermitianForm_add_left, cmLatticeHermitianForm_add_right]`.

Rewrite using `[cmLatticeHermitianForm_swap d x y]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmLatticeTranslationOperator_comp (d : ℕ) (x y : ℂ) (F : ℂ → ℂ) :
    U1 d x (U1 d y F) = fun z => Complex.exp (-(Real.pi : ℂ) * Complex.I * (((h1 d x y).im : ℝ) : ℂ)) *
      U1 d (x + y) F z := by
  funext z
  simp only [U1]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc z x y]
  congr 2
  simp only [cmLatticeHermitianForm_add_left, cmLatticeHermitianForm_add_right]
  rw [cmLatticeHermitianForm_swap d x y]
  ring

/- English proof (translation)
Unfold `U1 h1`. Use `fun_prop`.
-/
theorem differentiable_cmLatticeTranslationOperator (d : ℕ) (x : ℂ) (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    Differentiable ℂ (U1 d x F) := by
  unfold U1 h1
  fun_prop

/- English proof (translation)
Take `⟨u, v, h⟩` from `h`. Establish `hs : Real.sqrt d ≠ 0`. Establish `: (0 : ℝ) < d` using `by exact_mod_cast hd`. Conclude with `(Real.sqrt_pos.2 this).ne'`. Establish `him : (h1 d x y).im = v`.

Rewrite using `[h1, h, wK, Complex.im_ofReal_mul]`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Establish `hre : Complex.normSq (x + y) = Complex.normSq x + Complex.normSq y + (2 * u + v)`. Rewrite using `[Complex.normSq_add, h, wK]`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Use function extensionality and compare the values at `z`. Establish `h2 : U1 d x (W1 d y F) z = Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq y : ℝ) : ℂ)) * U1 d x (U1 d y F) z`. Simplify using `only [U1, W1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : W1 d x (W1 d y F) z = Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) * U1 d x (W1 d y F) z` using `rfl`. Rewrite using `[h3, h2, cmLatticeTranslationOperator_comp]`. Simplify using `only [W1]`. Rewrite using `[← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add, him, hre]`.

Use `congr 1`. Rewrite using `[Complex.exp_eq_exp_iff_exists_int]`. Use `⟨-(u + v), ?_⟩` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmLatticeWeylOperator_comp (d : ℕ) (hd : 0 < d) (x y : ℂ) (F : ℂ → ℂ) (h : InOK d (x * conj y)) :
    W1 d x (W1 d y F) = W1 d (x + y) F := by
  obtain ⟨u, v, h⟩ := h
  have hs : Real.sqrt d ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact (Real.sqrt_pos.2 this).ne'
  have him : (h1 d x y).im = v := by
    rw [h1, h, wK, Complex.im_ofReal_mul]
    simp
    field_simp
  have hre : Complex.normSq (x + y) = Complex.normSq x + Complex.normSq y + (2 * u + v) := by
    rw [Complex.normSq_add, h, wK]
    simp
    ring
  funext z
  have h2 : U1 d x (W1 d y F) z = Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq y : ℝ) : ℂ)) *
      U1 d x (U1 d y F) z := by
    simp only [U1, W1]; ring
  have h3 : W1 d x (W1 d y F) z = Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) *
      U1 d x (W1 d y F) z := rfl
  rw [h3, h2, cmLatticeTranslationOperator_comp]
  simp only [W1]
  rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add, him, hre]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(u + v), ?_⟩
  push_cast
  ring

/- English proof (translation)
Establish `a` using `congrFun h z`. Establish `b` using `congrFun h (z + t)`. Simplify using `only [W1, U1] at a b`. Simplify using `only [U1, kap1]`. Establish `e : z + l + t = z + t + l` using `by ring`.

Rewrite using `[e]`. Use `set A := θ (z + t + l)`. Use `set B := θ (z + l)`. Rewrite using `[← a, ← b]`. Establish `key : Complex.exp (-(Real.pi : ℂ) * h1 d (z + l) t - (Real.pi : ℂ) / 2 * h1 d t t) * Complex.exp (-(Real.pi : ℂ) * h1 d z l - (Real.pi : ℂ) / 2 * h1 d l l) = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (((h1 d l t).im : ℝ) : ℂ)) * (Complex.exp (-(Real.pi : ℂ) * h1 d (z + t) l …`.

Rewrite using `[← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Simplify using `only [cmLatticeHermitianForm_add_left]`. Rewrite using `[cmLatticeHermitianForm_swap d l t]`. Expand and normalize the polynomial expressions, which then agree.

Take the linear combination `(A * B * Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq l : ℝ) : ℂ))) * key`.
-/
theorem cmLatticeTranslationOperator_theta_quasiPeriodicity (d : ℕ) (θ : ℂ → ℂ) (t l z : ℂ) (h : W1 d l θ = θ) :
    U1 d t θ (z + l) * θ z = kap1 d l t * (U1 d t θ z * θ (z + l)) := by
  have a := congrFun h z
  have b := congrFun h (z + t)
  simp only [W1, U1] at a b
  simp only [U1, kap1]
  have e : z + l + t = z + t + l := by ring
  rw [e]
  set A := θ (z + t + l)
  set B := θ (z + l)
  rw [← a, ← b]
  have key : Complex.exp (-(Real.pi : ℂ) * h1 d (z + l) t - (Real.pi : ℂ) / 2 * h1 d t t) *
      Complex.exp (-(Real.pi : ℂ) * h1 d z l - (Real.pi : ℂ) / 2 * h1 d l l) =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (((h1 d l t).im : ℝ) : ℂ)) *
      (Complex.exp (-(Real.pi : ℂ) * h1 d (z + t) l - (Real.pi : ℂ) / 2 * h1 d l l) *
      Complex.exp (-(Real.pi : ℂ) * h1 d z t - (Real.pi : ℂ) / 2 * h1 d t t)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [cmLatticeHermitianForm_add_left]
    rw [cmLatticeHermitianForm_swap d l t]
    ring
  linear_combination (A * B * Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq l : ℝ) : ℂ))) * key

/- English proof (translation)
Introduce `d hd`. Use `⟨cmLatticeTranslationOperator_comp d, ?_, ?_, ?_, fun x y F _ h => cmLatticeWeylOperator_comp d hd x y F h, fun θ t l z h => cmLatticeTranslationOperator_theta_quasiPeriodicity d θ t l z h, ?_, ?_⟩` and prove the remaining obligations. Introduce `F`. Use function extensionality and compare the values at `z`. Simplify using `[U1, h1]`.

Introduce `x F hF`. Use `⟨differentiable_cmLatticeTranslationOperator d x F hF, ?_⟩` and prove the remaining obligations. Conclude with `(differentiable_cmLatticeTranslationOperator d x F hF).const_mul _`. Introduce `x F z`. Simplify using `only [U1, h1, map_neg]`.

Use `congr 1`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Introduce `x f F z`. Simplify using `only [W1, U1]`. Apply the tactic sequence `constructor <;> ring`. Introduce `x y z`. Simplify using `only [kap1, cmLatticeHermitianForm_add_left, cmLatticeHermitianForm_add_right, Complex.add_im, ← Complex.exp_add]`.

Apply the tactic sequence `constructor <;> (congr 1; push_cast; ring)`.
-/
theorem heisenbergOne : ∀ d : ℕ, 0 < d → (∀ (x y : ℂ) (F : ℂ → ℂ), U1 d x (U1 d y F) = fun z => Complex.exp (-(Real.pi : ℂ) * Complex.I * (((h1 d x y).im : ℝ) : ℂ)) * U1 d (x + y) F z) ∧ (∀ F, U1 d 0 F = F) ∧ (∀ (x : ℂ) (F : ℂ → ℂ), Differentiable ℂ F → Differentiable ℂ (U1 d x F) ∧ Differentiable ℂ (W1 d x F)) ∧ (∀ (x : ℂ) (F : ℂ → ℂ) (z : ℂ), U1 d x (fun z => F (-z)) z = U1 d (-x) F (-z)) ∧ (∀ (x y : ℂ) (F : ℂ → ℂ), d % 4 = 3 → InOK d (x * conj y) → W1 d x (W1 d y F) = W1 d (x + y) F) ∧ (∀ (θ : ℂ → ℂ) (t l z : ℂ), W1 d l θ = θ → U1 d t θ (z + l) * θ z = kap1 d l t * (U1 d t θ z * θ (z + l))) ∧ (∀ (x : ℂ) (f F : ℂ → ℂ) (z : ℂ), W1 d x (fun z => f z * F z) z = f (z + x) * W1 d x F z ∧ U1 d x (fun z => f z * F z) z = f (z + x) * U1 d x F z) ∧ ∀ (x y z : ℂ), kap1 d x (y + z) = kap1 d x y * kap1 d x z ∧ kap1 d (x + y) z = kap1 d x z * kap1 d y z := by
  intro d hd
  refine ⟨cmLatticeTranslationOperator_comp d, ?_, ?_, ?_, fun x y F _ h => cmLatticeWeylOperator_comp d hd x y F h,
    fun θ t l z h => cmLatticeTranslationOperator_theta_quasiPeriodicity d θ t l z h, ?_, ?_⟩
  · intro F
    funext z
    simp [U1, h1]
  · intro x F hF
    refine ⟨differentiable_cmLatticeTranslationOperator d x F hF, ?_⟩
    exact (differentiable_cmLatticeTranslationOperator d x F hF).const_mul _
  · intro x F z
    simp only [U1, h1, map_neg]
    congr 1
    · congr 1; ring
    · congr 1; ring
  · intro x f F z
    simp only [W1, U1]
    constructor <;> ring
  · intro x y z
    simp only [kap1, cmLatticeHermitianForm_add_left, cmLatticeHermitianForm_add_right, Complex.add_im, ← Complex.exp_add]
    constructor <;> (congr 1; push_cast; ring)

end GlobalTheory.MomOne
