import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeH
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.DetSqSplit

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simpa using hasDerivAt_const (0 : ℂ) a`. Consider the case `add p q hp hq`. Establish `e1 : (fun t => MvPolynomial.eval (g t) (p + q)) = fun t => MvPolynomial.eval (g t) p + MvPolynomial.eval (g t) q`. Use function extensionality and compare the values at `t`.

Rewrite using `[map_add]`. Rewrite using `[e1]`. Use `(hp.add hq).congr_deriv ?_` and prove the remaining obligations. Simplify using `only [map_add, add_mul, Finset.sum_add_distrib]`. Consider the case `mul_X p k0 hp`.

Establish `h` using `hp.mul (hg k0)`. Establish `e1 : (fun t => MvPolynomial.eval (g t) (p * MvPolynomial.X k0)) = fun t => MvPolynomial.eval (g t) p * g t k0`. Use function extensionality and compare the values at `t`. Rewrite using `[map_mul, MvPolynomial.eval_X]`. Rewrite using `[e1]`.

Use `h.congr_deriv ?_` and prove the remaining obligations. Use `symm`. Simplify using `only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, map_add, map_mul, MvPolynomial.eval_X, add_mul, Finset.sum_add_distrib]`. Establish `e : ∑ k, MvPolynomial.eval (g 0) p * MvPolynomial.eval (g 0) ((Pi.single k (1 : MvPolynomial ι ℂ) : ι → MvPolynomial ι ℂ) k0) * g' k = MvPolynomial.eval (g 0) p * g' k0`. Rewrite using `[Finset.sum_eq_single k0]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_apply, Ne.symm hb]`. Simplify using the standard rewrite rules. Rewrite using `[e, Finset.sum_mul]`.

Establish `e2 : ∑ k, g 0 k0 * MvPolynomial.eval (g 0) (MvPolynomial.pderiv k p) * g' k = ∑ k, MvPolynomial.eval (g 0) (MvPolynomial.pderiv k p) * g' k * g 0 k0` using `Finset.sum_congr rfl fun k _ => by ring`. Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_eval {ι : Type} [Fintype ι] [DecidableEq ι] (g : ℂ → ι → ℂ) (g' : ι → ℂ)
    (hg : ∀ k, HasDerivAt (fun t => g t k) (g' k) 0) (P : MvPolynomial ι ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (g t) P)
      (∑ k, MvPolynomial.eval (g 0) (MvPolynomial.pderiv k P) * g' k) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (0 : ℂ) a
  | add p q hp hq =>
    have e1 : (fun t => MvPolynomial.eval (g t) (p + q)) =
        fun t => MvPolynomial.eval (g t) p + MvPolynomial.eval (g t) q := by
      funext t; rw [map_add]
    rw [e1]
    refine (hp.add hq).congr_deriv ?_
    simp only [map_add, add_mul, Finset.sum_add_distrib]
  | mul_X p k0 hp =>
    have h := hp.mul (hg k0)
    have e1 : (fun t => MvPolynomial.eval (g t) (p * MvPolynomial.X k0)) =
        fun t => MvPolynomial.eval (g t) p * g t k0 := by
      funext t; rw [map_mul, MvPolynomial.eval_X]
    rw [e1]
    refine h.congr_deriv ?_
    symm
    simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, map_add, map_mul, MvPolynomial.eval_X,
      add_mul, Finset.sum_add_distrib]
    have e : ∑ k, MvPolynomial.eval (g 0) p * MvPolynomial.eval (g 0) ((Pi.single k (1 : MvPolynomial ι ℂ) : ι → MvPolynomial ι ℂ) k0) * g' k =
        MvPolynomial.eval (g 0) p * g' k0 := by
      rw [Finset.sum_eq_single k0]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, Ne.symm hb]
      · simp
    rw [e, Finset.sum_mul]
    have e2 : ∑ k, g 0 k0 * MvPolynomial.eval (g 0) (MvPolynomial.pderiv k p) * g' k =
        ∑ k, MvPolynomial.eval (g 0) (MvPolynomial.pderiv k p) * g' k * g 0 k0 :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [e2]
    ring

def cB (s : ℂ) (b : Bool) : ℂ := if b then Complex.I * s else -(Complex.I * s)

def alB (m : ℕ) (b : Bool) : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X

/- English proof (translation)
Rewrite using `[Algebra.smul_def, MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply]`. Both sides reduce to the same expression.
-/
theorem smulC (a : ℂ) (P : Fm n) : a • P = MvPolynomial.C (Polynomial.C a) * P := by
  rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply]
  rfl

def multPart (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : Fm n →ₗ[ℂ] Fm n :=
  (-(cB s b)) • (LinearMap.mulLeft ℂ (MvPolynomial.C (alB m b) * yv b l k)).restrictScalars ℂ

def derPart (s : ℂ) (b : Bool) (k l : Fin n) : Fm n →ₗ[ℂ] Fm n :=
  ∑ a : Fin n, ∑ d : Fin n, (-(cB s b)) •
    (LinearMap.mulLeft ℂ (yv b a k * yv b l d) ∘ₗ (MvPolynomial.pderiv (b, a, d)).toLinearMap.restrictScalars ℂ)

/- English proof (translation)
Apply the tactic sequence `cases b <;> rfl`.
-/
theorem opH_eq (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : opH s m b k l = multPart s m b k l + derPart s b k l := by
  cases b <;> rfl

/- English proof (translation)
Rewrite using `[multPart, LinearMap.smul_apply, smulC]`. Both sides reduce to the same expression.
-/
theorem multPart_apply (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (Q : Fm n) :
    multPart s m b k l Q = MvPolynomial.C (Polynomial.C (-(cB s b))) * (MvPolynomial.C (alB m b) * yv b l k * Q) := by
  rw [multPart, LinearMap.smul_apply, smulC]
  rfl

/- English proof (translation)
Rewrite using `[derPart, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, smulC]`.

Both sides reduce to the same expression.
-/
theorem derPart_apply (s : ℂ) (b : Bool) (k l : Fin n) (Q : Fm n) :
    derPart s b k l Q = ∑ a : Fin n, ∑ d : Fin n, MvPolynomial.C (Polynomial.C (-(cB s b))) *
      (yv b a k * yv b l d * MvPolynomial.pderiv (b, a, d) Q) := by
  rw [derPart, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply, smulC]
  rfl

end PositivityTheory.Rg.Sw.SP
