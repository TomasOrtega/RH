import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.GelfCyc

open GlobalTheory.SmoothForms (gelfA gelfA_eq_sum_pow)

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

/- English proof (translation)
Establish `hPQ : P * Q = 1` using `mul_eq_one_comm.1 hQP`. Set `φ : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) A` to `(algebraMap ℂ A).mapMatrix`. Establish `hc : ∀ (M : Matrix (Fin n) (Fin n) A) a b, (φ P * M * φ Q) a b = ∑ c, ∑ d, (P a c * Q d b) • M c d`. Introduce `M a b`. Simplify using `only [Matrix.mul_apply, φ, RingHom.mapMatrix_apply, Matrix.map_apply, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← Algebra.smul_def, ← Algebra.commutes, ← Algebra.smul_def, smul_smul, mul_comm]`. Establish `h1 : (Matrix.of fun a b => ∑ c, ∑ d, (P a c * Q d b) • G c d) = φ P * Matrix.of G * φ Q`. Use extensionality with `a b`.

Rewrite using `[hc]`. Both sides reduce to the same expression. Establish `h2 : ∀ m : ℕ, (φ P * Matrix.of G * φ Q) ^ m = φ P * Matrix.of G ^ m * φ Q`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => rw [pow_zero, pow_zero, mul_one, ← map_mul, hPQ, map_one]`. Consider the case `succ m ih`. Establish `: φ Q * φ P = 1` using `by rw [← map_mul, hQP, map_one]`. Rewrite using `[pow_succ, pow_succ, ih]`. Simplify using `only [mul_assoc]`.

Rewrite using `[← mul_assoc (φ Q), this, one_mul]`. Rewrite using `[gelfA_eq_sum_pow, gelfA_eq_sum_pow, h1, h2]`. Simplify using `only [hc]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Establish `: ∀ d, ∑ a, (P a c * Q d a) • (Matrix.of G ^ (k + 1)) c d = (Q * P) d c • (Matrix.of G ^ (k + 1)) c d`. Introduce `d`. Rewrite using `[← Finset.sum_smul, Matrix.mul_apply]`. Simplify using `only [mul_comm]`.

Simplify using `[this, hQP, Matrix.one_apply]`.
-/
theorem gelfA_conj (G : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (k : ℕ) :
    gelfA (fun a b => ∑ c, ∑ d, (P a c * Q d b) • G c d) k = gelfA G k := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  let φ : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix
  have hc : ∀ (M : Matrix (Fin n) (Fin n) A) a b, (φ P * M * φ Q) a b = ∑ c, ∑ d, (P a c * Q d b) • M c d := by
    intro M a b
    simp only [Matrix.mul_apply, φ, RingHom.mapMatrix_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [← Algebra.smul_def, ← Algebra.commutes, ← Algebra.smul_def, smul_smul, mul_comm]
  have h1 : (Matrix.of fun a b => ∑ c, ∑ d, (P a c * Q d b) • G c d) = φ P * Matrix.of G * φ Q := by
    ext a b
    rw [hc]
    rfl
  have h2 : ∀ m : ℕ, (φ P * Matrix.of G * φ Q) ^ m = φ P * Matrix.of G ^ m * φ Q := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, mul_one, ← map_mul, hPQ, map_one]
    | succ m ih =>
      have : φ Q * φ P = 1 := by rw [← map_mul, hQP, map_one]
      rw [pow_succ, pow_succ, ih]
      simp only [mul_assoc]
      rw [← mul_assoc (φ Q), this, one_mul]
  rw [gelfA_eq_sum_pow, gelfA_eq_sum_pow, h1, h2]
  simp only [hc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  have : ∀ d, ∑ a, (P a c * Q d a) • (Matrix.of G ^ (k + 1)) c d = (Q * P) d c • (Matrix.of G ^ (k + 1)) c d := by
    intro d
    rw [← Finset.sum_smul, Matrix.mul_apply]
    simp only [mul_comm]
  simp [this, hQP, Matrix.one_apply]

/- English proof (translation)
Rewrite using `[gelfA]`. Use `(Fintype.sum_equiv ((Equiv.neg (Fin (k + 1))).arrowCongr (Equiv.refl _)) _ _ fun idx => ?_).symm` and prove the remaining obligations. Use `congr 1`. Establish `h : ∀ a : Fin (k + 1), a.rev + 1 = -a` using `fun a => by`. Establish `: a.rev + a = Fin.last k` using `Fin.ext (by`.

Use `a.2` as an intermediate fact. Apply the tactic sequence `rw [Fin.val_add, Fin.val_rev, Fin.val_last, Nat.mod_eq_of_lt] <;> omega)`. Rewrite using `[eq_neg_iff_add_eq_zero, add_right_comm, this, Fin.last_add_one]`. Establish `h' : ∀ a : Fin (k + 1), a.rev = -(a + 1)` using `fun a => by`. Rewrite using `[neg_add, ← h, add_neg_cancel_right]`.

Establish `e : ∀ g : Fin (k + 1) → A, (List.ofFn g).reverse = List.ofFn fun a => g a.rev` using `fun g => by`. Apply `List.ext_getElem` to reduce the goal to its premises. Simplify using the standard rewrite rules. Introduce `i h1 h2`. Simplify using `only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]`.

Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Rewrite using `[h, h']`. Both sides reduce to the same expression.
-/
theorem gelfA_swap (E : Fin n → Fin n → A) (k : ℕ) :
    gelfA (fun a b => E b a) k = ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => E (idx a) (idx (a + 1))).reverse.prod := by
  rw [gelfA]
  refine (Fintype.sum_equiv ((Equiv.neg (Fin (k + 1))).arrowCongr (Equiv.refl _)) _ _ fun idx => ?_).symm
  congr 1
  have h : ∀ a : Fin (k + 1), a.rev + 1 = -a := fun a => by
    have : a.rev + a = Fin.last k := Fin.ext (by
      have := a.2
      rw [Fin.val_add, Fin.val_rev, Fin.val_last, Nat.mod_eq_of_lt] <;> omega)
    rw [eq_neg_iff_add_eq_zero, add_right_comm, this, Fin.last_add_one]
  have h' : ∀ a : Fin (k + 1), a.rev = -(a + 1) := fun a => by
    rw [neg_add, ← h, add_neg_cancel_right]
  have e : ∀ g : Fin (k + 1) → A, (List.ofFn g).reverse = List.ofFn fun a => g a.rev := fun g => by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
      congr 1
      ext
      simp
  rw [e]
  congr 1
  funext a
  rw [h, h']
  rfl

/- English proof (translation)
The claim follows from `| 0, _ => by simp | m + 1, g => by rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, prod_ofFn_neg m fun a => g a.succ, pow_succ] simp`.
-/
theorem prod_ofFn_neg : ∀ (m : ℕ) (g : Fin m → A),
    (List.ofFn fun a => -g a).prod = (-1 : ℂ) ^ m • (List.ofFn g).prod
  | 0, _ => by simp
  | m + 1, g => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, prod_ofFn_neg m fun a => g a.succ, pow_succ]
    simp

/- English proof (translation)
Establish `e : ∀ a b, φ (M * (Matrix.single a b 1)ᵀ * M⁻¹) = ∑ c, ∑ d, (M⁻¹ a c * M d b) • φ (Matrix.single d c 1)`. Introduce `a b`. Simplify using `only [← map_smul, ← map_sum]`. Use `congr 1`. Rewrite using `[Matrix.matrix_eq_sum_single (M * _ * _), Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one]`. Use `congr 1`. Simplify using `[Matrix.mul_apply, Matrix.single, ite_and, mul_comm]`. Rewrite using `[← gelfA_swap (fun a b => φ (Matrix.single a b 1)), ← gelfA_conj _ M⁻¹ M (Matrix.mul_nonsing_inv M hM), gelfA, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun idx _ => ?_` and prove the remaining obligations. Simplify using `only [map_neg, e]`. Conclude with `prod_ofFn_neg _ _`.
-/
theorem sum_words (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M.det) (k : ℕ) :
    ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (-(M * (Matrix.single (idx a) (idx (a + 1)) 1)ᵀ * M⁻¹))).prod =
    (-1 : ℂ) ^ (k + 1) • ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (Matrix.single (idx a) (idx (a + 1)) 1)).reverse.prod := by
  have e : ∀ a b, φ (M * (Matrix.single a b 1)ᵀ * M⁻¹) = ∑ c, ∑ d, (M⁻¹ a c * M d b) • φ (Matrix.single d c 1) := by
    intro a b
    simp only [← map_smul, ← map_sum]
    congr 1
    rw [Matrix.matrix_eq_sum_single (M * _ * _), Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    simp [Matrix.mul_apply, Matrix.single, ite_and, mul_comm]
  rw [← gelfA_swap (fun a b => φ (Matrix.single a b 1)),
    ← gelfA_conj _ M⁻¹ M (Matrix.mul_nonsing_inv M hM), gelfA, Finset.smul_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  simp only [map_neg, e]
  exact prod_ofFn_neg _ _

end Alg

open GlobalTheory.Mem.RealTranslate (derEnd)

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons Z w ih`. Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply]`. Use `show RderC θ V τ Z (wordDer θ V τ w f.1) = _`.

Rewrite using `[ih]`. Both sides reduce to the same expression.
-/
theorem wordDer_eq {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (τ : D.what₂.Tau)
    (w : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (f : SmFun θ V) :
    wordDer θ V τ w f.1 = ((w.map (derEnd hθ τ)).prod f).1 := by
  induction w with
  | nil => rfl
  | cons Z w ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    show RderC θ V τ Z (wordDer θ V τ w f.1) = _
    rw [ih]
    rfl

end GlobalTheory.RegSch.GelfCyc

end
