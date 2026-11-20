import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.NoFixOne

open MvPolynomial Formalism.BasicNotions.TH

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add g h hg hh => simp only [map_add, hg, hh, Finset.sum_add_distrib, add_mul]`. Consider the case `mul_X g n hg`. Establish `e : ∀ l, pderiv l (g * X n) = g * (Pi.single l (1 : MvPolynomial σ ℂ) : σ → MvPolynomial σ ℂ) n + X n * pderiv l g`.

Introduce `l`. Rewrite using `[Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]`. Rewrite using `[map_mul, aeval_X, Polynomial.derivative_mul, hg]`. Repeatedly rewrite using `[e, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib]`. Rewrite using `[add_comm]`.

Use `congr 1`. Rewrite using `[Finset.sum_eq_single n]`. Simplify using the standard rewrite rules. Introduce `l _ hl`. Simplify using `[Pi.single_apply, Ne.symm hl]`.

Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_mul]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `l _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chain {σ : Type} [Fintype σ] [DecidableEq σ] (p : σ → Polynomial ℂ) (f : MvPolynomial σ ℂ) :
    Polynomial.derivative (MvPolynomial.aeval p f) =
      ∑ l, MvPolynomial.aeval p (MvPolynomial.pderiv l f) * Polynomial.derivative (p l) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add g h hg hh => simp only [map_add, hg, hh, Finset.sum_add_distrib, add_mul]
  | mul_X g n hg =>
    have e : ∀ l, pderiv l (g * X n) = g * (Pi.single l (1 : MvPolynomial σ ℂ) : σ → MvPolynomial σ ℂ) n + X n * pderiv l g := by
      intro l; rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
    rw [map_mul, aeval_X, Polynomial.derivative_mul, hg]
    simp_rw [e, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · rw [Finset.sum_eq_single n]
      · simp
      · intro l _ hl; simp [Pi.single_apply, Ne.symm hl]
      · simp
    · rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro l _; ring

/- English proof (translation)
Use extensionality with `j`. Establish `hc` using `congrArg (fun q => Polynomial.coeff q j) h`. Simplify using `only [Polynomial.coeff_neg, Polynomial.coeff_C_mul] at hc`. Break down `j with _ | n` into its components or cases. Rewrite `hc` using `[Polynomial.coeff_X_mul_zero]`.

Establish `: N ≠ 0` using `fun h0 => by simp [h0] at hN`. Simplify using `only [Polynomial.coeff_zero]`. Establish `: N * ψ.coeff 0 = 0` using `by linear_combination hc`. Conclude with `(mul_eq_zero.mp this).resolve_left ‹N ≠ 0›`. Rewrite `hc` using `[Polynomial.coeff_X_mul, Polynomial.coeff_derivative]`.

Establish `hne : N + ((n : ℂ) + 1) ≠ 0`. Introduce `h0`. Use `congrArg Complex.re h0` as an intermediate fact. Simplify using `at this`. Establish `: (0:ℝ) ≤ n` using `n.cast_nonneg`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [Polynomial.coeff_zero]`. Establish `: (N + ((n : ℂ) + 1)) * ψ.coeff (n + 1) = 0` using `by push_cast at hc; linear_combination hc`. Conclude with `(mul_eq_zero.mp this).resolve_left hne`.
-/
theorem ode (ψ : Polynomial ℂ) (N : ℂ) (hN : 0 < N.re)
    (h : Polynomial.X * Polynomial.derivative ψ = -(Polynomial.C N * ψ)) : ψ = 0 := by
  ext j
  have hc := congrArg (fun q => Polynomial.coeff q j) h
  simp only [Polynomial.coeff_neg, Polynomial.coeff_C_mul] at hc
  rcases j with _ | n
  · rw [Polynomial.coeff_X_mul_zero] at hc
    have : N ≠ 0 := fun h0 => by simp [h0] at hN
    simp only [Polynomial.coeff_zero]
    have : N * ψ.coeff 0 = 0 := by linear_combination hc
    exact (mul_eq_zero.mp this).resolve_left ‹N ≠ 0›
  · rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative] at hc
    have hne : N + ((n : ℂ) + 1) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      have : (0:ℝ) ≤ n := n.cast_nonneg
      linarith
    simp only [Polynomial.coeff_zero]
    have : (N + ((n : ℂ) + 1)) * ψ.coeff (n + 1) = 0 := by push_cast at hc; linear_combination hc
    exact (mul_eq_zero.mp this).resolve_left hne

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`. Simplify using `[Jm, Formalism.UG.Jpq, Matrix.mul_apply, Matrix.fromBlocks, Matrix.one_apply, Fintype.sum_sum_type]`. Use `hY (Sum.inl a) (Sum.inr b) (by simp [sameBlock]); simp [this]` as an intermediate fact. Use `hY (Sum.inr a) (Sum.inl b) (by simp [sameBlock]); simp [this]` as an intermediate fact.
-/
theorem jm_comm {P Q : ℕ} (Y : Mat P Q) (hY : IsKC Y) : Jm P Q * Y = Y * Jm P Q := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.mul_apply, Matrix.fromBlocks, Matrix.one_apply, Fintype.sum_sum_type]
  · have := hY (Sum.inl a) (Sum.inr b) (by simp [sameBlock]); simp [this]
  · have := hY (Sum.inr a) (Sum.inl b) (by simp [sameBlock]); simp [this]

/- English proof (translation)
Use `show Aᴴ * Jm P Q + Jm P Q * A = 0`. Rewrite using `[hs, jm_comm A hA]`. Simplify using the standard rewrite rules.
-/
theorem upq_of {P Q : ℕ} (A : Mat P Q) (hA : IsKC A) (hs : Aᴴ = -A) : A ∈ upq P Q := by
  show Aᴴ * Jm P Q + Jm P Q * A = 0
  rw [hs, jm_comm A hA]; simp

/- English proof (translation)
Introduce `a b hab`. Simplify using `only [Matrix.conjTranspose_apply]`. Apply the tactic sequence `rw [hY b a (by rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock])]; simp`.
-/
theorem kc_conj {P Q : ℕ} (Y : Mat P Q) (hY : IsKC Y) : IsKC Yᴴ := by
  intro a b hab
  simp only [Matrix.conjTranspose_apply]
  rw [hY b a (by rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock])]; simp

/- English proof (translation)
Use `set A : Mat P Q := (1/2 : ℂ) • (Y - Yᴴ) with hAdef`. Use `set B : Mat P Q := (1/(2*Complex.I)) • (Y + Yᴴ) with hBdef`. Establish `hYAB : Y = A + Complex.I • B`. Rewrite using `[hAdef, hBdef, smul_smul]`. Establish `: Complex.I * (1 / (2 * Complex.I)) = 1/2` using `by field_simp`.

Rewrite using `[this, ← smul_add]`. Use extensionality with `a b`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `hcY` using `kc_conj Y hY`.

Establish `sw : ∀ a b : Ix P Q, ¬ sameBlock a b → ¬ sameBlock b a`. Apply the tactic sequence `intro a b; rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock]`. Establish `hA1 : IsKC A` using `by intro a b hab; simp [hAdef, hY a b hab, hY b a (sw a b hab)]`. Establish `hB1 : IsKC B` using `by intro a b hab; simp [hBdef, hY a b hab, hY b a (sw a b hab)]`. Establish `hA2 : Aᴴ = -A`.

Rewrite using `[hAdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]`. Use extensionality with `a b`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `hB2 : Bᴴ = -B`.

Rewrite using `[hBdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]`. Establish `: star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I))`. Simplify using `[Complex.ext_iff, div_eq_mul_inv]`. Rewrite using `[this]`. Use extensionality with `a b`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `hA` using `h A hA1 (upq_of A hA1 hA2)`. Establish `hB` using `h B hB1 (upq_of B hB1 hB2)`. Use `clear_value A B`.

Use `clear hAdef hBdef`. Rewrite using `[hYAB, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Matrix.trace_add, Matrix.trace_smul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [smul_eq_mul]`. Use `module`.

Use `_ = 0 := by rw [hA, hB, smul_zero, add_zero]`.
-/
theorem ext_kc {P Q R S : ℕ} (c : ℂ) (f : Pol P Q R S)
    (h : ∀ Y : Mat P Q, IsKC Y → Y ∈ upq P Q → fockAct1 P Q R S Y f + (c * Y.trace) • f = 0)
    (Y : Mat P Q) (hY : IsKC Y) : fockAct1 P Q R S Y f + (c * Y.trace) • f = 0 := by
  set A : Mat P Q := (1/2 : ℂ) • (Y - Yᴴ) with hAdef
  set B : Mat P Q := (1/(2*Complex.I)) • (Y + Yᴴ) with hBdef
  have hYAB : Y = A + Complex.I • B := by
    rw [hAdef, hBdef, smul_smul]
    have : Complex.I * (1 / (2 * Complex.I)) = 1/2 := by field_simp
    rw [this, ← smul_add]; ext a b; simp; ring
  have hcY := kc_conj Y hY
  have sw : ∀ a b : Ix P Q, ¬ sameBlock a b → ¬ sameBlock b a := by
    intro a b; rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock]
  have hA1 : IsKC A := by intro a b hab; simp [hAdef, hY a b hab, hY b a (sw a b hab)]
  have hB1 : IsKC B := by intro a b hab; simp [hBdef, hY a b hab, hY b a (sw a b hab)]
  have hA2 : Aᴴ = -A := by
    rw [hAdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    ext a b; simp; ring
  have hB2 : Bᴴ = -B := by
    rw [hBdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    have : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
      simp [Complex.ext_iff, div_eq_mul_inv]
    rw [this]; ext a b; simp; ring
  have hA := h A hA1 (upq_of A hA1 hA2)
  have hB := h B hB1 (upq_of B hB1 hB2)
  clear_value A B
  clear hAdef hBdef
  rw [hYAB, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Matrix.trace_add, Matrix.trace_smul]
  calc _ = (fockAct1 P Q R S A f + (c * A.trace) • f) + Complex.I • (fockAct1 P Q R S B f + (c * B.trace) • f) := by
          simp only [smul_eq_mul]; module
    _ = 0 := by rw [hA, hB, smul_zero, add_zero]

section Comp
variable {P Q R S : ℕ}

def Yv (v u : Fin Q → ℂ) : Mat P Q := Matrix.fromBlocks 0 0 0 (Matrix.vecMulVec v u)

def dl (v : Fin Q → ℂ) (w : Fin R → ℂ) : Ix P Q × Ix R S → ℂ
  | (.inr a, .inl x) => v a * w x
  | _ => 0

/- English proof (translation)
Introduce `a b hab`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock, Yv]`.
-/
theorem Yv_kc (v u : Fin Q → ℂ) : IsKC (Yv (P := P) v u) := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock, Yv]

/- English proof (translation)
Simplify using `[Yv, Matrix.trace, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.vecMulVec_apply]`.
-/
theorem Yv_trace (v u : Fin Q → ℂ) : (Yv (P := P) v u).trace = ∑ a, v a * u a := by
  simp [Yv, Matrix.trace, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.vecMulVec_apply]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Simplify using `[Yv, Eab, Matrix.sum_apply, Matrix.single_apply, Matrix.vecMulVec_apply, ite_and, Finset.sum_ite_eq']`.
-/
theorem Yv_eq (v u : Fin Q → ℂ) :
    Yv (P := P) v u = ∑ a, ∑ b, (v a * u b) • Eab (Sum.inr a : Ix P Q) (Sum.inr b) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Yv, Eab, Matrix.sum_apply, Matrix.single_apply, Matrix.vecMulVec_apply, ite_and, Finset.sum_ite_eq']

/- English proof (translation)
Rewrite using `[omE, LinearMap.add_apply, Module.End.mul_apply]`. Simplify using `only [raiB, lowB, linePos, if_true, LinearMap.mulLeft_apply, Derivation.coeFn_coe]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`.
-/
theorem omE_pp (a b : Fin Q) (x : Fin S) (g : Pol P Q R S) :
    omE ((Sum.inr a : Ix P Q), (Sum.inr x : Ix R S)) (Sum.inr b, Sum.inr x) g =
      X (Sum.inr a, Sum.inr x) * pderiv (Sum.inr b, Sum.inr x) g + (if a = b then (1/2 : ℂ) else 0) • g := by
  rw [omE, LinearMap.add_apply, Module.End.mul_apply]
  simp only [raiB, lowB, linePos, if_true, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
  by_cases h : a = b
  · subst h; simp
  · simp [h]

/- English proof (translation)
Rewrite using `[omE, LinearMap.add_apply, Module.End.mul_apply]`. Simplify using `only [raiB, lowB, linePos, Bool.false_eq_true, if_false, LinearMap.neg_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, Derivation.leibniz, pderiv_X, smul_eq_mul]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Use `module`. Establish `hl : ((Sum.inr b : Ix P Q), (Sum.inl x : Ix R S)) ≠ (Sum.inr a, Sum.inl x)` using `by simp [Ne.symm h]`. Simplify using `[h, Pi.single_apply, hl]`.
-/
theorem omE_mm (a b : Fin Q) (x : Fin R) (g : Pol P Q R S) :
    omE ((Sum.inr a : Ix P Q), (Sum.inl x : Ix R S)) (Sum.inr b, Sum.inl x) g =
      -(X (Sum.inr b, Sum.inl x) * pderiv (Sum.inr a, Sum.inl x) g) - (if a = b then (1/2 : ℂ) else 0) • g := by
  rw [omE, LinearMap.add_apply, Module.End.mul_apply]
  simp only [raiB, lowB, linePos, Bool.false_eq_true, if_false, LinearMap.neg_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, Derivation.leibniz, pderiv_X, smul_eq_mul]
  by_cases h : a = b
  · subst h; simp; module
  · have hl : ((Sum.inr b : Ix P Q), (Sum.inl x : Ix R S)) ≠ (Sum.inr a, Sum.inl x) := by simp [Ne.symm h]
    simp [h, Pi.single_apply, hl]

/- English proof (translation)
Rewrite using `[fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]`. Simplify using `only [omE_pp, omE_mm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]`. Distinguish the cases in `h : a = b`. Simplify using `only [h, if_true]`.

Use `module`. Simplify using `only [h, if_false]`. Use `module`.
-/
theorem act_Eab (a b : Fin Q) (g : Pol P Q R S) :
    fockAct1 P Q R S (Eab (Sum.inr a : Ix P Q) (Sum.inr b)) g =
      (∑ x : Fin S, X (Sum.inr a, Sum.inr x) * pderiv (Sum.inr b, Sum.inr x) g)
      - (∑ x : Fin R, X (Sum.inr b, Sum.inl x) * pderiv (Sum.inr a, Sum.inl x) g)
      + (if a = b then (((S : ℂ) - R) / 2) else 0) • g := by
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [omE_pp, omE_mm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]
  by_cases h : a = b
  · simp only [h, if_true]; module
  · simp only [h, if_false]; module

/- English proof (translation)
Rewrite using `[Yv_eq]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, act_Eab, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Use `congr 1`. Use `congr 1`. Simplify using `only [Finset.smul_sum, Finset.sum_mul_sum]`.

Rewrite using `[Finset.sum_comm (s := (Finset.univ : Finset (Fin S)))]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm (s := (Finset.univ : Finset (Fin S)))]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_smul_comm]`.

Simplify using `only [Finset.smul_sum, Finset.sum_mul_sum]`. Rewrite using `[Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Fin R)))]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm (s := (Finset.univ : Finset (Fin R)))]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_mul_smul_comm, mul_comm (u b)]`. Rewrite using `[Finset.mul_sum, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single a]`. Simplify using `only [if_true, smul_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules.
-/
theorem act_Yv (v u : Fin Q → ℂ) (g : Pol P Q R S) :
    fockAct1 P Q R S (Yv v u) g =
      (∑ x : Fin S, (∑ a, v a • X (Sum.inr a, Sum.inr x)) * ∑ b, u b • pderiv (Sum.inr b, Sum.inr x) g)
      - (∑ x : Fin R, (∑ b, u b • X (Sum.inr b, Sum.inl x)) * ∑ a, v a • pderiv (Sum.inr a, Sum.inl x) g)
      + ((((S : ℂ) - R) / 2) * ∑ a, v a * u a) • g := by
  rw [Yv_eq]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, act_Eab, smul_add, smul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 1
  · congr 1
    · simp only [Finset.smul_sum, Finset.sum_mul_sum]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin S)))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin S)))]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => ?_
      rw [smul_mul_smul_comm]
    · simp only [Finset.smul_sum, Finset.sum_mul_sum]
      rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Fin R)))]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin R)))]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
      rw [smul_mul_smul_comm, mul_comm (u b)]
  · rw [Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · simp only [if_true, smul_smul]; congr 1; ring
    · intro b _ hb; simp [Ne.symm hb]
    · simp

def path (pt : Ix P Q × Ix R S → ℂ) (v : Fin Q → ℂ) (w : Fin R → ℂ) : Ix P Q × Ix R S → Polynomial ℂ :=
  fun l => Polynomial.C (pt l) - (1 - Polynomial.X) * Polynomial.C (dl v w l)

/- English proof (translation)
Simplify using `[path, Polynomial.derivative_mul]`.
-/
theorem path_deriv (pt : Ix P Q × Ix R S → ℂ) (v : Fin Q → ℂ) (w : Fin R → ℂ) (l : Ix P Q × Ix R S) :
    Polynomial.derivative (path pt v w l) = Polynomial.C (dl v w l) := by
  simp [path, Polynomial.derivative_mul]

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add g h hg hh => simp only [map_add, Polynomial.eval_add, hg, hh]`. Consider the case `mul_X g n hg => rw [map_mul, map_mul, Polynomial.eval_mul, hg]`. Simplify using `[path]`.
-/
theorem path_eval (pt : Ix P Q × Ix R S → ℂ) (v : Fin Q → ℂ) (w : Fin R → ℂ) (g : Pol P Q R S) :
    Polynomial.eval 1 (aeval (path pt v w) g) = MvPolynomial.eval pt g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add g h hg hh => simp only [map_add, Polynomial.eval_add, hg, hh]
  | mul_X g n hg => rw [map_mul, map_mul, Polynomial.eval_mul, hg]; simp [path]

/- English proof (translation)
Use `set w : Fin R → ℂ := fun x => ∑ b, u b * pt (Sum.inr b, Sum.inl x) with hw`. Establish `h1 : ∀ x : Fin S, aeval (path pt v w) (∑ a, v a • (X (Sum.inr a, Sum.inr x) : Pol P Q R S)) = 0`. Introduce `x`. Simplify using `only [map_sum, map_smul, aeval_X, path, dl, map_zero, mul_zero, sub_zero, Polynomial.smul_C, smul_eq_mul]`. Rewrite using `[← map_sum, hv, map_zero]`.

Establish `h2 : ∀ x : Fin R, aeval (path pt v w) (∑ b, u b • (X (Sum.inr b, Sum.inl x) : Pol P Q R S)) = Polynomial.X * Polynomial.C (w x)`. Introduce `x`. Simplify using `only [map_sum, map_smul, aeval_X, path, dl, smul_sub, Finset.sum_sub_distrib, Polynomial.smul_eq_C_mul]`. Establish `e1 : ∑ b, Polynomial.C (u b) * Polynomial.C (pt (Sum.inr b, Sum.inl x)) = Polynomial.C (w x)`. Simplify using `only [hw, map_sum, map_mul]`.

Establish `e2 : ∑ b, Polynomial.C (u b) * ((1 - Polynomial.X) * Polynomial.C (v b * w x)) = (1 - Polynomial.X) * Polynomial.C (w x)`. Establish `: Polynomial.C (w x) = Polynomial.C ((∑ a, v a * u a) * w x)` using `by rw [huv, one_mul]`. Rewrite using `[this, Finset.sum_mul, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[act_Yv, huv, mul_one, map_add, map_sub, map_sum, map_sum, chain, map_smul, Polynomial.smul_eq_C_mul]`. Simplify using `only [map_mul, h1, h2, zero_mul, Finset.sum_const_zero, path_deriv]`.

Rewrite using `[Fintype.sum_prod_type, Fintype.sum_sum_type]`. Simplify using `only [Fintype.sum_sum_type, dl, map_zero, mul_zero, Finset.sum_const_zero, add_zero, zero_add, map_sum, map_smul, Polynomial.smul_eq_C_mul]`. Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Establish `: ∀ x : Fin R, Polynomial.X * Polynomial.C (w x) * ∑ a, Polynomial.C (v a) * aeval (path pt v w) (pderiv ((Sum.inr a : Ix P Q), (Sum.inl x : Ix R S)) g) = Polynomial.X * ∑ a, aeval (path pt v w) (pderiv ((Sum.inr a : Ix P Q), (Sum.inl x : Ix R S)) g) * Polynomial.C (v a * w x)`. Introduce `x`.

Rewrite using `[mul_assoc, Finset.mul_sum]`. Use `congrArg (fun t => Polynomial.X * t) (Finset.sum_congr rfl fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem comp (pt : Ix P Q × Ix R S → ℂ) (v u : Fin Q → ℂ) (g : Pol P Q R S)
    (hv : ∀ x : Fin S, ∑ a, v a * pt (Sum.inr a, Sum.inr x) = 0) (huv : ∑ a, v a * u a = 1) :
    aeval (path pt v (fun x => ∑ b, u b * pt (Sum.inr b, Sum.inl x))) (fockAct1 P Q R S (Yv v u) g) =
      Polynomial.C (((S : ℂ) - R) / 2) * aeval (path pt v (fun x => ∑ b, u b * pt (Sum.inr b, Sum.inl x))) g
      - Polynomial.X * Polynomial.derivative
          (aeval (path pt v (fun x => ∑ b, u b * pt (Sum.inr b, Sum.inl x))) g) := by
  set w : Fin R → ℂ := fun x => ∑ b, u b * pt (Sum.inr b, Sum.inl x) with hw
  have h1 : ∀ x : Fin S, aeval (path pt v w) (∑ a, v a • (X (Sum.inr a, Sum.inr x) : Pol P Q R S)) = 0 := by
    intro x
    simp only [map_sum, map_smul, aeval_X, path, dl, map_zero, mul_zero, sub_zero, Polynomial.smul_C,
      smul_eq_mul]
    rw [← map_sum, hv, map_zero]
  have h2 : ∀ x : Fin R, aeval (path pt v w) (∑ b, u b • (X (Sum.inr b, Sum.inl x) : Pol P Q R S)) =
      Polynomial.X * Polynomial.C (w x) := by
    intro x
    simp only [map_sum, map_smul, aeval_X, path, dl, smul_sub, Finset.sum_sub_distrib,
      Polynomial.smul_eq_C_mul]
    have e1 : ∑ b, Polynomial.C (u b) * Polynomial.C (pt (Sum.inr b, Sum.inl x)) = Polynomial.C (w x) := by
      simp only [hw, map_sum, map_mul]
    have e2 : ∑ b, Polynomial.C (u b) * ((1 - Polynomial.X) * Polynomial.C (v b * w x)) =
        (1 - Polynomial.X) * Polynomial.C (w x) := by
      have : Polynomial.C (w x) = Polynomial.C ((∑ a, v a * u a) * w x) := by rw [huv, one_mul]
      rw [this, Finset.sum_mul, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [map_mul]; ring
    rw [e1, e2]; ring
  rw [act_Yv, huv, mul_one, map_add, map_sub, map_sum, map_sum, chain, map_smul, Polynomial.smul_eq_C_mul]
  simp only [map_mul, h1, h2, zero_mul, Finset.sum_const_zero, path_deriv]
  rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, dl, map_zero, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
    map_sum, map_smul, Polynomial.smul_eq_C_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  have : ∀ x : Fin R, Polynomial.X * Polynomial.C (w x) * ∑ a, Polynomial.C (v a) *
      aeval (path pt v w) (pderiv ((Sum.inr a : Ix P Q), (Sum.inl x : Ix R S)) g) =
      Polynomial.X * ∑ a, aeval (path pt v w) (pderiv ((Sum.inr a : Ix P Q), (Sum.inl x : Ix R S)) g) *
        Polynomial.C (v a * w x) := by
    intro x
    rw [mul_assoc, Finset.mul_sum]
    refine congrArg (fun t => Polynomial.X * t) (Finset.sum_congr rfl fun a _ => ?_)
    rw [map_mul]; ring
  simp only [this]
  ring

/- English proof (translation)
Establish `hk : LinearMap.ker (Matrix.vecMulLinear (Matrix.of Z)) ≠ ⊥`. Apply `LinearMap.ker_ne_bot_of_finrank_lt` to reduce the goal to its premises. Simplify using `using hSQ`. Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hk`. Use `⟨v, hv0, fun x => ?_⟩` and prove the remaining obligations.

Use `congrFun (LinearMap.mem_ker.mp hv) x` as an intermediate fact. Simplify `this` using `[Matrix.vecMul, dotProduct]`.
-/
theorem exists_ker (hSQ : S < Q) (Z : Fin Q → Fin S → ℂ) :
    ∃ v : Fin Q → ℂ, v ≠ 0 ∧ ∀ x, ∑ a, v a * Z a x = 0 := by
  have hk : LinearMap.ker (Matrix.vecMulLinear (Matrix.of Z)) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simpa using hSQ
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  refine ⟨v, hv0, fun x => ?_⟩
  have := congrFun (LinearMap.mem_ker.mp hv) x
  simpa [Matrix.vecMul, dotProduct] using this

end Comp

/- English proof (translation)
Introduce `P Q R S c f hSQ hc h`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `pt`. Take `⟨v, hv0, hv⟩` from `exists_ker hSQ (fun a x => pt (Sum.inr a, Sum.inr x))`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hv0`.

Establish `hi' : v i ≠ 0` using `hi`. Use `set u : Fin Q → ℂ := Pi.single i (v i)⁻¹ with hu`. Establish `huv : ∑ a, v a * u a = 1`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[hu, hi']`.

Introduce `b _ hb`. Simplify using `[hu, hb]`. Simplify using the standard rewrite rules. Establish `hY` using `ext_kc c f h (Yv v u) (Yv_kc v u)`. Rewrite `hY` using `[Yv_trace, huv, mul_one]`.

Establish `hc'` using `comp pt v u f hv huv`. Use `set w : Fin R → ℂ := fun x => ∑ b, u b * pt (Sum.inr b, Sum.inl x) with hw`. Establish `h2` using `congrArg (aeval (path pt v w)) hY`. Rewrite `h2` using `[map_add, map_zero, hc', map_smul, Polynomial.smul_eq_C_mul]`. Establish `hψ : aeval (path pt v w) f = 0`.

Apply `ode _ ((((R : ℂ) - S) / 2) - c)` to reduce the goal to its premises. Establish `: ((((R : ℂ) - S) / 2) - c).re = ((R : ℝ) - S) / 2 - c.re` using `by simp`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : Polynomial.C ((((R : ℂ) - S) / 2) - c) = -Polynomial.C (((S : ℂ) - R) / 2) - Polynomial.C c`.

Rewrite using `[← map_neg, ← map_sub]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Take the linear combination `-h2`.

Rewrite using `[← path_eval pt v w f, hψ]`. Simplify using the standard rewrite rules.
-/
theorem no_fixed_fock_polynomial : ∀ (P Q R S : ℕ) (c : ℂ) (f : Formalism.BasicNotions.TH.Pol P Q R S), S < Q → c.re < ((R : ℝ) - S) / 2 →
    (∀ Y : Formalism.BasicNotions.TH.Mat P Q, Formalism.BasicNotions.TH.IsKC Y → Y ∈ Formalism.BasicNotions.TH.upq P Q →
      Formalism.BasicNotions.TH.fockAct1 P Q R S Y f + (c * Y.trace) • f = 0) → f = 0 := by
  intro P Q R S c f hSQ hc h
  apply MvPolynomial.funext
  intro pt
  obtain ⟨v, hv0, hv⟩ := exists_ker hSQ (fun a x => pt (Sum.inr a, Sum.inr x))
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have hi' : v i ≠ 0 := hi
  set u : Fin Q → ℂ := Pi.single i (v i)⁻¹ with hu
  have huv : ∑ a, v a * u a = 1 := by
    rw [Finset.sum_eq_single i]
    · simp [hu, hi']
    · intro b _ hb; simp [hu, hb]
    · simp
  have hY := ext_kc c f h (Yv v u) (Yv_kc v u)
  rw [Yv_trace, huv, mul_one] at hY
  have hc' := comp pt v u f hv huv
  set w : Fin R → ℂ := fun x => ∑ b, u b * pt (Sum.inr b, Sum.inl x) with hw
  have h2 := congrArg (aeval (path pt v w)) hY
  rw [map_add, map_zero, hc', map_smul, Polynomial.smul_eq_C_mul] at h2
  have hψ : aeval (path pt v w) f = 0 := by
    apply ode _ ((((R : ℂ) - S) / 2) - c)
    · have : ((((R : ℂ) - S) / 2) - c).re = ((R : ℝ) - S) / 2 - c.re := by simp
      rw [this]; linarith
    · have e : Polynomial.C ((((R : ℂ) - S) / 2) - c) = -Polynomial.C (((S : ℂ) - R) / 2) - Polynomial.C c := by
        rw [← map_neg, ← map_sub]; congr 1; ring
      rw [e]; linear_combination -h2
  rw [← path_eval pt v w f, hψ]; simp

end GlobalTheory.NoFixOne
