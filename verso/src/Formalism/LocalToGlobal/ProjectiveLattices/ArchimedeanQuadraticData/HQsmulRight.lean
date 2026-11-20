import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.RhoDotSelf
import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}

def Phi (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) (v : Fin r → K) : ι → Fin r → ℂ :=
  fun i => Q i *ᵥ embVec (σ i) v

def Theta (p : ℕ) (w : ι → Fin r → ℂ) : ι → Fin r → ℂ := fun i a => sgn p a * w i a

/- English proof (translation)
Unfold `sgn`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sgn_conj (p : ℕ) (a : Fin r) : conj (sgn p a) = sgn p a := by
  unfold sgn
  split_ifs <;> simp

/- English proof (translation)
Unfold `sgn`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sgn_norm (p : ℕ) (a : Fin r) : ‖sgn p a‖ = 1 := by
  unfold sgn
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `a`. Simplify using `[embVec]`.
-/
theorem embVec_add (τ : K →+* ℂ) (x y : Fin r → K) : embVec τ (x + y) = embVec τ x + embVec τ y := by
  ext a
  simp [embVec]

/- English proof (translation)
Use extensionality with `a`. Simplify using `[embVec]`.
-/
theorem embVec_smul (τ : K →+* ℂ) (c : K) (x : Fin r → K) : embVec τ (c • x) = τ c • embVec τ x := by
  ext a
  simp [embVec]

/- English proof (translation)
Use extensionality with `a`. Simplify using `[embVec, Rat.smul_def, map_ratCast]`.
-/
theorem embVec_qsmul (τ : K →+* ℂ) (q : ℚ) (x : Fin r → K) : embVec τ (q • x) = (q : ℂ) • embVec τ x := by
  ext a
  simp [embVec, Rat.smul_def, map_ratCast]

/- English proof (translation)
Use extensionality with `i a`. Simplify using `[Phi, embVec_add, Matrix.mulVec_add]`.
-/
theorem Phi_add (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) (x y : Fin r → K) :
    Phi σ Q (x + y) = Phi σ Q x + Phi σ Q y := by
  ext i a
  simp [Phi, embVec_add, Matrix.mulVec_add]

/- English proof (translation)
Use extensionality with `i a`. Simplify using `[Phi, embVec_qsmul, Matrix.mulVec_smul, Complex.ofReal_ratCast]`.
-/
theorem Phi_qsmul (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) (q : ℚ) (x : Fin r → K) :
    Phi σ Q (q • x) = ((q : ℝ) : ℂ) • Phi σ Q x := by
  ext i a
  simp [Phi, embVec_qsmul, Matrix.mulVec_smul, Complex.ofReal_ratCast]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Phi, embVec_smul, Matrix.mulVec_smul]`.
-/
theorem Phi_smul (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) (c : K) (x : Fin r → K) :
    Phi σ Q (c • x) = fun i => σ i c • Phi σ Q x i := by
  funext i
  simp [Phi, embVec_smul, Matrix.mulVec_smul]

/- English proof (translation)
Establish `h : ∀ i, embVec (σ i) (0 : Fin r → K) = 0` using `fun i => by ext a; simp [embVec]`. Use extensionality with `i a`. Simplify using `[Phi, h]`.
-/
theorem Phi_zero (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) : Phi σ Q (0 : Fin r → K) = 0 := by
  have h : ∀ i, embVec (σ i) (0 : Fin r → K) = 0 := fun i => by ext a; simp [embVec]
  ext i a
  simp [Phi, h]

/- English proof (translation)
Conclude with `map_sum (AddMonoidHom.mk' (Phi σ Q) (Phi_add σ Q)) x s`.
-/
theorem Phi_sum (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) {κ : Type} (s : Finset κ)
    (x : κ → Fin r → K) : Phi σ Q (∑ j ∈ s, x j) = ∑ j ∈ s, Phi σ Q (x j) := by
  exact map_sum (AddMonoidHom.mk' (Phi σ Q) (Phi_add σ Q)) x s

section Herm

variable (S : HermForm K r)

/- English proof (translation)
Simplify using `only [HermForm.h, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem h_add_left (x x' y : Fin r → K) : S.h (x + x') y = S.h x y + S.h x' y := by
  simp only [HermForm.h, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [HermForm.h, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem h_add_right (x y y' : Fin r → K) : S.h x (y + y') = S.h x y + S.h x y' := by
  simp only [HermForm.h, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem h_smul_left (c : K) (x y : Fin r → K) : S.h (c • x) y = S.c c * S.h x y := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Simplify using `only [HermForm.h, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem h_smul_right (c : K) (x y : Fin r → K) : S.h x (c • y) = c * S.h x y := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Establish `hq : q • x = (q : K) • x` using `by ext a; simp [Rat.smul_def]`. Rewrite using `[hq, h_smul_left, map_ratCast]`.
-/
theorem h_qsmul_left (q : ℚ) (x y : Fin r → K) : S.h (q • x) y = (q : K) * S.h x y := by
  have hq : q • x = (q : K) • x := by ext a; simp [Rat.smul_def]
  rw [hq, h_smul_left, map_ratCast]

/- English proof (translation)
Establish `hq : q • y = (q : K) • y` using `by ext a; simp [Rat.smul_def]`. Rewrite using `[hq, h_smul_right]`.
-/
theorem h_qsmul_right (q : ℚ) (x y : Fin r → K) : S.h x (q • y) = (q : K) * S.h x y := by
  have hq : q • y = (q : K) • y := by ext a; simp [Rat.smul_def]
  rw [hq, h_smul_right]

/- English proof (translation)
Simplify using `[HermForm.h]`.
-/
theorem h_zero_left (y : Fin r → K) : S.h 0 y = 0 := by
  simp [HermForm.h]

/- English proof (translation)
Conclude with `map_sum (AddMonoidHom.mk' (fun x => S.h x y) (fun a b => h_add_left S a b y)) x s`.
-/
theorem h_sum_left {κ : Type} (s : Finset κ) (x : κ → Fin r → K) (y : Fin r → K) :
    S.h (∑ j ∈ s, x j) y = ∑ j ∈ s, S.h (x j) y := by
  exact map_sum (AddMonoidHom.mk' (fun x => S.h x y) (fun a b => h_add_left S a b y)) x s

/- English proof (translation)
Conclude with `map_sum (AddMonoidHom.mk' (fun y => S.h x y) (fun a b => h_add_right S x a b)) y s`.
-/
theorem h_sum_right {κ : Type} (s : Finset κ) (x : Fin r → K) (y : κ → Fin r → K) :
    S.h x (∑ j ∈ s, y j) = ∑ j ∈ s, S.h x (y j) := by
  exact map_sum (AddMonoidHom.mk' (fun y => S.h x y) (fun a b => h_add_right S x a b)) y s

end Herm

end Formalism.L2.Pj.FundamentalDomainD5
