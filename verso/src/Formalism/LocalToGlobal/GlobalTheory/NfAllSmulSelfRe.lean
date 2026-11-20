import Formalism.LocalToGlobal.GlobalTheory.MemIffOfLocBasisG
import Formalism.LocalToGlobal.GlobalTheory.GL4.PColInf
import Formalism.LocalToGlobal.HermitianForms.FormsTied

noncomputable section

open Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions

section Map

variable {K L : Type} [Field K] [Field L] {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [MvPolynomial.algebraMap_eq]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.map_X]`.
-/
theorem map_aeval_sub (s : K →+* L) (f : (ι × Fin n × Fin n) → MvPolynomial (ι × Fin n × Fin n) K)
    (p : MvPolynomial (ι × Fin n × Fin n) K) :
    MvPolynomial.map s (MvPolynomial.aeval f p) = MvPolynomial.aeval (fun v => MvPolynomial.map s (f v)) (MvPolynomial.map s p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.map_X]

/- English proof (translation)
Unfold `Formalism.MainNotions.flipTwoThree.actAll`. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, map_aeval_sub]`. Use `congr 1`. Simplify using `only [map_prod, map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]`. Use `congr 1`.

Use `congr 1`. Use function extensionality and compare the values at `v`. Simplify using `[map_sum, Matrix.map_apply]`.
-/
theorem map_actAll (s : K →+* L) (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) K)
    (p : MvPolynomial (ι × Fin n × Fin n) K) :
    MvPolynomial.map s (Formalism.MainNotions.flipTwoThree.actAll lam g p) =
      Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => (g τ).map s) (MvPolynomial.map s p) := by
  unfold Formalism.MainNotions.flipTwoThree.actAll
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, map_aeval_sub]
  congr 1
  · simp only [map_prod, map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]
  · congr 1
    congr 1
    funext v
    simp [map_sum, Matrix.map_apply]

end Map

section Fock

variable {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem actAll_eq_subP (lam : ι → DomWeight n) (Z : ι → Matrix (Fin n) (Fin n) ℂ)
    (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.MainNotions.flipTwoThree.actAll lam Z p = (∏ τ, (Z τ).det ^ (lam τ).detShift) • Formalism.L2.Forms.subP (fun τ => (Z τ)ᵀ) p := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nfAll_eq (lam : ι → DomWeight n) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.MainNotions.flipTwoThree.nfAll lam p q = Formalism.L2.Forms.nfAll lam p q := rfl

/- English proof (translation)
Rewrite using `[Formalism.L2.GlobalTheoryTheory.TraceIntegrality.nfAll_smul_left, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.nfAll_smul_right, ← mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]`.
-/
theorem nfAll_smul_self_re (lam : ι → DomWeight n) (a : ℂ) (q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    (Formalism.MainNotions.flipTwoThree.nfAll lam (a • q) (a • q)).re = ‖a‖ ^ 2 * (Formalism.MainNotions.flipTwoThree.nfAll lam q q).re := by
  rw [Formalism.L2.GlobalTheoryTheory.TraceIntegrality.nfAll_smul_left, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.nfAll_smul_right, ← mul_assoc, Complex.mul_conj,
    Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]

end Fock

section Polar

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

def defect (φ : E →+* ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : ℂ :=
  star (Y *ᵥ fun i => φ (x i)) ⬝ᵥ (Y *ᵥ fun i => φ (y i)) - φ (star x ⬝ᵥ (G *ᵥ y))

variable (φ : E →+* ℂ) (hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a)) (Y : Matrix (Fin n) (Fin n) ℂ) (G : Matrix (Fin n) (Fin n) E)

/- English proof (translation)
Unfold `defect`. Establish `e : (fun i => φ ((x + x') i)) = (fun i => φ (x i)) + fun i => φ (x' i)` using `by funext i; simp`. Rewrite using `[e, Matrix.mulVec_add, star_add, add_dotProduct, star_add, add_dotProduct, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem defect_add_left (x x' y : Fin n → E) : defect φ Y G (x + x') y = defect φ Y G x y + defect φ Y G x' y := by
  unfold defect
  have e : (fun i => φ ((x + x') i)) = (fun i => φ (x i)) + fun i => φ (x' i) := by funext i; simp
  rw [e, Matrix.mulVec_add, star_add, add_dotProduct, star_add, add_dotProduct, map_add]
  ring

/- English proof (translation)
Unfold `defect`. Establish `e : (fun i => φ ((y + y') i)) = (fun i => φ (y i)) + fun i => φ (y' i)` using `by funext i; simp`. Rewrite using `[e, Matrix.mulVec_add, dotProduct_add, Matrix.mulVec_add, dotProduct_add, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem defect_add_right (x y y' : Fin n → E) : defect φ Y G x (y + y') = defect φ Y G x y + defect φ Y G x y' := by
  unfold defect
  have e : (fun i => φ ((y + y') i)) = (fun i => φ (y i)) + fun i => φ (y' i) := by funext i; simp
  rw [e, Matrix.mulVec_add, dotProduct_add, Matrix.mulVec_add, dotProduct_add, map_add]
  ring

include hφ in
/- English proof (translation)
Unfold `defect`. Establish `e : (fun i => φ ((t • x) i)) = φ t • fun i => φ (x i)` using `by funext i; simp`. Rewrite using `[e, Matrix.mulVec_smul, star_smul, smul_dotProduct, star_smul, smul_dotProduct]`. Simplify using `only [smul_eq_mul, map_mul, hφ, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem defect_smul_left (t : E) (x y : Fin n → E) :
    defect φ Y G (t • x) y = starRingEnd ℂ (φ t) * defect φ Y G x y := by
  unfold defect
  have e : (fun i => φ ((t • x) i)) = φ t • fun i => φ (x i) := by funext i; simp
  rw [e, Matrix.mulVec_smul, star_smul, smul_dotProduct, star_smul, smul_dotProduct]
  simp only [smul_eq_mul, map_mul, hφ, Complex.star_def]
  ring

/- English proof (translation)
Unfold `defect`. Establish `e : (fun i => φ ((t • y) i)) = φ t • fun i => φ (y i)` using `by funext i; simp`. Rewrite using `[e, Matrix.mulVec_smul, dotProduct_smul, Matrix.mulVec_smul, dotProduct_smul]`. Simplify using `only [smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem defect_smul_right (t : E) (x y : Fin n → E) :
    defect φ Y G x (t • y) = φ t * defect φ Y G x y := by
  unfold defect
  have e : (fun i => φ ((t • y) i)) = φ t • fun i => φ (y i) := by funext i; simp
  rw [e, Matrix.mulVec_smul, dotProduct_smul, Matrix.mulVec_smul, dotProduct_smul]
  simp only [smul_eq_mul, map_mul]
  ring

include hφ in

/- English proof (translation)
Establish `h1 : ∀ x y, defect φ Y G x y + defect φ Y G y x = 0` using `fun x y => by`. Use `h0 (x + y)` as an intermediate fact. Rewrite `this` using `[defect_add_left, defect_add_right, defect_add_right, h0 x, h0 y]`. Take the linear combination `this`. Establish `h2` using `h1 x (t • y)`.

Rewrite `h2` using `[defect_smul_right, defect_smul_left φ hφ]`. Establish `h3` using `h1 x y`. Establish `h4 : (φ t - starRingEnd ℂ (φ t)) * defect φ Y G x y = 0` using `by linear_combination h2 - starRingEnd ℂ (φ t) * h3`. Establish `h5 : φ t - starRingEnd ℂ (φ t) ≠ 0`. Introduce `h`.

Apply `ht` to reduce the goal to its premises. Use `congrArg Complex.im h` as an intermediate fact. Simplify using `only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add, Complex.zero_im] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(mul_eq_zero.1 h4).resolve_left h5`.
-/
theorem defect_eq_zero (t : E) (ht : (φ t).im ≠ 0) (h0 : ∀ x, defect φ Y G x x = 0) (x y : Fin n → E) :
    defect φ Y G x y = 0 := by
  have h1 : ∀ x y, defect φ Y G x y + defect φ Y G y x = 0 := fun x y => by
    have := h0 (x + y)
    rw [defect_add_left, defect_add_right, defect_add_right, h0 x, h0 y] at this
    linear_combination this
  have h2 := h1 x (t • y)
  rw [defect_smul_right, defect_smul_left φ hφ] at h2
  have h3 := h1 x y
  have h4 : (φ t - starRingEnd ℂ (φ t)) * defect φ Y G x y = 0 := by linear_combination h2 - starRingEnd ℂ (φ t) * h3
  have h5 : φ t - starRingEnd ℂ (φ t) ≠ 0 := by
    intro h
    apply ht
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add, Complex.zero_im] at this
    linarith
  exact (mul_eq_zero.1 h4).resolve_left h5

include hφ in

/- English proof (translation)
Establish `h0 : ∀ x, defect φ Y G x x = 0` using `fun x => by`. Unfold `defect`. Apply `Complex.ext` to reduce the goal to its premises. Rewrite using `[Complex.sub_re, h x, sub_self, Complex.zero_re]`. Rewrite using `[Complex.sub_im, Complex.zero_im]`.

Establish `i1 : (star (Y *ᵥ fun i => φ (x i)) ⬝ᵥ (Y *ᵥ fun i => φ (x i))).im = 0`. Simplify using `only [dotProduct, Pi.star_apply, Complex.im_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[RCLike.star_def, Complex.conj_mul']`. Use `norm_cast`.

Establish `i2 : (φ (star x ⬝ᵥ (G *ᵥ x))).im = 0`. Establish `e : star (star x ⬝ᵥ (G *ᵥ x)) = star x ⬝ᵥ (G *ᵥ x)`. Simplify using `only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Establish `hij : star (G j i) = G i j`. Use `congrFun (congrFun hG i) j` as an intermediate fact. Rewrite `this` using `[Matrix.conjTranspose_apply]`. Then use the resulting hypothesis. Rewrite using `[hij]`. Expand and normalize the polynomial expressions, which then agree.

Use `hφ (star x ⬝ᵥ (G *ᵥ x))` as an intermediate fact. Rewrite `this` using `[e]`. Use `congrArg Complex.im this` as an intermediate fact. Rewrite `this` using `[Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[i1, i2, sub_zero]`. Use extensionality with `i j`. Use `defect_eq_zero φ hφ Y G t ht h0 (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Unfold `defect at this`. Establish `e : ∀ k : Fin n, (fun a => φ ((Pi.single k (1 : E) : Fin n → E) a)) = Pi.single k 1` using `fun k => by`.

Use function extensionality and compare the values at `a`. Distinguish the cases in `hk : a = k`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hk]`.

Rewrite `this` using `[e, e, sub_eq_zero]`. Establish `k1 : star (Y *ᵥ (Pi.single i 1 : Fin n → ℂ)) ⬝ᵥ (Y *ᵥ (Pi.single j 1 : Fin n → ℂ)) = (Yᴴ * Y) i j`. Simplify using `[dotProduct, Matrix.mulVec, Pi.single_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]`. Establish `hs : star (Pi.single i (1 : E) : Fin n → E) = Pi.single i 1`. Use function extensionality and compare the values at `a`.

Distinguish the cases in `hk : a = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hk]`. Establish `k2 : star (Pi.single i (1 : E) : Fin n → E) ⬝ᵥ (G *ᵥ (Pi.single j 1 : Fin n → E)) = G i j`.

Rewrite using `[hs]`. Simplify using `[dotProduct, Matrix.mulVec, Pi.single_apply]`. Rewrite `this` using `[k1, k2]`. Rewrite using `[this, Matrix.map_apply]`.
-/
theorem gram_of_norm (hG : Gᴴ = G) (t : E) (ht : (φ t).im ≠ 0)
    (h : ∀ x : Fin n → E, (star (Y *ᵥ fun i => φ (x i)) ⬝ᵥ (Y *ᵥ fun i => φ (x i))).re = (φ (star x ⬝ᵥ (G *ᵥ x))).re) :
    Yᴴ * Y = G.map φ := by
  have h0 : ∀ x, defect φ Y G x x = 0 := fun x => by
    unfold defect
    apply Complex.ext
    · rw [Complex.sub_re, h x, sub_self, Complex.zero_re]
    · rw [Complex.sub_im, Complex.zero_im]
      have i1 : (star (Y *ᵥ fun i => φ (x i)) ⬝ᵥ (Y *ᵥ fun i => φ (x i))).im = 0 := by
        simp only [dotProduct, Pi.star_apply, Complex.im_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [RCLike.star_def, Complex.conj_mul']
        norm_cast
      have i2 : (φ (star x ⬝ᵥ (G *ᵥ x))).im = 0 := by
        have e : star (star x ⬝ᵥ (G *ᵥ x)) = star x ⬝ᵥ (G *ᵥ x) := by
          simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          have hij : star (G j i) = G i j := by
            have := congrFun (congrFun hG i) j
            rwa [Matrix.conjTranspose_apply] at this
          rw [hij]
          ring
        have := hφ (star x ⬝ᵥ (G *ᵥ x))
        rw [e] at this
        have := congrArg Complex.im this
        rw [Complex.conj_im] at this
        linarith
      rw [i1, i2, sub_zero]
  ext i j
  have := defect_eq_zero φ hφ Y G t ht h0 (Pi.single i 1) (Pi.single j 1)
  unfold defect at this
  have e : ∀ k : Fin n, (fun a => φ ((Pi.single k (1 : E) : Fin n → E) a)) = Pi.single k 1 := fun k => by
    funext a
    by_cases hk : a = k
    · subst hk; simp
    · simp [hk]
  rw [e, e, sub_eq_zero] at this
  have k1 : star (Y *ᵥ (Pi.single i 1 : Fin n → ℂ)) ⬝ᵥ (Y *ᵥ (Pi.single j 1 : Fin n → ℂ)) = (Yᴴ * Y) i j := by
    simp [dotProduct, Matrix.mulVec, Pi.single_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hs : star (Pi.single i (1 : E) : Fin n → E) = Pi.single i 1 := by
    funext a
    by_cases hk : a = i
    · subst hk; simp
    · simp [hk]
  have k2 : star (Pi.single i (1 : E) : Fin n → E) ⬝ᵥ (G *ᵥ (Pi.single j 1 : Fin n → E)) = G i j := by
    rw [hs]
    simp [dotProduct, Matrix.mulVec, Pi.single_apply]
  rw [k1, k2] at this
  rw [this, Matrix.map_apply]

end Polar

end Formalism.L2.GlobalTheoryTheory.ColValS
