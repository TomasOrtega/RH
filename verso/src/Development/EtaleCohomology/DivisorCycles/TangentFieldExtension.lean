import Development.EtaleCohomology.DivisorCycles.OpenCoset

open Matrix

namespace LateralTheory.DivDb.TangentFieldExtension
open LateralTheory.DivDb

variable {C : Type} [Field C] {N : ℕ}

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [dAt, ev, DX, MvPolynomial.derivation_C]`. Consider the case `add f g hf hg`. Rewrite using `[map_add, ev, map_add, ← ev, ← ev, hf, hg]`. Simplify using `only [dAt, map_add, ev, add_mul, Finset.sum_add_distrib]`.

Consider the case `mul_X f q hf`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Simplify using `only [ev, map_add, map_mul] at hf ⊢`. Rewrite using `[hf]`. Simplify using `only [DX, MvPolynomial.mkDerivation_X, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, dAt, ev, Derivation.leibniz, smul_eq_mul, map_add, map_mul, MvPolynomial.pderiv_X, add_mul, Finset.sum_add_distrib, Matrix.mul_apply]`.

Use `congr 1`. Simplify using `[Pi.single_apply, apply_ite (MvPolynomial.eval _)]`. Rewrite using `[Finset.mul_sum]`. Simplify using `only [mul_assoc]`.
-/
theorem ev_DX (Y x : Mat C N) (f : MP C N) : ev x (DX Y f) = dAt f x (Y * x) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [dAt, ev, DX, MvPolynomial.derivation_C]
  | add f g hf hg =>
    rw [map_add, ev, map_add, ← ev, ← ev, hf, hg]
    simp only [dAt, map_add, ev, add_mul, Finset.sum_add_distrib]
  | mul_X f q hf =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    simp only [ev, map_add, map_mul] at hf ⊢
    rw [hf]
    simp only [DX, MvPolynomial.mkDerivation_X, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      dAt, ev, Derivation.leibniz, smul_eq_mul, map_add, map_mul, MvPolynomial.pderiv_X, add_mul,
      Finset.sum_add_distrib, Matrix.mul_apply]
    congr 1
    · simp [Pi.single_apply, apply_ite (MvPolynomial.eval _)]
    · rw [Finset.mul_sum]; simp only [mul_assoc]

/- English proof (translation)
Introduce `C _ N S Y`. Prove the components needed by the constructor for the conclusion. Introduce `hY f hf s hs`. Take `⟨f', hev, hd⟩` from `hChain C N N (LinearMap.mulRight C s) f`. Establish `hf' : f' ∈ Van (S : Set (Mat C N))` using `fun x hx => by`.

Rewrite using `[hev, LinearMap.mulRight_apply]`. Conclude with `hf _ (S.mul_mem hx hs)`. Establish `h1 : dAt f' 1 Y = 0` using `hY f' hf'`. Rewrite `h1` using `[hd]`. Simplify using `only [LinearMap.mulRight_apply, one_mul] at h1`.

Use `show ev s (DX Y f) = 0`. Rewrite using `[ev_DX]`. Conclude with `h1`. Introduce `h f hf`. Establish `h1 : ev 1 (DX Y f) = 0` using `h f hf 1 S.one_mem`.

Rewrite `h1` using `[ev_DX, mul_one]`. Conclude with `h1`.
-/
theorem TanField_of (hChain : Chain) : TanField := by
  intro C _ N S Y
  constructor
  · intro hY f hf s hs
    obtain ⟨f', hev, hd⟩ := hChain C N N (LinearMap.mulRight C s) f
    have hf' : f' ∈ Van (S : Set (Mat C N)) := fun x hx => by
      rw [hev, LinearMap.mulRight_apply]; exact hf _ (S.mul_mem hx hs)
    have h1 : dAt f' 1 Y = 0 := hY f' hf'
    rw [hd] at h1
    simp only [LinearMap.mulRight_apply, one_mul] at h1
    show ev s (DX Y f) = 0
    rw [ev_DX]; exact h1
  · intro h f hf
    have h1 : ev 1 (DX Y f) = 0 := h f hf 1 S.one_mem
    rw [ev_DX, mul_one] at h1
    exact h1

end LateralTheory.DivDb.TangentFieldExtension
