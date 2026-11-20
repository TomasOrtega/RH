import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Introduce `L _ _ N h`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `Matrix.IsHermitian.ext fun s t => ?_` and prove the remaining obligations. Simplify using `only [gram, of_apply, star_trivial]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[← (mat_herm h w).apply t.1 s.1]`. Simplify using `only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x`. Establish `key : ∀ w, (star (realVec x w) ⬝ᵥ mat h w *ᵥ realVec x w).re = ∑ s, ∑ t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 * embO w (RingOfIntegers.basis L t.2)).re * x t)`.

Introduce `w`. Establish `hr : ∀ s t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 * embO w (RingOfIntegers.basis L t.2)).re * x t) = ((x s : ℂ) * (star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 * embO w (RingOfIntegers.basis L t.2)) * (x t : ℂ)).re`. Introduce `s t`. Rewrite using `[Complex.re_mul_ofReal, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hr, ← Complex.re_sum]`. Use `congr 1`. Simplify using `only [realVec, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', Complex.star_def, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `Eq.trans ?_ Finset.sum_comm.symm` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `Eq.trans ?_ Finset.sum_comm.symm` and prove the remaining obligations. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [qR, key]`.

Simplify using `only [dotProduct, mulVec, gram, of_apply, Finset.mul_sum, Finset.sum_mul]`. Combine the equalities or inequalities in the displayed calculation. Introduce `c`. Use function extensionality and compare the values at `w a`. Simplify using `[realVec, toR, intVec, map_sum, zsmul_eq_mul]`.

Set `E : (Fin N × BI L → ℤ) ≃ Lat L N` to `(Equiv.curry _ _ _).trans (Equiv.piCongrRight fun _ => (RingOfIntegers.basis L).equivFun.symm.toEquiv)`. Establish `hE : (intVec : (Fin N × BI L → ℤ) → Lat L N) = E`. Use function extensionality and compare the values at `c a`. Simplify using `[E, intVec, Module.Basis.equivFun_symm_apply, Equiv.curry]`. Rewrite using `[hE]`.

Conclude with `E.bijective`.
-/
theorem UpperTheory.V.KT.gramq :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), (gram h).IsHermitian ∧
    (∀ x : Fin N × BI L → ℝ, x ⬝ᵥ (gram h *ᵥ x) = qR h (realVec x)) ∧
    (∀ c : Fin N × BI L → ℤ, realVec (fun s => (c s : ℝ)) = toR (intVec c)) ∧
    Function.Bijective (intVec : (Fin N × BI L → ℤ) → Lat L N) := by
  intro L _ _ N h
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Matrix.IsHermitian.ext fun s t => ?_
    simp only [gram, of_apply, star_trivial]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← (mat_herm h w).apply t.1 s.1]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]
    ring
  · intro x
    have key : ∀ w, (star (realVec x w) ⬝ᵥ mat h w *ᵥ realVec x w).re =
        ∑ s, ∑ t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t) := by
      intro w
      have hr : ∀ s t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t) =
          ((x s : ℂ) * (star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)) * (x t : ℂ)).re := by
        intro s t
        rw [Complex.re_mul_ofReal, Complex.re_ofReal_mul]
        ring
      simp only [hr, ← Complex.re_sum]
      congr 1
      simp only [realVec, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', Complex.star_def,
        Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Eq.trans ?_ Finset.sum_comm.symm
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Eq.trans ?_ Finset.sum_comm.symm
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    simp only [qR, key]
    simp only [dotProduct, mulVec, gram, of_apply, Finset.mul_sum, Finset.sum_mul]
    calc ∑ s, ∑ t, ∑ w, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t)
        = ∑ s, ∑ w, ∑ t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t) :=
          Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  · intro c
    funext w a
    simp [realVec, toR, intVec, map_sum, zsmul_eq_mul]
  · let E : (Fin N × BI L → ℤ) ≃ Lat L N :=
      (Equiv.curry _ _ _).trans
        (Equiv.piCongrRight fun _ => (RingOfIntegers.basis L).equivFun.symm.toEquiv)
    have hE : (intVec : (Fin N × BI L → ℤ) → Lat L N) = E := by
      funext c a
      simp [E, intVec, Module.Basis.equivFun_symm_apply, Equiv.curry]
    rw [hE]
    exact E.bijective
