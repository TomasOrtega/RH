import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

noncomputable section

/- English proof (translation)
Introduce `H P hM c hc`. Take `⟨hP, hH, hdet, hPHP⟩` from `hM`. Use `set A := majInvolution H P with hAdef`. Establish `hHi : H⁻¹ * H = 1` using `nonsing_inv_mul H hdet`. Establish `hA2 : A * A = 1`.

Simplify using `only [hAdef, majInvolution]`. Combine the equalities or inequalities in the displayed calculation. Establish `hPA : P * A = H`. Simplify using `only [hAdef, majInvolution]`. Rewrite using `[← Matrix.mul_assoc, hPHP]`.

Establish `hAh : Aᴴ = P * H⁻¹`. Simplify using `only [hAdef, majInvolution, conjTranspose_mul, conjTranspose_nonsing_inv, hH.eq, hP.isHermitian.eq]`. Set `Dm : ℂ → Matrix ι ι ℂ` to `fun a => ((1 + a) / 2) • (1 : Matrix ι ι ℂ) + ((1 - a) / 2) • A`. Establish `hD : phaseOnMinus H P c = Dm c`. Simplify using `only [Dm, phaseOnMinus, ← hAdef]`.

Use `module`. Establish `hDD : ∀ a b : ℂ, a * b = 1 → Dm a * Dm b = 1`. Introduce `a b hab`. Simplify using `only [Dm, add_mul, mul_add, smul_mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hA2]`. Establish `e1 : (1 + a) / 2 * ((1 + b) / 2) + (1 - a) / 2 * ((1 - b) / 2) = 1`.

Take the linear combination `(1 / 2 : ℂ) * hab`. Establish `e2 : (1 + a) / 2 * ((1 - b) / 2) + (1 - a) / 2 * ((1 + b) / 2) = 0`. Take the linear combination `(-1 / 2 : ℂ) * hab`. Combine the equalities or inequalities in the displayed calculation. Establish `hDA : ∀ a : ℂ, Dm a * A = A * Dm a`.

Introduce `a`. Simplify using `only [Dm, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one]`. Establish `hDP : (Dm c)ᴴ * P = P * Dm (star c)`. Simplify using `only [Dm, conjTranspose_add, conjTranspose_smul, conjTranspose_one, hAh, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hPA]`. Simplify using `only [hPHP, star_div₀, star_add, star_sub, star_one]`.

Evaluate the numerical expressions. Establish `hcc : star c * c = 1`. Rewrite using `[Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]`. Evaluate the numerical expressions. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hD, hDP, Matrix.mul_assoc, hDD _ _ hcc, Matrix.mul_one]`. Rewrite using `[hD, ← hPA, ← Matrix.mul_assoc, hDP, Matrix.mul_assoc, ← hDA c, ← Matrix.mul_assoc, Matrix.mul_assoc P, hDD _ _ hcc, Matrix.mul_one]`. Introduce `u hu`. Rewrite using `[hD]`. Simplify using `only [Dm, add_mulVec, smul_mulVec, one_mulVec, hu]`.

Use `module`. Introduce `u hu`. Rewrite using `[hD]`. Simplify using `only [Dm, add_mulVec, smul_mulVec, one_mulVec, hu]`. Use `module`.
-/
theorem PhaseOnMinus.proof (ι : Type*) [Fintype ι] [DecidableEq ι] :
    PhaseOnMinus.Statement ι := by
  intro H P hM c hc
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  set A := majInvolution H P with hAdef
  have hHi : H⁻¹ * H = 1 := nonsing_inv_mul H hdet

  have hA2 : A * A = 1 := by
    simp only [hAdef, majInvolution]
    calc H⁻¹ * P * (H⁻¹ * P) = H⁻¹ * (P * H⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPHP, hHi]

  have hPA : P * A = H := by
    simp only [hAdef, majInvolution]; rw [← Matrix.mul_assoc, hPHP]

  have hAh : Aᴴ = P * H⁻¹ := by
    simp only [hAdef, majInvolution, conjTranspose_mul, conjTranspose_nonsing_inv,
      hH.eq, hP.isHermitian.eq]

  let Dm : ℂ → Matrix ι ι ℂ := fun a => ((1 + a) / 2) • (1 : Matrix ι ι ℂ) + ((1 - a) / 2) • A
  have hD : phaseOnMinus H P c = Dm c := by
    simp only [Dm, phaseOnMinus, ← hAdef]
    module
  have hDD : ∀ a b : ℂ, a * b = 1 → Dm a * Dm b = 1 := by
    intro a b hab
    simp only [Dm, add_mul, mul_add, smul_mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hA2]
    have e1 : (1 + a) / 2 * ((1 + b) / 2) + (1 - a) / 2 * ((1 - b) / 2) = 1 := by
      linear_combination (1 / 2 : ℂ) * hab
    have e2 : (1 + a) / 2 * ((1 - b) / 2) + (1 - a) / 2 * ((1 + b) / 2) = 0 := by
      linear_combination (-1 / 2 : ℂ) * hab
    calc _ = ((1 + a) / 2 * ((1 + b) / 2) + (1 - a) / 2 * ((1 - b) / 2)) • (1 : Matrix ι ι ℂ)
          + ((1 + a) / 2 * ((1 - b) / 2) + (1 - a) / 2 * ((1 + b) / 2)) • A := by module
      _ = 1 := by rw [e1, e2]; simp
  have hDA : ∀ a : ℂ, Dm a * A = A * Dm a := by
    intro a
    simp only [Dm, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul,
      Matrix.mul_one]

  have hDP : (Dm c)ᴴ * P = P * Dm (star c) := by
    simp only [Dm, conjTranspose_add, conjTranspose_smul, conjTranspose_one, hAh, add_mul,
      mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hPA]
    simp only [hPHP, star_div₀, star_add, star_sub, star_one]
    norm_num
  have hcc : star c * c = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hD, hDP, Matrix.mul_assoc, hDD _ _ hcc, Matrix.mul_one]
  · rw [hD, ← hPA, ← Matrix.mul_assoc, hDP, Matrix.mul_assoc, ← hDA c, ← Matrix.mul_assoc,
      Matrix.mul_assoc P, hDD _ _ hcc, Matrix.mul_one]
  · intro u hu
    rw [hD]
    simp only [Dm, add_mulVec, smul_mulVec, one_mulVec, hu]
    module
  · intro u hu
    rw [hD]
    simp only [Dm, add_mulVec, smul_mulVec, one_mulVec, hu]
    module

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
