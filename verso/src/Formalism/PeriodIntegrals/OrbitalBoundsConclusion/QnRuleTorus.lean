import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusConjugationRule.SecondHermitianPartDiagonal

/- English proof (translation)
Use `open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q PI.QnRT in`. Introduce `E _ _ k r l D f hD hf c hc g₁ hg₁ hmem`. Establish `hcl : c l ≠ 0` using `hc l`. Establish `h1 : -((1 / 2 : ℝ) : ℂ) = -star ((1 / 2 : ℝ) : ℂ)` using `by simp`. Establish `h2 : ((-1 / 2 : ℝ) : ℂ) * Complex.I = -star (((-1 / 2 : ℝ) : ℂ) * Complex.I)`.

Simplify using the standard rewrite rules. Establish `h3 : ((1 / 2 : ℝ) : ℂ) = -star (-((1 / 2 : ℝ) : ℂ))` using `by simp`. Use `set φ : (Fin r → ℂ) → E := fun c' => f (w1 k r l (c' l) * g₁) with hφ`. Use `set L := fderiv ℝ φ c with hL`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [EH, EabH]`. Rewrite using `[X1_eq, depthNumbers_threshold_eq, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h1, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h2]`. Simplify using `only [pOp, wirt, if_pos hc]`. Rewrite using `[lin_single l L (c l * ((1 / 2 : ℝ) : ℂ)), lin_single l L (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]`. Generalize the expression as in `L (Pi.single l 1) = A`.

Generalize the expression as in `L (Pi.single l Complex.I) = B`. Take `⟨a, b, hab⟩ : ∃ a b : ℝ, c l = (a : ℂ) + (b : ℂ) * Complex.I` from `⟨_, _, (Complex.re_add_im _).symm⟩`. Rewrite using `[hab]`. Simplify using `only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]`. Apply the tactic sequence `match_scalars <;> simp [Complex.ext_iff] <;> ring`.

Simplify using `only [EH, EabH]`. Rewrite using `[first_hermitian_part_diagonal, second_hermitian_part_diagonal, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h3, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h2]`. Simplify using `only [pbOp, wirtBar, if_pos hc]`. Rewrite using `[lin_single l L (c l * -((1 / 2 : ℝ) : ℂ)), lin_single l L (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]`. Generalize the expression as in `L (Pi.single l 1) = A`.

Generalize the expression as in `L (Pi.single l Complex.I) = B`. Take `⟨a, b, hab⟩ : ∃ a b : ℝ, c l = (a : ℂ) + (b : ℂ) * Complex.I` from `⟨_, _, (Complex.re_add_im _).symm⟩`. Rewrite using `[hab]`. Simplify using `only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]`. Apply the tactic sequence `match_scalars <;> simp [Complex.ext_iff] <;> ring`.
-/
theorem qnRuleTorus : Formalism.FourierDecayAlt.Q.RuleTorus := by
  open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q PI.QnRT in
  intro E _ _ k r l D f hD hf c hc g₁ hg₁ hmem
  have hcl : c l ≠ 0 := hc l
  have h1 : -((1 / 2 : ℝ) : ℂ) = -star ((1 / 2 : ℝ) : ℂ) := by simp
  have h2 : ((-1 / 2 : ℝ) : ℂ) * Complex.I = -star (((-1 / 2 : ℝ) : ℂ) * Complex.I) := by
    simp
  have h3 : ((1 / 2 : ℝ) : ℂ) = -star (-((1 / 2 : ℝ) : ℂ)) := by simp
  set φ : (Fin r → ℂ) → E := fun c' => f (w1 k r l (c' l) * g₁) with hφ
  set L := fderiv ℝ φ c with hL
  refine ⟨?_, ?_⟩
  · simp only [EH, EabH]
    rw [X1_eq, depthNumbers_threshold_eq, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h1,
      rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h2]
    simp only [pOp, wirt, if_pos hc]
    rw [lin_single l L (c l * ((1 / 2 : ℝ) : ℂ)), lin_single l L (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize L (Pi.single l 1) = A
    generalize L (Pi.single l Complex.I) = B
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, c l = (a : ℂ) + (b : ℂ) * Complex.I :=
      ⟨_, _, (Complex.re_add_im _).symm⟩
    rw [hab]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    match_scalars <;> simp [Complex.ext_iff] <;> ring
  · simp only [EH, EabH]
    rw [first_hermitian_part_diagonal, second_hermitian_part_diagonal, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h3,
      rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h2]
    simp only [pbOp, wirtBar, if_pos hc]
    rw [lin_single l L (c l * -((1 / 2 : ℝ) : ℂ)), lin_single l L (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize L (Pi.single l 1) = A
    generalize L (Pi.single l Complex.I) = B
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, c l = (a : ℂ) + (b : ℂ) * Complex.I :=
      ⟨_, _, (Complex.re_add_im _).symm⟩
    rw [hab]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    match_scalars <;> simp [Complex.ext_iff] <;> ring
