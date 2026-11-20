import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.MulVarSpan

variable {P Q R S : ℕ}

/- English proof (translation)
Unfold `heisOp`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single l]`. Simplify using `[Matrix.single_apply]`. Introduce `l' _ hne`.

Establish `h : ¬ (l.1 = l'.1 ∧ l.2 = l'.2)`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `hne (Prod.ext h1.symm h2.symm)`. Simplify using `[Matrix.single_apply, h]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ l) h`.
-/
theorem heisOp_single (l : Ln P Q R S) (a : ℂ) :
    heisOp (Matrix.single l.1 l.2 a) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
      (a • raiB l - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 * star a) • lowB l) := by
  unfold heisOp
  congr 1
  rw [Finset.sum_eq_single l]
  · simp [Matrix.single_apply]
  · intro l' _ hne
    have h : ¬ (l.1 = l'.1 ∧ l.2 = l'.2) := by
      rintro ⟨h1, h2⟩; exact hne (Prod.ext h1.symm h2.symm)
    simp [Matrix.single_apply, h]
  · intro h; exact absurd (Finset.mem_univ l) h

/- English proof (translation)
Establish `: 0 < Real.sqrt (2 * Real.pi)` using `Real.sqrt_pos.mpr (by positivity)`. Conclude with `this.ne'` after adjusting the coercions.
-/
theorem sq_ne (l : Ln P Q R S) : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
  have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  exact_mod_cast this.ne'

/- English proof (translation)
Apply the tactic sequence `cases a <;> cases b <;> simp [lineSign]`.
-/
theorem lineSign_sq (a : Ix P Q) (b : Ix R S) : lineSign a b * lineSign a b = 1 := by
  cases a <;> cases b <;> simp [lineSign]

/- English proof (translation)
Use `set s : ℂ := ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)`. Establish `key : (2 * s) • raiB l = heisOp (Matrix.single l.1 l.2 1) - Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I)`. Rewrite using `[heisOp_single, heisOp_single]`. Simplify using `only [star_one, Complex.star_def, Complex.conj_I, one_smul, mul_one]`. Generalize the expression as in `raiB l = A`.

Generalize the expression as in `lowB l = B`. Generalize the expression as in `lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 = σ`. Simplify using `only [smul_sub, smul_smul]`. Establish `hI : Complex.I * (s * Complex.I) = -s` using `by ring_nf; simp [Complex.I_sq]`. Establish `hI2 : Complex.I * (s * (σ * -Complex.I)) = s * σ` using `by ring_nf; simp [Complex.I_sq]`.

Rewrite using `[hI, hI2]`. Use `module`. Establish `hs : (2 * s) ≠ 0` using `mul_ne_zero two_ne_zero (sq_ne l)`. Establish `: raiB l = (2 * s)⁻¹ • (heisOp (Matrix.single l.1 l.2 1) - Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I))`. Rewrite using `[← key, inv_smul_smul₀ hs]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))`.
-/
theorem raiB_mem (l : Ln P Q R S) :
    raiB l ∈ Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  set s : ℂ := ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
  have key : (2 * s) • raiB l = heisOp (Matrix.single l.1 l.2 1) - Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I) := by
    rw [heisOp_single, heisOp_single]
    simp only [star_one, Complex.star_def, Complex.conj_I, one_smul, mul_one]
    generalize raiB l = A
    generalize lowB l = B
    generalize lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 = σ
    simp only [smul_sub, smul_smul]
    have hI : Complex.I * (s * Complex.I) = -s := by ring_nf; simp [Complex.I_sq]
    have hI2 : Complex.I * (s * (σ * -Complex.I)) = s * σ := by ring_nf; simp [Complex.I_sq]
    rw [hI, hI2]
    module
  have hs : (2 * s) ≠ 0 := mul_ne_zero two_ne_zero (sq_ne l)
  have : raiB l = (2 * s)⁻¹ • (heisOp (Matrix.single l.1 l.2 1) - Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I)) := by
    rw [← key, inv_smul_smul₀ hs]
  rw [this]
  exact Submodule.smul_mem _ _ (sub_mem (Submodule.subset_span ⟨_, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))

/- English proof (translation)
Use `set s : ℂ := ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)`. Use `set σ := lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 with hσ`. Establish `hσσ : σ * σ = 1` using `lineSign_sq l.1 l.2`. Establish `key : (-2 * s * σ) • lowB l = heisOp (Matrix.single l.1 l.2 1) + Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I)`. Rewrite using `[heisOp_single, heisOp_single, ← hσ]`.

Simplify using `only [star_one, Complex.star_def, Complex.conj_I, one_smul, mul_one]`. Generalize the expression as in `raiB l = A`. Generalize the expression as in `lowB l = B`. Simplify using `only [smul_sub, smul_smul]`. Establish `hI : Complex.I * (s * Complex.I) = -s` using `by ring_nf; simp [Complex.I_sq]`.

Establish `hI2 : Complex.I * (s * (σ * -Complex.I)) = s * σ` using `by ring_nf; simp [Complex.I_sq]`. Rewrite using `[hI, hI2]`. Use `module`. Establish `hs : (-2 * s * σ) ≠ 0`. Use `mul_ne_zero (mul_ne_zero (by norm_num) (sq_ne l)) ?_` and prove the remaining obligations.

Introduce `h`. Rewrite `hσσ` using `[h, zero_mul]`. Conclude with `zero_ne_one hσσ`. Establish `: lowB l = (-2 * s * σ)⁻¹ • (heisOp (Matrix.single l.1 l.2 1) + Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I))`. Rewrite using `[← key, inv_smul_smul₀ hs]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (add_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))`.
-/
theorem lowB_mem (l : Ln P Q R S) :
    lowB l ∈ Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  set s : ℂ := ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
  set σ := lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 with hσ
  have hσσ : σ * σ = 1 := lineSign_sq l.1 l.2
  have key : (-2 * s * σ) • lowB l = heisOp (Matrix.single l.1 l.2 1) + Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I) := by
    rw [heisOp_single, heisOp_single, ← hσ]
    simp only [star_one, Complex.star_def, Complex.conj_I, one_smul, mul_one]
    generalize raiB l = A
    generalize lowB l = B
    simp only [smul_sub, smul_smul]
    have hI : Complex.I * (s * Complex.I) = -s := by ring_nf; simp [Complex.I_sq]
    have hI2 : Complex.I * (s * (σ * -Complex.I)) = s * σ := by ring_nf; simp [Complex.I_sq]
    rw [hI, hI2]
    module
  have hs : (-2 * s * σ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) (sq_ne l)) ?_
    intro h; rw [h, zero_mul] at hσσ; exact zero_ne_one hσσ
  have : lowB l = (-2 * s * σ)⁻¹ • (heisOp (Matrix.single l.1 l.2 1) + Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I)) := by
    rw [← key, inv_smul_smul₀ hs]
  rw [this]
  exact Submodule.smul_mem _ _ (add_mem (Submodule.subset_span ⟨_, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))

/- English proof (translation)
Introduce `P Q R S l`. Consider the cases of `h : linePos l`. Establish `e : LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) = lowB l` using `by simp [lowB, h]`. Rewrite using `[e]`. Conclude with `lowB_mem l`.

Establish `e : LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) = raiB l` using `by simp [raiB, h]`. Rewrite using `[e]`. Conclude with `raiB_mem l`.
-/
theorem mulX_mem_span : ∀ {P Q R S : ℕ} (l : Ln P Q R S), LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) ∈
    Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  intro P Q R S l
  cases h : linePos l
  · have e : LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) = lowB l := by simp [lowB, h]
    rw [e]; exact lowB_mem l
  · have e : LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) = raiB l := by simp [raiB, h]
    rw [e]; exact raiB_mem l

end GlobalTheory.MulVarSpan
