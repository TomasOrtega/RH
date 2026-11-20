import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

/- English proof (translation)
Take `⟨e, P, hP⟩` from `hs`. Establish `hcT : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ) = (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ).conjTranspose`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.conjTranspose_apply]`. Establish `hJ0 : Formalism.UG.Jpq r 0 = 1`.

Use extensionality with `i j`. Break down `i with i | i` into its components or cases. Break down `j with j | j` into its components or cases. Simplify using `[Formalism.UG.Jpq, Matrix.one_apply]`. Conclude with `j.elim0`.

Conclude with `i.elim0`. Rewrite `hP` using `[hcT, hJ0]`. Use `set P' : Matrix (Fin r) (Fin r) ℂ := (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ).submatrix e e with hP'`. Establish `h1 : P'.conjTranspose * G * P' = 1`. Use `congrArg (fun A : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ => A.submatrix e e) hP` as an intermediate fact.

Simplify using `only [Matrix.reindex_apply] at this`. Rewrite `this` using `[← Matrix.submatrix_mul_equiv _ _ _ e _, ← Matrix.submatrix_mul_equiv _ _ _ e _]`. Simplify `this` using `[Matrix.submatrix_submatrix, Matrix.conjTranspose_submatrix, hP']`. Use `set Q := fr * P' with hQ`. Establish `h2 : (Q.conjTranspose * Formalism.REAL.Jm ε) * Q = 1`.

Rewrite using `[← h1, ← h]`. Simplify using `only [hQ, Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Establish `h3 : Q * (Q.conjTranspose * Formalism.REAL.Jm ε) = 1` using `mul_eq_one_comm.mp h2`. Establish `h4 : Q * Q.conjTranspose = Formalism.REAL.Jm ε`. Use `congrArg (· * Formalism.REAL.Jm ε) h3` as an intermediate fact.

Simplify `this` using `[Matrix.mul_assoc, Formalism.REAL.Jm_mul_self]`. Introduce `i`. Assume the negation of the conclusion as `hi`. Establish `hi' : ε i = false` using `by simpa using hi`. Establish `h5` using `congrFun (congrFun h4 i) i`.

Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Formalism.REAL.Jm, Matrix.diagonal_apply_eq, hi'] at h5`. Establish `h6` using `congrArg Complex.re h5`. Simplify using `only [Complex.re_sum, Bool.false_eq_true, if_false, Complex.neg_re, Complex.one_re] at h6`. Establish `h7 : ∀ k, 0 ≤ (Q i k * star (Q i k)).re`. Introduce `k`.

Rewrite using `[Complex.star_def, Complex.mul_conj]`. Simplify using `[Complex.normSq_nonneg]`. Use `Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => h7 k)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem signs_pos_of_frame_gram_posdef {r : ℕ} (ε : Fin r → Bool) (fr G : Matrix (Fin r) (Fin r) ℂ)
    (h : fr.conjTranspose * Formalism.REAL.Jm ε * fr = G) (hs : Formalism.UG.HasSignature G r 0) :
    ∀ i, ε i = true := by
  obtain ⟨e, P, hP⟩ := hs
  have hcT : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ) =
      (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ).conjTranspose := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  have hJ0 : Formalism.UG.Jpq r 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  rw [hcT, hJ0] at hP
  set P' : Matrix (Fin r) (Fin r) ℂ := (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ).submatrix e e with hP'
  have h1 : P'.conjTranspose * G * P' = 1 := by
    have := congrArg (fun A : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ => A.submatrix e e) hP
    simp only [Matrix.reindex_apply] at this
    rw [← Matrix.submatrix_mul_equiv _ _ _ e _, ← Matrix.submatrix_mul_equiv _ _ _ e _] at this
    simpa [Matrix.submatrix_submatrix, Matrix.conjTranspose_submatrix, hP'] using this
  set Q := fr * P' with hQ
  have h2 : (Q.conjTranspose * Formalism.REAL.Jm ε) * Q = 1 := by
    rw [← h1, ← h]; simp only [hQ, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h3 : Q * (Q.conjTranspose * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.mp h2
  have h4 : Q * Q.conjTranspose = Formalism.REAL.Jm ε := by
    have := congrArg (· * Formalism.REAL.Jm ε) h3
    simpa [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self] using this
  intro i
  by_contra hi
  have hi' : ε i = false := by simpa using hi
  have h5 := congrFun (congrFun h4 i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Formalism.REAL.Jm, Matrix.diagonal_apply_eq, hi'] at h5
  have h6 := congrArg Complex.re h5
  simp only [Complex.re_sum, Bool.false_eq_true, if_false, Complex.neg_re, Complex.one_re] at h6
  have h7 : ∀ k, 0 ≤ (Q i k * star (Q i k)).re := by
    intro k
    rw [Complex.star_def, Complex.mul_conj]
    simp [Complex.normSq_nonneg]
  have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => h7 k)
  linarith

end GlobalTheory
