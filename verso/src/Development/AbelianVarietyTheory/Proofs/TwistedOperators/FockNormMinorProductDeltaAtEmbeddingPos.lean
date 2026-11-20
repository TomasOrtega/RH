import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockDelta

variable {D : D7}

/- English proof (translation)
Introduce `h`. Establish `hev` using `congrArg (MvPolynomial.eval fun y : FVar D m n => if (y.2.1 : ℕ) + b = (y.2.2 : ℕ) + a then (1 : ℂ) else 0) h`. Rewrite `hev` using `[RingHom.map_det, map_zero]`. Establish `hI : (MvPolynomial.eval fun y : FVar D m n => if (y.2.1 : ℕ) + b = (y.2.2 : ℕ) + a then (1 : ℂ) else 0).mapMatrix (Matrix.of fun α β : Fin k => (varF τ (a + (β : ℕ)) (b + (α : ℕ)) : MvPolynomial (FVar D m n) ℂ)) = 1`. Use extensionality with `α β`.

Establish `hα` using `α.isLt`. Establish `hβ` using `β.isLt`. Establish `hc : a + (β : ℕ) < m ∧ b + (α : ℕ) < n` using `⟨by omega, by omega⟩`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply]`. Unfold `varF`.

Rewrite using `[dif_pos hc, MvPolynomial.eval_X]`. Simplify using `only`. Use `split_ifs with h1 h2 h2`. Both sides reduce to the same expression. Conclude with `(h2 (Fin.ext (by omega))).elim`.

Conclude with `(h1 (by subst h2; omega)).elim`. Both sides reduce to the same expression. Rewrite `hev` using `[hI, Matrix.det_one]`. Conclude with `one_ne_zero hev`.
-/
theorem minor_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (a b k : ℕ) (ha : a + k ≤ m) (hb : b + k ≤ n) :
    (Matrix.of fun α β : Fin k =>
      (varF τ (a + (β : ℕ)) (b + (α : ℕ)) : MvPolynomial (FVar D m n) ℂ)).det ≠ 0 := by
  intro h
  have hev := congrArg (MvPolynomial.eval fun y : FVar D m n =>
    if (y.2.1 : ℕ) + b = (y.2.2 : ℕ) + a then (1 : ℂ) else 0) h
  rw [RingHom.map_det, map_zero] at hev
  have hI : (MvPolynomial.eval fun y : FVar D m n =>
      if (y.2.1 : ℕ) + b = (y.2.2 : ℕ) + a then (1 : ℂ) else 0).mapMatrix
      (Matrix.of fun α β : Fin k => (varF τ (a + (β : ℕ)) (b + (α : ℕ)) : MvPolynomial (FVar D m n) ℂ)) = 1 := by
    ext α β
    have hα := α.isLt
    have hβ := β.isLt
    have hc : a + (β : ℕ) < m ∧ b + (α : ℕ) < n := ⟨by omega, by omega⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply]
    unfold varF
    rw [dif_pos hc, MvPolynomial.eval_X]
    dsimp only
    split_ifs with h1 h2 h2
    · rfl
    · exact (h2 (Fin.ext (by omega))).elim
    · exact (h1 (by subst h2; omega)).elim
    · rfl
  rw [hI, Matrix.det_one] at hev
  exact one_ne_zero hev

/- English proof (translation)
Unfold `minorPlus`. Establish `h` using `minor_ne_zero (D := D) (m := m) (n := n) τ 0 0 k (by omega) (by omega)`. Simplify `h` using `only [zero_add]`.
-/
theorem minorPlus_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (k : ℕ) (hm : k ≤ m) (hn : k ≤ n) :
    (minorPlus τ k : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold minorPlus
  have h := minor_ne_zero (D := D) (m := m) (n := n) τ 0 0 k (by omega) (by omega)
  simpa only [zero_add] using h

/- English proof (translation)
Unfold `minorMinus`. Conclude with `minor_ne_zero τ p (n - k) k hm (by omega)`.
-/
theorem minorMinus_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (p k : ℕ) (hm : p + k ≤ m) (hn : k ≤ n) :
    (minorMinus τ p k : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold minorMinus
  exact minor_ne_zero τ p (n - k) k hm (by omega)

/- English proof (translation)
Unfold `deltaAt`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Use `Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (minorPlus_ne_zero τ (i + 1) ?_ ?_)` and prove the remaining obligations. Use `Finset.mem_range.mp hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `Finset.mem_range.mp hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (minorMinus_ne_zero τ p (i + 1) ?_ ?_)` and prove the remaining obligations. Use `Finset.mem_range.mp hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `Finset.mem_range.mp hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem deltaAt_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (p : ℕ) (ap : ℕ → ℕ) (q : ℕ) (am : ℕ → ℕ)
    (hpq : p + q ≤ m) (hmn : m ≤ n) :
    (deltaAt τ p ap q am : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold deltaAt
  refine mul_ne_zero ?_ ?_
  · refine Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (minorPlus_ne_zero τ (i + 1) ?_ ?_)
    · have := Finset.mem_range.mp hi
      omega
    · have := Finset.mem_range.mp hi
      omega
  · refine Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (minorMinus_ne_zero τ p (i + 1) ?_ ?_)
    · have := Finset.mem_range.mp hi
      omega
    · have := Finset.mem_range.mp hi
      omega

/- English proof (translation)
Unfold `delta`. Conclude with `Finset.prod_ne_zero_iff.mpr fun τ _ => deltaAt_ne_zero τ _ _ _ _ (hpq τ) hmn`.
-/
theorem delta_ne_zero {m n : ℕ} (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ)
    (hpq : ∀ τ, p τ + q τ ≤ m) (hmn : m ≤ n) :
    (delta p q ap am : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold delta
  exact Finset.prod_ne_zero_iff.mpr fun τ _ => deltaAt_ne_zero τ _ _ _ _ (hpq τ) hmn

/- English proof (translation)
Use `⟨∑ m ∈ P.support, Complex.normSq (P.coeff m) * (Formalism.A.mfact m : ℝ), ?_, ?_⟩` and prove the remaining obligations. Use `Finset.sum_pos (fun m hm => mul_pos ?_ ?_) ?_` and prove the remaining obligations. Conclude with `Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp hm)`. Unfold `Formalism.A.mfact`. Conclude with `Nat.cast_pos.mpr (Finset.prod_pos fun i _ => Nat.factorial_pos _)`.

Conclude with `Finset.nonempty_iff_ne_empty.mpr fun he => hP (MvPolynomial.support_eq_empty.mp he)`. Unfold `Formalism.E.fock`. Rewrite using `[Complex.ofReal_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.ofReal_mul, Complex.star_def, Complex.mul_conj, Complex.ofReal_natCast]`.
-/
theorem fock_self_pos {σ : Type*} (P : MvPolynomial σ ℂ) (hP : P ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ Formalism.E.fock P P = (a : ℂ) := by
  refine ⟨∑ m ∈ P.support, Complex.normSq (P.coeff m) * (Formalism.A.mfact m : ℝ), ?_, ?_⟩
  · refine Finset.sum_pos (fun m hm => mul_pos ?_ ?_) ?_
    · exact Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp hm)
    · unfold Formalism.A.mfact
      exact Nat.cast_pos.mpr (Finset.prod_pos fun i _ => Nat.factorial_pos _)
    · exact Finset.nonempty_iff_ne_empty.mpr fun he => hP (MvPolynomial.support_eq_empty.mp he)
  · unfold Formalism.E.fock
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.ofReal_mul, Complex.star_def, Complex.mul_conj, Complex.ofReal_natCast]

end GlobalTheory.FockDelta

open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues in

/- English proof (translation)
Introduce `D i σ`. Apply `GlobalTheory.FockDelta.fock_self_pos` to reduce the goal to its premises. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb`. Establish `hi` using `i.isLt`. Establish `hW : (Wc D i).rank = D.R.r` using `D.sp.W_rank _ (by omega) (by omega)`.

Apply `GlobalTheory.FockDelta.delta_ne_zero` to reduce the goal to its premises. Introduce `ρ`. Conclude with `le_of_eq (Formalism.BasicNotions.sig_sum _ (D.sp.W_sig _) _)`. Rewrite using `[hW]`. Conclude with `r_le_V i`.
-/
theorem GlobalTheory.FockDelta.fock_deltaAtEmb_pos :
    ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ∃ a : ℝ, 0 < a ∧
      Formalism.E.fock (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb D i σ) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb D i σ) = (a : ℂ) := by
  intro D i σ
  apply GlobalTheory.FockDelta.fock_self_pos
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb
  have hi := i.isLt
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (by omega) (by omega)
  apply GlobalTheory.FockDelta.delta_ne_zero
  · intro ρ
    exact le_of_eq (Formalism.BasicNotions.sig_sum _ (D.sp.W_sig _) _)
  · rw [hW]
    exact r_le_V i
