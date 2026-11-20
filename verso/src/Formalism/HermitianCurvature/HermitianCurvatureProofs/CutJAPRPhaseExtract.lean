import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPolyRadialCut

open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Break down `Nat.even_or_odd' (u 0 + u 1) with ⟨j, hj | hj⟩` into its components or cases. Use `⟨Polynomial.C (2 * a) * (Polynomial.X ^ 2 + Polynomial.C c) ^ j * Polynomial.X ^ (u 2), fun t s h => ?_⟩` and prove the remaining obligations. Simplify using `only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eva …`.

Rewrite using `[← pow_add, ← pow_add, hj, pow_mul, pow_mul, neg_sq, h]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨0, fun t s h => ?_⟩` and prove the remaining obligations. Simplify using `only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Polynomial.eval_zero]`. Rewrite using `[← pow_add, ← pow_add, hj, Odd.neg_pow ⟨j, rfl⟩]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `add p₁ p₂ h₁ h₂`. Take `⟨q₁, hq₁⟩` from `h₁`. Take `⟨q₂, hq₂⟩` from `h₂`. Use `⟨q₁ + q₂, fun t s h => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, map_add, Polynomial.eval_add, ← hq₁ t s h, ← hq₂ t s h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evenPart_poly (c : ℂ) (p : MvPolynomial (Fin 3) ℂ) :
    ∃ q : Polynomial ℂ, ∀ t s : ℂ, t ^ 2 = s ^ 2 + c →
      MvPolynomial.eval ![t, t, s] p + MvPolynomial.eval ![-t, -t, s] p = q.eval s := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    rcases Nat.even_or_odd' (u 0 + u 1) with ⟨j, hj | hj⟩
    · refine ⟨Polynomial.C (2 * a) * (Polynomial.X ^ 2 + Polynomial.C c) ^ j * Polynomial.X ^ (u 2), fun t s h => ?_⟩
      simp only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      rw [← pow_add, ← pow_add, hj, pow_mul, pow_mul, neg_sq, h]
      ring
    · refine ⟨0, fun t s h => ?_⟩
      simp only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Polynomial.eval_zero]
      rw [← pow_add, ← pow_add, hj, Odd.neg_pow ⟨j, rfl⟩]
      ring
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨q₁, hq₁⟩ := h₁
    obtain ⟨q₂, hq₂⟩ := h₂
    refine ⟨q₁ + q₂, fun t s h => ?_⟩
    rw [map_add, map_add, Polynomial.eval_add, ← hq₁ t s h, ← hq₂ t s h]
    ring

/- English proof (translation)
Introduce `TT f _ hPS hrot`. Take `⟨m, p, hp⟩` from `hPS`. Take `⟨q, hq⟩` from `evenPart_poly (TT : ℂ) p`. Use `⟨m, Polynomial.C (1 / 2) * q, fun ζ hζ => ?_⟩` and prove the remaining obligations. Establish `hn : Complex.normSq ((‖ζ‖ : ℝ) : ℂ) = Complex.normSq ζ`.

Rewrite using `[Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hn' : Complex.normSq (-((‖ζ‖ : ℝ) : ℂ)) = Complex.normSq ζ`. Rewrite using `[Complex.normSq_neg, hn]`. Establish `h1 : f ζ = f ((‖ζ‖ : ℝ) : ℂ)`.

Use `hrot (Complex.arg ζ) ((‖ζ‖ : ℝ) : ℂ) (by rw [hn]; exact hζ)` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Unfold `rot`. Rewrite using `[mul_comm, Complex.norm_mul_exp_arg_mul_I]`.

Establish `h2 : f ζ = f (-((‖ζ‖ : ℝ) : ℂ))`. Use `hrot Real.pi ((‖ζ‖ : ℝ) : ℂ) (by rw [hn]; exact hζ)` as an intermediate fact. Rewrite using `[h1, ← this]`. Use `congr 1`. Unfold `rot`.

Rewrite using `[Complex.exp_pi_mul_I]`. Expand and normalize the polynomial expressions, which then agree. Establish `e1` using `hp ((‖ζ‖ : ℝ) : ℂ) (by rw [hn]; exact hζ)`. Establish `e2` using `hp (-((‖ζ‖ : ℝ) : ℂ)) (by rw [hn']; exact hζ)`. Establish `g1 : gg TT ((‖ζ‖ : ℝ) : ℂ) = gg TT ζ` using `by unfold gg; rw [hn]`.

Establish `g2 : gg TT (-((‖ζ‖ : ℝ) : ℂ)) = gg TT ζ` using `by unfold gg; rw [hn']`. Establish `s1 : sig TT ((‖ζ‖ : ℝ) : ℂ) = sig TT ζ` using `by unfold sig; rw [hn]`. Establish `s2 : sig TT (-((‖ζ‖ : ℝ) : ℂ)) = sig TT ζ` using `by unfold sig; rw [hn']`. Rewrite `e1` using `[g1, s1, ← h1, Complex.conj_ofReal]`. Rewrite `e2` using `[g2, s2, ← h2, map_neg, Complex.conj_ofReal]`.

Establish `hcurve : (((‖ζ‖ : ℝ) : ℂ)) ^ 2 = sig TT ζ ^ 2 + (TT : ℂ)`. Unfold `sig`. Rewrite using `[← Complex.ofReal_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith), ← Complex.ofReal_add, Complex.normSq_eq_norm_sq]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use `hq _ _ hcurve` as an intermediate fact. Rewrite `this` using `[← e1, ← e2]`. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_C, ← this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phase_extraction_holds : PhaseExtract := by
  intro TT f _ hPS hrot
  obtain ⟨m, p, hp⟩ := hPS
  obtain ⟨q, hq⟩ := evenPart_poly (TT : ℂ) p
  refine ⟨m, Polynomial.C (1 / 2) * q, fun ζ hζ => ?_⟩
  have hn : Complex.normSq ((‖ζ‖ : ℝ) : ℂ) = Complex.normSq ζ := by
    rw [Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]; ring
  have hn' : Complex.normSq (-((‖ζ‖ : ℝ) : ℂ)) = Complex.normSq ζ := by
    rw [Complex.normSq_neg, hn]
  have h1 : f ζ = f ((‖ζ‖ : ℝ) : ℂ) := by
    have := hrot (Complex.arg ζ) ((‖ζ‖ : ℝ) : ℂ) (by rw [hn]; exact hζ)
    rw [← this]
    congr 1
    unfold rot
    rw [mul_comm, Complex.norm_mul_exp_arg_mul_I]
  have h2 : f ζ = f (-((‖ζ‖ : ℝ) : ℂ)) := by
    have := hrot Real.pi ((‖ζ‖ : ℝ) : ℂ) (by rw [hn]; exact hζ)
    rw [h1, ← this]
    congr 1
    unfold rot
    rw [Complex.exp_pi_mul_I]; ring
  have e1 := hp ((‖ζ‖ : ℝ) : ℂ) (by rw [hn]; exact hζ)
  have e2 := hp (-((‖ζ‖ : ℝ) : ℂ)) (by rw [hn']; exact hζ)
  have g1 : gg TT ((‖ζ‖ : ℝ) : ℂ) = gg TT ζ := by unfold gg; rw [hn]
  have g2 : gg TT (-((‖ζ‖ : ℝ) : ℂ)) = gg TT ζ := by unfold gg; rw [hn']
  have s1 : sig TT ((‖ζ‖ : ℝ) : ℂ) = sig TT ζ := by unfold sig; rw [hn]
  have s2 : sig TT (-((‖ζ‖ : ℝ) : ℂ)) = sig TT ζ := by unfold sig; rw [hn']
  rw [g1, s1, ← h1, Complex.conj_ofReal] at e1
  rw [g2, s2, ← h2, map_neg, Complex.conj_ofReal] at e2
  have hcurve : (((‖ζ‖ : ℝ) : ℂ)) ^ 2 = sig TT ζ ^ 2 + (TT : ℂ) := by
    unfold sig
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith), ← Complex.ofReal_add,
      Complex.normSq_eq_norm_sq]
    congr 1; ring
  have := hq _ _ hcurve
  rw [← e1, ← e2] at this
  rw [Polynomial.eval_mul, Polynomial.eval_C, ← this]
  ring

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
