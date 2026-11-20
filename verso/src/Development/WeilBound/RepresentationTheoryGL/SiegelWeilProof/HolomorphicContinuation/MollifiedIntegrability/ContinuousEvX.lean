import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DensDefs

noncomputable section

open MeasureTheory

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem gramX_star (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    star (gramX ε x i j) = gramX ε x j i := by
  simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, ↓reduceIte,
    Bool.false_eq_true, star_sub, star_sum, star_mul, star_star]

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem herm_hinv (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, star (T i j) = T j i) : herm (hinv T) = T := by
  ext i j
  have h1 : (T j i).re = (T i j).re := by rw [← hT i j]; simp
  have h2 : (T j i).im = -(T i j).im := by rw [← hT i j]; simp
  apply Complex.ext
  · simp [herm, hinv, h1, h2]
    try ring
  · simp [herm, hinv, h1, h2]
    try ring

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hinv_herm' (y : E n) : hinv (herm y) = y := by
  funext i j
  simp [hinv, herm]
  ring

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem herm_mul_apply (y y' : E n) (i j : Fin n) :
    herm y i j * herm y' j i =
      (((y i j * y' i j + y j i * y' j i) / 2 : ℝ) : ℂ) + Complex.I * (((y i j * y' j i - y j i * y' i j) / 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [herm] <;> ring

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Chain the equalities or inequalities of the calculation.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem trace_herm_mul (y y' : E n) : (herm y * herm y').trace = ((ip y y' : ℝ) : ℂ) := by
  have h1 : ∑ i, ∑ j, (y i j * y' j i - y j i * y' i j) / 2 = 0 := by
    simp only [sub_div, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j => y j i * y' i j / 2)]
    exact sub_self _
  have h2 : ∑ i, ∑ j, (y i j * y' i j + y j i * y' j i) / 2 = ip y y' := by
    simp only [add_div, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => y j i * y' j i / 2)]
    simp only [ip, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  calc (herm y * herm y').trace = ∑ i, ∑ j, herm y i j * herm y' j i := by
        simp [Matrix.trace, Matrix.mul_apply]
    _ = ((∑ i, ∑ j, (y i j * y' i j + y j i * y' j i) / 2 : ℝ) : ℂ) +
          Complex.I * ((∑ i, ∑ j, (y i j * y' j i - y j i * y' i j) / 2 : ℝ) : ℂ) := by
        simp only [herm_mul_apply, Finset.sum_add_distrib, Complex.ofReal_sum, Finset.mul_sum]
    _ = ((ip y y' : ℝ) : ℂ) := by rw [h1, h2]; simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem evX_detQ (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : evX (detQ ε) x = (gramX ε x).det := by
  rw [evX, detQ, RingHom.map_det]
  rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem continuous_evX (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun k => ?_)
  split_ifs
  · exact continuous_star.comp ((continuous_apply _).comp (continuous_apply _))
  · exact (continuous_apply _).comp (continuous_apply _)

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem continuous_qX (ε : Fin m → Bool) : Continuous (qX (n := n) ε) := by
  unfold qX hinv gramX
  exact continuous_pi fun i => continuous_pi fun j =>
    (Complex.continuous_re.comp (continuous_evX _)).add (Complex.continuous_im.comp (continuous_evX _))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem algA : AlgA := by
  intro m n ε
  refine ⟨fun y x => ?_, fun x => herm_hinv _ (gramX_star ε x), hinv_herm', evX_detQ ε, continuous_qX ε⟩
  have h := trace_herm_mul y (qX ε x)
  rwa [show herm (qX ε x) = gramX ε x from herm_hinv _ (gramX_star ε x)] at h

end PositivityTheory.Rg.Sw.WR.D
