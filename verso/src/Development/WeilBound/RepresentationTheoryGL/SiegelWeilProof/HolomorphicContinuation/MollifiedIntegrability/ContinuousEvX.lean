import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DensDefs

noncomputable section

open MeasureTheory

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

/- English proof (translation)
Simplify using `only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, ↓reduceIte, Bool.false_eq_true, star_sub, star_sum, star_mul, star_star]`.
-/
theorem gramX_star (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    star (gramX ε x i j) = gramX ε x j i := by
  simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, ↓reduceIte,
    Bool.false_eq_true, star_sub, star_sum, star_mul, star_star]

/- English proof (translation)
Use extensionality with `i j`. Establish `h1 : (T j i).re = (T i j).re` using `by rw [← hT i j]; simp`. Establish `h2 : (T j i).im = -(T i j).im` using `by rw [← hT i j]; simp`. Apply `Complex.ext` to reduce the goal to its premises. Apply the tactic sequence `simp [herm, hinv, h1, h2] try ring`.

Apply the tactic sequence `simp [herm, hinv, h1, h2] try ring`.
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
Use function extensionality and compare the values at `i j`. Simplify using `[hinv, herm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hinv_herm' (y : E n) : hinv (herm y) = y := by
  funext i j
  simp [hinv, herm]
  ring

/- English proof (translation)
Apply the tactic sequence `apply Complex.ext <;> simp [herm] <;> ring`.
-/
theorem herm_mul_apply (y y' : E n) (i j : Fin n) :
    herm y i j * herm y' j i =
      (((y i j * y' i j + y j i * y' j i) / 2 : ℝ) : ℂ) + Complex.I * (((y i j * y' j i - y j i * y' i j) / 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [herm] <;> ring

/- English proof (translation)
Establish `h1 : ∑ i, ∑ j, (y i j * y' j i - y j i * y' i j) / 2 = 0`. Simplify using `only [sub_div, Finset.sum_sub_distrib]`. Rewrite using `[Finset.sum_comm (f := fun i j => y j i * y' i j / 2)]`. Conclude with `sub_self _`. Establish `h2 : ∑ i, ∑ j, (y i j * y' i j + y j i * y' j i) / 2 = ip y y'`.

Simplify using `only [add_div, Finset.sum_add_distrib]`. Rewrite using `[Finset.sum_comm (f := fun i j => y j i * y' j i / 2)]`. Simplify using `only [ip, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Combine the equalities or inequalities in the displayed calculation. Simplify using `[Matrix.trace, Matrix.mul_apply]`. Use `_ = ((∑ i, ∑ j, (y i j * y' i j + y j i * y' j i) / 2 : ℝ) : ℂ) + Complex.I * ((∑ i, ∑ j, (y i j * y' j i - y j i * y' i j) / 2 : ℝ) : ℂ) := by`. Simplify using `only [herm_mul_apply, Finset.sum_add_distrib, Complex.ofReal_sum, Finset.mul_sum]`. Use `_ = ((ip y y' : ℝ) : ℂ) := by rw [h1, h2]; simp`.
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
Rewrite using `[evX, detQ, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem evX_detQ (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : evX (detQ ε) x = (gramX ε x).det := by
  rw [evX, detQ, RingHom.map_det]
  rfl

/- English proof (translation)
Use `(MvPolynomial.continuous_eval P).comp (continuous_pi fun k => ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `continuous_star.comp ((continuous_apply _).comp (continuous_apply _))`. Conclude with `(continuous_apply _).comp (continuous_apply _)`.
-/
theorem continuous_evX (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun k => ?_)
  split_ifs
  · exact continuous_star.comp ((continuous_apply _).comp (continuous_apply _))
  · exact (continuous_apply _).comp (continuous_apply _)

/- English proof (translation)
Unfold `qX hinv gramX`. Conclude with `continuous_pi fun i => continuous_pi fun j => (Complex.continuous_re.comp (continuous_evX _)).add (Complex.continuous_im.comp (continuous_evX _))`.
-/
theorem continuous_qX (ε : Fin m → Bool) : Continuous (qX (n := n) ε) := by
  unfold qX hinv gramX
  exact continuous_pi fun i => continuous_pi fun j =>
    (Complex.continuous_re.comp (continuous_evX _)).add (Complex.continuous_im.comp (continuous_evX _))

/- English proof (translation)
Introduce `m n ε`. Use `⟨fun y x => ?_, fun x => herm_hinv _ (gramX_star ε x), hinv_herm', evX_detQ ε, continuous_qX ε⟩` and prove the remaining obligations. Establish `h` using `trace_herm_mul y (qX ε x)`. Rewrite `h` using `[show herm (qX ε x) = gramX ε x from herm_hinv _ (gramX_star ε x)]`. Then use the resulting hypothesis.
-/
theorem algA : AlgA := by
  intro m n ε
  refine ⟨fun y x => ?_, fun x => herm_hinv _ (gramX_star ε x), hinv_herm', evX_detQ ε, continuous_qX ε⟩
  have h := trace_herm_mul y (qX ε x)
  rwa [show herm (qX ε x) = gramX ε x from herm_hinv _ (gramX_star ε x)] at h

end PositivityTheory.Rg.Sw.WR.D
