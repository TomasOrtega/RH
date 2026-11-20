import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussSt

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {m n : ℕ}

/- English proof (translation)
Simplify using `[evX, Qb, map_sum]`.
-/
theorem evX_Qb (ε : Fin m → Bool) (b : Bool) (i j : Fin n) (u : Fin m → Fin n → ℂ) :
    evX (Qb ε b i j) u = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a i) * u a j := by
  simp [evX, Qb, map_sum]

/- English proof (translation)
The claim follows from `evX_Qb ε b i j u`.
-/
theorem gramB_apply (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramB ε b u i j = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a i) * u a j := evX_Qb ε b i j u

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [gramB_apply]`. Use `Finset.sum_congr (Finset.filter_congr fun a _ => ?_) fun _ _ => rfl` and prove the remaining obligations. Apply the tactic sequence `cases ε a <;> cases b <;> simp`.
-/
theorem gramB_not (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    gramB (fun a => !ε a) b u = gramB ε (!b) u := by
  ext i j
  simp only [gramB_apply]
  refine Finset.sum_congr (Finset.filter_congr fun a _ => ?_) fun _ _ => rfl
  cases ε a <;> cases b <;> simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[gramX, gramB, Qp, evX, map_sub]`.
-/
theorem gramX_eq (ε : Fin m → Bool) (u : Fin m → Fin n → ℂ) :
    gramX ε u = gramB ε true u - gramB ε false u := by
  ext i j
  simp [gramX, gramB, Qp, evX, map_sub]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[gramB_apply, mul_apply, diagonal_apply, Finset.sum_filter, conjTranspose_apply]`.
-/
private theorem gramB_eq_conjTranspose_diagonal_mul (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    gramB ε b u = (Matrix.of u)ᴴ * diagonal (fun a => if ε a = b then (1 : ℂ) else 0) * Matrix.of u := by
  ext i j
  simp [gramB_apply, mul_apply, diagonal_apply, Finset.sum_filter, conjTranspose_apply]

/- English proof (translation)
Rewrite using `[gramB_eq_conjTranspose_diagonal_mul ε b u]`. Use `(gramB_eq_conjTranspose_diagonal_mul ε b (Matrix.of u * a)).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Matrix.of u * a)ᴴ * _ * (Matrix.of u * a) = _`. Rewrite using `[conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem gramB_mul (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (a : Matrix (Fin n) (Fin n) ℂ) :
    gramB ε b (Matrix.of u * a) = aᴴ * gramB ε b u * a := by
  rw [gramB_eq_conjTranspose_diagonal_mul ε b u]
  refine (gramB_eq_conjTranspose_diagonal_mul ε b (Matrix.of u * a)).trans ?_
  change (Matrix.of u * a)ᴴ * _ * (Matrix.of u * a) = _
  rw [conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[epsT, ht]`.
-/
theorem epsT_pos {t : ℝ} (ht : 0 < t) (ε : Fin m → Bool) : epsT t ε = ε := by
  funext a; simp [epsT, ht]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[epsT, ht]`.
-/
theorem epsT_nonpos {t : ℝ} (ht : ¬ 0 < t) (ε : Fin m → Bool) : epsT t ε = fun a => !ε a := by
  funext a; simp [epsT, ht]

/- English proof (translation)
Simplify using `only [cnt]`. Use `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (p := fun a => ε a = true)` as an intermediate fact. Simplify using `using this`.
-/
theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  simp only [cnt]
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (p := fun a => ε a = true)
  simpa using this

/- English proof (translation)
Unfold `chN gZf`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Rewrite using `[gramX_eq, conjTranspose_add, hb]`. Distinguish the cases in `ht : 0 < t`.

Rewrite using `[epsT_pos ht]`. Establish `htc' : t = c` using `by rw [← htc, abs_of_pos ht]`. Substitute `htc'` using the available equality. Simplify using `only [Matrix.add_mul, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[epsT_nonpos ht, gramB_not, gramB_not]`. Establish `htc' : t = -c` using `by rw [← htc, abs_of_nonpos (not_lt.mp ht), neg_neg]`. Substitute `htc'` using the available equality. Simplify using `only [Bool.not_true, Bool.not_false, Matrix.add_mul, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub, Complex.ofReal_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chN_mul_gZf (ε : Fin m → Bool) {t c : ℝ} (htc : |t| = c) (b Z : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b)
    (u : Fin m → Fin n → ℂ) : chN ε t b u * gZf ε t c Z u = gZf ε t c (Z + b) u := by
  unfold chN gZf
  rw [← Complex.exp_add]
  congr 1
  rw [gramX_eq, conjTranspose_add, hb]
  by_cases ht : 0 < t
  · rw [epsT_pos ht]
    have htc' : t = c := by rw [← htc, abs_of_pos ht]
    subst htc'
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]
    ring
  · rw [epsT_nonpos ht, gramB_not, gramB_not]
    have htc' : t = -c := by rw [← htc, abs_of_nonpos (not_lt.mp ht), neg_neg]
    subst htc'
    simp only [Bool.not_true, Bool.not_false, Matrix.add_mul, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub,
      Complex.ofReal_neg]
    ring

/- English proof (translation)
Rewrite using `[show Z * (aᴴ * G * a) = (Z * aᴴ * G) * a by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem trace_cyc (Z a G : Matrix (Fin n) (Fin n) ℂ) : (Z * (aᴴ * G * a)).trace = (a * Z * aᴴ * G).trace := by
  rw [show Z * (aᴴ * G * a) = (Z * aᴴ * G) * a by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Unfold `gZf`. Rewrite using `[gramB_mul, gramB_mul, trace_cyc, trace_cyc, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem gZf_mul (ε : Fin m → Bool) (t c : ℝ) (Z a : Matrix (Fin n) (Fin n) ℂ) (u : Fin m → Fin n → ℂ) :
    gZf ε t c Z (Matrix.of u * a) = gZf ε t c (a * Z * aᴴ) u := by
  unfold gZf
  rw [gramB_mul, gramB_mul, trace_cyc, trace_cyc, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

end PositivityTheory.Rg.Sw.Glob.GaussH
