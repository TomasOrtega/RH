import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStableAlt

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

def crd (k : Fin m × Fin n × Bool) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  if k.2.2 then (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.1))
  else (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.1)

/- English proof (translation)
Apply the tactic sequence `unfold crd; split_ifs <;> simp [Complex.conjCLE_apply, Complex.star_def]`.
-/
theorem crd_apply (k : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) :
    crd k x = if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1 := by
  unfold crd; split_ifs <;> simp [Complex.conjCLE_apply, Complex.star_def]

/- English proof (translation)
Simplify using `only [evX, crd_apply]`.
-/
theorem evX_eq (P : PX m n) (x : Fin m → Fin n → ℂ) : evX P x = MvPolynomial.eval (fun k => crd k x) P := by
  simp only [evX, crd_apply]

/- English proof (translation)
Rewrite using `[crd_apply]`. Establish `h : ‖x k.1 k.2.1‖ ≤ ‖x‖` using `(norm_le_pi_norm (x k.1) k.2.1).trans (norm_le_pi_norm x k.1)`. Apply the tactic sequence `split_ifs <;> simpa using h`.
-/
theorem norm_crd_le (k : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) : ‖crd k x‖ ≤ ‖x‖ := by
  rw [crd_apply]
  have h : ‖x k.1 k.2.1‖ ≤ ‖x‖ := (norm_le_pi_norm (x k.1) k.2.1).trans (norm_le_pi_norm x k.1)
  split_ifs <;> simpa using h

def dP (P : PX m n) (x : Fin m → Fin n → ℂ) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ := ∑ k, evX (pderiv k P) x • crd k

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `: dP (C a : PX m n) x = 0` using `by simp [dP, evX_eq]`. Establish `e : (fun y => evX (C a : PX m n) y) = fun _ => a` using `by funext y; simp [evX_eq]`. Rewrite using `[this, e]`.

Conclude with `hasFDerivAt_const a x`. Consider the case `add p q hp hq`. Establish `: dP (p + q) x = dP p x + dP q x` using `by simp [dP, evX_eq, Finset.sum_add_distrib, add_smul]`. Establish `e : (fun y => evX (p + q) y) = fun y => evX p y + evX q y` using `by funext y; simp [evX_eq]`. Rewrite using `[this, e]`.

Conclude with `hp.add hq`. Consider the case `mul_X p k hp`. Establish `h1 : HasFDerivAt (fun y => evX p y * crd k y) (evX p x • crd k + crd k x • dP p x) x` using `hp.mul (crd k).hasFDerivAt`. Establish `e1 : (fun y => evX (p * X k) y) = fun y => evX p y * crd k y`. Use function extensionality and compare the values at `y`.

Simplify using `[evX_eq]`. Establish `e2 : dP (p * X k) x = evX p x • crd k + crd k x • dP p x`. Use extensionality with `v`. Establish `hb : ∀ b, evX (pderiv b (p * X k)) x * crd b v = crd k x * (evX (pderiv b p) x * crd b v) + (if k = b then evX p x * crd k v else 0)`. Introduce `b`.

Rewrite using `[Derivation.leibniz, pderiv_X]`. Distinguish the cases in `h : k = b`. Substitute `h` using the available equality. Simplify using `[evX_eq]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[evX_eq, Pi.single_apply, Ne.symm h, h]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [dP, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_congr rfl fun b _ => hb b, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _), ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, e2]`. Conclude with `h1`.
-/
theorem hasFDerivAt_evX (P : PX m n) (x : Fin m → Fin n → ℂ) : HasFDerivAt (fun y => evX P y) (dP P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : dP (C a : PX m n) x = 0 := by simp [dP, evX_eq]
    have e : (fun y => evX (C a : PX m n) y) = fun _ => a := by funext y; simp [evX_eq]
    rw [this, e]; exact hasFDerivAt_const a x
  | add p q hp hq =>
    have : dP (p + q) x = dP p x + dP q x := by simp [dP, evX_eq, Finset.sum_add_distrib, add_smul]
    have e : (fun y => evX (p + q) y) = fun y => evX p y + evX q y := by funext y; simp [evX_eq]
    rw [this, e]; exact hp.add hq
  | mul_X p k hp =>
    have h1 : HasFDerivAt (fun y => evX p y * crd k y) (evX p x • crd k + crd k x • dP p x) x :=
      hp.mul (crd k).hasFDerivAt
    have e1 : (fun y => evX (p * X k) y) = fun y => evX p y * crd k y := by
      funext y; simp [evX_eq]
    have e2 : dP (p * X k) x = evX p x • crd k + crd k x • dP p x := by
      ext v
      have hb : ∀ b, evX (pderiv b (p * X k)) x * crd b v =
          crd k x * (evX (pderiv b p) x * crd b v) + (if k = b then evX p x * crd k v else 0) := by
        intro b
        rw [Derivation.leibniz, pderiv_X]
        by_cases h : k = b
        · subst h; simp [evX_eq]; ring
        · simp [evX_eq, Pi.single_apply, Ne.symm h, h]; ring
      simp only [dP, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
        Finset.sum_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _),
        ← Finset.mul_sum]
      ring
    rw [e1, e2]; exact h1

end PositivityTheory.Rg.Sw.LC.NullS
