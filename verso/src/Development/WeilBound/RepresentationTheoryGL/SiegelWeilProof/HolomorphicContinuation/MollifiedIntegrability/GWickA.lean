import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussS

noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def ent (a : Fin m) (i : Fin n) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)

def crd (k : Fin m × Fin n × Bool) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  if k.2.2 then (Complex.conjCLE.toContinuousLinearMap).comp (ent k.1 k.2.1) else ent k.1 k.2.1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ent_apply (a : Fin m) (i : Fin n) (v : Fin m → Fin n → ℂ) : ent a i v = v a i := rfl

/- English proof (translation)
Apply the tactic sequence `unfold crd; split_ifs <;> simp [ent_apply, Complex.conjCLE_apply]`.
-/
theorem crd_apply (k : Fin m × Fin n × Bool) (v : Fin m → Fin n → ℂ) :
    crd k v = if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1 := by
  unfold crd; split_ifs <;> simp [ent_apply, Complex.conjCLE_apply]

/- English proof (translation)
Simplify using `only [evX, crd_apply]`.
-/
theorem evX_eq (P : PX m n) (x : Fin m → Fin n → ℂ) : evX P x = MvPolynomial.eval (fun k => crd k x) P := by
  simp only [evX, crd_apply]

/- English proof (translation)
Rewrite using `[pderiv_mul, pderiv_X]`. Distinguish the cases in `h : k = b`. Substitute `h` using the available equality. Simplify using `[evX_eq]`. Simplify using `[evX_eq, Pi.single_apply, h]`.
-/
theorem evX_pderiv_mul_X (p : PX m n) (k b : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) :
    evX (pderiv b (p * X k)) x = evX (pderiv b p) x * crd k x + evX p x * (if k = b then 1 else 0) := by
  rw [pderiv_mul, pderiv_X]
  by_cases h : k = b
  · subst h; simp [evX_eq]
  · simp [evX_eq, Pi.single_apply, h]

def dEv (P : PX m n) (x : Fin m → Fin n → ℂ) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  ∑ k, evX (pderiv k P) x • crd k

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h : evX (C a : PX m n) = fun _ => a` using `by funext y; simp [evX]`. Rewrite using `[h]`. Use `(hasFDerivAt_const a x).congr_fderiv ?_` and prove the remaining obligations.

Simplify using `[dEv, evX]`. Consider the case `add p q hp hq`. Establish `h : evX (p + q) = fun y => evX p y + evX q y` using `by funext y; simp [evX]`. Rewrite using `[h]`. Use `(hp.add hq).congr_fderiv ?_` and prove the remaining obligations.

Unfold `dEv`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← add_smul]`. Use `congr 1`.

Simplify using `[evX]`. Consider the case `mul_X p k hp`. Establish `h : evX (p * X k) = fun y => evX p y * crd k y` using `by funext y; simp [evX_eq]`. Rewrite using `[h]`. Use `(hp.mul (crd k).hasFDerivAt).congr_fderiv ?_` and prove the remaining obligations.

Use extensionality with `v`. Simplify using `only [dEv, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul, evX_pderiv_mul_X, add_mul, Finset.sum_add_distrib]`. Establish `e1 : ∑ b, evX (pderiv b p) x * crd k x * crd b v = crd k x * ∑ b, evX (pderiv b p) x * crd b v`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∑ b, (evX p x * if k = b then 1 else 0) * crd b v = evX p x * crd k v`. Rewrite using `[Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules. Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasFDerivAt_evX (P : PX m n) (x : Fin m → Fin n → ℂ) : HasFDerivAt (evX P) (dEv P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : evX (C a : PX m n) = fun _ => a := by funext y; simp [evX]
    rw [h]; refine (hasFDerivAt_const a x).congr_fderiv ?_
    simp [dEv, evX]
  | add p q hp hq =>
    have h : evX (p + q) = fun y => evX p y + evX q y := by funext y; simp [evX]
    rw [h]; refine (hp.add hq).congr_fderiv ?_
    unfold dEv; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_smul]; congr 1; simp [evX]
  | mul_X p k hp =>
    have h : evX (p * X k) = fun y => evX p y * crd k y := by funext y; simp [evX_eq]
    rw [h]; refine (hp.mul (crd k).hasFDerivAt).congr_fderiv ?_
    ext v
    simp only [dEv, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul, evX_pderiv_mul_X, add_mul,
      Finset.sum_add_distrib]
    have e1 : ∑ b, evX (pderiv b p) x * crd k x * crd b v = crd k x * ∑ b, evX (pderiv b p) x * crd b v := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring
    have e2 : ∑ b, (evX p x * if k = b then 1 else 0) * crd b v = evX p x * crd k v := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    rw [e1, e2]; ring

end PositivityTheory.Rg.Sw.WR.G
