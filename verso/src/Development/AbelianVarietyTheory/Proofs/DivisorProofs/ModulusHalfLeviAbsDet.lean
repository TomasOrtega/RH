import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaHalfMulUnrTorus
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AbsHalfLevi

/- English proof (translation)
Introduce `E _ _ _ a b w m`. Rewrite using `[GlobalTheory.SmGL.deltaHalf_two, Units.val_mul]`. Establish `e1 : m.1.val.det = ((GeneralLinearGroup.det m.1 : (w.adicCompletion E)ˣ) : w.adicCompletion E)`. Simplify using `[GeneralLinearGroup.val_det_apply]`. Establish `e2 : m.2.val.det = ((GeneralLinearGroup.det m.2 : (w.adicCompletion E)ˣ) : w.adicCompletion E)`.

Simplify using `[GeneralLinearGroup.val_det_apply]`. Rewrite using `[e1, e2]`. Generalize the expression as in `GeneralLinearGroup.det m.1 = d1`. Generalize the expression as in `GeneralLinearGroup.det m.2 = d2`. Establish `n1` using `GlobalTheory.LGrp.BorelCompletion.nabs_completion w d1`.

Establish `n2` using `GlobalTheory.LGrp.BorelCompletion.nabs_completion w d2`. Establish `hb : ((Fintype.card (Fin b) : ℂ) / 2) = (((b : ℝ) / 2 : ℝ) : ℂ)` using `by simp`. Establish `ha : (-(Fintype.card (Fin a) : ℂ) / 2) = ((-(a : ℝ) / 2 : ℝ) : ℂ)` using `by simp`. Rewrite using `[hb, ha, GlobalTheory.SmGL.val_absPow_ofReal, GlobalTheory.SmGL.val_absPow_ofReal, n1, n2, ← Complex.ofReal_mul]`. Unfold `absHalf`.

Use `congr 1`. Establish `hd1 : ((d1 : w.adicCompletion E)) ≠ 0` using `d1.ne_zero`. Establish `hd2 : ((d2 : w.adicCompletion E)) ≠ 0` using `d2.ne_zero`. Establish `hx : ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) ≠ 0`. Conclude with `div_ne_zero (pow_ne_zero _ hd1) (pow_ne_zero _ hd2)`.

Establish `hv1 : Valued.v (d1 : w.adicCompletion E) ≠ 0` using `(Valuation.ne_zero_iff _).mpr hd1`. Establish `hv2 : Valued.v (d2 : w.adicCompletion E) ≠ 0` using `(Valuation.ne_zero_iff _).mpr hd2`. Establish `hord : ordL ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) = -((b : ℤ) * WithZero.log (Valued.v (d1 : w.adicCompletion E)) - (a : ℤ) * WithZero.log (Valued.v (d2 : w.adicCompletion E)))`. Establish `hv : Valued.v ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) ≠ 0` using `(Valuation.ne_zero_iff _).mpr hx`. Unfold `ordL`.

Rewrite using `[dif_neg hv, WithZero.toAdd_unzero_eq_log, map_div₀, map_pow, map_pow, WithZero.log_div (pow_ne_zero _ hv1) (pow_ne_zero _ hv2), WithZero.log_pow, WithZero.log_pow]`. Simplify using the standard rewrite rules. Rewrite using `[hord, neg_neg]`. Establish `hq : (0 : ℝ) < (qV E w : ℝ)`. Establish `: qV E w ≠ 0`.

Unfold `qV`. Conclude with `(Ideal.absNorm_eq_zero_iff).not.mpr w.ne_bot`. Conclude with `Nat.pos_of_ne_zero this` after adjusting the coercions. Generalize the expression as in `WithZero.log (Valued.v (d1 : w.adicCompletion E)) = l1`. Generalize the expression as in `WithZero.log (Valued.v (d2 : w.adicCompletion E)) = l2`.

Generalize the expression as in `(qV E w : ℝ) = q at hq ⊢`. Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_add hq]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem absHalf_det_div_eq_deltaHalf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m : GLw a w × GLw b w), absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = (GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b)) (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) : ℂ) := by
  intro E _ _ _ a b w m
  rw [GlobalTheory.SmGL.deltaHalf_two, Units.val_mul]
  have e1 : m.1.val.det = ((GeneralLinearGroup.det m.1 : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    simp [GeneralLinearGroup.val_det_apply]
  have e2 : m.2.val.det = ((GeneralLinearGroup.det m.2 : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    simp [GeneralLinearGroup.val_det_apply]
  rw [e1, e2]
  generalize GeneralLinearGroup.det m.1 = d1
  generalize GeneralLinearGroup.det m.2 = d2
  have n1 := GlobalTheory.LGrp.BorelCompletion.nabs_completion w d1
  have n2 := GlobalTheory.LGrp.BorelCompletion.nabs_completion w d2
  have hb : ((Fintype.card (Fin b) : ℂ) / 2) = (((b : ℝ) / 2 : ℝ) : ℂ) := by simp
  have ha : (-(Fintype.card (Fin a) : ℂ) / 2) = ((-(a : ℝ) / 2 : ℝ) : ℂ) := by simp
  rw [hb, ha, GlobalTheory.SmGL.val_absPow_ofReal, GlobalTheory.SmGL.val_absPow_ofReal, n1, n2, ← Complex.ofReal_mul]
  unfold absHalf
  congr 1
  have hd1 : ((d1 : w.adicCompletion E)) ≠ 0 := d1.ne_zero
  have hd2 : ((d2 : w.adicCompletion E)) ≠ 0 := d2.ne_zero
  have hx : ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) ≠ 0 := by
    exact div_ne_zero (pow_ne_zero _ hd1) (pow_ne_zero _ hd2)
  have hv1 : Valued.v (d1 : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd1
  have hv2 : Valued.v (d2 : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd2
  have hord : ordL ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) =
      -((b : ℤ) * WithZero.log (Valued.v (d1 : w.adicCompletion E)) - (a : ℤ) * WithZero.log (Valued.v (d2 : w.adicCompletion E))) := by
    have hv : Valued.v ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    unfold ordL
    rw [dif_neg hv, WithZero.toAdd_unzero_eq_log, map_div₀, map_pow, map_pow,
      WithZero.log_div (pow_ne_zero _ hv1) (pow_ne_zero _ hv2), WithZero.log_pow, WithZero.log_pow]
    simp
  rw [hord, neg_neg]
  have hq : (0 : ℝ) < (qV E w : ℝ) := by
    have : qV E w ≠ 0 := by
      unfold qV; exact (Ideal.absNorm_eq_zero_iff).not.mpr w.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  generalize WithZero.log (Valued.v (d1 : w.adicCompletion E)) = l1
  generalize WithZero.log (Valued.v (d2 : w.adicCompletion E)) = l2
  generalize (qV E w : ℝ) = q at hq ⊢
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_add hq]
  congr 1
  push_cast
  ring

end GlobalTheory.AbsHalfLevi
