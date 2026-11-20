import Mathlib
import Formalism.LocalRingCardinality.HostCls

namespace UpperTheory.Ram.Rd

open Formalism.BasicNotions

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Establish `he` using `H.two_le_e`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sixteen_dvd_QS : 16 ∣ H.QS := by
  have he := H.two_le_e
  calc 16 = 2 ^ 4 := by norm_num
    _ ∣ 2 ^ (R.e + 2) := Nat.pow_dvd_pow 2 (by omega)
    _ ∣ H.QS := H.tower_dvd

/- English proof (translation)
Conclude with `H.QS_pos` after adjusting the coercions.
-/
theorem one_le_QS_real : (1 : ℝ) ≤ H.QS := by exact_mod_cast H.QS_pos

/- English proof (translation)
Conclude with `H.QS_le` after adjusting the coercions.
-/
theorem QS_le_real : (H.QS : ℝ) ≤ (R.n : ℝ) ^ 2 := by exact_mod_cast H.QS_le

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_QS_le : Real.log H.QS ≤ 2 * Real.log R.n := by
  calc Real.log H.QS ≤ Real.log ((R.n : ℝ) ^ 2) :=
        Real.log_le_log (by linarith [one_le_QS_real H]) (QS_le_real H)
    _ = 2 * Real.log R.n := by rw [Real.log_pow]; norm_num

/- English proof (translation)
Unfold `Host.rdE`. Check the signs of the components of the expression.
-/
theorem rdE_nonneg : 0 ≤ H.rdE := by unfold Host.rdE; positivity

/- English proof (translation)
Establish `h : (4 * R.ord : ℝ) ≤ H.rdE ^ 2` using `H.der.rd_sq_ge`. Establish `h4 : (4 : ℝ) ≤ R.ord` using `by rw [← R.n_eq_ord]; exact_mod_cast H.four_le_n'`. Establish `h0` using `(rdE_nonneg H)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem four_le_rdE : 4 ≤ H.rdE := by
  have h : (4 * R.ord : ℝ) ≤ H.rdE ^ 2 := H.der.rd_sq_ge
  have h4 : (4 : ℝ) ≤ R.ord := by rw [← R.n_eq_ord]; exact_mod_cast H.four_le_n'
  have h0 := (rdE_nonneg H)
  nlinarith

/- English proof (translation)
Combine the linear relations using `[four_le_rdE H]`.
-/
theorem two_le_rdE : 2 ≤ H.rdE := by
  linarith [four_le_rdE H]

/- English proof (translation)
Use `(four_le_rdE H)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rdE_pos : 0 < H.rdE := by have := (four_le_rdE H); linarith

/- English proof (translation)
The claim follows from `H.der.rd_le`.
-/
theorem rdE_le_QS : H.rdE ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) := H.der.rd_le

/- English proof (translation)
Establish `hyp` using `H.hyp`. Unfold `Formalism.FrobeniusOrbits.HostHyp at hyp`. Establish `hq : (2 : ℝ) ≤ H.q` using `by exact_mod_cast hyp.1.two_le`. Establish `hd : (2 : ℝ) ≤ H.d` using `by exact_mod_cast hyp.2.1.two_le`. Rewrite using `[Real.sqrt_le_iff]`.

Prove the components needed by the constructor for the conclusion. Check the signs of the components of the expression. Use polynomial arithmetic with `[mul_le_mul hq hd (by norm_num) (by linarith)]`.
-/
theorem sqrt_qd_le : Real.sqrt ((H.q : ℝ) * H.d) ≤ (H.q : ℝ) * H.d := by
  have hyp := H.hyp
  unfold Formalism.FrobeniusOrbits.HostHyp at hyp
  have hq : (2 : ℝ) ≤ H.q := by exact_mod_cast hyp.1.two_le
  have hd : (2 : ℝ) ≤ H.d := by exact_mod_cast hyp.2.1.two_le
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [mul_le_mul hq hd (by norm_num) (by linarith)]

/- English proof (translation)
Establish `h1` using `rdE_le_QS H`. Establish `h2` using `sqrt_qd_le H`. Establish `h3 : (0 : ℝ) ≤ H.QS` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem two_mul_rdE_le_cond : 2 * H.rdE ≤ (H.QS : ℝ) * H.q * H.d := by
  have h1 := rdE_le_QS H
  have h2 := sqrt_qd_le H
  have h3 : (0 : ℝ) ≤ H.QS := by positivity
  calc 2 * H.rdE ≤ (H.QS : ℝ) * Real.sqrt ((H.q : ℝ) * H.d) := by linarith
    _ ≤ (H.QS : ℝ) * ((H.q : ℝ) * H.d) := mul_le_mul_of_nonneg_left h2 h3
    _ = (H.QS : ℝ) * H.q * H.d := by ring

/- English proof (translation)
Combine the linear relations using `[two_mul_rdE_le_cond H, rdE_nonneg H]`.
-/
theorem rdE_le_cond : H.rdE ≤ (H.QS : ℝ) * H.q * H.d := by
  linarith [two_mul_rdE_le_cond H, rdE_nonneg H]

/- English proof (translation)
Establish `hyp` using `H.hyp`. Unfold `Formalism.FrobeniusOrbits.HostHyp at hyp`. Establish `hq : (0 : ℝ) < H.q` using `by exact_mod_cast hyp.1.pos`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast hyp.2.1.pos`. Establish `hQ : (0 : ℝ) < H.QS` using `by exact_mod_cast H.QS_pos`.

Establish `hs : 0 < Real.sqrt ((H.q : ℝ) * H.d)` using `Real.sqrt_pos.2 (mul_pos hq hd)`. Establish `h1 : H.rdE ≤ (H.QS : ℝ) * Real.sqrt ((H.q : ℝ) * H.d)`. Use `rdE_le_QS H` as an intermediate fact. Use polynomial arithmetic with `[mul_pos hQ hs]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Real.log_mul hQ.ne' hs.ne', Real.log_sqrt (mul_pos hq hd).le, Real.log_mul hq.ne' hd.ne']`. Use `_ ≤ 2 * Real.log R.n + (Real.log H.q + Real.log H.d) / 2 := by linarith [log_QS_le H]`.
-/
theorem log_rdE_le : Real.log H.rdE ≤ 2 * Real.log R.n + (Real.log H.q + Real.log H.d) / 2 := by
  have hyp := H.hyp
  unfold Formalism.FrobeniusOrbits.HostHyp at hyp
  have hq : (0 : ℝ) < H.q := by exact_mod_cast hyp.1.pos
  have hd : (0 : ℝ) < H.d := by exact_mod_cast hyp.2.1.pos
  have hQ : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  have hs : 0 < Real.sqrt ((H.q : ℝ) * H.d) := Real.sqrt_pos.2 (mul_pos hq hd)
  have h1 : H.rdE ≤ (H.QS : ℝ) * Real.sqrt ((H.q : ℝ) * H.d) := by
    have := rdE_le_QS H
    nlinarith [mul_pos hQ hs]
  calc Real.log H.rdE ≤ Real.log ((H.QS : ℝ) * Real.sqrt ((H.q : ℝ) * H.d)) := Real.log_le_log (rdE_pos H) h1
    _ = Real.log H.QS + (Real.log H.q + Real.log H.d) / 2 := by
      rw [Real.log_mul hQ.ne' hs.ne', Real.log_sqrt (mul_pos hq hd).le, Real.log_mul hq.ne' hd.ne']
    _ ≤ 2 * Real.log R.n + (Real.log H.q + Real.log H.d) / 2 := by linarith [log_QS_le H]

/- English proof (translation)
Establish `hyp` using `H.hyp`. Unfold `Formalism.FrobeniusOrbits.HostHyp at hyp`. Establish `hq : (0 : ℝ) < H.q` using `by exact_mod_cast hyp.1.pos`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast hyp.2.1.pos`. Establish `hQ : (0 : ℝ) < H.QS` using `by exact_mod_cast H.QS_pos`.

Rewrite using `[Real.log_mul (mul_pos hQ hq).ne' hd.ne', Real.log_mul hQ.ne' hq.ne']`. Combine the linear relations using `[log_QS_le H]`.
-/
theorem log_cond_le : Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 2 * Real.log R.n + Real.log H.q + Real.log H.d := by
  have hyp := H.hyp
  unfold Formalism.FrobeniusOrbits.HostHyp at hyp
  have hq : (0 : ℝ) < H.q := by exact_mod_cast hyp.1.pos
  have hd : (0 : ℝ) < H.d := by exact_mod_cast hyp.2.1.pos
  have hQ : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  rw [Real.log_mul (mul_pos hQ hq).ne' hd.ne', Real.log_mul hQ.ne' hq.ne']
  linarith [log_QS_le H]

end UpperTheory.Ram.Rd
