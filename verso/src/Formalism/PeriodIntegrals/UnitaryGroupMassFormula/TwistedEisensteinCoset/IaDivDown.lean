import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.UnitCongruentToInteger

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

def NTAll : Prop := IntegerIntegralIffDvd ∧ IntegralApproximationByInteger ∧ ElementEqPrimePowerMulUnit ∧ ValuationExponentUnique ∧ UnitCongruentToInteger

section IntAtLem

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

/- English proof (translation)
Take `⟨r, s, hs, h1⟩` from `ha`. Take `⟨r', s', hs', h2⟩` from `hb`. Use `⟨r * r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, ← h1, ← h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ia_mul {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a * b) := by
  obtain ⟨r, s, hs, h1⟩ := ha
  obtain ⟨r', s', hs', h2⟩ := hb
  refine ⟨r * r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  rw [map_mul, map_mul, ← h1, ← h2]
  ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨k, 1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simp⟩`.
-/
theorem ia_nat (k : ℕ) : IntAt P (k : E) :=
  ⟨k, 1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simp⟩

/- English proof (translation)
Simplify using `using ia_nat P 0`.
-/
theorem ia_zero : IntAt P (0 : E) := by simpa using ia_nat P 0

/- English proof (translation)
Simplify using `using ia_nat P 1`.
-/
theorem ia_one : IntAt P (1 : E) := by simpa using ia_nat P 1

/- English proof (translation)
Take `⟨r, s, hs, h1⟩` from `ha`. Conclude with `⟨-r, s, hs, by rw [map_neg, ← h1]; ring⟩`.
-/
theorem ia_neg {a : E} (ha : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, h1⟩ := ha
  exact ⟨-r, s, hs, by rw [map_neg, ← h1]; ring⟩

/- English proof (translation)
Take `⟨r, s, hs, h1⟩` from `ha`. Take `⟨r', s', hs', h2⟩` from `hb`. Use `⟨r * s' + r' * s, s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, map_mul, ← h1, ← h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ia_add {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r, s, hs, h1⟩ := ha
  obtain ⟨r', s', hs', h2⟩ := hb
  refine ⟨r * s' + r' * s, s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  rw [map_add, map_mul, map_mul, map_mul, ← h1, ← h2]
  ring

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `ia_add P ha (ia_neg P hb)`.
-/
theorem ia_sub {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := by
  rw [sub_eq_add_neg]
  exact ia_add P ha (ia_neg P hb)

/- English proof (translation)
Use `ia_nat P (qOf P ^ k)` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.
-/
theorem ia_qpow (k : ℕ) : IntAt P ((qOf P : E) ^ k) := by
  have := ia_nat P (qOf P ^ k)
  push_cast at this
  exact this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using ia_zero P`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `ia_add P (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem ia_sum {ι : Type*} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    IntAt P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ia_zero P
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ia_add P (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Establish `e : (qOf P : E) ^ D * z = (qOf P : E) ^ (D - j) * ((qOf P : E) ^ j * z)`. Rewrite using `[← mul_assoc, ← pow_add, Nat.sub_add_cancel hjD]`. Rewrite using `[e]`. Conclude with `ia_mul P (ia_qpow P _) hz`.
-/
theorem ia_up {j D : ℕ} (hjD : j ≤ D) {z : E} (hz : IntAt P ((qOf P : E) ^ j * z)) :
    IntAt P ((qOf P : E) ^ D * z) := by
  have e : (qOf P : E) ^ D * z = (qOf P : E) ^ (D - j) * ((qOf P : E) ^ j * z) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hjD]
  rw [e]
  exact ia_mul P (ia_qpow P _) hz

/- English proof (translation)
The claim follows from `Nat.cast_ne_zero.2 hp.ne_zero`.
-/
theorem qE_ne (hp : (Ideal.absNorm P.asIdeal).Prime) : (qOf P : E) ≠ 0 :=
  Nat.cast_ne_zero.2 hp.ne_zero

/- English proof (translation)
Establish `e : x / (qOf P : E) ^ b' = (qOf P : E) ^ (b - b') * (x / (qOf P : E) ^ b)`. Establish `hq` using `qE_ne P hp`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_assoc, ← pow_add, Nat.add_sub_cancel' hb]`. Rewrite using `[e]`.

Conclude with `ia_mul P (ia_qpow P _) hx`.
-/
theorem ia_div_down (hp : (Ideal.absNorm P.asIdeal).Prime) {b b' : ℕ} (hb : b' ≤ b) {x : E}
    (hx : IntAt P (x / (qOf P : E) ^ b)) : IntAt P (x / (qOf P : E) ^ b') := by
  have e : x / (qOf P : E) ^ b' = (qOf P : E) ^ (b - b') * (x / (qOf P : E) ^ b) := by
    have hq := qE_ne P hp
    field_simp
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hb]
  rw [e]
  exact ia_mul P (ia_qpow P _) hx

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Conclude with `⟨0, by rw [ha, mul_zero]; exact ia_zero P⟩`. Take `⟨e, w, rfl, -, hw, -⟩` from `hN.2.2.1 E P hp hq a ha`. Use `⟨(-e).toNat, ?_⟩` and prove the remaining obligations. Establish `hq0` using `qE_ne P hp`.

Establish `: (qOf P : E) ^ (-e).toNat * ((qOf P : E) ^ e * w) = (qOf P : E) ^ (((-e).toNat : ℤ) + e).toNat * w`. Rewrite using `[← mul_assoc, ← zpow_natCast, ← zpow_add₀ hq0, ← zpow_natCast]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this]`.

Conclude with `ia_mul P (ia_qpow P _) hw`.
-/
theorem ia_bound (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (a : E) :
    ∃ g : ℕ, IntAt P ((qOf P : E) ^ g * a) := by
  by_cases ha : a = 0
  · exact ⟨0, by rw [ha, mul_zero]; exact ia_zero P⟩
  obtain ⟨e, w, rfl, -, hw, -⟩ := hN.2.2.1 E P hp hq a ha
  refine ⟨(-e).toNat, ?_⟩
  have hq0 := qE_ne P hp
  have : (qOf P : E) ^ (-e).toNat * ((qOf P : E) ^ e * w) =
      (qOf P : E) ^ (((-e).toNat : ℤ) + e).toNat * w := by
    rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ hq0, ← zpow_natCast]
    congr 2
    omega
  rw [this]
  exact ia_mul P (ia_qpow P _) hw

end IntAtLem

section Val

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

def UnitAt (w : E) : Prop := w ≠ 0 ∧ IntAt P w ∧ IntAt P w⁻¹

open Classical in

def vq (a : E) : ℤ :=
  if h : ∃ e : ℤ, ∃ w : E, a = (qOf P : E) ^ e * w ∧ UnitAt P w then h.choose else 0

variable {P}

/- English proof (translation)
Assemble the required witnesses or components as `⟨mul_ne_zero h.1 h'.1, ia_mul P h.2.1 h'.2.1, by rw [mul_inv]; exact ia_mul P h.2.2 h'.2.2⟩`.
-/
theorem unitAt_mul {w w' : E} (h : UnitAt P w) (h' : UnitAt P w') : UnitAt P (w * w') :=
  ⟨mul_ne_zero h.1 h'.1, ia_mul P h.2.1 h'.2.1, by rw [mul_inv]; exact ia_mul P h.2.2 h'.2.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨one_ne_zero, ia_one P, by rw [inv_one]; exact ia_one P⟩`.
-/
theorem unitAt_one : UnitAt P (1 : E) := ⟨one_ne_zero, ia_one P, by rw [inv_one]; exact ia_one P⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨inv_ne_zero h.1, h.2.2, by rw [inv_inv]; exact h.2.1⟩`.
-/
theorem unitAt_inv {w : E} (h : UnitAt P w) : UnitAt P w⁻¹ := ⟨inv_ne_zero h.1, h.2.2, by rw [inv_inv]; exact h.2.1⟩

variable (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
include hN hp hq

/- English proof (translation)
Establish `h : ∃ e : ℤ, ∃ w : E, a = (qOf P : E) ^ e * w ∧ UnitAt P w`. Take `⟨e, w, h1, h2, h3, h4⟩` from `hN.2.2.1 E P hp hq a ha`. Conclude with `⟨e, w, h1, h2, h3, h4⟩`. Unfold `vq`. Rewrite using `[dif_pos h]`.

Conclude with `h.choose_spec`.
-/
theorem vq_spec {a : E} (ha : a ≠ 0) : ∃ w : E, a = (qOf P : E) ^ vq P a * w ∧ UnitAt P w := by
  have h : ∃ e : ℤ, ∃ w : E, a = (qOf P : E) ^ e * w ∧ UnitAt P w := by
    obtain ⟨e, w, h1, h2, h3, h4⟩ := hN.2.2.1 E P hp hq a ha
    exact ⟨e, w, h1, h2, h3, h4⟩
  unfold vq
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Establish `ha : a ≠ 0`. Rewrite using `[h]`. Conclude with `mul_ne_zero (zpow_ne_zero _ (qE_ne P hp)) hw.1`. Take `⟨w1, h1, hw1⟩` from `vq_spec hN hp hq ha`. Conclude with `hN.2.2.2.1 E P hp hq _ _ w1 w hw1.1 hw1.2.1 hw1.2.2 hw.2.1 hw.2.2 (h1.symm.trans h)`.
-/
theorem vq_eq {a w : E} {e : ℤ} (h : a = (qOf P : E) ^ e * w) (hw : UnitAt P w) : vq P a = e := by
  have ha : a ≠ 0 := by
    rw [h]
    exact mul_ne_zero (zpow_ne_zero _ (qE_ne P hp)) hw.1
  obtain ⟨w1, h1, hw1⟩ := vq_spec hN hp hq ha
  exact hN.2.2.2.1 E P hp hq _ _ w1 w hw1.1 hw1.2.1 hw1.2.2 hw.2.1 hw.2.2 (h1.symm.trans h)

/- English proof (translation)
Take `⟨w, h1, hw⟩` from `vq_spec hN hp hq ha`. Take `⟨w', h2, hw'⟩` from `vq_spec hN hp hq hb`. Apply `vq_eq hN hp hq _ (unitAt_mul hw hw')` to reduce the goal to its premises. Rewrite using `[zpow_add₀ (qE_ne P hp)]`. Use `conv_lhs => rw [h1, h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem vq_mul {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) : vq P (a * b) = vq P a + vq P b := by
  obtain ⟨w, h1, hw⟩ := vq_spec hN hp hq ha
  obtain ⟨w', h2, hw'⟩ := vq_spec hN hp hq hb
  apply vq_eq hN hp hq _ (unitAt_mul hw hw')
  rw [zpow_add₀ (qE_ne P hp)]
  conv_lhs => rw [h1, h2]
  ring

/- English proof (translation)
The claim follows from `vq_eq hN hp hq (by simp) unitAt_one`.
-/
theorem vq_one : vq P (1 : E) = 0 := vq_eq hN hp hq (by simp) unitAt_one

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using vq_one hN hp hq`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, vq_mul hN hp hq (hf a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)), ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]`.
-/
theorem vq_prod {ι : Type*} (s : Finset ι) (f : ι → E) (hf : ∀ i ∈ s, f i ≠ 0) :
    vq P (∏ i ∈ s, f i) = ∑ i ∈ s, vq P (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vq_one hN hp hq
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      vq_mul hN hp hq (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

end Val

end PI.TwistedEisensteinNonvanishing.W
