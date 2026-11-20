import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.UnitCongruentToInteger
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.UniformContinuityGaloisGroup

open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

namespace NTA

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

/- English proof (translation)
Take `⟨r1, s1, hs1, h1⟩` from `ha`. Take `⟨r2, s2, hs2, h2⟩` from `hb`. Use `⟨r1 * r2, s1 * s2, fun h => ?_, ?_⟩` and prove the remaining obligations. Break down `P.isPrime.mem_or_mem h with h | h exacts [hs1 h, hs2 h]` into its components or cases. Simplify using `only [map_mul]`.

Rewrite using `[← h1, ← h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iMul {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a * b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨r1 * r2, s1 * s2, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h | h
    exacts [hs1 h, hs2 h]
  · simp only [map_mul]
    rw [← h1, ← h2]
    ring
/- English proof (translation)
Take `⟨r1, s1, hs1, h1⟩` from `ha`. Take `⟨r2, s2, hs2, h2⟩` from `hb`. Use `⟨r1 * s2 + r2 * s1, s1 * s2, fun h => ?_, ?_⟩` and prove the remaining obligations. Break down `P.isPrime.mem_or_mem h with h | h exacts [hs1 h, hs2 h]` into its components or cases. Simplify using `only [map_mul, map_add]`.

Rewrite using `[← h1, ← h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iAdd {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨r1 * s2 + r2 * s1, s1 * s2, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h | h
    exacts [hs1 h, hs2 h]
  · simp only [map_mul, map_add]
    rw [← h1, ← h2]
    ring
/- English proof (translation)
Take `⟨r1, s1, hs1, h1⟩` from `ha`. Take `⟨r2, s2, hs2, h2⟩` from `hb`. Use `⟨r1 * s2 - r2 * s1, s1 * s2, fun h => ?_, ?_⟩` and prove the remaining obligations. Break down `P.isPrime.mem_or_mem h with h | h exacts [hs1 h, hs2 h]` into its components or cases. Simplify using `only [map_mul, map_sub]`.

Rewrite using `[← h1, ← h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iSub {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨r1 * s2 - r2 * s1, s1 * s2, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h | h
    exacts [hs1 h, hs2 h]
  · simp only [map_mul, map_sub]
    rw [← h1, ← h2]
    ring
/- English proof (translation)
Assemble the required witnesses or components as `⟨(m : 𝓞 E), 1, (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top, by simp⟩`.
-/
theorem iNat (m : ℕ) : IntAt P (m : E) := ⟨(m : 𝓞 E), 1, (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top, by simp⟩
/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using iNat P 1`. Consider the case `succ m ih => rw [pow_succ]`. Conclude with `iMul P ih ha`.
-/
theorem iPow {a : E} (ha : IntAt P a) (m : ℕ) : IntAt P (a ^ m) := by
  induction m with
  | zero => simpa using iNat P 1
  | succ m ih => rw [pow_succ]; exact iMul P ih ha
/- English proof (translation)
Assemble the required witnesses or components as `⟨x, 1, (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top, by simp⟩`.
-/
theorem iAlg (x : 𝓞 E) : IntAt P (algebraMap (𝓞 E) E x) := ⟨x, 1, (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top, by simp⟩

/- English proof (translation)
The claim follows from `Ideal.absNorm_mem P.asIdeal`.
-/
theorem qO_mem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal

/- English proof (translation)
Conclude with `Nat.cast_ne_zero.mpr hp.ne_zero`.
-/
theorem q_ne (hp : (Ideal.absNorm P.asIdeal).Prime) : (qOf P : E) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr hp.ne_zero

/- English proof (translation)
The claim follows from `(Ideal.ne_top_iff_one _).mp P.isPrime.ne_top`.
-/
theorem one_nm : (1 : 𝓞 E) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top

/- English proof (translation)
Introduce and unpack `⟨r, s, hs, h⟩`. Apply `hs` to reduce the goal to its premises. Establish `hq` using `q_ne P hp`. Establish `e : algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E (r * ((qOf P : ℕ) : 𝓞 E))`. Rewrite using `[map_mul, ← h, map_natCast, mul_assoc, inv_mul_cancel₀ hq, mul_one]`.

Rewrite using `[IsFractionRing.injective (𝓞 E) E e]`. Conclude with `Ideal.mul_mem_left _ _ (qO_mem P)`.
-/
theorem not_int_inv_q (hp : (Ideal.absNorm P.asIdeal).Prime) : ¬ IntAt P ((qOf P : E)⁻¹) := by
  rintro ⟨r, s, hs, h⟩
  apply hs
  have hq := q_ne P hp
  have e : algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E (r * ((qOf P : ℕ) : 𝓞 E)) := by
    rw [map_mul, ← h, map_natCast, mul_assoc, inv_mul_cancel₀ hq, mul_one]
  rw [IsFractionRing.injective (𝓞 E) E e]
  exact Ideal.mul_mem_left _ _ (qO_mem P)

/- English proof (translation)
Introduce `hmP`. Establish `hcop : IsCoprime ((qOf P : ℕ) : ℤ) (m : ℤ)` using `Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)`. Take `⟨u, v, huv⟩` from `hcop`. Apply `one_nm P` to reduce the goal to its premises. Establish `e : (((u * ((qOf P : ℕ) : ℤ) + v * (m : ℤ) : ℤ)) : 𝓞 E) = 1`.

Rewrite using `[huv]`. Simplify using the standard rewrite rules. Rewrite using `[← e]`. Use `push_cast`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ (qO_mem P)) (Ideal.mul_mem_left _ _ hmP)`.
-/
theorem natCast_notMem (hp : (Ideal.absNorm P.asIdeal).Prime) {m : ℕ} (hm : ¬ qOf P ∣ m) :
    (m : 𝓞 E) ∉ P.asIdeal := by
  intro hmP
  have hcop : IsCoprime ((qOf P : ℕ) : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  obtain ⟨u, v, huv⟩ := hcop
  apply one_nm P
  have e : (((u * ((qOf P : ℕ) : ℤ) + v * (m : ℤ) : ℤ)) : 𝓞 E) = 1 := by
    rw [huv]
    simp
  rw [← e]
  push_cast
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (qO_mem P)) (Ideal.mul_mem_left _ _ hmP)

/- English proof (translation)
Establish `hm0 : (m : E) ≠ 0`. Establish `: m ≠ 0` using `fun h => hm (h ▸ dvd_zero _)`. Conclude with `this` after adjusting the coercions. Use `⟨1, (m : 𝓞 E), natCast_notMem P hp hm, ?_⟩` and prove the remaining obligations. Rewrite using `[map_natCast, map_one, mul_inv_cancel₀ hm0]`.
-/
theorem int_inv_nat (hp : (Ideal.absNorm P.asIdeal).Prime) {m : ℕ} (hm : ¬ qOf P ∣ m) : IntAt P ((m : E)⁻¹) := by
  have hm0 : (m : E) ≠ 0 := by
    have : m ≠ 0 := fun h => hm (h ▸ dvd_zero _)
    exact_mod_cast this
  refine ⟨1, (m : 𝓞 E), natCast_notMem P hp hm, ?_⟩
  rw [map_natCast, map_one, mul_inv_cancel₀ hm0]

/- English proof (translation)
Establish `hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = qOf P`. Unfold `qOf`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `haveI : Finite (𝓞 E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)`. Set `f : Fin (qOf P) → 𝓞 E ⧸ P.asIdeal` to `fun d => Ideal.Quotient.mk P.asIdeal ((d : ℕ) : 𝓞 E)`.

Establish `hinj : Function.Injective f`. Introduce `d d' h`. Establish `h' : ((d : ℕ) : 𝓞 E) - ((d' : ℕ) : 𝓞 E) ∈ P.asIdeal` using `Ideal.Quotient.eq.mp h`. Establish `hd` using `d.isLt`. Establish `hd'` using `d'.isLt`.

Apply `Fin.ext` to reduce the goal to its premises. Assume the negation of the conclusion as `hne`. Break down `Nat.lt_or_gt_of_ne hne with hlt | hlt` into its components or cases. Establish `hm : ((d'.val - d.val : ℕ) : 𝓞 E) ∈ P.asIdeal`. Rewrite using `[Nat.cast_sub hlt.le]`.

Use `P.asIdeal.neg_mem h'` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis. Conclude with `natCast_notMem P hp (fun hdvd => by`. Use `Nat.le_of_dvd (by omega) hdvd` as an intermediate fact. Use the proof step `omega) hm`.

Establish `hm : ((d.val - d'.val : ℕ) : 𝓞 E) ∈ P.asIdeal`. Rewrite using `[Nat.cast_sub hlt.le]`. Conclude with `h'`. Conclude with `natCast_notMem P hp (fun hdvd => by`. Use `Nat.le_of_dvd (by omega) hdvd` as an intermediate fact.

Use the proof step `omega) hm`. Establish `hbij` using `hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin])`. Take `⟨d, hd⟩` from `hbij.2 x`. Conclude with `⟨d.val, d.isLt, hd⟩`.
-/
theorem res_surj (hp : (Ideal.absNorm P.asIdeal).Prime) (x : 𝓞 E ⧸ P.asIdeal) :
    ∃ d : ℕ, d < qOf P ∧ Ideal.Quotient.mk P.asIdeal (d : 𝓞 E) = x := by
  have hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = qOf P := by
    unfold qOf
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ P.asIdeal) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  let f : Fin (qOf P) → 𝓞 E ⧸ P.asIdeal := fun d => Ideal.Quotient.mk P.asIdeal ((d : ℕ) : 𝓞 E)
  have hinj : Function.Injective f := by
    intro d d' h
    have h' : ((d : ℕ) : 𝓞 E) - ((d' : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.Quotient.eq.mp h
    have hd := d.isLt
    have hd' := d'.isLt
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hm : ((d'.val - d.val : ℕ) : 𝓞 E) ∈ P.asIdeal := by
        rw [Nat.cast_sub hlt.le]
        have := P.asIdeal.neg_mem h'
        rwa [neg_sub] at this
      exact natCast_notMem P hp (fun hdvd => by
        have := Nat.le_of_dvd (by omega) hdvd
        omega) hm
    · have hm : ((d.val - d'.val : ℕ) : 𝓞 E) ∈ P.asIdeal := by
        rw [Nat.cast_sub hlt.le]
        exact h'
      exact natCast_notMem P hp (fun hdvd => by
        have := Nat.le_of_dvd (by omega) hdvd
        omega) hm
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨d, hd⟩ := hbij.2 x
  exact ⟨d.val, d.isLt, hd⟩

/- English proof (translation)
Establish `hle : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal` using `(Ideal.span_singleton_le_iff_mem _).mpr (qO_mem P)`. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.mpr hle`. Establish `hJP : ¬ J ≤ P.asIdeal`. Introduce `h`. Apply `hq` to reduce the goal to its premises.

Establish `h2 : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal ^ 2`. Rewrite using `[hJ, pow_two]`. Conclude with `Ideal.mul_mono_right h`. Conclude with `h2 (Ideal.mem_span_singleton_self _)`. Take `⟨t, htJ, htP⟩` from `SetLike.not_le_iff_exists.mp hJP`.

Establish `hmem : α * t ∈ Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)}`. Rewrite using `[hJ]`. Conclude with `Ideal.mul_mem_mul hα htJ`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hmem`. Establish `hq0` using `q_ne P hp`.

Use `⟨c, t, htP, ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (algebraMap (𝓞 E) E) hc`. Simplify using `only [map_mul, map_natCast] at e`. Rewrite using `[mul_div_assoc', div_eq_iff hq0]`. Unfold `qOf`.

Take the linear combination `-e`.
-/
private theorem intAt_div_qOf_of_mem (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {α : 𝓞 E} (hα : α ∈ P.asIdeal) :
    IntAt P (algebraMap (𝓞 E) E α / (qOf P : E)) := by
  have hle : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr (qO_mem P)
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hJP : ¬ J ≤ P.asIdeal := by
    intro h
    apply hq
    have h2 : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right h
    exact h2 (Ideal.mem_span_singleton_self _)
  obtain ⟨t, htJ, htP⟩ := SetLike.not_le_iff_exists.mp hJP
  have hmem : α * t ∈ Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hα htJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hq0 := q_ne P hp
  refine ⟨c, t, htP, ?_⟩
  have e := congrArg (algebraMap (𝓞 E) E) hc
  simp only [map_mul, map_natCast] at e
  rw [mul_div_assoc', div_eq_iff hq0]
  unfold qOf
  linear_combination -e

/- English proof (translation)
Use `haveI : P.asIdeal.IsMaximal := P.isMaximal`. Use `letI := Ideal.Quotient.field P.asIdeal`. Take `⟨r, s, hs, hy'⟩` from `hy`. Establish `hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0` using `fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)`. Take `⟨d, hdq, hd⟩` from `res_surj P hp (Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹)`.

Establish `hmem : r - (d : 𝓞 E) * s ∈ P.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hd, mul_assoc, inv_mul_cancel₀ hs0, mul_one, sub_self]`. Take `⟨c, t, ht, hct⟩` from `intAt_div_qOf_of_mem P hp hq hmem`. Establish `hs' : algebraMap (𝓞 E) E s ≠ 0`. Introduce `h`.

Apply `hs` to reduce the goal to its premises. Rewrite using `[IsFractionRing.injective (𝓞 E) E (h.trans (map_zero _).symm)]`. Conclude with `P.asIdeal.zero_mem`. Establish `hq0` using `q_ne P hp`. Use `⟨d, hdq, c, t * s, fun h => ?_, ?_⟩` and prove the remaining obligations.

Break down `P.isPrime.mem_or_mem h with h | h exacts [ht h, hs h]` into its components or cases. Establish `hy2 : y = algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E s`. Rewrite using `[eq_div_iff hs', mul_comm]`. Conclude with `hy'`. Rewrite using `[← hct, hy2, map_mul, map_sub, map_mul, map_natCast]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem approx1 (hp : (Ideal.absNorm P.asIdeal).Prime) (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    {y : E} (hy : IntAt P y) : ∃ d : ℕ, d < qOf P ∧ IntAt P ((y - d) / (qOf P : E)) := by
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  obtain ⟨r, s, hs, hy'⟩ := hy
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨d, hdq, hd⟩ :=
    res_surj P hp (Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹)
  have hmem : r - (d : 𝓞 E) * s ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hd, mul_assoc, inv_mul_cancel₀ hs0,
      mul_one, sub_self]
  obtain ⟨c, t, ht, hct⟩ := intAt_div_qOf_of_mem P hp hq hmem
  have hs' : algebraMap (𝓞 E) E s ≠ 0 := by
    intro h
    apply hs
    rw [IsFractionRing.injective (𝓞 E) E (h.trans (map_zero _).symm)]
    exact P.asIdeal.zero_mem
  have hq0 := q_ne P hp
  refine ⟨d, hdq, c, t * s, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h | h
    exacts [ht h, hs h]
  · have hy2 : y = algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E s := by
      rw [eq_div_iff hs', mul_comm]
      exact hy'
    rw [← hct, hy2, map_mul, map_sub, map_mul, map_natCast]
    field_simp

/- English proof (translation)
Use `haveI := P.isPrime`. Take `⟨r, s, hs, h⟩` from `h`. Establish `hq0` using `q_ne P hp`. Establish `e : algebraMap (𝓞 E) E (s * α) = algebraMap (𝓞 E) E (r * ((qOf P : ℕ) : 𝓞 E) ^ K)`. Rewrite using `[map_mul, map_mul, map_pow, map_natCast, ← h]`.

Clear the denominators using the available nonvanishing facts. Establish `hsα : s * α ∈ P.asIdeal ^ K`. Rewrite using `[IsFractionRing.injective (𝓞 E) E e]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (qO_mem P) K)`. Conclude with `(Ideal.IsPrime.mul_mem_pow P.asIdeal hsα).resolve_left hs`.
-/
theorem mem_pow_of (hp : (Ideal.absNorm P.asIdeal).Prime) {α : 𝓞 E} {K : ℕ}
    (h : IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ K)) : α ∈ P.asIdeal ^ K := by
  haveI := P.isPrime
  obtain ⟨r, s, hs, h⟩ := h
  have hq0 := q_ne P hp
  have e : algebraMap (𝓞 E) E (s * α) = algebraMap (𝓞 E) E (r * ((qOf P : ℕ) : 𝓞 E) ^ K) := by
    rw [map_mul, map_mul, map_pow, map_natCast, ← h]
    field_simp
  have hsα : s * α ∈ P.asIdeal ^ K := by
    rw [IsFractionRing.injective (𝓞 E) E e]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (qO_mem P) K)
  exact (Ideal.IsPrime.mul_mem_pow P.asIdeal hsα).resolve_left hs

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hall : ∀ K, α ∈ P.asIdeal ^ K` using `fun K => mem_pow_of P hp (hcon K)`. Establish `hbot` using `Ideal.iInf_pow_eq_bot_of_isDomain P.asIdeal P.isPrime.ne_top`. Establish `hin : α ∈ (⨅ i, P.asIdeal ^ i)` using `Ideal.mem_iInf.mpr hall`.

Rewrite `hin` using `[hbot, Ideal.mem_bot]`. Conclude with `hα hin`.
-/
theorem exists_not_int (hp : (Ideal.absNorm P.asIdeal).Prime) {α : 𝓞 E} (hα : α ≠ 0) :
    ∃ K : ℕ, ¬ IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ K) := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ K, α ∈ P.asIdeal ^ K := fun K => mem_pow_of P hp (hcon K)
  have hbot := Ideal.iInf_pow_eq_bot_of_isDomain P.asIdeal P.isPrime.ne_top
  have hin : α ∈ (⨅ i, P.asIdeal ^ i) := Ideal.mem_iInf.mpr hall
  rw [hbot, Ideal.mem_bot] at hin
  exact hα hin

/- English proof (translation)
Establish `hex` using `exists_not_int P hp hα`. Establish `hK : ¬ IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ Nat.find hex)` using `Nat.find_spec hex`. Establish `hK0 : Nat.find hex ≠ 0`. Introduce `h0`. Apply `hK` to reduce the goal to its premises.

Rewrite using `[h0, pow_zero, div_one]`. Conclude with `iAlg P α`. Take `⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1` from `⟨Nat.find hex - 1, by omega⟩`. Establish `hint : IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ k)` using `not_not.mp (Nat.find_min hex (by omega : k < Nat.find hex))`. Rewrite `hK` using `[hk]`.

Establish `hq0` using `q_ne P hp`. Establish `hα' : algebraMap (𝓞 E) E α ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hα`. Establish `hu0 : algebraMap (𝓞 E) E α / (qOf P : E) ^ k ≠ 0` using `div_ne_zero hα' (pow_ne_zero _ hq0)`. Use `⟨k, algebraMap (𝓞 E) E α / (qOf P : E) ^ k, ?_, hu0, hint, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.

Take `⟨r, s, hs, hrs⟩` from `hint`. Establish `hrP : r ∉ P.asIdeal`. Introduce `hr`. Apply `hK` to reduce the goal to its premises. Take `⟨c, t, ht, hct⟩` from `intAt_div_qOf_of_mem P hp hq hr`.

Use `⟨c, t * s, fun h => ?_, ?_⟩` and prove the remaining obligations. Break down `P.isPrime.mem_or_mem h with h | h exacts [ht h, hs h]` into its components or cases. Rewrite using `[← hct, ← hrs, map_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `⟨s, r, hrP, ?_⟩` and prove the remaining obligations. Rewrite using `[← hrs, mul_assoc, mul_inv_cancel₀ hu0, mul_one]`.
-/
theorem decomp (hp : (Ideal.absNorm P.asIdeal).Prime) (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    {α : 𝓞 E} (hα : α ≠ 0) : ∃ (k : ℕ) (u : E), algebraMap (𝓞 E) E α = (qOf P : E) ^ k * u ∧ u ≠ 0 ∧
      IntAt P u ∧ IntAt P u⁻¹ := by
  classical
  have hex := exists_not_int P hp hα
  have hK : ¬ IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ Nat.find hex) := Nat.find_spec hex
  have hK0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hK
    rw [h0, pow_zero, div_one]
    exact iAlg P α
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hint : IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ k) :=
    not_not.mp (Nat.find_min hex (by omega : k < Nat.find hex))
  rw [hk] at hK
  have hq0 := q_ne P hp
  have hα' : algebraMap (𝓞 E) E α ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hα
  have hu0 : algebraMap (𝓞 E) E α / (qOf P : E) ^ k ≠ 0 := div_ne_zero hα' (pow_ne_zero _ hq0)
  refine ⟨k, algebraMap (𝓞 E) E α / (qOf P : E) ^ k, ?_, hu0, hint, ?_⟩
  · field_simp
  · obtain ⟨r, s, hs, hrs⟩ := hint
    have hrP : r ∉ P.asIdeal := by
      intro hr
      apply hK
      obtain ⟨c, t, ht, hct⟩ := intAt_div_qOf_of_mem P hp hq hr
      refine ⟨c, t * s, fun h => ?_, ?_⟩
      · rcases P.isPrime.mem_or_mem h with h | h
        exacts [ht h, hs h]
      · rw [← hct, ← hrs, map_mul]
        field_simp
        ring
    refine ⟨s, r, hrP, ?_⟩
    rw [← hrs, mul_assoc, mul_inv_cancel₀ hu0, mul_one]

/- English proof (translation)
Establish `hq0` using `q_ne P hp`. Establish `hw'0 : w' ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[mul_zero]`. Conclude with `hw h`.

Establish `hint : IntAt P (w⁻¹ * w' * (qOf P : E) ^ d)` using `iMul P (iMul P hwi hw') (iPow P (iNat P _) d)`. Establish `e : w⁻¹ * w' * (qOf P : E) ^ d = (qOf P : E)⁻¹`. Rewrite using `[h]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hint` using `[e]`. Conclude with `not_int_inv_q P hp hint`.
-/
theorem no_shift (hp : (Ideal.absNorm P.asIdeal).Prime) (d : ℕ) {w w' : E} (hw : w ≠ 0) (hwi : IntAt P w⁻¹)
    (hw' : IntAt P w') (h : w = (qOf P : E) ^ (d + 1) * w') : False := by
  have hq0 := q_ne P hp
  have hw'0 : w' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact hw h
  have hint : IntAt P (w⁻¹ * w' * (qOf P : E) ^ d) :=
    iMul P (iMul P hwi hw') (iPow P (iNat P _) d)
  have e : w⁻¹ * w' * (qOf P : E) ^ d = (qOf P : E)⁻¹ := by
    rw [h]
    field_simp
    ring
  rw [e] at hint
  exact not_int_inv_q P hp hint

end NTA

open NTA in
/- English proof (translation)
Introduce `E _ _ P hp hq i e`. Establish `hq0` using `q_ne P hp`. Prove the components needed by the constructor for the conclusion. Introduce `hI`. Assume the negation of the conclusion as `hnd`.

Establish `hi0 : i ≠ 0`. Introduce and unpack `rfl`. Conclude with `hnd (dvd_zero _)`. Take `⟨f, j, hj, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hi0 (qOf P) hp.one_lt.ne'`. Establish `hfe : f < e`.

Assume the negation of the conclusion as `hfe`. Use `push_neg at hfe`. Conclude with `hnd (Dvd.dvd.mul_right (pow_dvd_pow _ hfe) _)`. Establish `h1 : IntAt P ((((qOf P ^ f * j : ℕ) : E) / (qOf P : E) ^ e) * (j : E)⁻¹ * (qOf P : E) ^ (e - f - 1))` using `iMul P (iMul P hI (int_inv_nat P hp hj)) (iPow P (iNat P _) _)`. Establish `hj0 : (j : E) ≠ 0`.

Establish `: j ≠ 0` using `fun h => hj (h ▸ dvd_zero _)`. Conclude with `this` after adjusting the coercions. Establish `e2 : (((qOf P ^ f * j : ℕ) : E) / (qOf P : E) ^ e) * (j : E)⁻¹ * (qOf P : E) ^ (e - f - 1) = (qOf P : E)⁻¹`. Take `⟨g, rfl⟩ : ∃ g, e = f + g + 1` from `⟨e - f - 1, by omega⟩`. Establish `hg : f + g + 1 - f - 1 = g` using `by omega`.

Rewrite using `[hg]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[e2]`.

Conclude with `not_int_inv_q P hp h1`. Introduce and unpack `⟨k, rfl⟩`. Establish `e2 : (((qOf P ^ e * k : ℕ) : E) / (qOf P : E) ^ e) = (k : E)`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e2]`. Conclude with `iNat P k`.
-/
theorem integer_integral_iff_dvd : IntegerIntegralIffDvd := by
  intro E _ _ P hp hq i e
  have hq0 := q_ne P hp
  constructor
  · intro hI
    by_contra hnd
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hnd (dvd_zero _)
    obtain ⟨f, j, hj, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi0 (qOf P) hp.one_lt.ne'
    have hfe : f < e := by
      by_contra hfe
      push_neg at hfe
      exact hnd (Dvd.dvd.mul_right (pow_dvd_pow _ hfe) _)
    have h1 : IntAt P ((((qOf P ^ f * j : ℕ) : E) / (qOf P : E) ^ e) * (j : E)⁻¹ *
        (qOf P : E) ^ (e - f - 1)) :=
      iMul P (iMul P hI (int_inv_nat P hp hj)) (iPow P (iNat P _) _)
    have hj0 : (j : E) ≠ 0 := by
      have : j ≠ 0 := fun h => hj (h ▸ dvd_zero _)
      exact_mod_cast this
    have e2 : (((qOf P ^ f * j : ℕ) : E) / (qOf P : E) ^ e) * (j : E)⁻¹ * (qOf P : E) ^ (e - f - 1) =
        (qOf P : E)⁻¹ := by
      obtain ⟨g, rfl⟩ : ∃ g, e = f + g + 1 := ⟨e - f - 1, by omega⟩
      have hg : f + g + 1 - f - 1 = g := by omega
      rw [hg]
      push_cast
      field_simp
      ring
    rw [e2] at h1
    exact not_int_inv_q P hp h1
  · rintro ⟨k, rfl⟩
    have e2 : (((qOf P ^ e * k : ℕ) : E) / (qOf P : E) ^ e) = (k : E) := by
      push_cast
      field_simp
    rw [e2]
    exact iNat P k

open NTA in
/- English proof (translation)
Introduce `E _ _ P hp hq x N hx`. Establish `hq0` using `q_ne P hp`. Proceed by induction on `N with`. Consider the case `zero => exact ⟨0, by simp, by simpa using hx⟩`. Consider the case `succ N ih`.

Take `⟨i, hi, hz⟩` from `ih`. Take `⟨d, hd, hzd⟩` from `approx1 P hp hq hz`. Use `⟨i + d * qOf P ^ N, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `e : (x - ((i + d * qOf P ^ N : ℕ) : E)) / (qOf P : E) ^ (N + 1) = ((x - i) / (qOf P : E) ^ N - d) / (qOf P : E)`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hzd`.
-/
theorem integral_approximation_by_integer : IntegralApproximationByInteger := by
  intro E _ _ P hp hq x N hx
  have hq0 := q_ne P hp
  induction N with
  | zero => exact ⟨0, by simp, by simpa using hx⟩
  | succ N ih =>
    obtain ⟨i, hi, hz⟩ := ih
    obtain ⟨d, hd, hzd⟩ := approx1 P hp hq hz
    refine ⟨i + d * qOf P ^ N, ?_, ?_⟩
    · calc i + d * qOf P ^ N < qOf P ^ N + d * qOf P ^ N := Nat.add_lt_add_right hi _
        _ = (d + 1) * qOf P ^ N := by ring
        _ ≤ qOf P * qOf P ^ N := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hd)
        _ = qOf P ^ (N + 1) := by ring
    · have e : (x - ((i + d * qOf P ^ N : ℕ) : E)) / (qOf P : E) ^ (N + 1) =
          ((x - i) / (qOf P : E) ^ N - d) / (qOf P : E) := by
        push_cast
        field_simp
        ring
      rw [e]
      exact hzd

open NTA in
/- English proof (translation)
Introduce `E _ _ P hp hq a ha`. Establish `hq0` using `q_ne P hp`. Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective (𝓞 E) a`. Establish `hy0 : y ≠ 0` using `nonZeroDivisors.ne_zero hy`. Establish `hx0 : x ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at ha`. Take `⟨k, u, hu, hu0, hui, huii⟩` from `decomp P hp hq hx0`. Take `⟨k', u', hu', hu0', hui', huii'⟩` from `decomp P hp hq hy0`. Use `⟨(k : ℤ) - k', u / u', ?_, div_ne_zero hu0 hu0', ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hu, hu', zpow_sub₀ hq0, zpow_natCast, zpow_natCast]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[div_eq_mul_inv]`. Conclude with `iMul P hui huii'`. Rewrite using `[inv_div, div_eq_mul_inv]`.

Conclude with `iMul P hui' huii`.
-/
theorem element_eq_prime_power_mul_unit : ElementEqPrimePowerMulUnit := by
  intro E _ _ P hp hq a ha
  have hq0 := q_ne P hp
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨k, u, hu, hu0, hui, huii⟩ := decomp P hp hq hx0
  obtain ⟨k', u', hu', hu0', hui', huii'⟩ := decomp P hp hq hy0
  refine ⟨(k : ℤ) - k', u / u', ?_, div_ne_zero hu0 hu0', ?_, ?_⟩
  · rw [hu, hu', zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
    field_simp
  · rw [div_eq_mul_inv]
    exact iMul P hui huii'
  · rw [inv_div, div_eq_mul_inv]
    exact iMul P hui' huii

open NTA in
/- English proof (translation)
Introduce `E _ _ P hp hq e e' w w' hw hwi hwii hw'i hw'ii h`. Establish `hq0` using `q_ne P hp`. Establish `hw' : w' ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[mul_zero]`.

Conclude with `hw ((mul_eq_zero.mp h).resolve_left (zpow_ne_zero _ hq0))`. Break down `lt_trichotomy e e' with hlt | heq | hgt` into its components or cases. It suffices to derive a contradiction. Take `⟨d, hd⟩ : ∃ d : ℕ, e' - e = (d : ℤ) + 1` from `⟨(e' - e - 1).toNat, by omega⟩`. Apply `no_shift P hp d hw hwii hw'i` to reduce the goal to its premises.

Establish `hpw : (qOf P : E) ^ (d + 1) = (qOf P : E) ^ (e' - e)`. Rewrite using `[hd, ← Nat.cast_succ, zpow_natCast]`. Rewrite using `[hpw, zpow_sub₀ hq0, div_mul_eq_mul_div, eq_div_iff (zpow_ne_zero _ hq0)]`. Take the linear combination `h`. Conclude with `heq`.

It suffices to derive a contradiction. Take `⟨d, hd⟩ : ∃ d : ℕ, e - e' = (d : ℤ) + 1` from `⟨(e - e' - 1).toNat, by omega⟩`. Apply `no_shift P hp d hw' hw'ii hwi` to reduce the goal to its premises. Establish `hpw : (qOf P : E) ^ (d + 1) = (qOf P : E) ^ (e - e')`. Rewrite using `[hd, ← Nat.cast_succ, zpow_natCast]`.

Rewrite using `[hpw, zpow_sub₀ hq0, div_mul_eq_mul_div, eq_div_iff (zpow_ne_zero _ hq0)]`. Take the linear combination `-h`.
-/
theorem valuation_exponent_unique : ValuationExponentUnique := by
  intro E _ _ P hp hq e e' w w' hw hwi hwii hw'i hw'ii h
  have hq0 := q_ne P hp
  have hw' : w' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact hw ((mul_eq_zero.mp h).resolve_left (zpow_ne_zero _ hq0))
  rcases lt_trichotomy e e' with hlt | heq | hgt
  · exfalso
    obtain ⟨d, hd⟩ : ∃ d : ℕ, e' - e = (d : ℤ) + 1 := ⟨(e' - e - 1).toNat, by omega⟩
    apply no_shift P hp d hw hwii hw'i
    have hpw : (qOf P : E) ^ (d + 1) = (qOf P : E) ^ (e' - e) := by
      rw [hd, ← Nat.cast_succ, zpow_natCast]
    rw [hpw, zpow_sub₀ hq0, div_mul_eq_mul_div, eq_div_iff (zpow_ne_zero _ hq0)]
    linear_combination h
  · exact heq
  · exfalso
    obtain ⟨d, hd⟩ : ∃ d : ℕ, e - e' = (d : ℤ) + 1 := ⟨(e - e' - 1).toNat, by omega⟩
    apply no_shift P hp d hw' hw'ii hwi
    have hpw : (qOf P : E) ^ (d + 1) = (qOf P : E) ^ (e - e') := by
      rw [hd, ← Nat.cast_succ, zpow_natCast]
    rw [hpw, zpow_sub₀ hq0, div_mul_eq_mul_div, eq_div_iff (zpow_ne_zero _ hq0)]
    linear_combination -h

open NTA in
/- English proof (translation)
Introduce `E _ _ P hp hq w N hw hwi hwii`. Establish `hq0` using `q_ne P hp`. Consider the cases of `N with`. Consider the case `zero => exact ⟨1, Nat.coprime_one_left _, by simpa using iSub P hwi (iNat P 1)⟩`. Consider the case `succ N`.

Take `⟨i, hi, hI⟩` from `integral_approximation_by_integer E P hp hq w (N + 1) hwi`. Use `⟨i, ?_, hI⟩` and prove the remaining obligations. Rewrite using `[Nat.coprime_comm]`. Use `(Nat.Prime.coprime_iff_not_dvd hp).mpr ?_` and prove the remaining obligations. Introduce and unpack `⟨j, rfl⟩`.

Apply `not_int_inv_q P hp` to reduce the goal to its premises. Establish `h1 : IntAt P (w / (qOf P : E))`. Establish `e : w / (qOf P : E) = (w - ((qOf P * j : ℕ) : E)) / (qOf P : E) ^ (N + 1) * (qOf P : E) ^ N + (j : E)`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `iAdd P (iMul P hI (iPow P (iNat P _) N)) (iNat P j)`. Establish `e2 : (qOf P : E)⁻¹ = w / (qOf P : E) * w⁻¹`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e2]`. Conclude with `iMul P h1 hwii`.
-/
theorem unit_congruent_to_integer : UnitCongruentToInteger := by
  intro E _ _ P hp hq w N hw hwi hwii
  have hq0 := q_ne P hp
  cases N with
  | zero => exact ⟨1, Nat.coprime_one_left _, by simpa using iSub P hwi (iNat P 1)⟩
  | succ N =>
    obtain ⟨i, hi, hI⟩ := integral_approximation_by_integer E P hp hq w (N + 1) hwi
    refine ⟨i, ?_, hI⟩
    rw [Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr ?_
    rintro ⟨j, rfl⟩
    apply not_int_inv_q P hp
    have h1 : IntAt P (w / (qOf P : E)) := by
      have e : w / (qOf P : E) = (w - ((qOf P * j : ℕ) : E)) / (qOf P : E) ^ (N + 1) *
          (qOf P : E) ^ N + (j : E) := by
        push_cast
        field_simp
        ring
      rw [e]
      exact iAdd P (iMul P hI (iPow P (iNat P _) N)) (iNat P j)
    have e2 : (qOf P : E)⁻¹ = w / (qOf P : E) * w⁻¹ := by
      field_simp
    rw [e2]
    exact iMul P h1 hwii

end PI.TwistedEisensteinNonvanishing.W
