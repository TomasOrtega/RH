import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.Development

noncomputable section

namespace PI.DefPosDefWork

open Matrix ComplexOrder

/- English proof (translation)
Establish `key : ∀ q : ℚ, z + (q : ℂ) ≠ 0 → (w.re + q) * z.im + w.im * (z.re + q) = 0 ∧ 0 < (w.re + q) * (z.re + q) - w.im * z.im`. Introduce `q hq`. Take `⟨c, hc, he⟩` from `h q hq`. Establish `him` using `congrArg Complex.im he`. Establish `hre` using `congrArg Complex.re he`.

Simplify using `only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.ratCast_re, Complex.ratCast_im, add_zero] at him hre`. Prove the components needed by the constructor for the conclusion. Take the linear combination `him`. Establish `hc' : (w.re + q) * (z.re + q) - w.im * z.im = c` using `by linear_combination hre`. Rewrite using `[hc']`.

Conclude with `hc`. Rewrite using `[Complex.ext_iff, Complex.conj_re, Complex.conj_im]`. Distinguish the cases in `hd : z.im = 0`. Establish `hne : ∀ q : ℚ, z.re + q ≠ 0 → z + (q : ℂ) ≠ 0` using `fun q hq h0 => hq (by simpa using congrArg Complex.re h0)`. Choose the witnesses or unpack the hypotheses as in `⟨q0, hq0⟩ : ∃ q : ℚ, z.re + q ≠ 0 := by`.

Distinguish the cases in `h0 : z.re = 0`. Conclude with `⟨1, by rw [h0]; norm_num⟩`. Conclude with `⟨0, by simpa using h0⟩`. Establish `k` using `key q0 (hne q0 hq0)`. Establish `e4 : w.im * (z.re + q0) = 0` using `by linear_combination k.1 - (w.re + (q0 : ℝ)) * hd`.

Establish `him : w.im = 0` using `(mul_eq_zero.mp e4).resolve_right hq0`. Establish `ere : w.re = z.re`. Assume the negation of the conclusion as `hne'`. Break down `lt_or_gt_of_ne hne' with hlt | hlt` into its components or cases. Take `⟨q, hq1, hq2⟩` from `exists_rat_btwn (neg_lt_neg hlt)`.

Establish `hA : w.re + q < 0` using `by linarith`. Establish `hB : 0 < z.re + q` using `by linarith`. Establish `k2` using `(key q (hne q hB.ne')).2`. Rewrite `k2` using `[him, zero_mul, sub_zero]`. Combine the linear relations using `[mul_neg_of_neg_of_pos hA hB]`.

Take `⟨q, hq1, hq2⟩` from `exists_rat_btwn (neg_lt_neg hlt)`. Establish `hA : 0 < w.re + q` using `by linarith`. Establish `hB : z.re + q < 0` using `by linarith`. Establish `k2` using `(key q (hne q hB.ne)).2`. Rewrite `k2` using `[him, zero_mul, sub_zero]`.

Combine the linear relations using `[mul_neg_of_pos_of_neg hA hB]`. Conclude with `⟨ere, by rw [him, hd, neg_zero]⟩`. Establish `hne : ∀ q : ℚ, z + (q : ℂ) ≠ 0` using `fun q h0 => hd (by simpa using congrArg Complex.im h0)`. Establish `k0` using `key 0 (hne 0)`. Establish `k1` using `key 1 (hne 1)`.

Move the coercions through the operations in `at k0 k1`. Establish `e1 : w.im = -z.im` using `by linear_combination k1.1 - k0.1`. Establish `e2 : z.im * (w.re - z.re) = 0` using `by linear_combination k0.1 - z.re * e1`. Establish `e3 : w.re = z.re`. Break down `mul_eq_zero.mp e2 with h0 | h0` into its components or cases.

Conclude with `absurd h0 hd`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨e3, e1⟩`.
-/
theorem conj_of_pos (w z : ℂ)
    (h : ∀ q : ℚ, z + (q : ℂ) ≠ 0 → ∃ c : ℝ, 0 < c ∧ (w + (q : ℂ)) * (z + (q : ℂ)) = (c : ℂ)) :
    w = (starRingEnd ℂ) z := by
  have key : ∀ q : ℚ, z + (q : ℂ) ≠ 0 →
      (w.re + q) * z.im + w.im * (z.re + q) = 0 ∧ 0 < (w.re + q) * (z.re + q) - w.im * z.im := by
    intro q hq
    obtain ⟨c, hc, he⟩ := h q hq
    have him := congrArg Complex.im he
    have hre := congrArg Complex.re he
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ratCast_re, Complex.ratCast_im, add_zero] at him hre
    constructor
    · linear_combination him
    · have hc' : (w.re + q) * (z.re + q) - w.im * z.im = c := by linear_combination hre
      rw [hc']
      exact hc
  rw [Complex.ext_iff, Complex.conj_re, Complex.conj_im]
  by_cases hd : z.im = 0
  · have hne : ∀ q : ℚ, z.re + q ≠ 0 → z + (q : ℂ) ≠ 0 := fun q hq h0 =>
      hq (by simpa using congrArg Complex.re h0)
    obtain ⟨q0, hq0⟩ : ∃ q : ℚ, z.re + q ≠ 0 := by
      by_cases h0 : z.re = 0
      · exact ⟨1, by rw [h0]; norm_num⟩
      · exact ⟨0, by simpa using h0⟩
    have k := key q0 (hne q0 hq0)
    have e4 : w.im * (z.re + q0) = 0 := by linear_combination k.1 - (w.re + (q0 : ℝ)) * hd
    have him : w.im = 0 := (mul_eq_zero.mp e4).resolve_right hq0
    have ere : w.re = z.re := by
      by_contra hne'
      rcases lt_or_gt_of_ne hne' with hlt | hlt
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (neg_lt_neg hlt)
        have hA : w.re + q < 0 := by linarith
        have hB : 0 < z.re + q := by linarith
        have k2 := (key q (hne q hB.ne')).2
        rw [him, zero_mul, sub_zero] at k2
        linarith [mul_neg_of_neg_of_pos hA hB]
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (neg_lt_neg hlt)
        have hA : 0 < w.re + q := by linarith
        have hB : z.re + q < 0 := by linarith
        have k2 := (key q (hne q hB.ne)).2
        rw [him, zero_mul, sub_zero] at k2
        linarith [mul_neg_of_pos_of_neg hA hB]
    exact ⟨ere, by rw [him, hd, neg_zero]⟩
  · have hne : ∀ q : ℚ, z + (q : ℂ) ≠ 0 := fun q h0 => hd (by simpa using congrArg Complex.im h0)
    have k0 := key 0 (hne 0)
    have k1 := key 1 (hne 1)
    push_cast at k0 k1
    have e1 : w.im = -z.im := by linear_combination k1.1 - k0.1
    have e2 : z.im * (w.re - z.re) = 0 := by linear_combination k0.1 - z.re * e1
    have e3 : w.re = z.re := by
      rcases mul_eq_zero.mp e2 with h0 | h0
      · exact absurd h0 hd
      · linarith
    exact ⟨e3, e1⟩

/- English proof (translation)
Unfold `PI.hform`. Simplify using `[Pi.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_assoc, mul_comm, mul_left_comm]`. Rewrite using `[Finset.sum_eq_single i0]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[hb]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i0) h`.
-/
theorem hform_single {E : Type} [CommRing E] (σ : E →+* E) {k : ℕ} (J : Matrix (Fin k) (Fin k) E)
    (i0 : Fin k) (s : E) :
    hform σ J (Pi.single i0 s) (Pi.single i0 s) = σ s * J i0 i0 * s := by
  unfold PI.hform
  simp [Pi.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_assoc, mul_comm, mul_left_comm]
  rw [Finset.sum_eq_single i0]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i0) h

/- English proof (translation)
Take `⟨i0⟩ : Nonempty (Fin k)` from `⟨⟨0, hk⟩⟩`. Establish `hx1 : (Pi.single i0 s : Fin k → E) ≠ 0` using `fun h0 => hs (by simpa using congrFun h0 i0)`. Establish `hx2 : (Pi.single i0 (1 : E) : Fin k → E) ≠ 0` using `fun h0 => by`. Simplify using `using congrFun h0 i0`. Establish `hv1 : hform (σ : E →+* E) J (Pi.single i0 s) (Pi.single i0 s) = σ s * J i0 i0 * s` using `hform_single (σ : E →+* E) J i0 s`.

Establish `hv2 : hform (σ : E →+* E) J (Pi.single i0 1) (Pi.single i0 1) = J i0 i0`. Rewrite using `[hform_single]`. Simplify using the standard rewrite rules. Establish `key : ∀ a b : F, algebraMap F E a = σ s * J i0 i0 * s → algebraMap F E b = J i0 i0 → 0 < r a * r b → ∃ c : ℝ, 0 < c ∧ φ (σ s) * φ s = c`. Introduce `a b ha hb hab`.

Establish `hb0 : r b ≠ 0`. Introduce `h0`. Rewrite `hab` using `[h0, mul_zero]`. Conclude with `lt_irrefl _ hab`. Use `⟨r a / r b, ?_, ?_⟩` and prove the remaining obligations.

Break down `lt_or_gt_of_ne hb0 with h | h` into its components or cases. Conclude with `div_pos_of_neg_of_neg (by nlinarith) h`. Conclude with `div_pos (by nlinarith) h`. Establish `e1 : (r a : ℂ) = φ (σ s) * (r b : ℂ) * φ s`. Rewrite using `[← hr a, ← hr b, ha, hb, map_mul, map_mul]`.

Establish `hb0' : (r b : ℂ) ≠ 0` using `by exact_mod_cast hb0`. Rewrite using `[Complex.ofReal_div, e1, eq_div_iff hb0']`. Expand and normalize the polynomial expressions, which then agree. Break down `hD r with hpos | hneg` into its components or cases. Take `⟨a, ha, ha0⟩` from `hpos _ hx1`.

Take `⟨b, hb, hb0⟩` from `hpos _ hx2`. Conclude with `key a b (ha.trans hv1) (hb.trans hv2) (mul_pos ha0 hb0)`. Take `⟨a, ha, ha0⟩` from `hneg _ hx1`. Take `⟨b, hb, hb0⟩` from `hneg _ hx2`. Conclude with `key a b (ha.trans hv1) (hb.trans hv2) (mul_pos_of_neg_of_neg ha0 hb0)`.
-/
theorem pos_pair {F E : Type} [Field F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {k : ℕ} (J : Matrix (Fin k) (Fin k) E) (hk : 0 < k) (hD : IsDef σ J)
    (φ : E →+* ℂ) (r : F →+* ℝ) (hr : ∀ a, φ (algebraMap F E a) = (r a : ℂ))
    (s : E) (hs : s ≠ 0) : ∃ c : ℝ, 0 < c ∧ φ (σ s) * φ s = (c : ℂ) := by
  obtain ⟨i0⟩ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hx1 : (Pi.single i0 s : Fin k → E) ≠ 0 := fun h0 => hs (by simpa using congrFun h0 i0)
  have hx2 : (Pi.single i0 (1 : E) : Fin k → E) ≠ 0 := fun h0 => by
    simpa using congrFun h0 i0
  have hv1 : hform (σ : E →+* E) J (Pi.single i0 s) (Pi.single i0 s) = σ s * J i0 i0 * s :=
    hform_single (σ : E →+* E) J i0 s
  have hv2 : hform (σ : E →+* E) J (Pi.single i0 1) (Pi.single i0 1) = J i0 i0 := by
    rw [hform_single]
    simp
  have key : ∀ a b : F, algebraMap F E a = σ s * J i0 i0 * s → algebraMap F E b = J i0 i0 →
      0 < r a * r b → ∃ c : ℝ, 0 < c ∧ φ (σ s) * φ s = c := by
    intro a b ha hb hab
    have hb0 : r b ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hab
      exact lt_irrefl _ hab
    refine ⟨r a / r b, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hb0 with h | h
      · exact div_pos_of_neg_of_neg (by nlinarith) h
      · exact div_pos (by nlinarith) h
    · have e1 : (r a : ℂ) = φ (σ s) * (r b : ℂ) * φ s := by
        rw [← hr a, ← hr b, ha, hb, map_mul, map_mul]
      have hb0' : (r b : ℂ) ≠ 0 := by exact_mod_cast hb0
      rw [Complex.ofReal_div, e1, eq_div_iff hb0']
      ring
  rcases hD r with hpos | hneg
  · obtain ⟨a, ha, ha0⟩ := hpos _ hx1
    obtain ⟨b, hb, hb0⟩ := hpos _ hx2
    exact key a b (ha.trans hv1) (hb.trans hv2) (mul_pos ha0 hb0)
  · obtain ⟨a, ha, ha0⟩ := hneg _ hx1
    obtain ⟨b, hb, hb0⟩ := hneg _ hx2
    exact key a b (ha.trans hv1) (hb.trans hv2) (mul_pos_of_neg_of_neg ha0 hb0)

/- English proof (translation)
Introduce `F E _ _ _ _ _ hreal σ k J hk _ hD φ x`. Take `⟨r, hr⟩` from `hreal (φ.comp (algebraMap F E))`. Apply `conj_of_pos` to reduce the goal to its premises. Introduce `q hq`. Establish `hs : x + (q : E) ≠ 0`.

Introduce `h0`. Apply `hq` to reduce the goal to its premises. Rewrite using `[← map_ratCast φ q, ← map_add, h0, map_zero]`. Take `⟨c, hc, he⟩` from `pos_pair σ J hk hD φ r (fun a => hr a) (x + q) hs`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations.

Rewrite using `[← he]`. Simplify using `only [map_add, map_ratCast]`.
-/
theorem splitting_of_extension : Step1 := by
  intro F E _ _ _ _ _ hreal σ k J hk _ hD φ x
  obtain ⟨r, hr⟩ := hreal (φ.comp (algebraMap F E))
  apply conj_of_pos
  intro q hq
  have hs : x + (q : E) ≠ 0 := by
    intro h0
    apply hq
    rw [← map_ratCast φ q, ← map_add, h0, map_zero]
  obtain ⟨c, hc, he⟩ := pos_pair σ J hk hD φ r (fun a => hr a) (x + q) hs
  refine ⟨c, hc, ?_⟩
  rw [← he]
  simp only [map_add, map_ratCast]

end PI.DefPosDefWork
