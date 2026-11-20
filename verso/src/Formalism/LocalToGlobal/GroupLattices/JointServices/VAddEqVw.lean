import Formalism.LocalRingCardinality.DataArith
import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.NormaliserValuationBound

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions (vAdd)
open Formalism.DivisionValues (vw)

noncomputable section

namespace Formalism.L2.G.ServJoint

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem vAdd_mul_of_ne_zero (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold Formalism.BasicNotions.vAdd
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hx) ((Valuation.ne_zero_iff _).mpr hy)]
  ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem vw_mul_of_ne_zero (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    Formalism.DivisionValues.vw w (x * y) = Formalism.DivisionValues.vw w x + Formalism.DivisionValues.vw w y := by
  have hx' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hx
  have hy' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hy
  unfold Formalism.DivisionValues.vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K w hx' hy']

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem vAdd_algebraMap_eq_vw_of_ne_zero (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0) :
    vAdd w (algebraMap (𝓞 K) K a) = Formalism.DivisionValues.vw w (algebraMap (𝓞 K) K a) := by
  have hI : (Ideal.span {a} : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha
  unfold Formalism.BasicNotions.vAdd Formalism.DivisionValues.vw
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ ha, WithZero.log_exp,
    neg_neg, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w hI]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem vAdd_eq_vw (w : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) : vAdd w x = vw w x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h; apply hx; rw [h, zero_div]
  have ha0 : a ≠ 0 := by
    rintro rfl; exact haK (map_zero _)
  have hq : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K b = algebraMap (𝓞 K) K a :=
    div_mul_cancel₀ _ hbK
  have h1 := vAdd_mul_of_ne_zero w hx hbK
  have h2 := vw_mul_of_ne_zero w hx hbK
  rw [hq] at h1 h2
  have e1 := vAdd_algebraMap_eq_vw_of_ne_zero w a ha0
  have e2 := vAdd_algebraMap_eq_vw_of_ne_zero w b hb0
  linarith

def VGeq (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) (z : K) : Prop := z = 0 ∨ s ≤ (vAdd w z : ℝ)

/- English proof (translation)
Prove the first alternative.
-/
theorem VGeq.zero (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) : VGeq w s (0 : K) := Or.inl rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem VGeq.mono {w : HeightOneSpectrum (𝓞 K)} {s s' : ℝ} {z : K} (h : VGeq w s z) (hs : s' ≤ s) : VGeq w s' z :=
  h.imp id (fun h' => hs.trans h')

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Replace the relevant objects with their definitions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem vAdd_le_of_valuation_le {w : HeightOneSpectrum (𝓞 K)} {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : w.valuation K y ≤ w.valuation K x) : vAdd w x ≤ vAdd w y := by
  have hx' : w.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hy' : w.valuation K y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  have h' : WithZero.exp (WithZero.log (w.valuation K y)) ≤ WithZero.exp (WithZero.log (w.valuation K x)) := by
    rwa [WithZero.exp_log hx', WithZero.exp_log hy']
  have h'' := WithZero.exp_le_exp.mp h'
  unfold Formalism.BasicNotions.vAdd
  linarith

/- English proof (translation)
Consider separately whether the proposition holds or fails. Simplify to obtain the desired conclusion from the available facts. Consider separately whether the proposition holds or fails. Simplify to obtain the desired conclusion from the available facts. Consider separately whether the proposition holds or fails.

Prove the first alternative. Separate the alternatives or extract the components of the hypothesis. Separate the alternatives or extract the components of the hypothesis. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem VGeq.add {w : HeightOneSpectrum (𝓞 K)} {s : ℝ} {a b : K} (ha : VGeq w s a) (hb : VGeq w s b) :
    VGeq w s (a + b) := by
  by_cases ha0 : a = 0
  · simpa [ha0] using hb
  by_cases hb0 : b = 0
  · simpa [hb0] using ha
  by_cases hab : a + b = 0
  · exact Or.inl hab
  rcases ha with h | ha
  · exact absurd h ha0
  rcases hb with h | hb
  · exact absurd h hb0
  right
  rcases le_max_iff.mp ((w.valuation K).map_add a b) with h | h
  · exact ha.trans (by exact_mod_cast vAdd_le_of_valuation_le ha0 hab h)
  · exact hb.trans (by exact_mod_cast vAdd_le_of_valuation_le hb0 hab h)

/- English proof (translation)
Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem VGeq.int_mul {w : HeightOneSpectrum (𝓞 K)} {s : ℝ} {a : K} (c : 𝓞 K) (ha : VGeq w s a) :
    VGeq w s ((c : K) * a) := by
  by_cases ha0 : a = 0
  · left; simp [ha0]
  by_cases hc : (c : K) = 0
  · left; simp [hc]
  rcases ha with h | ha
  · exact absurd h ha0
  right
  have hca : (c : K) * a ≠ 0 := mul_ne_zero hc ha0
  have hv : w.valuation K ((c : K) * a) ≤ w.valuation K a := by
    rw [map_mul]
    exact mul_le_of_le_one_left' (HeightOneSpectrum.valuation_le_one w c)
  exact ha.trans (by exact_mod_cast vAdd_le_of_valuation_le ha0 hca hv)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem VGeq.sum {w : HeightOneSpectrum (𝓞 K)} {s : ℝ} {ι : Type*} (S : Finset ι) (f : ι → K)
    (h : ∀ i ∈ S, VGeq w s (f i)) : VGeq w s (∑ i ∈ S, f i) := by
  exact Finset.sum_induction f (VGeq w s) (fun a b ha hb => ha.add hb) (VGeq.zero w s) h

/- English proof (translation)
Consider separately whether the proposition holds or fails. Prove the first alternative. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem VGeq.vw {w : HeightOneSpectrum (𝓞 K)} {s : ℝ} {z : K} (h : VGeq w s z) : z = 0 ∨ s ≤ (Formalism.DivisionValues.vw w z : ℝ) := by
  by_cases hz : z = 0
  · exact Or.inl hz
  rcases h with h | h
  · exact Or.inl h
  right
  rw [← vAdd_eq_vw w z hz]
  exact h

end Formalism.L2.G.ServJoint

end
