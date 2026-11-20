import Mathlib
import Formalism.PairingDivisors.StatementA
import Formalism.PairingDivisors.StatementN
import Formalism.PairingDivisors.PairingDivisorProofs.Height

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)

namespace Formalism.PairingDivisionLocalBalance

section Val

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem vw_ringOfIntegers_eq_count_factors_span (w : Pl K) (x : 𝓞 K) (hx : x ≠ 0) :
    vw w (x : K) = ((Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {x})).factors : ℤ) := by
  unfold Formalism.DivisionValues.vw
  rw [show (x : K) = algebraMap (𝓞 K) K x from rfl, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe]
  simpa using hx

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem intValuation_eq_exp (w : Pl K) (x : 𝓞 K) (hx : x ≠ 0) :
    w.intValuation x = WithZero.exp (-(vw w (x : K))) := by
  rw [vw_ringOfIntegers_eq_count_factors_span w x hx]
  first
  | exact w.intValuation_if_neg hx
  | (rw [w.intValuation_if_neg hx])
  | (rw [IsDedekindDomain.HeightOneSpectrum.intValuation_def, if_neg hx])

/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
private theorem le_of_withZero_exp_le_exp {a b : ℤ} (h : WithZero.exp a ≤ WithZero.exp b) : a ≤ b := by
  first
  | exact WithZero.exp_le_exp.mp h
  | simpa [WithZero.exp] using h

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem vw_add_int (w : Pl K) (x y : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (vw w (x : K)) (vw w (y : K)) ≤ vw w ((x + y : 𝓞 K) : K) := by
  have h := w.intValuation.map_add x y
  rw [intValuation_eq_exp w x hx, intValuation_eq_exp w y hy,
    intValuation_eq_exp w (x + y) hxy] at h
  rcases le_max_iff.mp h with h1 | h1
  · have h2 := le_of_withZero_exp_le_exp h1
    exact min_le_of_left_le (by omega)
  · have h2 := le_of_withZero_exp_le_exp h1
    exact min_le_of_right_le (by omega)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
private theorem vw_mul_lemma (w : Pl K) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a * b) = vw w a + vw w b := by
  unfold Formalism.DivisionValues.vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul]
  · exact fun h => ha (FractionalIdeal.spanSingleton_eq_zero_iff.mp h)
  · exact fun h => hb (FractionalIdeal.spanSingleton_eq_zero_iff.mp h)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
private theorem vw_div_eq_sub_of_ne_zero (w : Pl K) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a / b) = vw w a - vw w b := by
  have h1 := vw_mul_lemma w (a / b) b (div_ne_zero ha hb) hb
  rw [div_mul_cancel₀ a hb] at h1
  omega

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem min_vw_le_vw_add_of_ne_zero (w : Pl K) (x y : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) :
    min (vw w (algebraMap (𝓞 K) K x)) (vw w (algebraMap (𝓞 K) K y)) ≤
      vw w (algebraMap (𝓞 K) K (x + y)) :=
  vw_add_int w x y hx hy hxy

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem vw_add (w : Pl K) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    min (vw w a) (vw w b) ≤ vw w (a + b) := by
  obtain ⟨x, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  obtain ⟨y, e, he, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) b
  have hd0 : algebraMap (𝓞 K) K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have he0 : algebraMap (𝓞 K) K e ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors he
  have hde : algebraMap (𝓞 K) K (d * e) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero hd0 he0
  have h1 : algebraMap (𝓞 K) K x / algebraMap (𝓞 K) K d =
      algebraMap (𝓞 K) K (x * e) / algebraMap (𝓞 K) K (d * e) := by
    rw [div_eq_div_iff hd0 hde, map_mul, map_mul]; ring
  have h2 : algebraMap (𝓞 K) K y / algebraMap (𝓞 K) K e =
      algebraMap (𝓞 K) K (y * d) / algebraMap (𝓞 K) K (d * e) := by
    rw [div_eq_div_iff he0 hde, map_mul, map_mul]; ring
  rw [h1] at ha hab ⊢
  rw [h2] at hb hab ⊢
  rw [← add_div, ← map_add (algebraMap (𝓞 K) K)] at hab ⊢
  have nz : ∀ z : 𝓞 K, z ≠ 0 → algebraMap (𝓞 K) K z ≠ 0 := fun z hz h =>
    hz ((IsFractionRing.injective (𝓞 K) K) (by rw [h, map_zero]))
  have hxe : x * e ≠ 0 := fun h => ha (by rw [h, map_zero, zero_div])
  have hyd : y * d ≠ 0 := fun h => hb (by rw [h, map_zero, zero_div])
  have hs : x * e + y * d ≠ 0 := fun h => hab (by rw [h, map_zero, zero_div])
  rw [vw_div_eq_sub_of_ne_zero w _ _ (nz _ hxe) hde, vw_div_eq_sub_of_ne_zero w _ _ (nz _ hyd) hde,
    vw_div_eq_sub_of_ne_zero w _ _ (nz _ hs) hde, min_sub_sub_right]
  exact sub_le_sub_right (min_vw_le_vw_add_of_ne_zero w _ _ hxe hyd hs) _

def GeV (w : Pl K) (c : ℝ) (x : K) : Prop := x = 0 ∨ c ≤ (vw w x : ℝ)

/- English proof (translation)
Replace the relevant objects with their definitions. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Prove the second alternative. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Prove the second alternative. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Prove the second alternative. Consider separately whether the proposition holds or fails. Prove the first alternative. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem GeV.add {w : Pl K} {c : ℝ} {x y : K} (hx : GeV w c x) (hy : GeV w c y) :
    GeV w c (x + y) := by
  unfold GeV at *
  rcases hx with hx | hx
  · rw [hx, zero_add]; exact hy
  rcases hy with hy | hy
  · rw [hy, add_zero]; exact Or.inr hx
  by_cases hx0 : x = 0
  · rw [hx0, zero_add]; exact Or.inr hy
  by_cases hy0 : y = 0
  · rw [hy0, add_zero]; exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  right
  have h := vw_add w x y hx0 hy0 hxy
  have h2 : min (vw w x : ℝ) (vw w y : ℝ) ≤ (vw w (x + y) : ℝ) := by exact_mod_cast h
  exact le_trans (le_min hx hy) h2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GeV.sum {w : Pl K} {c : ℝ} {ι : Type} (s : Finset ι) (f : ι → K)
    (h : ∀ i ∈ s, GeV w c (f i)) : GeV w c (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f (GeV w c) (fun a b ha hb => GeV.add ha hb) (Or.inl rfl) h

/- English proof (translation)
Replace the relevant objects with their definitions. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem GeV.mul {w : Pl K} {c c' : ℝ} {x y : K} (hx : GeV w c x) (hy : GeV w c' y) :
    GeV w (c + c') (x * y) := by
  unfold GeV at *
  rcases hx with hx | hx
  · left; rw [hx, zero_mul]
  rcases hy with hy | hy
  · left; rw [hy, mul_zero]
  by_cases hx0 : x = 0
  · left; rw [hx0, zero_mul]
  by_cases hy0 : y = 0
  · left; rw [hy0, mul_zero]
  right
  rw [vw_mul_lemma w x y hx0 hy0]
  push_cast
  linarith

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem GeV.mul0 {w : Pl K} {x y : K} (hx : GeV w 0 x) (hy : GeV w 0 y) : GeV w 0 (x * y) := by
  have h := GeV.mul hx hy
  rwa [add_zero] at h

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem GeV.of_eq_zero {w : Pl K} {x : K} (h : vw w x = 0) : GeV w 0 x := by
  unfold GeV
  right
  rw [h]
  simp

/- English proof (translation)
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. Check the signs of the components of the expression. A detailed English derivation is pending.
-/
theorem GeV.int (w : Pl K) (x : 𝓞 K) : GeV w 0 (x : K) := by
  unfold GeV
  by_cases hx : x = 0
  · left
    rw [hx]
    first
    | rfl
    | simp
    | exact map_zero (algebraMap (𝓞 K) K)
  right
  rw [vw_ringOfIntegers_eq_count_factors_span w x hx]
  positivity

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem GeV.one (w : Pl K) : GeV w 0 (1 : K) := by
  apply GeV.of_eq_zero
  have h0 := vw_pow w (1 : K) one_ne_zero 0
  simpa using h0

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Move the embeddings inside the algebraic operations. Use linear arithmetic over natural numbers and integers.
-/
theorem GeV.negOne (w : Pl K) : GeV w 0 (-1 : K) := by
  apply GeV.of_eq_zero
  have h1 := vw_pow w (-1 : K) (neg_ne_zero.mpr one_ne_zero) 2
  have h0 := vw_pow w (1 : K) one_ne_zero 0
  simp at h0
  rw [neg_one_sq, h0] at h1
  push_cast at h1
  omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GeV.sub {w : Pl K} {x y : K} (hx : GeV w 0 x) (hy : GeV w 0 y) : GeV w 0 (x - y) := by
  rw [sub_eq_add_neg, neg_eq_neg_one_mul]
  exact GeV.add hx (GeV.mul0 (GeV.negOne w) hy)

end Val

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem valuation_add : ValAdd := by
  unfold ValAdd
  intro K _ _ _ w a b ha hb hab
  exact vw_add w a b ha hb hab

end Formalism.PairingDivisionLocalBalance
