import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerMore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

/- English proof (translation)
Introduce `x hx`. Rewrite `h` using `[Ideal.height_eq_zero_iff_eq_bot]`. Establish `: Ideal.Quotient.mk P x ∈ Q.map (Ideal.Quotient.mk P)` using `Ideal.mem_map_of_mem _ hx`. Rewrite `this` using `[h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`. Then use the resulting hypothesis.
-/
theorem RegularityDivisorSupportClosed.le_of_height_map_eq_zero {A : Type*} [CommRing A] {P Q : Ideal A} [P.IsPrime]
    (h : (Q.map (Ideal.Quotient.mk P)).height = 0) : Q ≤ P := by
  intro x hx
  rw [Ideal.height_eq_zero_iff_eq_bot] at h
  have : Ideal.Quotient.mk P x ∈ Q.map (Ideal.Quotient.mk P) := Ideal.mem_map_of_mem _ hx
  rwa [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this

/- English proof (translation)
Establish `h' : (m : ℕ∞) + a + b = ((m + 1 : ℕ) : ℕ∞)` using `by exact_mod_cast h`. Proceed by induction on `a using ENat.recTopCoe with`. Consider the case `top => simp at h'; exact ENat.natCast_ne_top (m + 1) (by exact_mod_cast h'.symm)`. Consider the case `coe a`. Proceed by induction on `b using ENat.recTopCoe with`.

Consider the case `top => simp at h'; exact ENat.natCast_ne_top (m + 1) (by exact_mod_cast h'.symm)`. Consider the case `coe b`. Establish `: m + a + b = m + 1` using `by exact_mod_cast h'`. Establish `: a ≠ 0` using `by exact_mod_cast ha`. Establish `: b ≠ 0` using `by exact_mod_cast hb`.

Use linear arithmetic over natural numbers and integers.
-/
theorem RegularityDivisorSupportClosed.not_add_add {m : ℕ} {a b : ℕ∞} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ((m : WithBot ℕ∞) + (a : WithBot ℕ∞)) + (b : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞)) :
    False := by
  have h' : (m : ℕ∞) + a + b = ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
  induction a using ENat.recTopCoe with
  | top => simp at h'; exact ENat.natCast_ne_top (m + 1) (by exact_mod_cast h'.symm)
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp at h'; exact ENat.natCast_ne_top (m + 1) (by exact_mod_cast h'.symm)
    | coe b =>
      have : m + a + b = m + 1 := by exact_mod_cast h'
      have : a ≠ 0 := by exact_mod_cast ha
      have : b ≠ 0 := by exact_mod_cast hb
      omega

/- English proof (translation)
Introduce `K _ ι _ P s a W hP hs hsP`. Take `⟨-, ⟨hPp, hPh, -⟩, -, hPdim⟩` from `hP`. Use `hPp` as an intermediate fact. Establish `hsW' : ∀ {Q : Ideal (MRing ι)}, P ⊔ Ideal.span {s} ≤ Q → s ∈ Q` using `fun h => h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hWmin, hWrel⟩`. Establish `h1` using `dim_quot_minimal_add_one P W s hsP hWmin`. Rewrite `h1` using `[hPdim]`. Use `⟨⟨⟨hWmin.1.1, isMultiHomogIdeal_of_mem_minimalPrimes hPh hs hWmin, hWrel⟩, withBot_eq_of_add_one (by rw [h1, Nat.add_comm])⟩, le_sup_left.trans hWmin.1.2, hsW' hWmin.1.2⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨⟨hWp, -, hWrel⟩, hWdim⟩, hPW, hsW⟩`.

Establish `hle : P ⊔ Ideal.span {s} ≤ W` using `sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)`. Use `⟨⟨⟨hWp, hle⟩, fun Q hQ hQW => ?_⟩, hWrel⟩` and prove the remaining obligations. Use `hQ.1` as an intermediate fact. Establish `hPQ : P ≤ Q` using `le_sup_left.trans hQ.2`. Establish `e1` using `mvPolynomialInt_dimFormula P Q hPQ`.

Establish `e2` using `mvPolynomialInt_dimFormula Q W hQW`. Rewrite `e1` using `[hPdim]`. Rewrite `e2` using `[hWdim]`. Assume the negation of the conclusion as `hWQ`. Establish `ha : (W.map (Ideal.Quotient.mk Q)).height ≠ 0` using `fun h0 => hWQ (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0)`.

Establish `hb : (Q.map (Ideal.Quotient.mk P)).height ≠ 0` using `fun h0 => hsP (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0 (hsW' hQ.2))`. Rewrite `e1` using `[← e2]`. Conclude with `RegularityDivisorSupportClosed.not_add_add ha hb (by rw [e1, Nat.add_comm])`.
-/
theorem RegularityDivisorSupportClosed.proof : RegularityDivisorSupportClosed.Statement := by
  intro K _ ι _ P s a W hP hs hsP
  obtain ⟨-, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  have := hPp
  have hsW' : ∀ {Q : Ideal (MRing ι)}, P ⊔ Ideal.span {s} ≤ Q → s ∈ Q := fun h =>
    h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  constructor
  · rintro ⟨hWmin, hWrel⟩
    have h1 := dim_quot_minimal_add_one P W s hsP hWmin
    rw [hPdim] at h1
    refine ⟨⟨⟨hWmin.1.1, isMultiHomogIdeal_of_mem_minimalPrimes hPh hs hWmin, hWrel⟩,
      withBot_eq_of_add_one (by rw [h1, Nat.add_comm])⟩, le_sup_left.trans hWmin.1.2, hsW' hWmin.1.2⟩
  · rintro ⟨⟨⟨hWp, -, hWrel⟩, hWdim⟩, hPW, hsW⟩
    have hle : P ⊔ Ideal.span {s} ≤ W := sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)
    refine ⟨⟨⟨hWp, hle⟩, fun Q hQ hQW => ?_⟩, hWrel⟩
    have := hQ.1
    have hPQ : P ≤ Q := le_sup_left.trans hQ.2
    have e1 := mvPolynomialInt_dimFormula P Q hPQ
    have e2 := mvPolynomialInt_dimFormula Q W hQW
    rw [hPdim] at e1
    rw [hWdim] at e2
    by_contra hWQ
    have ha : (W.map (Ideal.Quotient.mk Q)).height ≠ 0 := fun h0 =>
      hWQ (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0)
    have hb : (Q.map (Ideal.Quotient.mk P)).height ≠ 0 := fun h0 =>
      hsP (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0 (hsW' hQ.2))
    rw [← e2] at e1
    exact RegularityDivisorSupportClosed.not_add_add ha hb (by rw [e1, Nat.add_comm])

end

end GroundTheory.Heights₂.Heights.Inter
