import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.ThetaRunParameters

/- English proof (translation)
Take `⟨q, hq⟩` from `exists_nat_gt (1 + |c₁| + 2 * |c₂| + B * (33 + d + |C|))`. Establish `h1` using `abs_nonneg c₁`. Establish `h2` using `abs_nonneg c₂`. Establish `h3` using `abs_nonneg C`. Establish `h1'` using `le_abs_self c₁`.

Establish `h2'` using `le_abs_self c₂`. Establish `h3'` using `le_abs_self C`. Establish `h4 : 0 ≤ B * (33 + d + |C|)` using `by positivity`. Establish `hq1 : (1 : ℝ) ≤ q` using `by linarith`. Establish `hK : 33 + d + |C| ≤ (q : ℝ) / B`.

Rewrite using `[le_div_iff₀ hB]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog : Real.log q ≤ q - 1` using `Real.log_le_sub_one_of_pos (by linarith)`. Establish `hm : (q : ℝ) * (33 + d + |C|) ≤ q * ((q : ℝ) / B)` using `mul_le_mul_of_nonneg_left hK (by linarith)`. Establish `hqd : d ≤ q * d` using `le_mul_of_one_le_left hd hq1`.

Establish `hqC : |C| ≤ q * |C|` using `le_mul_of_one_le_left h3 hq1`. Use `⟨q, by exact_mod_cast hq1, by linarith, by linarith, by linarith, ?_, ?_⟩` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_large_nat (B c₁ c₂ d C : ℝ) (hB : 0 < B) (hd : 0 ≤ d) :
    ∃ q : ℕ, 1 ≤ q ∧ c₁ < q ∧ c₂ ≤ (q : ℝ) / 2 ∧ 1 ≤ (q : ℝ) / B ∧
      4 * (7 + Real.log q) + d + 1 ≤ q * ((q : ℝ) / B) ∧ C ≤ q * ((q : ℝ) / B) := by
  obtain ⟨q, hq⟩ := exists_nat_gt (1 + |c₁| + 2 * |c₂| + B * (33 + d + |C|))
  have h1 := abs_nonneg c₁
  have h2 := abs_nonneg c₂
  have h3 := abs_nonneg C
  have h1' := le_abs_self c₁
  have h2' := le_abs_self c₂
  have h3' := le_abs_self C
  have h4 : 0 ≤ B * (33 + d + |C|) := by positivity
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hK : 33 + d + |C| ≤ (q : ℝ) / B := by
    rw [le_div_iff₀ hB]; linarith
  have hlog : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hm : (q : ℝ) * (33 + d + |C|) ≤ q * ((q : ℝ) / B) :=
    mul_le_mul_of_nonneg_left hK (by linarith)
  have hqd : d ≤ q * d := le_mul_of_one_le_left hd hq1
  have hqC : |C| ≤ q * |C| := le_mul_of_one_le_left h3 hq1
  refine ⟨q, by exact_mod_cast hq1, by linarith, by linarith, by linarith, ?_, ?_⟩
  · nlinarith
  · nlinarith

/- English proof (translation)
Introduce `E _ _ _ r m hfr hm1 hmf hfrd hf2 hrd`. Establish `hf : 0 < PT.f E`. Break down `Nat.eq_zero_or_pos (PT.f E) with h | h` into its components or cases. Rewrite `hfr` using `[h]`. Use linear arithmetic over natural numbers and integers.

Conclude with `h`. Establish `hfR : (0 : ℝ) < PT.f E` using `by exact_mod_cast hf`. Establish `hrd0 : 0 < PT.rd E` using `by linarith`. Establish `hRR : 0 < RR (E` using `E) := by unfold RR; positivity`. Use `set S : ℝ := 270 + 90 * (((PT.f E * r : ℕ) : ℝ) + 1) with hS`.

Establish `hS0 : 0 < S` using `by positivity`. Establish `hsq : Real.sqrt S ^ 2 = S` using `Real.sq_sqrt hS0.le`. Establish `hB : 0 < Real.sqrt S ^ 2 * RR (E` using `E) ^ 4 := by rw [hsq]; positivity`. Establish `hA : 0 < PT.f E * Real.sqrt S ^ 2 * RR (E` using `E) ^ 3 := by rw [hsq]; positivity`. Take `⟨q, hq1, hc1, hc2, hb, h5, h6⟩` from `exists_large_nat (Real.sqrt S ^ 2 * RR (E := E) ^ 4) ((dstar (E := E) m : ℝ) ^ 2 * omStar (E := E) * (PT.f E * Real.sqrt S ^ 2 * RR (E := E) ^ 3)) (M1 (E := E) m) (dstar (E := E) m) (((PT.f E * r : ℕ) : ℝ) * Real.log 2 + 2 * dstar (E := E) m + 3 + (1 + 1) * (r * Real.log r + 3 * …`.

Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast hq1`. Use `⟨q, Real.sqrt S, Real.sqrt_pos.mpr (div_pos hA hq0), ?_⟩` and prove the remaining obligations. Introduce `X hX hdim`. Substitute `hX` using the available equality. Use `⟨⟨q, Real.sqrt S, m, hq1, le_rfl, hfr, hdim, hm1, hmf, hfrd, hf2, hrd, ?_, ?_, hb, hc2, hq1, ?_, ?_⟩, rfl, rfl, rfl⟩` and prove the remaining obligations.

Rewrite using `[hsq, hS]`. Unfold `PT.gA`. Establish `: (0 : ℝ) ≤ ((PT.f E * X.r : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Prove the components needed by the constructor for the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[Nat.cast_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `th`. Rewrite using `[Real.sq_sqrt (div_pos hA hq0).le, ← mul_div_assoc, div_lt_one hq0]`. Conclude with `hc1`.

Unfold `t0 b0`. Rewrite using `[Nat.cast_one, mul_one, mul_one]`. Conclude with `h5`. Unfold `t0 b0 PT.gA`. Rewrite using `[Nat.cast_one]`.

Conclude with `h6`.
-/
theorem exists_par : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r m : ℕ),
    2 ≤ PT.f E * r → 1 ≤ m → m ^ 4 ≤ PT.f E → (PT.f E : ℝ) ≤ PT.rd E →
    (PT.f E : ℝ) ^ 2 ≤ PT.rd E → 16 ≤ PT.rd E →
    ∃ (q : ℕ) (R0 : ℝ), 0 < th (E := E) q R0 ∧ ∀ X : PT E, X.r = r → (∃ τ, X.dim τ ≤ m) →
      ∃ P : Par X 1, P.q = q ∧ P.R0 = R0 ∧ P.m = m := by
  intro E _ _ _ r m hfr hm1 hmf hfrd hf2 hrd
  have hf : 0 < PT.f E := by
    rcases Nat.eq_zero_or_pos (PT.f E) with h | h
    · rw [h] at hfr; omega
    · exact h
  have hfR : (0 : ℝ) < PT.f E := by exact_mod_cast hf
  have hrd0 : 0 < PT.rd E := by linarith
  have hRR : 0 < RR (E := E) := by unfold RR; positivity
  set S : ℝ := 270 + 90 * (((PT.f E * r : ℕ) : ℝ) + 1) with hS
  have hS0 : 0 < S := by positivity
  have hsq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0.le
  have hB : 0 < Real.sqrt S ^ 2 * RR (E := E) ^ 4 := by rw [hsq]; positivity
  have hA : 0 < PT.f E * Real.sqrt S ^ 2 * RR (E := E) ^ 3 := by rw [hsq]; positivity
  obtain ⟨q, hq1, hc1, hc2, hb, h5, h6⟩ := exists_large_nat (Real.sqrt S ^ 2 * RR (E := E) ^ 4)
    ((dstar (E := E) m : ℝ) ^ 2 * omStar (E := E) * (PT.f E * Real.sqrt S ^ 2 * RR (E := E) ^ 3))
    (M1 (E := E) m) (dstar (E := E) m)
    (((PT.f E * r : ℕ) : ℝ) * Real.log 2 + 2 * dstar (E := E) m + 3 +
      (1 + 1) * (r * Real.log r + 3 * r + 3)) hB (Nat.cast_nonneg _)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  refine ⟨q, Real.sqrt S, Real.sqrt_pos.mpr (div_pos hA hq0), ?_⟩
  intro X hX hdim
  subst hX
  refine ⟨⟨q, Real.sqrt S, m, hq1, le_rfl, hfr, hdim, hm1, hmf, hfrd, hf2, hrd, ?_, ?_, hb, hc2,
    hq1, ?_, ?_⟩, rfl, rfl, rfl⟩
  · rw [hsq, hS]
    unfold PT.gA
    have : (0 : ℝ) ≤ ((PT.f E * X.r : ℕ) : ℝ) := Nat.cast_nonneg _
    constructor
    · linarith
    · rw [Nat.cast_one]; linarith
  · unfold th
    rw [Real.sq_sqrt (div_pos hA hq0).le, ← mul_div_assoc, div_lt_one hq0]
    exact hc1
  · unfold t0 b0
    rw [Nat.cast_one, mul_one, mul_one]
    exact h5
  · unfold t0 b0 PT.gA
    rw [Nat.cast_one]
    exact h6

end GlobalTheory.ThetaRunParameters
