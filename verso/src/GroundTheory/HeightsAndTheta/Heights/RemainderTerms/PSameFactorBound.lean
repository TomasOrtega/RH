import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsTop
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PowerSums
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
The claim follows from `| 0, h, _ => absurd h (by norm_num) | 1, _, _ => by simp [Nat.descFactorial] | k + 2, _, hN => by have ih : (n₁ + (k + 1)).descFactorial (k + 1) * 2 ^ k ≤ (n₁ + 1) * (2 * (n₁ + N)) ^ k := by simpa using sameFactor_descFactorial_le n₁ N (k + 1) (by omega) (by omega) have hd : (n₁ …`.
-/
theorem sameFactor_descFactorial_le (n₁ N : ℕ) :
    ∀ k : ℕ, 1 ≤ k → k ≤ N →
      (n₁ + k).descFactorial k * 2 ^ (k - 1) ≤ (n₁ + 1) * (2 * (n₁ + N)) ^ (k - 1)
  | 0, h, _ => absurd h (by norm_num)
  | 1, _, _ => by simp [Nat.descFactorial]
  | k + 2, _, hN => by
    have ih : (n₁ + (k + 1)).descFactorial (k + 1) * 2 ^ k ≤ (n₁ + 1) * (2 * (n₁ + N)) ^ k := by
      simpa using sameFactor_descFactorial_le n₁ N (k + 1) (by omega) (by omega)
    have hd : (n₁ + (k + 2)).descFactorial (k + 2) =
        (n₁ + (k + 1) + 1) * (n₁ + (k + 1)).descFactorial (k + 1) := by
      rw [show n₁ + (k + 2) = n₁ + (k + 1) + 1 by omega, Nat.succ_descFactorial_succ]
    rw [show k + 2 - 1 = k + 1 by omega, pow_succ, pow_succ, hd]
    calc (n₁ + (k + 1) + 1) * (n₁ + (k + 1)).descFactorial (k + 1) * (2 ^ k * 2)
        = ((n₁ + (k + 1)).descFactorial (k + 1) * 2 ^ k) * (2 * (n₁ + (k + 1) + 1)) := by ring
      _ ≤ ((n₁ + 1) * (2 * (n₁ + N)) ^ k) * (2 * (n₁ + N)) :=
          Nat.mul_le_mul ih (by omega)
      _ = (n₁ + 1) * ((2 * (n₁ + N)) ^ k * (2 * (n₁ + N))) := by ring

/- English proof (translation)
Establish `h` using `sameFactor_descFactorial_le (r * a) (r + a) k hk1 hkN`. Rewrite `h` using `[Nat.descFactorial_eq_factorial_mul_choose]`. Establish `hq : ((k.factorial * Nat.choose (r * a + k) k * 2 ^ (k - 1) : ℕ) : ℚ) ≤ ((((r * a) + 1) * (2 * ((r * a) + (r + a))) ^ (k - 1) : ℕ) : ℚ)` using `by exact_mod_cast h`. Establish `hX : restX r a = ((2 * ((r * a) + (r + a)) : ℕ) : ℚ)`. Simplify using `only [restX]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity), hX]`. Move the coercions through the operations in `at hq ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sameFactor_choose_le (r a k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ r + a) :
    (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) / ((r * a : ℕ) + 1 : ℚ) ≤
      restX r a ^ (k - 1) / (k.factorial : ℚ) := by
  have h := sameFactor_descFactorial_le (r * a) (r + a) k hk1 hkN
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  have hq : ((k.factorial * Nat.choose (r * a + k) k * 2 ^ (k - 1) : ℕ) : ℚ) ≤
      ((((r * a) + 1) * (2 * ((r * a) + (r + a))) ^ (k - 1) : ℕ) : ℚ) := by exact_mod_cast h
  have hX : restX r a = ((2 * ((r * a) + (r + a)) : ℕ) : ℚ) := by
    simp only [restX]; push_cast; ring
  rw [div_le_div_iff₀ (by positivity) (by positivity), hX]
  push_cast at hq ⊢
  linarith

/- English proof (translation)
Introduce `f r a c hf hr ha`. Take `⟨C₀, hC₀, hJ, hT⟩` from `hF f r a c hf hr ha`. Establish `hfR : (0 : ℚ) < numStandardTable (rectangle r a)` using `by exact_mod_cast hR r a`. Take `⟨f', rfl⟩ : ∃ f', f = f' + 1` from `⟨f - 1, by omega⟩`. Establish `hJabs : |fibreDegree (f' + 1) r a c| = |C₀| * (((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) * (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1))`.

Establish `hJp : (0 : ℚ) ≤ ((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) * (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1)` using `by positivity`. Rewrite using `[hJ, ← abs_of_nonneg hJp, ← abs_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, hD (f' + 1) r a c, ?_⟩` and prove the remaining obligations.

Rewrite using `[hJ]`. Conclude with `mul_ne_zero (div_ne_zero (mul_ne_zero hC₀ (by positivity)) (by positivity)) (pow_ne_zero _ hfR.ne')`. Introduce `Q hQ k hk2 hkN τ`. Take `⟨S, hSP, hTk⟩` from `hT Q hQ k hk2 hkN τ`. Establish `hk1 : 1 ≤ k` using `by omega`.

Use `set s : ℚ := c.sign with hs_def`. Apply the tactic sequence `have hs : s = 1 ∨ s = -1 := by cases c <;> simp [hs_def, SmallBlock.sign]`. Apply the tactic sequence `have hsk : |s ^ k| = 1 := by rcases hs with h | h <;> simp [h]`. Establish `hmem : ∀ nu ∈ partitionsOf r k, Antitone nu ∧ ∑ i, nu i = k`. Introduce `nu hnu`.

Simplify using `only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hnu`. Conclude with `⟨fun i j hij => hnu.2 i j hij, hnu.1⟩`. Use `set chi : (Fin r → ℕ) → ℚ := fun nu => symmetricGroupCharacter (fun i => a + nu i) ((k - 1) :: List.replicate (r * a + 1) 1) with hchi`. Establish `hex` using `fun nu (hnu : nu ∈ partitionsOf r k) => hS (r + a) r k hk1 hkN nu s hs (hmem nu hnu).1 (hmem nu hnu).2`. Use `choose! Sν hSν1 hSν2 using hex`.

Establish `hSeq : S = ∑ nu ∈ partitionsOf r k, C (chi nu) * Sν nu`. Apply `Flag.powerSumHom_injective` to reduce the goal to its premises. Rewrite using `[hSP, map_sum]`. Use `Finset.sum_congr rfl fun nu hnu => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hSν1 nu hnu]`.

Use `congr 1`. Simplify using `[powerSumHom, hchi]`. Use `set e : Fin (r + a) →₀ ℕ := Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1 with he`. Establish `hcoef : |coeff e S| ≤ (∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1), |chi nu|) / k`. Rewrite using `[hSeq, coeff_sum]`.

Simplify using `only [coeff_C_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun nu hnu => ?_` and prove the remaining obligations. Rewrite using `[hSν2 nu hnu]`. Use `split_ifs`.

Rewrite using `[abs_mul, abs_mul, hsk, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Use `_ = _ := by rw [Finset.sum_div, Finset.sum_filter]`. Establish `hhook` using `hH r a k chi hk1 (fun nu hnu => hB r _ _ (fun i j hij => Nat.add_le_add_left ((hmem nu hnu).1 hij) a) (fun q hq => by`.

Simplify using `only [List.mem_cons, List.mem_replicate] at hq`. Use the proof step `omega))`. Use `set K : ℚ := k * ((f' + 1) * (r * a) + 1).factorial / (((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f' + 1 - 1)) * (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1 - 1) with hK`. Establish `hK0 : 0 ≤ K` using `by positivity`. Establish `hTabs : |restTerm (f' + 1) (r + a) Q k τ (smallPowerSum (f' + 1) r a c (k - 1) τ)| = |C₀| * K * |coeff e S|`.

Rewrite using `[hTk, show ∀ x : ℚ, C₀ * k * ((f' + 1) * (r * a) + 1).factorial / (((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f' + 1 - 1)) * (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1 - 1) * x = C₀ * K * x from fun x => by rw [hK]; ring, abs_mul, abs_mul, abs_of_nonneg hK0]`. Rewrite using `[hTabs, hJabs]`. Use `set B : ℚ := (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a) with hBdef`. Establish `hk0 : (0 : ℚ) < k` using `by exact_mod_cast (show 0 < k by omega)`. Establish `hcoefB : |coeff e S| ≤ B / k` using `le_trans hcoef (div_le_div_of_nonneg_right hhook hk0.le)`.

Establish `hKB : K * (B / k) = ((f' + 1) * (r * a) + 1 : ℕ) * ((((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) * (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1))) * ((Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) / ((r * a : ℕ) + 1 : ℚ))`. Rewrite using `[hK, hBdef, Nat.add_sub_cancel, Nat.factorial_succ, Nat.factorial_succ (r * a)]`. Establish `: ((r * a).factorial : ℚ) ≠ 0` using `by positivity`. Establish `: (((f' + 1) * (r * a)).factorial : ℚ) ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hP : (0 : ℚ) ≤ ((f' + 1) * (r * a) + 1 : ℕ) * ((((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) * (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1)))` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, hKB]`.

Use `_ ≤ |C₀| * (((f' + 1) * (r * a) + 1 : ℕ) * ((((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) * (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1))) * (restX r a ^ (k - 1) / (k.factorial : ℚ))) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sameFactor_ …`. Use `_ = _ := by ring`.
-/
theorem SameFactorBound.proof (hF : SameFactorFormula.Statement) (hS : SchurSignCoefficient.Statement)
    (hB : CharacterBound.Statement) (hH : HookSumBound.Statement)
    (hR : RectangleTablePos.Statement) (hD : RestPolynomialDecomposes.Statement) :
    SameFactorBound.Statement := by
  intro f r a c hf hr ha
  obtain ⟨C₀, hC₀, hJ, hT⟩ := hF f r a c hf hr ha
  have hfR : (0 : ℚ) < numStandardTable (rectangle r a) := by exact_mod_cast hR r a
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  have hJabs : |fibreDegree (f' + 1) r a c| =
      |C₀| * (((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
        (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1)) := by
    have hJp : (0 : ℚ) ≤ ((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
        (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1) := by positivity
    rw [hJ, ← abs_of_nonneg hJp, ← abs_mul]
    congr 1
    ring
  refine ⟨?_, hD (f' + 1) r a c, ?_⟩
  · rw [hJ]
    exact mul_ne_zero (div_ne_zero (mul_ne_zero hC₀ (by positivity)) (by positivity))
      (pow_ne_zero _ hfR.ne')
  intro Q hQ k hk2 hkN τ
  obtain ⟨S, hSP, hTk⟩ := hT Q hQ k hk2 hkN τ
  have hk1 : 1 ≤ k := by omega
  set s : ℚ := c.sign with hs_def
  have hs : s = 1 ∨ s = -1 := by cases c <;> simp [hs_def, SmallBlock.sign]
  have hsk : |s ^ k| = 1 := by rcases hs with h | h <;> simp [h]
  have hmem : ∀ nu ∈ partitionsOf r k, Antitone nu ∧ ∑ i, nu i = k := by
    intro nu hnu
    simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hnu
    exact ⟨fun i j hij => hnu.2 i j hij, hnu.1⟩
  set chi : (Fin r → ℕ) → ℚ := fun nu =>
    symmetricGroupCharacter (fun i => a + nu i) ((k - 1) :: List.replicate (r * a + 1) 1)
    with hchi
  have hex := fun nu (hnu : nu ∈ partitionsOf r k) =>
    hS (r + a) r k hk1 hkN nu s hs (hmem nu hnu).1 (hmem nu hnu).2
  choose! Sν hSν1 hSν2 using hex

  have hSeq : S = ∑ nu ∈ partitionsOf r k, C (chi nu) * Sν nu := by
    apply Flag.powerSumHom_injective
    rw [hSP, map_sum]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [map_mul, hSν1 nu hnu]
    congr 1
    simp [powerSumHom, hchi]
  set e : Fin (r + a) →₀ ℕ := Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1 with he
  have hcoef : |coeff e S| ≤
      (∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
        |chi nu|) / k := by
    rw [hSeq, coeff_sum]
    simp only [coeff_C_mul]
    calc |∑ nu ∈ partitionsOf r k, chi nu * coeff e (Sν nu)|
        ≤ ∑ nu ∈ partitionsOf r k, |chi nu * coeff e (Sν nu)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ nu ∈ partitionsOf r k,
            if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then |chi nu| / k else 0 := by
          refine Finset.sum_congr rfl fun nu hnu => ?_
          rw [hSν2 nu hnu]
          split_ifs
          · rw [abs_mul, abs_mul, hsk, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
            ring
          · simp
      _ = _ := by rw [Finset.sum_div, Finset.sum_filter]
  have hhook := hH r a k chi hk1 (fun nu hnu => hB r _ _
    (fun i j hij => Nat.add_le_add_left ((hmem nu hnu).1 hij) a)
    (fun q hq => by
      simp only [List.mem_cons, List.mem_replicate] at hq
      omega))

  set K : ℚ := k * ((f' + 1) * (r * a) + 1).factorial /
      (((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f' + 1 - 1)) *
      (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1 - 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hTabs : |restTerm (f' + 1) (r + a) Q k τ (smallPowerSum (f' + 1) r a c (k - 1) τ)| =
      |C₀| * K * |coeff e S| := by
    rw [hTk, show ∀ x : ℚ, C₀ * k * ((f' + 1) * (r * a) + 1).factorial /
        (((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f' + 1 - 1)) *
        (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1 - 1) * x = C₀ * K * x from
        fun x => by rw [hK]; ring, abs_mul, abs_mul, abs_of_nonneg hK0]
  rw [hTabs, hJabs]
  set B : ℚ := (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) *
    numStandardTable (rectangle r a) with hBdef
  have hk0 : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcoefB : |coeff e S| ≤ B / k := le_trans hcoef (div_le_div_of_nonneg_right hhook hk0.le)
  have hKB : K * (B / k) = ((f' + 1) * (r * a) + 1 : ℕ) *
      ((((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
        (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1))) *
      ((Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) / ((r * a : ℕ) + 1 : ℚ)) := by
    rw [hK, hBdef, Nat.add_sub_cancel, Nat.factorial_succ, Nat.factorial_succ (r * a)]
    have : ((r * a).factorial : ℚ) ≠ 0 := by positivity
    have : (((f' + 1) * (r * a)).factorial : ℚ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  have hP : (0 : ℚ) ≤ ((f' + 1) * (r * a) + 1 : ℕ) *
      ((((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
        (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1))) := by positivity
  calc |C₀| * K * |coeff e S| ≤ |C₀| * K * (B / k) :=
        mul_le_mul_of_nonneg_left hcoefB (by positivity)
    _ = |C₀| * (((f' + 1) * (r * a) + 1 : ℕ) *
          ((((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
            (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1))) *
          ((Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) / ((r * a : ℕ) + 1 : ℚ))) := by
        rw [mul_assoc, hKB]
    _ ≤ |C₀| * (((f' + 1) * (r * a) + 1 : ℕ) *
          ((((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
            (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1))) *
          (restX r a ^ (k - 1) / (k.factorial : ℚ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (sameFactor_choose_le r a k hk1 hkN) hP) (abs_nonneg _)
    _ = _ := by ring

end

end GroundTheory.Heights₂.Heights.RestTerms
