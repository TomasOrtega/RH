import Mathlib
import GroundTheory.PAdicHodge.FieldOfNorms
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField IsLocalRing

section Tower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `hres : ∀ z : 𝒪[F], residue 𝒪[F] z = 0 ↔ nrm K ((z : F) : Ω) < 1`. Introduce `z`. Rewrite using `[residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]`. Rewrite using `[← map_one (valuation F), ← not_le, ← not_le, valuation_le_iff_nrm_le]`.

Simplify using the standard rewrite rules. Use `haveI : CharP 𝓀[F] p := by`. Use `(CharP.charP_iff_prime_eq_zero hp).mpr ?_` and prove the remaining obligations. Use `(hres (p : 𝒪[F])).mpr (by simpa using hp1)` as an intermediate fact. Simplify using `using this`.

Use `haveI : Finite 𝓀[F] := inferInstance`. Take `⟨z, rfl⟩ : ∃ z : F, (z : Ω) = y` from `⟨⟨y, hy⟩, rfl⟩`. Establish `hz : z ∈ 𝒪[F]` using `(mem_integer_iff_nrm_le_one F z).mpr hy1`. Take `⟨β, hβ⟩` from `((surjective_frobenius 𝓀[F] p).iterate j) (residue 𝒪[F] ⟨z, hz⟩)`. Take `⟨b, rfl⟩` from `residue_surjective β`.

Use `⟨((b : F) : Ω), (b : F).2, (mem_integer_iff_nrm_le_one F _).mp b.2, ?_⟩` and prove the remaining obligations. Rewrite `hβ` using `[iterate_frobenius, ← map_pow, ← sub_eq_zero, ← map_sub]`. Use `(hres _).mp hβ` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_pow_sub_lt_one (F : IntermediateField K Ω) [FiniteDimensional K F] (hp : p.Prime)
    (hp1 : nrm K (p : Ω) < 1) {y : Ω} (hy : y ∈ F) (hy1 : nrm K y ≤ 1) (j : ℕ) :
    ∃ b ∈ F, nrm K b ≤ 1 ∧ nrm K (b ^ (p ^ j) - y) < 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hres : ∀ z : 𝒪[F], residue 𝒪[F] z = 0 ↔ nrm K ((z : F) : Ω) < 1 := by
    intro z
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    rw [← map_one (valuation F), ← not_le, ← not_le, valuation_le_iff_nrm_le]
    simp
  haveI : CharP 𝓀[F] p := by
    refine (CharP.charP_iff_prime_eq_zero hp).mpr ?_
    have := (hres (p : 𝒪[F])).mpr (by simpa using hp1)
    simpa using this
  haveI : Finite 𝓀[F] := inferInstance
  obtain ⟨z, rfl⟩ : ∃ z : F, (z : Ω) = y := ⟨⟨y, hy⟩, rfl⟩
  have hz : z ∈ 𝒪[F] := (mem_integer_iff_nrm_le_one F z).mpr hy1
  obtain ⟨β, hβ⟩ := ((surjective_frobenius 𝓀[F] p).iterate j) (residue 𝒪[F] ⟨z, hz⟩)
  obtain ⟨b, rfl⟩ := residue_surjective β
  refine ⟨((b : F) : Ω), (b : F).2, (mem_integer_iff_nrm_le_one F _).mp b.2, ?_⟩
  rw [iterate_frobenius, ← map_pow, ← sub_eq_zero, ← map_sub] at hβ
  have := (hres _).mp hβ
  simpa using this

namespace NormTower

variable (t : NormTower K Ω p)

/- English proof (translation)
Use `haveI := t.finiteDimensional n`. Use `set d := p ^ t.k n`. Take `⟨w, hw, hw1, hwN⟩` from `exists_pow_sub_lt_one (t.E n) t.prime t.nrm_p_lt_one (t.N_mem n hz.1) (t.nrm_N_le_one n hz.2) (t.k n)`. Use `⟨w, ⟨hw, hw1⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : nrm K (z ^ d - w ^ d) < 1`.

Establish `e : z ^ d - w ^ d = (z ^ d - t.N n z) + -(w ^ d - t.N n z)` using `by ring`. Rewrite using `[e]`. Use `lt_of_le_of_lt (nrm_add_le_max _ _) (max_lt ?_ ?_)` and prove the remaining obligations. Rewrite using `[nrm_sub_comm]`. Conclude with `(t.nrm_N_sub_pow_le n hz.1 hz.2).trans_lt t.c_lt_one`.

Rewrite using `[nrm_neg]`. Conclude with `hwN`. Establish `h2 : nrm K ((z - w) ^ d - (z ^ d - w ^ d)) < 1`. Establish `hm1 : nrm K (-w) ≤ 1` using `by rw [nrm_neg]; exact hw1`. Establish `h3` using `nrm_add_pow_prime_pow_sub_le t.prime hz.2 hm1 (t.k n)`.

Establish `e : (z - w) ^ d - (z ^ d - w ^ d) = ((z + -w) ^ d - z ^ d - (-w) ^ d) + ((-w) ^ d + w ^ d)`. Rewrite using `[sub_eq_add_neg z w]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `lt_of_le_of_lt (nrm_add_le_max _ _) (max_lt (h3.trans_lt t.nrm_p_lt_one) ?_)` and prove the remaining obligations.

Break down `t.prime.eq_two_or_odd' with hp2 | hodd` into its components or cases. Break down `Nat.eq_zero_or_pos (t.k n) with hk | hk` into its components or cases. Simplify using `only [d, hk, pow_zero, pow_one, neg_add_cancel, nrm_zero]`. Conclude with `one_pos`. Establish `hev : Even d`.

Simplify using `only [d, hp2]`. Conclude with `(Nat.even_pow.mpr ⟨even_two, hk.ne'⟩)`. Rewrite using `[hev.neg_pow, ← two_mul, nrm_mul]`. Establish `h2' : nrm K (2 : Ω) < 1`. Use `t.nrm_p_lt_one` as an intermediate fact.

Rewrite `this` using `[hp2]`. Conclude with `this` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Establish `hodd' : Odd d` using `hodd.pow`. Rewrite using `[hodd'.neg_pow, neg_add_cancel, nrm_zero]`.

Conclude with `one_pos`. Establish `h4 : nrm K ((z - w) ^ d) < 1`. Establish `e : (z - w) ^ d = ((z - w) ^ d - (z ^ d - w ^ d)) + (z ^ d - w ^ d)` using `by ring`. Rewrite using `[e]`. Conclude with `lt_of_le_of_lt (nrm_add_le_max _ _) (max_lt h2 h1)`.

Rewrite `h4` using `[nrm_pow]`. Conclude with `(pow_lt_one_iff_of_nonneg (nrm_nonneg _) (pow_pos t.prime.pos _).ne').mp h4`.
-/
theorem exists_nrm_sub_lt_one (n : ℕ) {z : Ω} (hz : z ∈ t.intSet (n + 1)) :
    ∃ w ∈ t.intSet n, nrm K (z - w) < 1 := by
  haveI := t.finiteDimensional n
  set d := p ^ t.k n
  obtain ⟨w, hw, hw1, hwN⟩ := exists_pow_sub_lt_one (t.E n) t.prime t.nrm_p_lt_one
    (t.N_mem n hz.1) (t.nrm_N_le_one n hz.2) (t.k n)
  refine ⟨w, ⟨hw, hw1⟩, ?_⟩

  have h1 : nrm K (z ^ d - w ^ d) < 1 := by
    have e : z ^ d - w ^ d = (z ^ d - t.N n z) + -(w ^ d - t.N n z) := by ring
    rw [e]
    refine lt_of_le_of_lt (nrm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [nrm_sub_comm]; exact (t.nrm_N_sub_pow_le n hz.1 hz.2).trans_lt t.c_lt_one
    · rw [nrm_neg]; exact hwN
  have h2 : nrm K ((z - w) ^ d - (z ^ d - w ^ d)) < 1 := by
    have hm1 : nrm K (-w) ≤ 1 := by rw [nrm_neg]; exact hw1
    have h3 := nrm_add_pow_prime_pow_sub_le t.prime hz.2 hm1 (t.k n)
    have e : (z - w) ^ d - (z ^ d - w ^ d) =
        ((z + -w) ^ d - z ^ d - (-w) ^ d) + ((-w) ^ d + w ^ d) := by
      rw [sub_eq_add_neg z w]; ring
    rw [e]
    refine lt_of_le_of_lt (nrm_add_le_max _ _) (max_lt (h3.trans_lt t.nrm_p_lt_one) ?_)

    rcases t.prime.eq_two_or_odd' with hp2 | hodd
    · rcases Nat.eq_zero_or_pos (t.k n) with hk | hk
      · simp only [d, hk, pow_zero, pow_one, neg_add_cancel, nrm_zero]; exact one_pos
      · have hev : Even d := by
          simp only [d, hp2]
          exact (Nat.even_pow.mpr ⟨even_two, hk.ne'⟩)
        rw [hev.neg_pow, ← two_mul, nrm_mul]
        have h2' : nrm K (2 : Ω) < 1 := by
          have := t.nrm_p_lt_one; rw [hp2] at this; exact_mod_cast this
        calc nrm K (2 : Ω) * nrm K (w ^ d) ≤ nrm K (2 : Ω) * 1 :=
              mul_le_mul_of_nonneg_left (nrm_le_one_of_pow hw1 _) (nrm_nonneg _)
          _ < 1 := by rw [mul_one]; exact h2'
    · have hodd' : Odd d := hodd.pow
      rw [hodd'.neg_pow, neg_add_cancel, nrm_zero]; exact one_pos
  have h4 : nrm K ((z - w) ^ d) < 1 := by
    have e : (z - w) ^ d = ((z - w) ^ d - (z ^ d - w ^ d)) + (z ^ d - w ^ d) := by ring
    rw [e]
    exact lt_of_le_of_lt (nrm_add_le_max _ _) (max_lt h2 h1)
  rw [nrm_pow] at h4
  exact (pow_lt_one_iff_of_nonneg (nrm_nonneg _) (pow_pos t.prime.pos _).ne').mp h4

/- English proof (translation)
Proceed by induction on `n generalizing z with`. Consider the case `zero => exact ⟨z, hz, by simp⟩`. Consider the case `succ n ih`. Take `⟨w, hw, hzw⟩` from `t.exists_nrm_sub_lt_one n hz`. Take `⟨w', hw', hww'⟩` from `ih hw`.

Use `⟨w', hw', ?_⟩` and prove the remaining obligations. Establish `e : z - w' = (z - w) + (w - w')` using `by ring`. Rewrite using `[e]`. Conclude with `lt_of_le_of_lt (nrm_add_le_max _ _) (max_lt hzw hww')`.
-/
theorem exists_nrm_sub_lt_one_zero (n : ℕ) {z : Ω} (hz : z ∈ t.intSet n) :
    ∃ w ∈ t.intSet 0, nrm K (z - w) < 1 := by
  induction n generalizing z with
  | zero => exact ⟨z, hz, by simp⟩
  | succ n ih =>
    obtain ⟨w, hw, hzw⟩ := t.exists_nrm_sub_lt_one n hz
    obtain ⟨w', hw', hww'⟩ := ih hw
    refine ⟨w', hw', ?_⟩
    have e : z - w' = (z - w) + (w - w') := by ring
    rw [e]
    exact lt_of_le_of_lt (nrm_add_le_max _ _) (max_lt hzw hww')

/- English proof (translation)
Break down `eq_or_ne y 0 with rfl | hy0` into its components or cases. Rewrite using `[nrm_zero]`. Conclude with `(t.value_pos n).le`. Take `⟨j, hj⟩` from `t.value_zpow n y hy hy0`. Rewrite `h`, the goal using `[hj]`.

Establish `hj1 : 1 ≤ j`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `: 1 ≤ t.value n ^ j` using `one_le_zpow_of_nonpos₀ (t.value_pos n) (t.value_lt_one n).le (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem nrm_le_value_of_lt_one (n : ℕ) {y : Ω} (hy : y ∈ t.E n) (h : nrm K y < 1) :
    nrm K y ≤ t.value n := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [nrm_zero]; exact (t.value_pos n).le
  obtain ⟨j, hj⟩ := t.value_zpow n y hy hy0
  rw [hj] at h ⊢
  have hj1 : 1 ≤ j := by
    by_contra hcon
    push Not at hcon
    have : 1 ≤ t.value n ^ j :=
      one_le_zpow_of_nonpos₀ (t.value_pos n) (t.value_lt_one n).le (by omega)
    linarith
  calc t.value n ^ j ≤ t.value n ^ (1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ (t.value_pos n) (t.value_lt_one n).le hj1
    _ = t.value n := zpow_one _

/- English proof (translation)
Set `C : ℕ → Set Ω` to `fun n ↦ {z | nrm K (z ^ t.D 0 n - y) ≤ t.value n}`. Establish `hcl : ∀ n, IsClosed (C n)` using `fun n ↦ isClosed_le ((continuous_nrm K Ω).comp ((continuous_pow _).sub continuous_const)) continuous_const`. Establish `hne : ∀ n, (t.intSet n ∩ C n).Nonempty`. Introduce `n`. Use `haveI := t.finiteDimensional 0`.

Establish `hD : ∃ j, t.D 0 n = p ^ j` using `⟨∑ m ∈ Finset.range n, t.k (0 + m), by`. Rewrite using `[D, Finset.prod_pow_eq_pow_sum]⟩`. Take `⟨j, hj⟩` from `hD`. Take `⟨b, hb, hb1, hby⟩` from `exists_pow_sub_lt_one (t.E 0) t.prime t.nrm_p_lt_one hy.1 hy.2 j`. Use `⟨b, ⟨t.E_mono (Nat.zero_le n) hb, hb1⟩, ?_⟩` and prove the remaining obligations.

Use `show nrm K (b ^ t.D 0 n - y) ≤ t.value n`. Rewrite using `[hj]`. Establish `hmem : b ^ p ^ j - y ∈ t.E n` using `sub_mem (pow_mem (t.E_mono (Nat.zero_le n) hb) _) (t.E_mono (Nat.zero_le n) hy.1)`. Conclude with `t.nrm_le_value_of_lt_one n hmem hby`. Establish `hN : ∀ n, ∀ z ∈ t.intSet (n + 1) ∩ C (n + 1), t.N n z ∈ C n`.

Introduce `n z hz`. Take `⟨⟨hzE, hz1⟩, hzy⟩` from `hz`. Express the relevant statement in the definitionally equal form `nrm K (z ^ t.D 0 (n + 1) - y) ≤ t.value (n + 1) at hzy`. Use `show nrm K (t.N n z ^ t.D 0 n - y) ≤ t.value n`. Establish `hD : t.D 0 (n + 1) = t.D 0 n * p ^ t.k n` using `by rw [D_succ, zero_add]`.

Establish `h1 : nrm K (t.N n z ^ t.D 0 n - z ^ t.D 0 (n + 1)) ≤ t.c`. Rewrite using `[hD, pow_mul']`. Conclude with `(nrm_pow_sub_pow_le (t.nrm_N_le_one n hz1) (nrm_le_one_of_pow hz1 _) _).trans (t.nrm_N_sub_pow_le n hzE hz1)`. Establish `h2 : nrm K (t.N n z ^ t.D 0 n - y) < 1`. Establish `e : t.N n z ^ t.D 0 n - y = (t.N n z ^ t.D 0 n - z ^ t.D 0 (n + 1)) + (z ^ t.D 0 (n + 1) - y)` using `by ring`.

Rewrite using `[e]`. Conclude with `lt_of_le_of_lt (nrm_add_le_max _ _) (max_lt (h1.trans_lt t.c_lt_one) (hzy.trans_lt (t.value_lt_one _)))`. Conclude with `t.nrm_le_value_of_lt_one n (sub_mem (pow_mem (t.N_mem n hzE) _) (t.E_mono (Nat.zero_le n) hy.1)) h2`. Take `⟨z, hz, hzC⟩` from `t.exists_intFam_mem hcl hne hN`. Use `⟨⟨z, hz⟩, ?_⟩` and prove the remaining obligations.

Use `hzC 0` as an intermediate fact. Express the relevant statement in the definitionally equal form `nrm K (z 0 ^ t.D 0 0 - y) ≤ t.value 0 at this`. Establish `hD : t.D 0 0 = 1` using `by simp [D]`. Rewrite `this` using `[hD, pow_one]`. Conclude with `this.trans_lt (t.value_lt_one 0)`.
-/
theorem exists_plus_nrm_sub_lt_one {y : Ω} (hy : y ∈ t.intSet 0) :
    ∃ x : t.Plus, nrm K (x.1 0 - y) < 1 := by

  let C : ℕ → Set Ω := fun n ↦ {z | nrm K (z ^ t.D 0 n - y) ≤ t.value n}
  have hcl : ∀ n, IsClosed (C n) := fun n ↦
    isClosed_le ((continuous_nrm K Ω).comp ((continuous_pow _).sub continuous_const))
      continuous_const
  have hne : ∀ n, (t.intSet n ∩ C n).Nonempty := by
    intro n
    haveI := t.finiteDimensional 0
    have hD : ∃ j, t.D 0 n = p ^ j := ⟨∑ m ∈ Finset.range n, t.k (0 + m), by
      rw [D, Finset.prod_pow_eq_pow_sum]⟩
    obtain ⟨j, hj⟩ := hD
    obtain ⟨b, hb, hb1, hby⟩ := exists_pow_sub_lt_one (t.E 0) t.prime t.nrm_p_lt_one hy.1 hy.2 j
    refine ⟨b, ⟨t.E_mono (Nat.zero_le n) hb, hb1⟩, ?_⟩
    show nrm K (b ^ t.D 0 n - y) ≤ t.value n
    rw [hj]
    have hmem : b ^ p ^ j - y ∈ t.E n :=
      sub_mem (pow_mem (t.E_mono (Nat.zero_le n) hb) _) (t.E_mono (Nat.zero_le n) hy.1)
    exact t.nrm_le_value_of_lt_one n hmem hby
  have hN : ∀ n, ∀ z ∈ t.intSet (n + 1) ∩ C (n + 1), t.N n z ∈ C n := by
    intro n z hz
    obtain ⟨⟨hzE, hz1⟩, hzy⟩ := hz
    change nrm K (z ^ t.D 0 (n + 1) - y) ≤ t.value (n + 1) at hzy
    show nrm K (t.N n z ^ t.D 0 n - y) ≤ t.value n
    have hD : t.D 0 (n + 1) = t.D 0 n * p ^ t.k n := by rw [D_succ, zero_add]
    have h1 : nrm K (t.N n z ^ t.D 0 n - z ^ t.D 0 (n + 1)) ≤ t.c := by
      rw [hD, pow_mul']
      exact (nrm_pow_sub_pow_le (t.nrm_N_le_one n hz1) (nrm_le_one_of_pow hz1 _) _).trans
        (t.nrm_N_sub_pow_le n hzE hz1)
    have h2 : nrm K (t.N n z ^ t.D 0 n - y) < 1 := by
      have e : t.N n z ^ t.D 0 n - y =
          (t.N n z ^ t.D 0 n - z ^ t.D 0 (n + 1)) + (z ^ t.D 0 (n + 1) - y) := by ring
      rw [e]
      exact lt_of_le_of_lt (nrm_add_le_max _ _)
        (max_lt (h1.trans_lt t.c_lt_one) (hzy.trans_lt (t.value_lt_one _)))
    exact t.nrm_le_value_of_lt_one n
      (sub_mem (pow_mem (t.N_mem n hzE) _) (t.E_mono (Nat.zero_le n) hy.1)) h2
  obtain ⟨z, hz, hzC⟩ := t.exists_intFam_mem hcl hne hN
  refine ⟨⟨z, hz⟩, ?_⟩
  have := hzC 0
  change nrm K (z 0 ^ t.D 0 0 - y) ≤ t.value 0 at this
  have hD : t.D 0 0 = 1 := by simp [D]
  rw [hD, pow_one] at this
  exact this.trans_lt (t.value_lt_one 0)

end NormTower

end Tower

section FieldOfNorms

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
  {L : IntermediateField K Ω} [IsGalois K L]
  [hsapf : Fact (IsStrictlyAPF K Ω L)] [hinf : Fact (¬ FiniteDimensional K L)]

namespace FieldOfNorms

instance isLocalRing_integer_L : IsLocalRing 𝒪[L] :=
  inferInstanceAs (IsLocalRing (valuation L).valuationSubring)

/- English proof (translation)
Rewrite using `[Valuation.mem_integer_iff, ← map_one (valuation L), ← (valuation L).vle_iff_le, ← IntermediateField.coe_vle_coe_iff, ← nrm_le_nrm_iff (K := K)]`. Simplify using the standard rewrite rules.
-/
theorem mem_integer_L_iff (z : L) : z ∈ 𝒪[L] ↔ nrm K (z : Ω) ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation L), ← (valuation L).vle_iff_le,
    ← IntermediateField.coe_vle_coe_iff, ← nrm_le_nrm_iff (K := K)]
  simp

/- English proof (translation)
Rewrite using `[mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one, ← map_one (valuation L), ← not_le, ← not_le, ← (valuation L).vle_iff_le, ← IntermediateField.coe_vle_coe_iff, ← nrm_le_nrm_iff (K := K)]`. Simplify using the standard rewrite rules.
-/
theorem mem_maximalIdeal_L_iff (z : 𝒪[L]) : z ∈ maximalIdeal 𝒪[L] ↔ nrm K ((z : L) : Ω) < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
    ← map_one (valuation L), ← not_le, ← not_le, ← (valuation L).vle_iff_le,
    ← IntermediateField.coe_vle_coe_iff, ← nrm_le_nrm_iff (K := K)]
  simp

/- English proof (translation)
Rewrite using `[Valuation.mem_integer_iff, ← map_one (valuation _), ← (valuation _).vle_iff_le, vle_iff_norm_le, norm_one]`.
-/
theorem mem_integer_iff (x : FieldOfNorms K Ω L) : x ∈ 𝒪[FieldOfNorms K Ω L] ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation _), ← (valuation _).vle_iff_le,
    vle_iff_norm_le, norm_one]

/- English proof (translation)
Rewrite using `[mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one, ← map_one (valuation _), ← not_le, ← not_le, ← (valuation _).vle_iff_le, vle_iff_norm_le, norm_one]`.
-/
theorem mem_maximalIdeal_iff (x : 𝒪[FieldOfNorms K Ω L]) :
    x ∈ maximalIdeal 𝒪[FieldOfNorms K Ω L] ↔ ‖(x : FieldOfNorms K Ω L)‖ < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
    ← map_one (valuation _), ← not_le, ← not_le, ← (valuation _).vle_iff_le, vle_iff_norm_le,
    norm_one]

abbrev E₀ : FinSub K Ω L := (isTowerFor (L := L)).finSub 0

def toL (x : FieldOfNorms K Ω L) : L := ⟨x.1 E₀, E₀.2.1 (x.2.1 E₀)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nrm_toL (x : FieldOfNorms K Ω L) : nrm K ((toL x : L) : Ω) = ‖x‖ := rfl

/- English proof (translation)
Rewrite using `[mem_integer_L_iff, nrm_toL, ← mem_integer_iff]`. Conclude with `x.2`.
-/
theorem toL_mem (x : 𝒪[FieldOfNorms K Ω L]) : toL (x : FieldOfNorms K Ω L) ∈ 𝒪[L] := by
  rw [mem_integer_L_iff, nrm_toL, ← mem_integer_iff]; exact x.2

def toPlus (x : 𝒪[FieldOfNorms K Ω L]) : (tower K Ω L).Plus :=
  ⟨(equivFam K Ω L x).1, NormTower.Fam.isIntFam_of_nrm_le (by
    have := (mem_integer_iff _).mp x.2
    rw [norm_def, NormTower.Fam.norm_def] at this
    exact this)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem equivFam_eq_toPlus (x : 𝒪[FieldOfNorms K Ω L]) :
    equivFam K Ω L (x : FieldOfNorms K Ω L) = (toPlus x).toFam := rfl

/- English proof (translation)
Establish `h : equivFam K Ω L ((x : FieldOfNorms K Ω L) + y) = (toPlus x + toPlus y).toFam`. Rewrite using `[equivFam_add, equivFam_eq_toPlus, equivFam_eq_toPlus, NormTower.Fam.toFam_add]`. Establish `h2` using `NormTower.Plus.add_cong (toPlus x) (toPlus y) 0`. Establish `e : ((x : FieldOfNorms K Ω L) + y).1 E₀ = (toPlus x + toPlus y).1 0`. Rewrite using `[← equivFam_val, h]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h2.trans_lt (tower K Ω L).ρ_lt_one`.
-/
theorem add_val_cong (x y : 𝒪[FieldOfNorms K Ω L]) :
    nrm K (((x : FieldOfNorms K Ω L) + y).1 E₀ - (x.1.1 E₀ + y.1.1 E₀)) < 1 := by
  have h : equivFam K Ω L ((x : FieldOfNorms K Ω L) + y) = (toPlus x + toPlus y).toFam := by
    rw [equivFam_add, equivFam_eq_toPlus, equivFam_eq_toPlus, NormTower.Fam.toFam_add]
  have h2 := NormTower.Plus.add_cong (toPlus x) (toPlus y) 0
  have e : ((x : FieldOfNorms K Ω L) + y).1 E₀ = (toPlus x + toPlus y).1 0 := by
    rw [← equivFam_val, h]; rfl
  rw [e]
  exact h2.trans_lt (tower K Ω L).ρ_lt_one

def reduction : 𝒪[FieldOfNorms K Ω L] →+* 𝓀[L] where
  toFun x := residue 𝒪[L] ⟨toL (x : FieldOfNorms K Ω L), toL_mem x⟩
  map_one' := by
    rw [← map_one (residue 𝒪[L])]
    congr 1
    refine Subtype.ext (Subtype.ext ?_)
    show (1 : FieldOfNorms K Ω L).1 E₀ = 1
    rw [← equivFam_val, equivFam_one, NormTower.Fam.one_val]
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    refine Subtype.ext (Subtype.ext ?_)
    show ((x : FieldOfNorms K Ω L) * y).1 E₀ = x.1.1 E₀ * y.1.1 E₀
    exact mul_val _ _ _
  map_zero' := by
    rw [← map_zero (residue 𝒪[L])]
    congr 1
    refine Subtype.ext (Subtype.ext ?_)
    show (0 : FieldOfNorms K Ω L).1 E₀ = 0
    rw [← equivFam_val, equivFam_zero, NormTower.Fam.zero_val]
  map_add' x y := by
    rw [← map_add, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal_L_iff]
    exact add_val_cong x y

/- English proof (translation)
Use `show residue 𝒪[L] ⟨toL (x : FieldOfNorms K Ω L), toL_mem x⟩ = 0 ↔ _`. Rewrite using `[residue_eq_zero_iff, mem_maximalIdeal_L_iff, mem_maximalIdeal_iff]`. Both sides reduce to the same expression.
-/
theorem reduction_eq_zero_iff (x : 𝒪[FieldOfNorms K Ω L]) :
    reduction (K := K) (Ω := Ω) (L := L) x = 0 ↔ x ∈ maximalIdeal 𝒪[FieldOfNorms K Ω L] := by
  show residue 𝒪[L] ⟨toL (x : FieldOfNorms K Ω L), toL_mem x⟩ = 0 ↔ _
  rw [residue_eq_zero_iff, mem_maximalIdeal_L_iff, mem_maximalIdeal_iff]
  rfl

/- English proof (translation)
Introduce `r`. Take `⟨⟨z, hz⟩, rfl⟩` from `residue_surjective r`. Establish `hz1` using `(mem_integer_L_iff z).mp hz`. Take `⟨n, hn⟩` from `(isTowerFor (L := L)).exists_mem (z : Ω) z.2`. Take `⟨w, hw, hzw⟩` from `(tower K Ω L).exists_nrm_sub_lt_one_zero n ⟨hn, hz1⟩`.

Take `⟨a, ha⟩` from `(tower K Ω L).exists_plus_nrm_sub_lt_one hw`. Set `x : FieldOfNorms K Ω L` to `(equivFam K Ω L).symm a.toFam`. Establish `hx : equivFam K Ω L x = a.toFam` using `(equivFam K Ω L).apply_symm_apply _`. Establish `hxval : x.1 E₀ = a.1 0`. Rewrite using `[← equivFam_val, hx]`.

Both sides reduce to the same expression. Establish `hxint : x ∈ 𝒪[FieldOfNorms K Ω L]`. Rewrite using `[mem_integer_iff, norm_def, hx, NormTower.Fam.norm_def]`. Conclude with `a.nrm_le 0`. Use `⟨⟨x, hxint⟩, ?_⟩` and prove the remaining obligations.

Use `show residue 𝒪[L] _ = residue 𝒪[L] _`. Rewrite using `[← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal_L_iff]`. Use `show nrm K (x.1 E₀ - (z : Ω)) < 1`. Rewrite using `[hxval]`. Establish `e : a.1 0 - (z : Ω) = (a.1 0 - w) - ((z : Ω) - w)` using `by ring`.

Rewrite using `[e]`. Conclude with `lt_of_le_of_lt (nrm_sub_le_max _ _) (max_lt ha hzw)`.
-/
theorem reduction_surjective : Function.Surjective (reduction (K := K) (Ω := Ω) (L := L)) := by
  intro r
  obtain ⟨⟨z, hz⟩, rfl⟩ := residue_surjective r
  have hz1 := (mem_integer_L_iff z).mp hz
  obtain ⟨n, hn⟩ := (isTowerFor (L := L)).exists_mem (z : Ω) z.2
  obtain ⟨w, hw, hzw⟩ := (tower K Ω L).exists_nrm_sub_lt_one_zero n ⟨hn, hz1⟩
  obtain ⟨a, ha⟩ := (tower K Ω L).exists_plus_nrm_sub_lt_one hw
  let x : FieldOfNorms K Ω L := (equivFam K Ω L).symm a.toFam
  have hx : equivFam K Ω L x = a.toFam := (equivFam K Ω L).apply_symm_apply _
  have hxval : x.1 E₀ = a.1 0 := by
    rw [← equivFam_val, hx]; rfl
  have hxint : x ∈ 𝒪[FieldOfNorms K Ω L] := by
    rw [mem_integer_iff, norm_def, hx, NormTower.Fam.norm_def]; exact a.nrm_le 0
  refine ⟨⟨x, hxint⟩, ?_⟩
  show residue 𝒪[L] _ = residue 𝒪[L] _
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal_L_iff]
  show nrm K (x.1 E₀ - (z : Ω)) < 1
  rw [hxval]
  have e : a.1 0 - (z : Ω) = (a.1 0 - w) - ((z : Ω) - w) := by ring
  rw [e]
  exact lt_of_le_of_lt (nrm_sub_le_max _ _) (max_lt ha hzw)

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[RingHom.mem_ker, reduction_eq_zero_iff]`.
-/
theorem ker_reduction : RingHom.ker (reduction (K := K) (Ω := Ω) (L := L)) =
    maximalIdeal 𝒪[FieldOfNorms K Ω L] := by
  ext x; rw [RingHom.mem_ker, reduction_eq_zero_iff]

def residueFieldEquiv : 𝓀[FieldOfNorms K Ω L] ≃+* 𝓀[L] :=
  (Ideal.quotEquivOfEq ker_reduction.symm).trans
    (RingHom.quotientKerEquivOfSurjective reduction_surjective)

end FieldOfNorms

end FieldOfNorms

end GroundTheory.PAdicHodge
