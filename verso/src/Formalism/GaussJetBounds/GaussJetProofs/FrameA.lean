import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.StatementK
import Formalism.GaussJetBounds.GaussJetProofs.NormDetLeOneOfEntries
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero _ hl.ne_zero), sub_zero, norm_zero]`. Conclude with `norm_nonneg _`. Consider the case `insert a S ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Establish `hV : ‖∑ b ∈ S, U b‖ ≤ 1` using `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun b _ => hU b)`. Choose the witnesses or unpack the hypotheses as in `⟨R, hReq, hRle⟩ : ∃ R : K, (U a + ∑ b ∈ S, U b) ^ (l ^ e) = U a ^ (l ^ e) + (∑ b ∈ S, U b) ^ (l ^ e) + (l : K) * R ∧ ‖R‖ ≤ 1 := by`. Use `⟨_, add_pow_prime_pow_eq' hl (U a) (∑ b ∈ S, U b) e, ?_⟩` and prove the remaining obligations. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun k _ => ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_mul, norm_pow, norm_pow]`. Establish `h1 : ‖U a‖ ^ k ≤ 1` using `pow_le_one₀ (norm_nonneg _) (hU a)`. Establish `h2 : ‖∑ b ∈ S, U b‖ ^ (l ^ e - k) ≤ 1` using `pow_le_one₀ (norm_nonneg _) hV`. Establish `h3` using `IsUltrametricDist.norm_natCast_le_one K ((l ^ e).choose k / l)`. Combine the equalities or inequalities in the displayed calculation.

Establish `heq : (U a + ∑ b ∈ S, U b) ^ (l ^ e) - (U a ^ (l ^ e) + ∑ b ∈ S, U b ^ (l ^ e)) = ((∑ b ∈ S, U b) ^ (l ^ e) - ∑ b ∈ S, U b ^ (l ^ e)) + (l : K) * R`. Rewrite using `[hReq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem frameA_frob_norm {K : Type*} [NormedField K] [IsUltrametricDist K] {l : ℕ}
    (hl : l.Prime) {ι : Type*} (U : ι → K) (hU : ∀ a, ‖U a‖ ≤ 1) (e : ℕ) (S : Finset ι) :
    ‖(∑ a ∈ S, U a) ^ (l ^ e) - ∑ a ∈ S, U a ^ (l ^ e)‖ ≤ ‖(l : K)‖ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero _ hl.ne_zero), sub_zero,
      norm_zero]
    exact norm_nonneg _
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hV : ‖∑ b ∈ S, U b‖ ≤ 1 :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun b _ => hU b)
    obtain ⟨R, hReq, hRle⟩ : ∃ R : K, (U a + ∑ b ∈ S, U b) ^ (l ^ e) =
        U a ^ (l ^ e) + (∑ b ∈ S, U b) ^ (l ^ e) + (l : K) * R ∧ ‖R‖ ≤ 1 := by
      refine ⟨_, add_pow_prime_pow_eq' hl (U a) (∑ b ∈ S, U b) e, ?_⟩
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun k _ => ?_)
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 : ‖U a‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) (hU a)
      have h2 : ‖∑ b ∈ S, U b‖ ^ (l ^ e - k) ≤ 1 := pow_le_one₀ (norm_nonneg _) hV
      have h3 := IsUltrametricDist.norm_natCast_le_one K ((l ^ e).choose k / l)
      calc ‖U a‖ ^ k * ‖∑ b ∈ S, U b‖ ^ (l ^ e - k) * ‖(((l ^ e).choose k / l : ℕ) : K)‖
          ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by ring
    have heq : (U a + ∑ b ∈ S, U b) ^ (l ^ e) - (U a ^ (l ^ e) + ∑ b ∈ S, U b ^ (l ^ e)) =
        ((∑ b ∈ S, U b) ^ (l ^ e) - ∑ b ∈ S, U b ^ (l ^ e)) + (l : K) * R := by
      rw [hReq]; ring
    rw [heq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)
    rw [norm_mul]
    calc ‖(l : K)‖ * ‖R‖ ≤ ‖(l : K)‖ * 1 := by gcongr
      _ = ‖(l : K)‖ := mul_one _

/- English proof (translation)
Use `set A : Matrix (Fin J) (Fin J) K := Matrix.of fun (i i' : Fin J) => ∑ a, lam i a * y (e i') a with hA`. Set `c : Fin N0 → Fin J → K` to `fun k i => ∑ a, lam i a * y k a`. Establish `hc : ∀ k i, ‖c k i‖ ≤ 1` using `fun k i => IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun a _ => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hlam i a) (norm_nonneg _) (hy k a))`.

Establish `hAc : ∀ i i', A i i' = c (e i') i` using `fun _ _ => rfl`. Establish `hAint : ∀ i i', ‖A i i'‖ ≤ 1` using `fun i i' => hc _ _`. Establish `hAinv : ∀ i i', ‖A⁻¹ i i'‖ ≤ 1` using `norm_inv_entry_le_one A hAint hdet`. Establish `hne : A.det ≠ 0`. Introduce `h0`.

Rewrite `hdet` using `[h0, norm_zero]`. Conclude with `zero_ne_one hdet`. Establish `hunit : IsUnit A.det` using `isUnit_iff_ne_zero.mpr hne`. Set `z : Fin J → Fin N0 → K` to `fun i' a => ∑ i'', A⁻¹ i'' i' * y (e i'') a`. Establish `hz : ∀ i a, ‖z i a‖ ≤ 1` using `fun i a => IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i'' _ => by`.

Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hAinv _ _) (norm_nonneg _) (hy _ _))`. Establish `hcz : ∀ k a, ‖∑ i', c k i' * z i' a‖ ≤ 1` using `fun k a => IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i' _ => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hc _ _) (norm_nonneg _) (hz _ _))`.

Establish `hlz : ∀ i i', ∑ a, lam i a * z i' a = if i = i' then 1 else 0`. Introduce `i i'`. Establish `h1 : ∑ a, lam i a * z i' a = ∑ i'', A i i'' * A⁻¹ i'' i'`. Simplify using `only [z, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun i'' _ => ?_)` and prove the remaining obligations. Rewrite using `[hAc]`. Simplify using `only [c, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl (fun a _ => by ring)`. Rewrite using `[h1, ← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hunit, Matrix.one_apply]`.

Establish `hzy : ∀ i'' a, ∑ i', c (e i'') i' * z i' a = y (e i'') a`. Introduce `i'' a`. Establish `h1 : ∑ i', c (e i'') i' * z i' a = ∑ m, (∑ i', A⁻¹ m i' * A i' i'') * y (e m) a`. Simplify using `only [z, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun i' _ => ?_))` and prove the remaining obligations. Rewrite using `[hAc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Simplify using `only [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hunit, Matrix.one_apply]`.

Simplify using the standard rewrite rules. Set `x : Fin N0 → Fin N0 → K` to `fun k a => if top k then y k a else if h : ∃ i, e i = k then z h.choose a else y k a - ∑ i', c k i' * z i' a`. Set `T : Fin N0 → Fin N0 → K` to `fun i k => (if (∃ i', e i' = i) then 0 else if k = i then 1 else 0) + ∑ i', if k = e i' then c i i' else 0`. Establish `hxe : ∀ i a, x (e i) a = z i a`. Introduce `i a`.

Establish `hex : ∃ i', e i' = e i` using `⟨i, rfl⟩`. Establish `hch : hex.choose = i` using `he hex.choose_spec`. Simplify using `only [x]`. Rewrite using `[if_neg (htop i), dif_pos hex, hch]`. Establish `hxn : ∀ k a, ¬ top k → (¬ ∃ i, e i = k) → x k a = y k a - ∑ i', c k i' * z i' a`.

Introduce `k a h1 h2`. Simplify using `only [x]`. Rewrite using `[if_neg h1, dif_neg h2]`. Establish `hsumT : ∀ i k, (∑ i', if k = e i' then c i i' else 0) = 0 ∨ ∃ i', (∑ i', if k = e i' then c i i' else 0) = c i i'`. Introduce `i k`.

Distinguish the cases in `h : ∃ i', e i' = k`. Take `⟨i0, rfl⟩` from `h right`. Use `⟨i0, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i0]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Rewrite using `[if_neg (fun h => hb (he h).symm)]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `left`.

Use `Finset.sum_eq_zero (fun i' _ => ?_)` and prove the remaining obligations. Rewrite using `[if_neg (fun hk => h ⟨i', hk.symm⟩)]`. Use `⟨x, T, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k a`. Distinguish the cases in `h1 : top k`.

Simplify using `only [x]`. Rewrite using `[if_pos h1]`. Conclude with `hy _ _`. Distinguish the cases in `h2 : ∃ i, e i = k`. Take `⟨i, rfl⟩` from `h2`.

Rewrite using `[hxe]`. Conclude with `hz _ _`. Rewrite using `[hxn k a h1 h2, sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy _ _) ?_)` and prove the remaining obligations. Rewrite using `[norm_neg]`.

Conclude with `hcz _ _`. Introduce `i k`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Break down `hsumT i k with h | ⟨i', h⟩` into its components or cases.

Rewrite using `[h]`. Simplify using the standard rewrite rules. Rewrite using `[h]`. Conclude with `hc _ _`. Introduce `k a h1`.

Simplify using `only [x]`. Rewrite using `[if_pos h1]`. Introduce `i a hi`. Establish `hT0 : ∀ k, (if top k then 0 else T i k) = T i k`. Introduce `k`.

Use `split_ifs with hk`. Use `symm`. Establish `h1 : k ≠ i` using `fun h => hi (h ▸ hk)`. Establish `h2 : (∑ i', if k = e i' then c i i' else 0) = 0` using `Finset.sum_eq_zero (fun i' _ => by`. Rewrite using `[if_neg (fun h : k = e i' => htop i' (h ▸ hk))])`.

Simplify using `only [T]`. Rewrite using `[h2, if_neg h1]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Simplify using `only [hT0]`.

Establish `hsecond : ∑ k, (∑ i', if k = e i' then c i i' else 0) * x k a = ∑ i', c i i' * z i' a`. Simplify using `only [Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun i' _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (e i')]`.

Rewrite using `[if_pos rfl, hxe]`. Introduce `b _ hb`. Rewrite using `[if_neg hb, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Simplify using `only [T, add_mul, Finset.sum_add_distrib]`. Rewrite using `[hsecond]`. Distinguish the cases in `h2 : ∃ i', e i' = i`. Simplify using `only [if_pos h2, zero_mul, Finset.sum_const_zero, zero_add]`. Take `⟨i0, rfl⟩` from `h2`.

Conclude with `(hzy i0 a).symm`. Simplify using `only [if_neg h2]`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[if_pos rfl, one_mul, hxn i a hi h2]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `b _ hb`. Rewrite using `[if_neg hb, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `i k hk hne'`.

Distinguish the cases in `h2 : ∃ i', e i' = k`. Take `⟨i0, rfl⟩` from `h2`. Simplify using `only [hxe]`. Rewrite using `[hlz, if_neg (fun h : i = i0 => hne' (h ▸ rfl))]`. Simplify using `only [hxn k _ hk h2, mul_sub, Finset.sum_sub_distrib]`.

Establish `h3 : ∑ a, lam i a * ∑ i', c k i' * z i' a = ∑ i', c k i' * ∑ a, lam i a * z i' a`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun a _ => by ring))`. Rewrite using `[h3]`.

Simplify using `only [hlz]`. Simplify using `[c]`.
-/
theorem frameA_letter {K : Type u} [NormedField K] [IsUltrametricDist K] (J N0 : ℕ)
    (lam : Fin J → Fin N0 → K) (y : Fin N0 → Fin N0 → K) (hlam : ∀ i a, ‖lam i a‖ ≤ 1)
    (hy : ∀ k a, ‖y k a‖ ≤ 1) (e : Fin J → Fin N0) (he : Function.Injective e)
    (top : Fin N0 → Prop) [DecidablePred top] (htop : ∀ i, ¬ top (e i))
    (hdet : ‖(Matrix.of fun (i i' : Fin J) => ∑ a, lam i a * y (e i') a).det‖ = 1) :
    ∃ (x T : Fin N0 → Fin N0 → K), (∀ k a, ‖x k a‖ ≤ 1) ∧ (∀ i k, ‖T i k‖ ≤ 1) ∧
      (∀ k a, top k → x k a = y k a) ∧
      (∀ i a, ¬ top i → y i a = ∑ k, (if top k then 0 else T i k) * x k a) ∧
      (∀ i k, ¬ top k → k ≠ e i → ∑ a, lam i a * x k a = 0) := by
  classical
  set A : Matrix (Fin J) (Fin J) K := Matrix.of fun (i i' : Fin J) => ∑ a, lam i a * y (e i') a
    with hA
  let c : Fin N0 → Fin J → K := fun k i => ∑ a, lam i a * y k a
  have hc : ∀ k i, ‖c k i‖ ≤ 1 := fun k i =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun a _ => by
      rw [norm_mul]; exact mul_le_one₀ (hlam i a) (norm_nonneg _) (hy k a))
  have hAc : ∀ i i', A i i' = c (e i') i := fun _ _ => rfl
  have hAint : ∀ i i', ‖A i i'‖ ≤ 1 := fun i i' => hc _ _
  have hAinv : ∀ i i', ‖A⁻¹ i i'‖ ≤ 1 := norm_inv_entry_le_one A hAint hdet
  have hne : A.det ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hdet; exact zero_ne_one hdet
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hne
  let z : Fin J → Fin N0 → K := fun i' a => ∑ i'', A⁻¹ i'' i' * y (e i'') a
  have hz : ∀ i a, ‖z i a‖ ≤ 1 := fun i a =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i'' _ => by
      rw [norm_mul]; exact mul_le_one₀ (hAinv _ _) (norm_nonneg _) (hy _ _))
  have hcz : ∀ k a, ‖∑ i', c k i' * z i' a‖ ≤ 1 := fun k a =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i' _ => by
      rw [norm_mul]; exact mul_le_one₀ (hc _ _) (norm_nonneg _) (hz _ _))

  have hlz : ∀ i i', ∑ a, lam i a * z i' a = if i = i' then 1 else 0 := by
    intro i i'
    have h1 : ∑ a, lam i a * z i' a = ∑ i'', A i i'' * A⁻¹ i'' i' := by
      simp only [z, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i'' _ => ?_)
      rw [hAc]
      simp only [c, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [h1, ← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hunit, Matrix.one_apply]

  have hzy : ∀ i'' a, ∑ i', c (e i'') i' * z i' a = y (e i'') a := by
    intro i'' a
    have h1 : ∑ i', c (e i'') i' * z i' a = ∑ m, (∑ i', A⁻¹ m i' * A i' i'') * y (e m) a := by
      simp only [z, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun i' _ => ?_))
      rw [hAc]; ring
    rw [h1]
    simp only [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hunit, Matrix.one_apply]
    simp
  let x : Fin N0 → Fin N0 → K := fun k a =>
    if top k then y k a else if h : ∃ i, e i = k then z h.choose a
      else y k a - ∑ i', c k i' * z i' a
  let T : Fin N0 → Fin N0 → K := fun i k =>
    (if (∃ i', e i' = i) then 0 else if k = i then 1 else 0) + ∑ i', if k = e i' then c i i' else 0
  have hxe : ∀ i a, x (e i) a = z i a := by
    intro i a
    have hex : ∃ i', e i' = e i := ⟨i, rfl⟩
    have hch : hex.choose = i := he hex.choose_spec
    simp only [x]
    rw [if_neg (htop i), dif_pos hex, hch]
  have hxn : ∀ k a, ¬ top k → (¬ ∃ i, e i = k) → x k a = y k a - ∑ i', c k i' * z i' a := by
    intro k a h1 h2
    simp only [x]
    rw [if_neg h1, dif_neg h2]
  have hsumT : ∀ i k, (∑ i', if k = e i' then c i i' else 0) = 0 ∨
      ∃ i', (∑ i', if k = e i' then c i i' else 0) = c i i' := by
    intro i k
    by_cases h : ∃ i', e i' = k
    · obtain ⟨i0, rfl⟩ := h
      right
      refine ⟨i0, ?_⟩
      rw [Finset.sum_eq_single i0]
      · simp
      · intro b _ hb
        rw [if_neg (fun h => hb (he h).symm)]
      · intro h; exact absurd (Finset.mem_univ _) h
    · left
      refine Finset.sum_eq_zero (fun i' _ => ?_)
      rw [if_neg (fun hk => h ⟨i', hk.symm⟩)]
  refine ⟨x, T, ?_, ?_, ?_, ?_, ?_⟩
  · intro k a
    by_cases h1 : top k
    · simp only [x]; rw [if_pos h1]; exact hy _ _
    · by_cases h2 : ∃ i, e i = k
      · obtain ⟨i, rfl⟩ := h2
        rw [hxe]; exact hz _ _
      · rw [hxn k a h1 h2, sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy _ _) ?_)
        rw [norm_neg]; exact hcz _ _
  · intro i k
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · split_ifs <;> simp
    · rcases hsumT i k with h | ⟨i', h⟩
      · rw [h]; simp
      · rw [h]; exact hc _ _
  · intro k a h1
    simp only [x]; rw [if_pos h1]
  · intro i a hi
    have hT0 : ∀ k, (if top k then 0 else T i k) = T i k := by
      intro k
      split_ifs with hk
      · symm
        have h1 : k ≠ i := fun h => hi (h ▸ hk)
        have h2 : (∑ i', if k = e i' then c i i' else 0) = 0 :=
          Finset.sum_eq_zero (fun i' _ => by
            rw [if_neg (fun h : k = e i' => htop i' (h ▸ hk))])
        simp only [T]
        rw [h2, if_neg h1]
        simp
      · rfl
    simp only [hT0]
    have hsecond : ∑ k, (∑ i', if k = e i' then c i i' else 0) * x k a = ∑ i', c i i' * z i' a := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i' _ => ?_)
      rw [Finset.sum_eq_single (e i')]
      · rw [if_pos rfl, hxe]
      · intro b _ hb
        rw [if_neg hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [T, add_mul, Finset.sum_add_distrib]
    rw [hsecond]
    by_cases h2 : ∃ i', e i' = i
    · simp only [if_pos h2, zero_mul, Finset.sum_const_zero, zero_add]
      obtain ⟨i0, rfl⟩ := h2
      exact (hzy i0 a).symm
    · simp only [if_neg h2]
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, one_mul, hxn i a hi h2]; ring
      · intro b _ hb
        rw [if_neg hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
  · intro i k hk hne'
    by_cases h2 : ∃ i', e i' = k
    · obtain ⟨i0, rfl⟩ := h2
      simp only [hxe]
      rw [hlz, if_neg (fun h : i = i0 => hne' (h ▸ rfl))]
    · simp only [hxn k _ hk h2, mul_sub, Finset.sum_sub_distrib]
      have h3 : ∑ a, lam i a * ∑ i', c k i' * z i' a = ∑ i', c k i' * ∑ a, lam i a * z i' a := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun a _ => by ring))
      rw [h3]
      simp only [hlz]
      simp [c]

/- English proof (translation)
Introduce `hGen K _ _ _ l d N0 N1 _ hl hl3 hd hde hlK h0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I xg hxg nu1 nu2 size hnu1 hnu2 hsize a ha hsa J lab hlabinj hlab lam hlam hlampos hlamneg e he hetop hdet`. Establish `hL` using `fun s : ZMod d => frameA_letter (J s) N0 (lam s) (fun k a => xg (s, k, a)) (hlam s) (fun k a => hxg _) (e s) (he s) (fun k => s ∈ TT ∧ k.val = 0) (hetop s) (hdet s)`. Use `choose xs T hxs hT hxtop hrec hdual using hL`. Set `x : ZMod d × Fin N0 × Fin N0 → K` to `fun y => xs y.1 y.2.1 y.2.2`. Set `spec : ZMod d × Fin N0 → Option (ZMod d × ℤ)` to `fun r => if h : ∃ i, e r.1 i = r.2 then some (lab r.1 h.choose) else none`.

Establish `hspec_e : ∀ s i, spec (s, e s i) = some (lab s i)`. Introduce `s i`. Establish `hex : ∃ i', e s i' = e s i` using `⟨i, rfl⟩`. Establish `hch : hex.choose = i` using `he s hex.choose_spec`. Use `show (if h : ∃ i', e s i' = e s i then some (lab s h.choose) else none) = _`.

Rewrite using `[dif_pos hex, hch]`. Establish `hspec_some : ∀ s k, spec (s, k) ≠ none → ∃ i, k = e s i`. Introduce `s k h`. Assume the negation of the conclusion as `hcon`. Apply `h` to reduce the goal to its premises.

Use `show (if h : ∃ i', e s i' = k then some (lab s h.choose) else none) = _`. Rewrite using `[dif_neg (fun ⟨i, hi⟩ => hcon ⟨i, hi.symm⟩)]`. Use `hGen K l d N0 N1 hl hl3 hd hde hlK h0 K0 hK0 ζ hζ be hbe x (fun y => hxs _ _ _) g hg0 hg U hU ε hε TT colN p hp hp1 I T hT xg ?_ nu1 nu2 size hnu1 hnu2 hsize a ha hsa spec ?_ ?_ ?_` and prove the remaining obligations. Introduce `s i b`. Distinguish the cases in `hi : s ∈ TT ∧ i.val = 0`.

Simplify using `only [effMat, if_pos hi]`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[if_pos rfl, one_mul]`. Conclude with `(hxtop s i b hi).symm`. Introduce `k _ hk`.

Rewrite using `[if_neg hk, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Simplify using `only [effMat, if_neg hi]`. Conclude with `hrec s i b hi`.

Introduce `s k s0 j hsp`. Take `⟨i, rfl⟩` from `hspec_some s k (by rw [hsp]; simp)`. Rewrite `hsp` using `[hspec_e]`. Establish `hlb : lab s i = (s0, j)` using `Option.some.inj hsp`. Take `⟨h1, h2, h3, h4, h5⟩` from `(hlab s s0 j).mp ⟨i, hlb⟩`.

Conclude with `⟨h1, h2, h3, hetop s i, h4, h5⟩`. Introduce and unpack `⟨s, k⟩ ⟨s', k'⟩ hne heq`. Take `⟨i, rfl⟩` from `hspec_some s k hne`. Take `⟨i', rfl⟩` from `hspec_some s' k' (by rw [← heq]; exact hne)`. Rewrite `heq` using `[hspec_e, hspec_e]`.

Establish `hlb : lab s i = lab s' i'` using `Option.some.inj heq`. Establish `e1` using `((hlab s (lab s i).1 (lab s i).2).mp ⟨i, rfl⟩).2.2.1`. Establish `e2` using `((hlab s' (lab s' i').1 (lab s' i').2).mp ⟨i', rfl⟩).2.2.1`. Establish `hss : s = s'` using `by rw [e1, e2, hlb]`. Substitute `hss` using the available equality.

Establish `hii : i = i'` using `hlabinj s hlb`. Rewrite using `[hii]`. Introduce `s0 hs0 s k j hk hj hs hpos hneg hsp`. Take `⟨i, hi⟩` from `(hlab s s0 j).mpr ⟨hs0, hj, hs, hpos, hneg⟩`. Establish `hki : k ≠ e s i`.

Introduce `h`. Apply `hsp` to reduce the goal to its premises. Rewrite using `[h, hspec_e, hi]`. Establish `hzero : ∑ b, lam s i b * xs s k b = 0` using `hdual s i k hk hki`. Establish `hx0 : ∀ b, x (s0, ⟨0, h0⟩, b) = xg (s0, ⟨0, h0⟩, b)` using `fun b => hxtop s0 ⟨0, h0⟩ b ⟨hs0, rfl⟩`.

Establish `hi1 : (lab s i).1 = s0` using `by rw [hi]`. Establish `hi2 : (lab s i).2 = j` using `by rw [hi]`. Use `split_ifs with hj0`. Establish `hjpos : 0 < j`. Break down `hj with ⟨m, hm⟩` into its components or cases.

Use linear arithmetic over natural numbers and integers. Establish `hl1 : ∀ b, x (s0, ⟨0, h0⟩, b) ^ (l ^ j.toNat) = lam s i b`. Introduce `b`. Use `hlampos s i b (by rw [hi2]; exact hjpos)` as an intermediate fact. Rewrite `this` using `[hi1, hi2]`.

Rewrite using `[this, hx0]`. Simplify using `only [hl1]`. Use `show ‖∑ b, lam s i b * xs s k b‖ ≤ _`. Rewrite using `[hzero, norm_zero]`. Conclude with `norm_nonneg _`.

Establish `hjneg : j < 0` using `not_le.mp hj0`. Establish `hl1 : ∀ b, x (s0, ⟨0, h0⟩, b) = lam s i b ^ (l ^ (-j).toNat)`. Introduce `b`. Use `hlamneg s i b (by rw [hi2]; exact hjneg)` as an intermediate fact. Rewrite `this` using `[hi1, hi2]`.

Rewrite using `[this, hx0]`. Establish `hfr` using `frameA_frob_norm (K := K) hl (fun b => lam s i b * xs s k b) (fun b => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hlam s i b) (norm_nonneg _) (hxs s k b)) (-j).toNat`. Use the proof step `Finset.univ`.

Rewrite `hfr` using `[hzero, zero_pow (pow_ne_zero _ hl.ne_zero), zero_sub, norm_neg]`. Simplify using `only [hl1]`. Use `show ‖∑ b, lam s i b ^ (l ^ (-j).toNat) * xs s k b ^ (l ^ (-j).toNat)‖ ≤ _`. Simplify `hfr` using `only [mul_pow]`.
-/
theorem thmAFrame_of : ThmAGen.{u} → ThmAFrame.{u} := by
  intro hGen K _ _ _ l d N0 N1 _ hl hl3 hd hde hlK h0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p
    hp hp1 I xg hxg nu1 nu2 size hnu1 hnu2 hsize a ha hsa J lab hlabinj hlab lam hlam hlampos hlamneg
    e he hetop hdet
  classical
  have hL := fun s : ZMod d => frameA_letter (J s) N0 (lam s) (fun k a => xg (s, k, a)) (hlam s)
    (fun k a => hxg _) (e s) (he s) (fun k => s ∈ TT ∧ k.val = 0) (hetop s) (hdet s)
  choose xs T hxs hT hxtop hrec hdual using hL
  let x : ZMod d × Fin N0 × Fin N0 → K := fun y => xs y.1 y.2.1 y.2.2
  let spec : ZMod d × Fin N0 → Option (ZMod d × ℤ) := fun r =>
    if h : ∃ i, e r.1 i = r.2 then some (lab r.1 h.choose) else none
  have hspec_e : ∀ s i, spec (s, e s i) = some (lab s i) := by
    intro s i
    have hex : ∃ i', e s i' = e s i := ⟨i, rfl⟩
    have hch : hex.choose = i := he s hex.choose_spec
    show (if h : ∃ i', e s i' = e s i then some (lab s h.choose) else none) = _
    rw [dif_pos hex, hch]
  have hspec_some : ∀ s k, spec (s, k) ≠ none → ∃ i, k = e s i := by
    intro s k h
    by_contra hcon
    apply h
    show (if h : ∃ i', e s i' = k then some (lab s h.choose) else none) = _
    rw [dif_neg (fun ⟨i, hi⟩ => hcon ⟨i, hi.symm⟩)]
  refine hGen K l d N0 N1 hl hl3 hd hde hlK h0 K0 hK0 ζ hζ be hbe x (fun y => hxs _ _ _) g hg0 hg U hU
    ε hε TT colN p hp hp1 I T hT xg ?_ nu1 nu2 size hnu1 hnu2 hsize a ha hsa spec ?_ ?_ ?_
  · intro s i b
    by_cases hi : s ∈ TT ∧ i.val = 0
    · simp only [effMat, if_pos hi]
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, one_mul]
        exact (hxtop s i b hi).symm
      · intro k _ hk
        rw [if_neg hk, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [effMat, if_neg hi]
      exact hrec s i b hi
  · intro s k s0 j hsp
    obtain ⟨i, rfl⟩ := hspec_some s k (by rw [hsp]; simp)
    rw [hspec_e] at hsp
    have hlb : lab s i = (s0, j) := Option.some.inj hsp
    obtain ⟨h1, h2, h3, h4, h5⟩ := (hlab s s0 j).mp ⟨i, hlb⟩
    exact ⟨h1, h2, h3, hetop s i, h4, h5⟩
  · rintro ⟨s, k⟩ ⟨s', k'⟩ hne heq
    obtain ⟨i, rfl⟩ := hspec_some s k hne
    obtain ⟨i', rfl⟩ := hspec_some s' k' (by rw [← heq]; exact hne)
    rw [hspec_e, hspec_e] at heq
    have hlb : lab s i = lab s' i' := Option.some.inj heq
    have e1 := ((hlab s (lab s i).1 (lab s i).2).mp ⟨i, rfl⟩).2.2.1
    have e2 := ((hlab s' (lab s' i').1 (lab s' i').2).mp ⟨i', rfl⟩).2.2.1
    have hss : s = s' := by rw [e1, e2, hlb]
    subst hss
    have hii : i = i' := hlabinj s hlb
    rw [hii]
  · intro s0 hs0 s k j hk hj hs hpos hneg hsp
    obtain ⟨i, hi⟩ := (hlab s s0 j).mpr ⟨hs0, hj, hs, hpos, hneg⟩
    have hki : k ≠ e s i := by
      intro h
      apply hsp
      rw [h, hspec_e, hi]
    have hzero : ∑ b, lam s i b * xs s k b = 0 := hdual s i k hk hki
    have hx0 : ∀ b, x (s0, ⟨0, h0⟩, b) = xg (s0, ⟨0, h0⟩, b) := fun b =>
      hxtop s0 ⟨0, h0⟩ b ⟨hs0, rfl⟩
    have hi1 : (lab s i).1 = s0 := by rw [hi]
    have hi2 : (lab s i).2 = j := by rw [hi]
    split_ifs with hj0
    · have hjpos : 0 < j := by
        rcases hj with ⟨m, hm⟩
        omega
      have hl1 : ∀ b, x (s0, ⟨0, h0⟩, b) ^ (l ^ j.toNat) = lam s i b := by
        intro b
        have := hlampos s i b (by rw [hi2]; exact hjpos)
        rw [hi1, hi2] at this
        rw [this, hx0]
      simp only [hl1]
      show ‖∑ b, lam s i b * xs s k b‖ ≤ _
      rw [hzero, norm_zero]
      exact norm_nonneg _
    · have hjneg : j < 0 := not_le.mp hj0
      have hl1 : ∀ b, x (s0, ⟨0, h0⟩, b) = lam s i b ^ (l ^ (-j).toNat) := by
        intro b
        have := hlamneg s i b (by rw [hi2]; exact hjneg)
        rw [hi1, hi2] at this
        rw [this, hx0]
      have hfr := frameA_frob_norm (K := K) hl (fun b => lam s i b * xs s k b) (fun b => by
        rw [norm_mul]; exact mul_le_one₀ (hlam s i b) (norm_nonneg _) (hxs s k b)) (-j).toNat
        Finset.univ
      rw [hzero, zero_pow (pow_ne_zero _ hl.ne_zero), zero_sub, norm_neg] at hfr
      simp only [hl1]
      show ‖∑ b, lam s i b ^ (l ^ (-j).toNat) * xs s k b ^ (l ^ (-j).toNat)‖ ≤ _
      simpa only [mul_pow] using hfr

/- English proof (translation)
The claim follows from `thmAFrame_of thmAGen`.
-/
theorem theorem_A_frame : ThmAFrame.{u} := thmAFrame_of thmAGen

end Formalism.DworkPowerSeriesWeights
