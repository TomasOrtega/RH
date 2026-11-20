import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingCoefficientFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeVandermondeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookFunctionalPowerSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookFunctionalPowerSumOtherStatement

noncomputable section
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula

namespace GlobalTheory.FlagHook.KapFormula

/- English proof (translation)
Simplify using `only [altCoeff, coeff_sum, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem altCoeff_sum {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (n : ι → Fin N → ℕ)
    {α : Type} (s : Finset α) (P : α → MvPolynomial (ι × Fin N) ℝ) :
    altCoeff n (∑ a ∈ s, P a) = ∑ a ∈ s, altCoeff n (P a) := by
  simp only [altCoeff, coeff_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/- English proof (translation)
Simplify using `only [hookFl, altCoeff_sum, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem hookFl_sum {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ : ι) (k : ℕ)
    {α : Type} (s : Finset α) (P : α → MvPolynomial (ι × Fin N) ℝ) :
    hookFl τ k (∑ a ∈ s, P a) = ∑ a ∈ s, hookFl τ k (P a) := by
  simp only [hookFl, altCoeff_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/- English proof (translation)
Unfold `rho`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun c => N - 1 - c) N, Finset.sum_range_reflect (fun c => c) N, Finset.sum_range_id]`.
-/
theorem sum_rho (N : ℕ) : ∑ c, rho N c = N * (N - 1) / 2 := by
  unfold rho
  rw [Fin.sum_univ_eq_sum_range (fun c => N - 1 - c) N, Finset.sum_range_reflect (fun c => c) N,
    Finset.sum_range_id]

/- English proof (translation)
The claim follows from `| 0 => by simp | N + 1 => by rw [Finset.sum_range_succ, sum_hook_indicator a r N] simp only [Nat.succ_ne_zero, if_false] split_ifs <;> omega`.
-/
theorem sum_hook_indicator (a r : ℕ) : ∀ N : ℕ,
    ∑ c ∈ range (N + 1), (if c = 0 then a else if c ≤ r then 1 else 0) = a + min N r
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ, sum_hook_indicator a r N]
    simp only [Nat.succ_ne_zero, if_false]
    split_ifs <;> omega

/- English proof (translation)
Establish `h1` using `sum_rho N`. Unfold `rho at h1`. Unfold `hookRho`. Rewrite using `[Finset.sum_add_distrib, h1, Fin.sum_univ_eq_sum_range (fun c => if c = 0 then k - r else if c ≤ r then 1 else 0) N]`. Take `⟨M, rfl⟩ : ∃ M, N = M + 1` from `⟨N - 1, by omega⟩`.

Rewrite using `[sum_hook_indicator]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_hookRho (N k r : ℕ) (hr : r < k) (hk : k ≤ N) :
    ∑ c, hookRho N k r c = N * (N - 1) / 2 + k := by
  have h1 := sum_rho N
  unfold rho at h1
  unfold hookRho
  rw [Finset.sum_add_distrib, h1,
    Fin.sum_univ_eq_sum_range (fun c => if c = 0 then k - r else if c ≤ r then 1 else 0) N]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [sum_hook_indicator]
  omega

/- English proof (translation)
Establish `: ∀ t : ι, ∑ c, (if t = τ then hookRho N k r else rho N) c = N * (N - 1) / 2 + if t = τ then k else 0`. Introduce `t`. Use `split_ifs`. Conclude with `sum_hookRho N k r hr hk`. Simplify using `using sum_rho N`.

Simplify using `only [this, Finset.sum_add_distrib]`. Simplify using `[dimFl]`.
-/
theorem sum_exp {ι : Type} [Fintype ι] [DecidableEq ι] (N k r : ℕ) (τ : ι) (hr : r < k)
    (hk : k ≤ N) :
    ∑ t : ι, ∑ c, (if t = τ then hookRho N k r else rho N) c = dimFl ι N + k := by
  have : ∀ t : ι, ∑ c, (if t = τ then hookRho N k r else rho N) c
      = N * (N - 1) / 2 + if t = τ then k else 0 := by
    intro t
    split_ifs
    · exact sum_hookRho N k r hr hk
    · simpa using sum_rho N
  simp only [this, Finset.sum_add_distrib]
  simp [dimFl]

/- English proof (translation)
Establish `hc : 1 ≤ Fintype.card ι` using `Fintype.card_pos_iff.mpr ⟨τ⟩`. Establish `h2 : N - 1 ≤ N * (N - 1) / 2`. Break down `Nat.lt_or_ge N 2 with h | h` into its components or cases. Use linear arithmetic over natural numbers and integers. Rewrite using `[Nat.le_div_iff_mul_le (by norm_num), mul_comm]`.

Conclude with `Nat.mul_le_mul_right _ h`. Establish `h3 : N * (N - 1) / 2 ≤ dimFl ι N` using `Nat.le_mul_of_pos_left _ hc`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_dimFl {ι : Type} [Fintype ι] (τ : ι) (N k : ℕ) (hk : k ≤ N) : k ≤ dimFl ι N + 1 := by
  have hc : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨τ⟩
  have h2 : N - 1 ≤ N * (N - 1) / 2 := by
    rcases Nat.lt_or_ge N 2 with h | h
    · omega
    · rw [Nat.le_div_iff_mul_le (by norm_num), mul_comm]
      exact Nat.mul_le_mul_right _ h
  have h3 : N * (N - 1) / 2 ≤ dimFl ι N := Nat.le_mul_of_pos_left _ hc
  omega

/- English proof (translation)
Establish `: ∀ m : ℕ, (pderiv i)^[m] (hookR N k) = ∑ r ∈ range k, C ((-1 : ℝ) ^ r) * (pderiv i)^[m] (detE (hookRho N k r))`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => rfl`. Consider the case `succ m ih`.

Simplify using `only [Function.iterate_succ_apply', ih, map_sum, pderiv_C_mul]`. Rewrite using `[this, map_sum]`. Simplify using `only [map_mul, eval_C]`.
-/
theorem iter_pderiv_hookR (N k m : ℕ) (i : Fin N) (v : Fin N → ℝ) :
    eval v ((pderiv i)^[m] (hookR N k))
      = ∑ r ∈ range k, (-1 : ℝ) ^ r * eval v ((pderiv i)^[m] (detE (hookRho N k r))) := by
  have : ∀ m : ℕ, (pderiv i)^[m] (hookR N k)
      = ∑ r ∈ range k, C ((-1 : ℝ) ^ r) * (pderiv i)^[m] (detE (hookRho N k r)) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [Function.iterate_succ_apply', ih, map_sum, pderiv_C_mul]
  rw [this, map_sum]
  simp only [map_mul, eval_C]

/- English proof (translation)
Rewrite using `[GlobalTheory.T.flag_degree_vandermonde.2]`. Use `div_ne_zero ?_ ?_` and prove the remaining obligations. Use `Finset.prod_ne_zero_iff.mpr fun a _ => Finset.prod_ne_zero_iff.mpr fun b hb => ?_` and prove the remaining obligations. Conclude with `sub_ne_zero.mpr (hv a b (ne_of_lt (Finset.mem_Ioi.mp hb)))`. Conclude with `Finset.prod_ne_zero_iff.mpr fun m _ => by exact_mod_cast m.factorial_ne_zero`.
-/
theorem eval_detE_rho_ne_zero (N : ℕ) (v : Fin N → ℝ) (hv : ∀ a b, a ≠ b → v a ≠ v b) :
    eval v (detE (rho N)) ≠ 0 := by
  rw [GlobalTheory.T.flag_degree_vandermonde.2]
  refine div_ne_zero ?_ ?_
  · refine Finset.prod_ne_zero_iff.mpr fun a _ => Finset.prod_ne_zero_iff.mpr fun b hb => ?_
    exact sub_ne_zero.mpr (hv a b (ne_of_lt (Finset.mem_Ioi.mp hb)))
  · exact Finset.prod_ne_zero_iff.mpr fun m _ => by exact_mod_cast m.factorial_ne_zero

/- English proof (translation)
Establish `hh : (γ * Q τ k).IsHomogeneous (dimFl ι N)`. Use `hγ.mul (hQ.1 τ k h1 hk)` as an intermediate fact. Establish `e : k - 1 + (dimFl ι N + 1 - k) = dimFl ι N`. Use `le_dimFl τ N k hk` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Rewrite using `[hQ.2]`. Simplify using `only [Finset.mul_sum, hookFl_sum, mul_left_comm γ]`. Rewrite using `[Finset.sum_eq_single τ, Finset.sum_eq_single k]`. Conclude with `(GlobalTheory.T.hook_functional_power_sum ι N τ k _ h1 hk hh).symm`.

Introduce `k' hk' hne`. Conclude with `GlobalTheory.T.hook_functional_power_sum_other ι N τ τ k k' _ h1 hk (Finset.mem_Icc.mp hk').1 (by simpa using hne)`. Introduce `h`. Conclude with `absurd (Finset.mem_Icc.mpr ⟨h1, hk⟩) h`. Introduce `t _ hne`.

Use `Finset.sum_eq_zero fun k' hk' => ?_` and prove the remaining obligations. Conclude with `GlobalTheory.T.hook_functional_power_sum_other ι N τ t k k' _ h1 hk (Finset.mem_Icc.mp hk').1 (by simp [hne])`. Simplify using the standard rewrite rules.
-/
theorem degFl_eq_hookFl {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (u : ι → Fin N → ℝ)
    (Q : ι → ℕ → MvPolynomial (ι × Fin N) ℝ) (hQ : IsDecomp u Q) (τ : ι) (k : ℕ) (h1 : 1 ≤ k)
    (hk : k ≤ N) (γ : MvPolynomial (ι × Fin N) ℝ) (hγ : γ.IsHomogeneous (k - 1)) :
    degFl ι N (γ * Q τ k) = hookFl τ k (γ * linRoot u ^ (dimFl ι N + 1)) := by
  have hh : (γ * Q τ k).IsHomogeneous (dimFl ι N) := by
    have := hγ.mul (hQ.1 τ k h1 hk)
    have e : k - 1 + (dimFl ι N + 1 - k) = dimFl ι N := by
      have := le_dimFl τ N k hk
      omega
    rwa [e] at this
  rw [hQ.2]
  simp only [Finset.mul_sum, hookFl_sum, mul_left_comm γ]
  rw [Finset.sum_eq_single τ, Finset.sum_eq_single k]
  · exact (GlobalTheory.T.hook_functional_power_sum ι N τ k _ h1 hk hh).symm
  · intro k' hk' hne
    exact GlobalTheory.T.hook_functional_power_sum_other ι N τ τ k k' _ h1 hk (Finset.mem_Icc.mp hk').1 (by simpa using hne)
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨h1, hk⟩) h
  · intro t _ hne
    refine Finset.sum_eq_zero fun k' hk' => ?_
    exact GlobalTheory.T.hook_functional_power_sum_other ι N τ t k k' _ h1 hk (Finset.mem_Icc.mp hk').1 (by simp [hne])
  · simp

/- English proof (translation)
Introduce `ι _ _ N u Q hu hQ τ τ' i k h1 hk`. Establish `hE : ∀ t, eval (u t) (detE (rho N)) ≠ 0` using `fun t => eval_detE_rho_ne_zero N _ (hu t)`. Establish `hγ : (X (τ', i) ^ (k - 1) : MvPolynomial (ι × Fin N) ℝ).IsHomogeneous (k - 1)`. Simplify using `using (isHomogeneous_X ℝ (τ', i)).pow (k - 1)`. Establish `hk0 : (k : ℝ) ≠ 0` using `by exact_mod_cast (by omega : k ≠ 0)`.

Establish `hD : ((dimFl ι N).factorial : ℝ) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero _`. Establish `hD1 : ((dimFl ι N : ℝ) + 1) ≠ 0` using `by positivity`. Establish `hsign : (-1 : ℝ) ^ (dimFl ι N + (dimFl ι N + 1)) = -1`. Rewrite using `[← add_assoc, pow_succ, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.

Establish `hfac : (((dimFl ι N + 1).factorial : ℕ) : ℝ) = ((dimFl ι N : ℝ) + 1) * (dimFl ι N).factorial`. Rewrite using `[Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hterm : ∀ r ∈ range k, (-1 : ℝ) ^ r * altCoeff (fun t => if t = τ then hookRho N k r else rho N) (X (τ', i) ^ (k - 1) * linRoot u ^ (dimFl ι N + 1)) = -(((dimFl ι N : ℝ) + 1) * (dimFl ι N).factorial) * ((-1 : ℝ) ^ r * (eval (u τ') ((pderiv i)^[k - 1] (detE (if τ' = τ then hookRho …`.

Introduce `r hr`. Rewrite using `[GlobalTheory.T.alternating_coefficient_formula ι N _ u τ' i (k - 1) (dimFl ι N + 1) (by rw [sum_exp N k r τ (Finset.mem_range.mp hr) hk]; omega), hsign, hfac]`. Expand and normalize the polynomial expressions, which then agree. Unfold `kap`. Rewrite using `[degFl_eq_hookFl u Q hQ τ k h1 hk _ hγ, GlobalTheory.T.flag_degree_vandermonde.1, hookFl, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.mul_prod_erase univ _ (Finset.mem_univ τ')]`.

Distinguish the cases in `h : τ' = τ`. Substitute `h` using the available equality. Establish `hP : ∀ r, ∏ t ∈ univ.erase τ', eval (u t) (detE (if t = τ' then hookRho N k r else rho N)) = ∏ t ∈ univ.erase τ', eval (u t) (detE (rho N))` using `fun r => Finset.prod_congr rfl fun t ht => by rw [if_neg (Finset.ne_of_mem_erase ht)]`. Establish `hP0 : ∏ t ∈ univ.erase τ', eval (u t) (detE (rho N)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun t _ => hE t`. Simplify using `only [hP, if_true, ← mul_assoc, ← Finset.sum_mul, ← iter_pderiv_hookR]`.

Use `hE τ'` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Establish `hmem : τ ∈ univ.erase τ'` using `Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ _⟩`. Establish `hP : ∀ r, ∏ t ∈ univ.erase τ', eval (u t) (detE (if t = τ then hookRho N k r else rho N)) = eval (u τ) (detE (hookRho N k r)) * ∏ t ∈ (univ.erase τ').erase τ, eval (u t) (detE (rho N))` using `fun r => by`. Rewrite using `[← Finset.mul_prod_erase _ _ hmem, if_pos rfl]`.

Use `congr 1`. Conclude with `Finset.prod_congr rfl fun t ht => by rw [if_neg (Finset.ne_of_mem_erase ht)]`. Establish `hP0 : ∏ t ∈ (univ.erase τ').erase τ, eval (u t) (detE (rho N)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun t _ => hE t`. Establish `hR` using `iter_pderiv_hookR N k 0 i (u τ)`. Simplify using `only [Function.iterate_zero, id] at hR`.

Establish `hS : ∑ r ∈ range k, (-1 : ℝ) ^ r * (eval (u τ') ((pderiv i)^[k - 1] (detE (if τ' = τ then hookRho N k r else rho N))) * ∏ t ∈ univ.erase τ', eval (u t) (detE (if t = τ then hookRho N k r else rho N))) = eval (u τ) (hookR N k) * (eval (u τ') ((pderiv i)^[k - 1] (detE (rho N))) * ∏ …`. Rewrite using `[hR, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[hP, if_neg h]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hS, if_neg h, ← Finset.mul_prod_erase _ (fun t => eval (u t) (detE (rho N))) hmem]`. Use `hE τ'` as an intermediate fact. Use `hE τ` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem kap_formula : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (u : ι → Fin N → ℝ) (Q : ι → ℕ → MvPolynomial (ι × Fin N) ℝ), (∀ τ a b, a ≠ b → u τ a ≠ u τ b) → IsDecomp u Q → ∀ (τ τ' : ι) (i : Fin N) (k : ℕ), 1 ≤ k → k ≤ N → kap u k (X (τ', i) ^ (k - 1)) (Q τ k) = if τ' = τ then -(eval (u τ) ((pderiv i)^[k - 1] (hookR N k)) / eval (u τ) (detE (rho N))) else -(eval (u τ) (hookR N k) / eval (u τ) (detE (rho N)) * (eval (u τ') ((pderiv i)^[k - 1] (detE (rho N))) / eval (u τ') (detE (rho N)))) := by
  intro ι _ _ N u Q hu hQ τ τ' i k h1 hk
  have hE : ∀ t, eval (u t) (detE (rho N)) ≠ 0 := fun t => eval_detE_rho_ne_zero N _ (hu t)
  have hγ : (X (τ', i) ^ (k - 1) : MvPolynomial (ι × Fin N) ℝ).IsHomogeneous (k - 1) := by
    simpa using (isHomogeneous_X ℝ (τ', i)).pow (k - 1)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hD : ((dimFl ι N).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hD1 : ((dimFl ι N : ℝ) + 1) ≠ 0 := by positivity
  have hsign : (-1 : ℝ) ^ (dimFl ι N + (dimFl ι N + 1)) = -1 := by
    rw [← add_assoc, pow_succ, ← two_mul, pow_mul]; simp
  have hfac : (((dimFl ι N + 1).factorial : ℕ) : ℝ)
      = ((dimFl ι N : ℝ) + 1) * (dimFl ι N).factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hterm : ∀ r ∈ range k, (-1 : ℝ) ^ r *
      altCoeff (fun t => if t = τ then hookRho N k r else rho N)
        (X (τ', i) ^ (k - 1) * linRoot u ^ (dimFl ι N + 1))
      = -(((dimFl ι N : ℝ) + 1) * (dimFl ι N).factorial) * ((-1 : ℝ) ^ r *
        (eval (u τ') ((pderiv i)^[k - 1] (detE (if τ' = τ then hookRho N k r else rho N))) *
          ∏ t ∈ univ.erase τ', eval (u t) (detE (if t = τ then hookRho N k r else rho N)))) := by
    intro r hr
    rw [GlobalTheory.T.alternating_coefficient_formula ι N _ u τ' i (k - 1) (dimFl ι N + 1)
      (by rw [sum_exp N k r τ (Finset.mem_range.mp hr) hk]; omega), hsign, hfac]
    ring
  unfold kap
  rw [degFl_eq_hookFl u Q hQ τ k h1 hk _ hγ, GlobalTheory.T.flag_degree_vandermonde.1, hookFl, Finset.sum_congr rfl hterm,
    ← Finset.mul_sum, ← Finset.mul_prod_erase univ _ (Finset.mem_univ τ')]
  by_cases h : τ' = τ
  · subst h
    have hP : ∀ r, ∏ t ∈ univ.erase τ', eval (u t) (detE (if t = τ' then hookRho N k r else rho N))
        = ∏ t ∈ univ.erase τ', eval (u t) (detE (rho N)) := fun r =>
      Finset.prod_congr rfl fun t ht => by rw [if_neg (Finset.ne_of_mem_erase ht)]
    have hP0 : ∏ t ∈ univ.erase τ', eval (u t) (detE (rho N)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun t _ => hE t
    simp only [hP, if_true, ← mul_assoc, ← Finset.sum_mul, ← iter_pderiv_hookR]
    have := hE τ'
    field_simp
  · have hmem : τ ∈ univ.erase τ' := Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ _⟩
    have hP : ∀ r, ∏ t ∈ univ.erase τ', eval (u t) (detE (if t = τ then hookRho N k r else rho N))
        = eval (u τ) (detE (hookRho N k r)) *
          ∏ t ∈ (univ.erase τ').erase τ, eval (u t) (detE (rho N)) := fun r => by
      rw [← Finset.mul_prod_erase _ _ hmem, if_pos rfl]
      congr 1
      exact Finset.prod_congr rfl fun t ht => by rw [if_neg (Finset.ne_of_mem_erase ht)]
    have hP0 : ∏ t ∈ (univ.erase τ').erase τ, eval (u t) (detE (rho N)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun t _ => hE t
    have hR := iter_pderiv_hookR N k 0 i (u τ)
    simp only [Function.iterate_zero, id] at hR
    have hS : ∑ r ∈ range k, (-1 : ℝ) ^ r *
        (eval (u τ') ((pderiv i)^[k - 1] (detE (if τ' = τ then hookRho N k r else rho N))) *
          ∏ t ∈ univ.erase τ', eval (u t) (detE (if t = τ then hookRho N k r else rho N)))
        = eval (u τ) (hookR N k) * (eval (u τ') ((pderiv i)^[k - 1] (detE (rho N))) *
          ∏ t ∈ (univ.erase τ').erase τ, eval (u t) (detE (rho N))) := by
      rw [hR, Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hP, if_neg h]
      ring
    rw [hS, if_neg h, ← Finset.mul_prod_erase _ (fun t => eval (u t) (detE (rho N))) hmem]
    have := hE τ'
    have := hE τ
    field_simp

end GlobalTheory.FlagHook.KapFormula
