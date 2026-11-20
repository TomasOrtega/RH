import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AllCuspidalOpenBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentEigenvalueSumFormula
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt

noncomputable section

namespace UpperTheory.GalN

open GlobalTheory

/- English proof (translation)
Establish `hq1 : (1 : ℝ) < q` using `by exact_mod_cast hq`. Establish `hq0 : (0 : ℝ) < q` using `by linarith`. Establish `e2 : ‖α‖ = (q : ℝ) ^ (y - x)`. Rewrite using `[Real.rpow_sub hq0, ← e, mul_div_assoc, div_self (Real.rpow_pos_of_pos hq0 x).ne', mul_one]`. Take `⟨h1, h2⟩` from `h`.

Rewrite `h1`, `h2` using `[e2, Real.rpow_lt_rpow_left_iff hq1, hm]`. Establish `a1 : (-1 : ℤ) < m`. Establish `: ((-1 : ℤ) : ℝ) < m` using `by push_cast; linarith`. Conclude with `this` after adjusting the coercions. Establish `a2 : m < 1`.

Establish `: (m : ℝ) < ((1 : ℤ) : ℝ)` using `by push_cast; linarith`. Conclude with `this` after adjusting the coercions. Establish `: m = 0` using `by omega`. Rewrite `hm` using `[this]`. Simplify using `at hm`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem OpenB.exp_eq {q : ℕ} {α : ℂ} (h : OpenB q α) (hq : 1 < q) {x y : ℝ} (e : ‖α‖ * (q : ℝ) ^ x = (q : ℝ) ^ y)
    (m : ℤ) (hm : y - x = (m : ℝ) / 2) : x = y := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have e2 : ‖α‖ = (q : ℝ) ^ (y - x) := by
    rw [Real.rpow_sub hq0, ← e, mul_div_assoc, div_self (Real.rpow_pos_of_pos hq0 x).ne', mul_one]
  obtain ⟨h1, h2⟩ := h
  rw [e2, Real.rpow_lt_rpow_left_iff hq1, hm] at h1 h2
  have a1 : (-1 : ℤ) < m := by
    have : ((-1 : ℤ) : ℝ) < m := by push_cast; linarith
    exact_mod_cast this
  have a2 : m < 1 := by
    have : (m : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have : m = 0 := by omega
  rw [this] at hm
  simp at hm
  linarith

/- English proof (translation)
Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast (by omega : 0 < q)`. Establish `hp : (0 : ℝ) < (q : ℝ) ^ (1 / 2 : ℝ)` using `Real.rpow_pos_of_pos hq0 _`. Take `⟨h1, h2⟩` from `h`. Rewrite `h1` using `[Real.rpow_neg hq0.le]`. Establish `h0 : 0 < ‖α‖` using `(inv_pos.2 hp).trans h1`.

Rewrite using `[OpenB, norm_inv, Real.rpow_neg hq0.le]`. Conclude with `⟨(inv_lt_inv₀ hp h0).2 h2, (inv_lt_comm₀ h0 hp).2 h1⟩`.
-/
theorem OpenB.inv {q : ℕ} {α : ℂ} (h : OpenB q α) (hq : 1 < q) : OpenB q α⁻¹ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hp : (0 : ℝ) < (q : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hq0 _
  obtain ⟨h1, h2⟩ := h
  rw [Real.rpow_neg hq0.le] at h1
  have h0 : 0 < ‖α‖ := (inv_pos.2 hp).trans h1
  rw [OpenB, norm_inv, Real.rpow_neg hq0.le]
  exact ⟨(inv_lt_inv₀ hp h0).2 h2, (inv_lt_comm₀ h0 hp).2 h1⟩

/- English proof (translation)
The claim follows from `h.2.le.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq.le) hx)`.
-/
theorem OpenB.le_rpow {q : ℕ} {α : ℂ} (h : OpenB q α) (hq : 1 < q) {x : ℝ} (hx : 1 / 2 ≤ x) : ‖α‖ ≤ (q : ℝ) ^ x :=
  h.2.le.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq.le) hx)

/- English proof (translation)
Introduce `q t L Rw c hq ht hc hRw hL hsum`. Establish `hq0 : 0 < q` using `by omega`. Establish `hq1 : (1:ℝ) < q` using `by exact_mod_cast hq`. Establish `nm : ∀ s : ℝ, ‖(q : ℂ) ^ ((s : ℝ) : ℂ)‖ = (q : ℝ) ^ s` using `norm_natCast_cpow_ofReal hq0`. Establish `Pne : ∀ s : ℝ, (q : ℂ) ^ ((s : ℝ) : ℂ) ≠ 0`.

Introduce `s h0`. Establish `h` using `nm s`. Rewrite `h` using `[h0, norm_zero]`. Conclude with `(Real.rpow_pos_of_pos (by positivity) s).ne' h.symm`. Simplify using `only [bind_pure_comp, List.map_eq_map, List.map_map, Function.comp_def] at hsum`.

Take `⟨n, rfl⟩ : ∃ n, t = n + 1` from `⟨t - 1, by omega⟩`. Establish `hright : ((List.range (n+1)).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - (k : ℝ) : ℝ) : ℂ)} : Multiset ℂ)).sum = {c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ …`. Rewrite using `[List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]`. Use `congr 2`. Simplify using the standard rewrite rules.

Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `k _`. Simplify using the standard rewrite rules. Rewrite `hsum` using `[hright]`. Establish `hsmall : ∀ x ∈ Rw + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum, ‖x‖ < (q : ℝ) ^ ((((n+1:ℕ) : ℝ) - 1) / 2)`.

Introduce `x hx`. Break down `Multiset.mem_add.1 hx with hx | hx` into its components or cases. Conclude with `hRw x hx`. Take `⟨m, hm, hxm⟩` from `(multiset_mem_list_sum' _ _).1 hx`. Take `⟨k, _, rfl⟩` from `List.mem_map.1 hm`.

Rewrite `hxm` using `[Multiset.mem_singleton]`. Substitute `hxm` using the available equality. Rewrite using `[norm_mul, hc, nm, one_mul]`. Conclude with `Real.rpow_lt_rpow_of_exponent_lt hq1 (by have := Nat.cast_nonneg (α := ℝ) k; linarith)`. Establish `hsum' : (L.map fun e => ((List.range e.1).map fun k => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum).sum = {c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} + (Rw + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) …`.

Rewrite using `[hsum, add_left_comm]`. Use `clear hsum hright`. Prove the components needed by the constructor for the conclusion. Establish `hmem` using `hsum' ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self _))`. Take `⟨m, hm, hxm⟩` from `(multiset_mem_list_sum' _ _).1 hmem`.

Take `⟨e, he, rfl⟩` from `List.mem_map.1 hm`. Take `⟨m', hm', hxm'⟩` from `(multiset_mem_list_sum' _ _).1 hxm`. Take `⟨k, _, rfl⟩` from `List.mem_map.1 hm'`. Take `⟨α, hα, hαeq⟩` from `Multiset.mem_map.1 hxm'`. Establish `hn` using `congrArg norm hαeq`.

Rewrite `hn` using `[norm_mul, norm_mul, hc, nm, nm, one_mul]`. Establish `hx : ((e.1 : ℝ) - 1) / 2 - (k : ℝ) = (((n + 1 : ℕ) : ℝ) - 1) / 2` using `((hL e he).2.2.1 α hα).exp_eq hq hn ((n : ℤ) + 1 - e.1 + 2 * k) (by push_cast; ring)`. Use `⟨e, he, ?_⟩` and prove the remaining obligations. Establish `: ((n + 1 : ℕ) : ℝ) ≤ (e.1 : ℝ)`. Establish `hk : (0:ℝ) ≤ k` using `by positivity`.

Move the coercions through the operations in `at hx ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions. Introduce `e he hte`. Take `⟨hd1, hE0, -, hEn⟩` from `hL e he`.

Use `replace hEn := hEn hte`. Establish `hle : e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - ((0:ℕ) : ℝ) : ℝ)) : ℂ)) ≤ {c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} + (Rw + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum)`. Rewrite using `[← hsum']`. Use `(multiset_le_list_sum' ((List.range e.1).map fun (k : ℕ) => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))) _ ?_).trans (multiset_le_list_sum' _ _ ?_)` and prove the remaining obligations. Conclude with `List.mem_map.2 ⟨0, List.mem_range.2 (by omega), rfl⟩`.

Conclude with `List.mem_map.2 ⟨e, he, rfl⟩`. Establish `h1` using `Multiset.filter_le_filter (fun x : ℂ => (q : ℝ) ^ ((((n+1:ℕ) : ℝ) - 1) / 2) ≤ ‖x‖) hle`. Rewrite `h1` using `[Multiset.filter_eq_self.2, Multiset.filter_add, Multiset.filter_eq_nil.2 (fun x hx => not_le.2 (hsmall x hx)), add_zero]`. Use `swap`. Introduce `x hx`.

Take `⟨α, hα, rfl⟩` from `Multiset.mem_map.1 hx`. Rewrite using `[norm_mul, hEn α hα, nm, one_mul]`. Apply `Real.rpow_le_rpow_of_exponent_le hq1.le` to reduce the goal to its premises. Establish `: ((n + 1 : ℕ) : ℝ) ≤ (e.1 : ℝ)` using `by exact_mod_cast hte`. Move the coercions through the operations in `at this ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `h1.trans (Multiset.filter_le _ _)`. Establish `hcard : Multiset.card ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} : Multiset ℂ) ≤ Multiset.card (e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - ((0:ℕ) : ℝ) : ℝ)) : ℂ)))`. Rewrite using `[Multiset.card_singleton, Multiset.card_map]`. Conclude with `Multiset.card_pos.2 hE0`.

Establish `h3` using `Multiset.eq_of_le_of_card_le h2 hcard`. Take `⟨α, hEα, hαeq⟩` from `Multiset.map_eq_singleton.1 h3`. Establish `hα : α ∈ e.2` using `by rw [hEα]; exact Multiset.mem_singleton_self _`. Establish `hn` using `congrArg norm hαeq`. Rewrite `hn` using `[norm_mul, norm_mul, hEn α hα, hc, nm, nm, one_mul, one_mul]`.

Establish `hx` using `rpow_exponent_inj_of_one_lt hq1 hn`. Establish `hd : e.1 = n + 1`. Establish `: (e.1 : ℝ) = ((n + 1 : ℕ) : ℝ)` using `by push_cast at hx ⊢; linarith`. Conclude with `this` after adjusting the coercions. Use `⟨hd, ?_⟩` and prove the remaining obligations.

Rewrite using `[hEα]`. Use `congr 1`. Simplify using `only [hd, Nat.cast_zero, sub_zero] at hαeq`. Conclude with `mul_right_cancel₀ (Pne _) hαeq`.
-/
theorem string_count :
    ∀ (q t : ℕ) (L : List (ℕ × Multiset ℂ)) (Rw : Multiset ℂ) (c : ℂ), 1 < q → 1 ≤ t → ‖c‖ = 1 → (∀ x ∈ Rw, ‖x‖ < (q : ℝ) ^ (((t : ℝ) - 1) / 2)) → (∀ e ∈ L, 1 ≤ e.1 ∧ e.2 ≠ 0 ∧ (∀ α ∈ e.2, OpenB q α) ∧ (t ≤ e.1 → ∀ α ∈ e.2, ‖α‖ = 1)) → (L.map fun e => ((List.range e.1).map fun k => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum).sum = Rw + ((List.range t).map fun k => ({c * (q : ℂ) ^ (((((t : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ)} : Multiset ℂ)).sum → (∃ e ∈ L, t ≤ e.1) ∧ ∀ e ∈ L, t ≤ e.1 → e.1 = t ∧ e.2 = {c} := by
  intro q t L Rw c hq ht hc hRw hL hsum
  have hq0 : 0 < q := by omega
  have hq1 : (1:ℝ) < q := by exact_mod_cast hq
  have nm : ∀ s : ℝ, ‖(q : ℂ) ^ ((s : ℝ) : ℂ)‖ = (q : ℝ) ^ s := norm_natCast_cpow_ofReal hq0
  have Pne : ∀ s : ℝ, (q : ℂ) ^ ((s : ℝ) : ℂ) ≠ 0 := by
    intro s h0
    have h := nm s
    rw [h0, norm_zero] at h
    exact (Real.rpow_pos_of_pos (by positivity) s).ne' h.symm
  simp only [bind_pure_comp, List.map_eq_map, List.map_map, Function.comp_def] at hsum
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have hright : ((List.range (n+1)).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - (k : ℝ) : ℝ) : ℂ)} : Multiset ℂ)).sum
      = {c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum := by
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    congr 2
    · simp
    · apply List.map_congr_left
      intro k _
      simp
  rw [hright] at hsum
  have hsmall : ∀ x ∈ Rw + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum,
      ‖x‖ < (q : ℝ) ^ ((((n+1:ℕ) : ℝ) - 1) / 2) := by
    intro x hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · exact hRw x hx
    · obtain ⟨m, hm, hxm⟩ := (multiset_mem_list_sum' _ _).1 hx
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hm
      rw [Multiset.mem_singleton] at hxm
      subst hxm
      rw [norm_mul, hc, nm, one_mul]
      exact Real.rpow_lt_rpow_of_exponent_lt hq1 (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hsum' : (L.map fun e => ((List.range e.1).map fun k => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum).sum
      = {c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} + (Rw + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum) := by
    rw [hsum, add_left_comm]
  clear hsum hright
  constructor
  · have hmem := hsum' ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self _))
    obtain ⟨m, hm, hxm⟩ := (multiset_mem_list_sum' _ _).1 hmem
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    obtain ⟨m', hm', hxm'⟩ := (multiset_mem_list_sum' _ _).1 hxm
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hm'
    obtain ⟨α, hα, hαeq⟩ := Multiset.mem_map.1 hxm'
    have hn := congrArg norm hαeq
    rw [norm_mul, norm_mul, hc, nm, nm, one_mul] at hn
    have hx : ((e.1 : ℝ) - 1) / 2 - (k : ℝ) = (((n + 1 : ℕ) : ℝ) - 1) / 2 :=
      ((hL e he).2.2.1 α hα).exp_eq hq hn ((n : ℤ) + 1 - e.1 + 2 * k) (by push_cast; ring)
    refine ⟨e, he, ?_⟩
    have : ((n + 1 : ℕ) : ℝ) ≤ (e.1 : ℝ) := by
      have hk : (0:ℝ) ≤ k := by positivity
      push_cast at hx ⊢
      linarith
    exact_mod_cast this
  · intro e he hte
    obtain ⟨hd1, hE0, -, hEn⟩ := hL e he
    replace hEn := hEn hte
    have hle : e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - ((0:ℕ) : ℝ) : ℝ)) : ℂ))
        ≤ {c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} + (Rw + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum) := by
      rw [← hsum']
      refine (multiset_le_list_sum' ((List.range e.1).map fun (k : ℕ) => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))) _ ?_).trans (multiset_le_list_sum' _ _ ?_)
      · exact List.mem_map.2 ⟨0, List.mem_range.2 (by omega), rfl⟩
      · exact List.mem_map.2 ⟨e, he, rfl⟩
    have h1 := Multiset.filter_le_filter (fun x : ℂ => (q : ℝ) ^ ((((n+1:ℕ) : ℝ) - 1) / 2) ≤ ‖x‖) hle
    rw [Multiset.filter_eq_self.2, Multiset.filter_add, Multiset.filter_eq_nil.2 (fun x hx => not_le.2 (hsmall x hx)), add_zero] at h1
    swap
    · intro x hx
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hx
      rw [norm_mul, hEn α hα, nm, one_mul]
      apply Real.rpow_le_rpow_of_exponent_le hq1.le
      have : ((n + 1 : ℕ) : ℝ) ≤ (e.1 : ℝ) := by exact_mod_cast hte
      push_cast at this ⊢
      linarith
    have h2 := h1.trans (Multiset.filter_le _ _)
    have hcard : Multiset.card ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} : Multiset ℂ) ≤ Multiset.card (e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - ((0:ℕ) : ℝ) : ℝ)) : ℂ))) := by
      rw [Multiset.card_singleton, Multiset.card_map]
      exact Multiset.card_pos.2 hE0
    have h3 := Multiset.eq_of_le_of_card_le h2 hcard
    obtain ⟨α, hEα, hαeq⟩ := Multiset.map_eq_singleton.1 h3
    have hα : α ∈ e.2 := by rw [hEα]; exact Multiset.mem_singleton_self _
    have hn := congrArg norm hαeq
    rw [norm_mul, norm_mul, hEn α hα, hc, nm, nm, one_mul, one_mul] at hn
    have hx := rpow_exponent_inj_of_one_lt hq1 hn
    have hd : e.1 = n + 1 := by
      have : (e.1 : ℝ) = ((n + 1 : ℕ) : ℝ) := by push_cast at hx ⊢; linarith
      exact_mod_cast this
    refine ⟨hd, ?_⟩
    rw [hEα]
    congr 1
    simp only [hd, Nat.cast_zero, sub_zero] at hαeq
    exact mul_right_cancel₀ (Pne _) hαeq

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

/- English proof (translation)
The claim follows from `NumberField.HeightOneSpectrum.one_lt_absNorm w`.
-/
theorem one_lt_q (w : PlE H) : 1 < normV w := NumberField.HeightOneSpectrum.one_lt_absNorm w

/- English proof (translation)
Establish `: 2 ≤ R.r`. Establish `h1` using `R.two_le_m`. Establish `h2` using `R.m_add_three_le_k`. Use `show 2 ≤ R.k + R.m - 1`. Use linear arithmetic over natural numbers and integers.

Establish `h' : (2 : ℝ) ≤ R.r` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem half_le_r (R : Ranks) : (1 / 2 : ℝ) ≤ ((R.r : ℝ) - 1) / 2 := by
  have : 2 ≤ R.r := by
    have h1 := R.two_le_m
    have h2 := R.m_add_three_le_k
    show 2 ≤ R.k + R.m - 1
    omega
  have h' : (2 : ℝ) ≤ R.r := by exact_mod_cast this
  linarith

/- English proof (translation)
Introduce `α hα` and use `⟨h.2 hu α hα, fun e => (A.tempered_unr _ hu).1 (h.1 e) α hα⟩`.
-/
theorem TempAt.part {a : ℕ} {π : A.CG a} {w : PlE H} (h : TempAt N A π w) (hu : A.unr (A.locG π w)) :
    ∀ α ∈ A.frobEig (A.locG π w), OpenB (normV w) α ∧ (a = 1 → ‖α‖ = 1) :=
  fun α hα => ⟨h.2 hu α hα, fun e => (A.tempered_unr _ hu).1 (h.1 e) α hα⟩

/- English proof (translation)
Introduce `α hα`. Establish `hd` using `A.locG_dim A.etaT w`. Establish `heu` using `A.etaT_unr w`. Take `⟨e, he⟩` from `Multiset.card_eq_one.mp ((A.frobEig_card _ heu).trans hd)`. Establish `hen : ‖e‖ = 1` using `(A.tempered_unr _ heu).1 (hAut.2.2.1 w) e (by rw [he]; simp)`.

Establish `k` using `h.part (by rw [A.locG_tw]; exact A.unr_char _ _ hd hu heu) (α * e) (by`. Rewrite using `[A.locG_tw, A.frobEig_char _ _ e hu heu hd he]`. Conclude with `Multiset.mem_map_of_mem _ hα)`. Conclude with `⟨k.1.of_mul hen, fun e1 => by simpa [hen] using k.2 e1⟩`.
-/
theorem TempAt.part_tw (hAut : TieAut N A) {a : ℕ} {π : A.CG a} {w : PlE H} (h : TempAt N A (A.tw π A.etaT) w)
    (hu : A.unr (A.locG π w)) : ∀ α ∈ A.frobEig (A.locG π w), OpenB (normV w) α ∧ (a = 1 → ‖α‖ = 1) := by
  intro α hα
  have hd := A.locG_dim A.etaT w
  have heu := A.etaT_unr w
  obtain ⟨e, he⟩ := Multiset.card_eq_one.mp ((A.frobEig_card _ heu).trans hd)
  have hen : ‖e‖ = 1 := (A.tempered_unr _ heu).1 (hAut.2.2.1 w) e (by rw [he]; simp)
  have k := h.part (by rw [A.locG_tw]; exact A.unr_char _ _ hd hu heu) (α * e) (by
    rw [A.locG_tw, A.frobEig_char _ _ e hu heu hd he]
    exact Multiset.mem_map_of_mem _ hα)
  exact ⟨k.1.of_mul hen, fun e1 => by simpa [hen] using k.2 e1⟩

/- English proof (translation)
Establish `h1 : p.a * p.d ≤ rankIso N A Pa` using `List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem (f := fun p : Part A.CG => p.a * p.d) hp)`. Establish `h2 : R.r + 5 ≤ R.t` using `R.rank_add_five_le`. Rewrite `h1` using `[hr, Ranks.nV]`. Assume the negation of the conclusion as `hne`. Establish `h3 : 2 * R.t ≤ p.a * p.d` using `Nat.mul_le_mul (by omega) ht`.

Use linear arithmetic over natural numbers and integers.
-/
theorem rank_one_of_long {Pa : List (Part A.CG)} (hr : rankIso N A Pa = R.nV) {p : Part A.CG} (hp : p ∈ Pa)
    (ha : 1 ≤ p.a) (ht : R.t ≤ p.d) : p.a = 1 := by
  have h1 : p.a * p.d ≤ rankIso N A Pa :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem (f := fun p : Part A.CG => p.a * p.d) hp)
  have h2 : R.r + 5 ≤ R.t := R.rank_add_five_le
  rw [hr, Ranks.nV] at h1
  by_contra hne
  have h3 : 2 * R.t ≤ p.a * p.d := Nat.mul_le_mul (by omega) ht
  omega

end UpperTheory.GalN
