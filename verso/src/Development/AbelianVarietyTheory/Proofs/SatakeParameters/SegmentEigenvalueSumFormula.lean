import Mathlib

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih => simp [List.sum_cons, Multiset.mem_add, ih]`.
-/
theorem multiset_mem_list_sum' {α : Type*} (l : List (Multiset α)) (x : α) :
    x ∈ l.sum ↔ ∃ m ∈ l, x ∈ m := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.sum_cons, Multiset.mem_add, ih]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp at h`. Consider the case `cons a l ih`. Rewrite using `[List.sum_cons]`. Break down `List.mem_cons.1 h with rfl | h` into its components or cases.

Conclude with `Multiset.le_add_right _ _`. Conclude with `(ih h).trans (Multiset.le_add_left _ _)`.
-/
theorem multiset_le_list_sum' {α : Type*} (l : List (Multiset α)) (m : Multiset α) (h : m ∈ l) :
    m ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Multiset.le_add_right _ _
    · exact (ih h).trans (Multiset.le_add_left _ _)

/- English proof (translation)
Rewrite using `[Complex.norm_natCast_cpow_of_pos hq]`. Simplify using the standard rewrite rules.
-/
theorem norm_natCast_cpow_ofReal {q : ℕ} (hq : 0 < q) (s : ℝ) :
    ‖(q : ℂ) ^ ((s : ℝ) : ℂ)‖ = (q : ℝ) ^ s := by
  rw [Complex.norm_natCast_cpow_of_pos hq]
  simp

/- English proof (translation)
Break down `lt_trichotomy x y with hxy | hxy | hxy` into its components or cases. Conclude with `absurd h (ne_of_lt (Real.rpow_lt_rpow_of_exponent_lt hb hxy))`. Conclude with `hxy`. Conclude with `absurd h (ne_of_gt (Real.rpow_lt_rpow_of_exponent_lt hb hxy))`.
-/
theorem rpow_exponent_inj_of_one_lt {b : ℝ} (hb : 1 < b) {x y : ℝ} (h : b ^ x = b ^ y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact absurd h (ne_of_lt (Real.rpow_lt_rpow_of_exponent_lt hb hxy))
  · exact hxy
  · exact absurd h (ne_of_gt (Real.rpow_lt_rpow_of_exponent_lt hb hxy))

/- English proof (translation)
Introduce `q t L Rw c hq ht hc hRw hL hsum`. Establish `hq0 : 0 < q` using `by omega`. Establish `hq1 : (1:ℝ) < q` using `by exact_mod_cast hq`. Establish `nm : ∀ s : ℝ, ‖(q : ℂ) ^ ((s : ℝ) : ℂ)‖ = (q : ℝ) ^ s` using `norm_natCast_cpow_ofReal hq0`. Establish `Pne : ∀ s : ℝ, (q : ℂ) ^ ((s : ℝ) : ℂ) ≠ 0`.

Introduce `s h0`. Establish `h` using `nm s`. Rewrite `h` using `[h0, norm_zero]`. Conclude with `(Real.rpow_pos_of_pos (by positivity) s).ne' h.symm`. Simplify using `only [bind_pure_comp, List.map_eq_map, List.map_map, Function.comp_def] at hsum`.

Take `⟨n, rfl⟩ : ∃ n, t = n + 1` from `⟨t - 1, by omega⟩`. Establish `hright : ((List.range (n+1)).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - (k : ℝ) : ℝ) : ℂ)} : Multiset ℂ)).sum = {c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ …`. Rewrite using `[List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]`. Use `congr 2`. Simplify using the standard rewrite rules.

Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `k _`. Simplify using the standard rewrite rules. Rewrite `hsum` using `[hright]`. Establish `hsmall : ∀ x ∈ Rw + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum, ‖x‖ < (q : ℝ) ^ ((((n+1:ℕ) : ℝ) - 1) / 2)`.

Introduce `x hx`. Break down `Multiset.mem_add.1 hx with hx | hx` into its components or cases. Conclude with `hRw x hx`. Take `⟨m, hm, hxm⟩` from `(multiset_mem_list_sum' _ _).1 hx`. Take `⟨k, _, rfl⟩` from `List.mem_map.1 hm`.

Rewrite `hxm` using `[Multiset.mem_singleton]`. Substitute `hxm` using the available equality. Rewrite using `[norm_mul, hc, nm, one_mul]`. Conclude with `Real.rpow_lt_rpow_of_exponent_lt hq1 (by have := Nat.cast_nonneg (α := ℝ) k; linarith)`. Establish `hsum' : (L.map fun e => ((List.range e.1).map fun k => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum).sum = {c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} + (Rw + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) …`.

Rewrite using `[hsum, add_left_comm]`. Use `clear hsum hright`. Prove the components needed by the constructor for the conclusion. Establish `hmem` using `hsum' ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self _))`. Take `⟨m, hm, hxm⟩` from `(multiset_mem_list_sum' _ _).1 hmem`.

Take `⟨e, he, rfl⟩` from `List.mem_map.1 hm`. Take `⟨m', hm', hxm'⟩` from `(multiset_mem_list_sum' _ _).1 hxm`. Take `⟨k, _, rfl⟩` from `List.mem_map.1 hm'`. Take `⟨α, hα, hαeq⟩` from `Multiset.mem_map.1 hxm'`. Establish `hn` using `congrArg norm hαeq`.

Rewrite `hn` using `[norm_mul, norm_mul, (hL e he).2.2 α hα, hc, nm, nm, one_mul, one_mul]`. Establish `hx` using `rpow_exponent_inj_of_one_lt hq1 hn`. Use `⟨e, he, ?_⟩` and prove the remaining obligations. Establish `: ((n + 1 : ℕ) : ℝ) ≤ (e.1 : ℝ)`. Establish `hk : (0:ℝ) ≤ k` using `by positivity`.

Move the coercions through the operations in `at hx ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions. Introduce `e he hte`. Take `⟨hd1, hE0, hEn⟩` from `hL e he`.

Establish `hle : e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - ((0:ℕ) : ℝ) : ℝ)) : ℂ)) ≤ {c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} + (Rw + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum)`. Rewrite using `[← hsum']`. Use `(multiset_le_list_sum' ((List.range e.1).map fun (k : ℕ) => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))) _ ?_).trans (multiset_le_list_sum' _ _ ?_)` and prove the remaining obligations. Conclude with `List.mem_map.2 ⟨0, List.mem_range.2 (by omega), rfl⟩`. Conclude with `List.mem_map.2 ⟨e, he, rfl⟩`.

Establish `h1` using `Multiset.filter_le_filter (fun x : ℂ => (q : ℝ) ^ ((((n+1:ℕ) : ℝ) - 1) / 2) ≤ ‖x‖) hle`. Rewrite `h1` using `[Multiset.filter_eq_self.2, Multiset.filter_add, Multiset.filter_eq_nil.2 (fun x hx => not_le.2 (hsmall x hx)), add_zero]`. Use `swap`. Introduce `x hx`. Take `⟨α, hα, rfl⟩` from `Multiset.mem_map.1 hx`.

Rewrite using `[norm_mul, hEn α hα, nm, one_mul]`. Apply `Real.rpow_le_rpow_of_exponent_le hq1.le` to reduce the goal to its premises. Establish `: ((n + 1 : ℕ) : ℝ) ≤ (e.1 : ℝ)` using `by exact_mod_cast hte`. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2` using `h1.trans (Multiset.filter_le _ _)`. Establish `hcard : Multiset.card ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} : Multiset ℂ) ≤ Multiset.card (e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - ((0:ℕ) : ℝ) : ℝ)) : ℂ)))`. Rewrite using `[Multiset.card_singleton, Multiset.card_map]`. Conclude with `Multiset.card_pos.2 hE0`. Establish `h3` using `Multiset.eq_of_le_of_card_le h2 hcard`.

Take `⟨α, hEα, hαeq⟩` from `Multiset.map_eq_singleton.1 h3`. Establish `hα : α ∈ e.2` using `by rw [hEα]; exact Multiset.mem_singleton_self _`. Establish `hn` using `congrArg norm hαeq`. Rewrite `hn` using `[norm_mul, norm_mul, hEn α hα, hc, nm, nm, one_mul, one_mul]`. Establish `hx` using `rpow_exponent_inj_of_one_lt hq1 hn`.

Establish `hd : e.1 = n + 1`. Establish `: (e.1 : ℝ) = ((n + 1 : ℕ) : ℝ)` using `by push_cast at hx ⊢; linarith`. Conclude with `this` after adjusting the coercions. Use `⟨hd, ?_⟩` and prove the remaining obligations. Rewrite using `[hEα]`.

Use `congr 1`. Simplify using `only [hd, Nat.cast_zero, sub_zero] at hαeq`. Conclude with `mul_right_cancel₀ (Pne _) hαeq`.
-/
theorem longest_segment_unique_of_bounded_remainder :
    ∀ (q t : ℕ) (L : List (ℕ × Multiset ℂ)) (Rw : Multiset ℂ) (c : ℂ), 1 < q → 1 ≤ t → ‖c‖ = 1 → (∀ x ∈ Rw, ‖x‖ < (q : ℝ) ^ (((t : ℝ) - 1) / 2)) → (∀ e ∈ L, 1 ≤ e.1 ∧ e.2 ≠ 0 ∧ ∀ α ∈ e.2, ‖α‖ = 1) → (L.map fun e => ((List.range e.1).map fun k => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum).sum = Rw + ((List.range t).map fun k => ({c * (q : ℂ) ^ (((((t : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ)} : Multiset ℂ)).sum → (∃ e ∈ L, t ≤ e.1) ∧ ∀ e ∈ L, t ≤ e.1 → e.1 = t ∧ e.2 = {c} := by
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
    rw [norm_mul, norm_mul, (hL e he).2.2 α hα, hc, nm, nm, one_mul, one_mul] at hn
    have hx := rpow_exponent_inj_of_one_lt hq1 hn
    refine ⟨e, he, ?_⟩
    have : ((n + 1 : ℕ) : ℝ) ≤ (e.1 : ℝ) := by
      have hk : (0:ℝ) ≤ k := by positivity
      push_cast at hx ⊢
      linarith
    exact_mod_cast this
  · intro e he hte
    obtain ⟨hd1, hE0, hEn⟩ := hL e he
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

end GlobalTheory
