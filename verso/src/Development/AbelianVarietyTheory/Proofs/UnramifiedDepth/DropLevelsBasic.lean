import Mathlib
import Formalism.DropLevelBounds.Statement
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds

namespace GlobalTheory.BasicFlow

/- English proof (translation)
Use `set t := s.filter fun i => x i ≠ 0 with ht`. Apply the tactic sequence `let E : (t → ℝ) →ₗ[ℝ] (ι → ℝ) := { toFun := fun v i => if h : i ∈ t then v ⟨i, h⟩ else 0 map_add' := fun v w => by ext i; by_cases h : i ∈ t <;> simp [h] map_smul' := fun c v => by ext i; by_cases h : i ∈ t <;> simp [h] }`. Establish `hker : LinearMap.ker (T ∘ₗ E) ≠ ⊥`. Apply `LinearMap.ker_ne_bot_of_finrank_lt` to reduce the goal to its premises. Simplify using `using hc`.

Take `⟨w, hw, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hker`. Establish `hw' : T (E w) = 0` using `hw`. Establish `hE0 : E w ≠ 0`. Introduce `h`. Apply `hw0` to reduce the goal to its premises.

Use extensionality with `⟨i, hi⟩`. Use `congrFun h i` as an intermediate fact. Simplify `this` using `[E, hi]`. Establish `hEt : ∀ i, i ∉ t → E w i = 0` using `fun i hi => by simp [E, hi]`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv0, hvt, hvT, hvφ⟩ : ∃ v : ι → ℝ, v ≠ 0 ∧ (∀ i, i ∉ t → v i = 0) ∧ T v = 0 ∧ 0 ≤ φ v := by`.

Break down `le_total 0 (φ (E w)) with h | h` into its components or cases. Conclude with `⟨E w, hE0, hEt, hw', h⟩`. Use `⟨-E w, neg_ne_zero.2 hE0, fun i hi => by simp [hEt i hi], by simp [hw'], ?_⟩` and prove the remaining obligations. Simplify using `using h`. Establish `hneg : (t.filter fun i => v i < 0).Nonempty`.

Assume the negation of the conclusion as `hn`. Apply `hv0` to reduce the goal to its premises. Use `hT v (fun i hi => hvt i fun h => hi (Finset.mem_filter.1 h).1) (fun i => ?_) hvT` and prove the remaining obligations. Distinguish the cases in `hi : i ∈ t`. Assume the negation of the conclusion as `hlt`.

Conclude with `hn ⟨i, Finset.mem_filter.2 ⟨hi, not_le.1 hlt⟩⟩`. Conclude with `(hvt i hi).ge`. Take `⟨j, hj, hmin⟩` from `Finset.exists_min_image _ (fun i => x i / (-v i)) hneg`. Take `⟨hjt, hjv⟩` from `Finset.mem_filter.1 hj`. Establish `hc0 : 0 ≤ x j / (-v j)` using `div_nonneg (hx j) (by linarith)`.

Establish `hzero : ∀ i, x i = 0 → (x + (x j / (-v j)) • v) i = 0`. Introduce `i hi`. Establish `: v i = 0` using `hvt i fun h => (Finset.mem_filter.1 h).2 hi`. Simplify using `[hi, this]`. Use `⟨x + (x j / (-v j)) • v, fun i => ?_, by simp [hvT], ?_, hzero, ?_⟩` and prove the remaining obligations.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `hi : v i < 0`. Establish `hit : i ∈ t`. Assume the negation of the conclusion as `h`. Conclude with `hi.ne (hvt i h)`.

Use `hmin i (Finset.mem_filter.2 ⟨hit, hi⟩)` as an intermediate fact. Rewrite `this` using `[le_div_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `mul_nonneg hc0 (not_lt.1 hi)` as an intermediate fact. Combine the linear relations using `[hx i]`.

Rewrite using `[map_add, map_smul, smul_eq_mul]`. Use `mul_nonneg hc0 hvφ` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Apply `Finset.card_lt_card` to reduce the goal to its premises. Use `⟨fun i hi => ?_, fun h => ?_⟩` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `Finset.mem_filter.1 hi`. Conclude with `Finset.mem_filter.2 ⟨h1, fun h => h2 (hzero i h)⟩`. Apply `(Finset.mem_filter.1 (h hjt)).2` to reduce the goal to its premises. Establish `: v j ≠ 0` using `hjv.ne`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma pivot {ι κ : Type} [DecidableEq ι] [Fintype κ] (s : Finset ι)
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (φ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hT : ∀ v : ι → ℝ, (∀ i, i ∉ s → v i = 0) → (∀ i, 0 ≤ v i) → T v = 0 → v = 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hs : ∀ i, i ∉ s → x i = 0)
    (hc : Fintype.card κ < (s.filter fun i => x i ≠ 0).card) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ T y = T x ∧ φ x ≤ φ y ∧ (∀ i, x i = 0 → y i = 0) ∧
      (s.filter fun i => y i ≠ 0).card < (s.filter fun i => x i ≠ 0).card := by
  set t := s.filter fun i => x i ≠ 0 with ht
  let E : (t → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun v i => if h : i ∈ t then v ⟨i, h⟩ else 0
      map_add' := fun v w => by ext i; by_cases h : i ∈ t <;> simp [h]
      map_smul' := fun c v => by ext i; by_cases h : i ∈ t <;> simp [h] }
  have hker : LinearMap.ker (T ∘ₗ E) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simpa using hc
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hw' : T (E w) = 0 := hw
  have hE0 : E w ≠ 0 := by
    intro h
    apply hw0
    ext ⟨i, hi⟩
    have := congrFun h i
    simpa [E, hi] using this
  have hEt : ∀ i, i ∉ t → E w i = 0 := fun i hi => by simp [E, hi]
  obtain ⟨v, hv0, hvt, hvT, hvφ⟩ :
      ∃ v : ι → ℝ, v ≠ 0 ∧ (∀ i, i ∉ t → v i = 0) ∧ T v = 0 ∧ 0 ≤ φ v := by
    rcases le_total 0 (φ (E w)) with h | h
    · exact ⟨E w, hE0, hEt, hw', h⟩
    · refine ⟨-E w, neg_ne_zero.2 hE0, fun i hi => by simp [hEt i hi], by simp [hw'], ?_⟩
      simpa using h
  have hneg : (t.filter fun i => v i < 0).Nonempty := by
    by_contra hn
    apply hv0
    refine hT v (fun i hi => hvt i fun h => hi (Finset.mem_filter.1 h).1) (fun i => ?_) hvT
    by_cases hi : i ∈ t
    · by_contra hlt
      exact hn ⟨i, Finset.mem_filter.2 ⟨hi, not_le.1 hlt⟩⟩
    · exact (hvt i hi).ge
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image _ (fun i => x i / (-v i)) hneg
  obtain ⟨hjt, hjv⟩ := Finset.mem_filter.1 hj
  have hc0 : 0 ≤ x j / (-v j) := div_nonneg (hx j) (by linarith)
  have hzero : ∀ i, x i = 0 → (x + (x j / (-v j)) • v) i = 0 := by
    intro i hi
    have : v i = 0 := hvt i fun h => (Finset.mem_filter.1 h).2 hi
    simp [hi, this]
  refine ⟨x + (x j / (-v j)) • v, fun i => ?_, by simp [hvT], ?_, hzero, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : v i < 0
    · have hit : i ∈ t := by
        by_contra h
        exact hi.ne (hvt i h)
      have := hmin i (Finset.mem_filter.2 ⟨hit, hi⟩)
      rw [le_div_iff₀ (by linarith)] at this
      linarith
    · have := mul_nonneg hc0 (not_lt.1 hi)
      linarith [hx i]
  · rw [map_add, map_smul, smul_eq_mul]
    have := mul_nonneg hc0 hvφ
    linarith
  · apply Finset.card_lt_card
    refine ⟨fun i hi => ?_, fun h => ?_⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hi
      exact Finset.mem_filter.2 ⟨h1, fun h => h2 (hzero i h)⟩
    · apply (Finset.mem_filter.1 (h hjt)).2
      have : v j ≠ 0 := hjv.ne
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring

/- English proof (translation)
Use the proof step `induction' h : (s.filter fun i => x i ≠ 0).card using Nat.strong_induction_on with n ih generalizing x`. Distinguish the cases in `hc : (s.filter fun i => x i ≠ 0).card ≤ Fintype.card κ`. Conclude with `⟨x, hx, rfl, le_rfl, fun _ h => h, hc⟩`. Take `⟨y, h1, h2, h3, h4, h5⟩` from `pivot s T φ hT x hx hs (not_le.1 hc)`. Take `⟨z, g1, g2, g3, g4, g5⟩` from `ih _ (h ▸ h5) y h1 (fun i hi => h4 i (hs i hi)) rfl`.

Conclude with `⟨z, g1, g2.trans h2, h3.trans g3, fun i hi => g4 i (h4 i hi), g5⟩`.
-/
lemma basic {ι κ : Type} [DecidableEq ι] [Fintype κ] (s : Finset ι)
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (φ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hT : ∀ v : ι → ℝ, (∀ i, i ∉ s → v i = 0) → (∀ i, 0 ≤ v i) → T v = 0 → v = 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hs : ∀ i, i ∉ s → x i = 0) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ T y = T x ∧ φ x ≤ φ y ∧ (∀ i, x i = 0 → y i = 0) ∧
      (s.filter fun i => y i ≠ 0).card ≤ Fintype.card κ := by
  induction' h : (s.filter fun i => x i ≠ 0).card using Nat.strong_induction_on
    with n ih generalizing x
  by_cases hc : (s.filter fun i => x i ≠ 0).card ≤ Fintype.card κ
  · exact ⟨x, hx, rfl, le_rfl, fun _ h => h, hc⟩
  · obtain ⟨y, h1, h2, h3, h4, h5⟩ := pivot s T φ hT x hx hs (not_le.1 hc)
    obtain ⟨z, g1, g2, g3, g4, g5⟩ :=
      ih _ (h ▸ h5) y h1 (fun i hi => h4 i (hs i hi)) rfl
    exact ⟨z, g1, g2.trans h2, h3.trans g3, fun i hi => g4 i (h4 i hi), g5⟩

/- English proof (translation)
Take `⟨h0, h2⟩` from `hx`. Establish `hl1 : (1 : ℝ) ≤ l` using `by exact_mod_cast (by omega : 1 ≤ l)`. Establish `e1 : (l : ℝ) ^ i * x a i ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i` using `Finset.single_le_sum (f := fun i => (l : ℝ) ^ i * x a i) (fun j _ => mul_nonneg (by positivity) (h0 a j)) hi`. Establish `e2 : 0 ≤ ∑ i ∈ oddLevels d, x (a - i) i` using `Finset.sum_nonneg fun j _ => h0 _ j`. Establish `e3 : x a i ≤ (l : ℝ) ^ i * x a i` using `le_mul_of_one_le_left (h0 a i) (one_le_pow₀ hl1)`.

Use `h2 a` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma entry_le (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (W : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ)
    (hx : IsFlow l d W x) (a : ZMod d) (i : ℕ) (hi : i ∈ oddLevels d) : x a i ≤ W a := by
  obtain ⟨h0, h2⟩ := hx
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have e1 : (l : ℝ) ^ i * x a i ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i :=
    Finset.single_le_sum (f := fun i => (l : ℝ) ^ i * x a i)
      (fun j _ => mul_nonneg (by positivity) (h0 a j)) hi
  have e2 : 0 ≤ ∑ i ∈ oddLevels d, x (a - i) i := Finset.sum_nonneg fun j _ => h0 _ j
  have e3 : x a i ≤ (l : ℝ) ^ i * x a i := le_mul_of_one_le_left (h0 a i) (one_le_pow₀ hl1)
  have := h2 a
  linarith

/- English proof (translation)
Set `S : Set (ZMod d → ℕ → ℝ)` to `{x | IsFlow l d W x ∧ ∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → x a i = 0}`. Establish `hclosed : IsClosed S`. Simplify using `only [S, IsFlow, Set.setOf_and, Set.setOf_forall]`. Use `IsClosed.inter (IsClosed.inter ?_ ?_) ?_` and prove the remaining obligations. Conclude with `isClosed_iInter fun a => isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)`.

Conclude with `isClosed_iInter fun a => isClosed_le (by fun_prop) continuous_const`. Conclude with `isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (by fun_prop) continuous_const`. Establish `hK : IsCompact (Set.pi Set.univ fun a : ZMod d => Set.pi Set.univ fun _ : ℕ => Set.Icc (0 : ℝ) (W a))` using `isCompact_univ_pi fun a => isCompact_univ_pi fun _ => isCompact_Icc`. Establish `hS : IsCompact S`. Use `hK.of_isClosed_subset hclosed ?_` and prove the remaining obligations.

Introduce and unpack `x ⟨h0, h1⟩ a - i -`. Use `⟨h0.1 a i, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : i ∈ oddLevels d`. Conclude with `entry_le l d hl W x h0 a i h`. Rewrite using `[h1 a i (Or.inr h)]`.

Conclude with `hW a`. Establish `hne : S.Nonempty` using `⟨fun _ _ => 0, ⟨fun _ _ => le_rfl, fun a => by simpa using hW a⟩, fun _ _ _ => rfl⟩`. Take `⟨x, hx, hmax⟩` from `hS.exists_isMaxOn hne (f := fun x => flowVal d x) (Continuous.continuousOn (by unfold flowVal; fun_prop))`. Conclude with `⟨x, hx, fun x' h1 h2 => hmax (a := x') ⟨h1, h2⟩⟩`.
-/
lemma low_optimum (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (W : ZMod d → ℝ) (hW : 0 ≤ W) (i0 : ℕ) :
    ∃ x : ZMod d → ℕ → ℝ, (IsFlow l d W x ∧ ∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → x a i = 0) ∧
      ∀ x' : ZMod d → ℕ → ℝ, IsFlow l d W x' →
        (∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → x' a i = 0) → flowVal d x' ≤ flowVal d x := by
  let S : Set (ZMod d → ℕ → ℝ) :=
    {x | IsFlow l d W x ∧ ∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → x a i = 0}
  have hclosed : IsClosed S := by
    simp only [S, IsFlow, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · exact isClosed_iInter fun a => isClosed_iInter fun i =>
        isClosed_le continuous_const (by fun_prop)
    · exact isClosed_iInter fun a => isClosed_le (by fun_prop) continuous_const
    · exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
        isClosed_eq (by fun_prop) continuous_const
  have hK : IsCompact (Set.pi Set.univ fun a : ZMod d =>
      Set.pi Set.univ fun _ : ℕ => Set.Icc (0 : ℝ) (W a)) :=
    isCompact_univ_pi fun a => isCompact_univ_pi fun _ => isCompact_Icc
  have hS : IsCompact S := by
    refine hK.of_isClosed_subset hclosed ?_
    rintro x ⟨h0, h1⟩ a - i -
    refine ⟨h0.1 a i, ?_⟩
    by_cases h : i ∈ oddLevels d
    · exact entry_le l d hl W x h0 a i h
    · rw [h1 a i (Or.inr h)]; exact hW a
  have hne : S.Nonempty := ⟨fun _ _ => 0, ⟨fun _ _ => le_rfl, fun a => by simpa using hW a⟩,
    fun _ _ _ => rfl⟩
  obtain ⟨x, hx, hmax⟩ := hS.exists_isMaxOn hne
    (f := fun x => flowVal d x) (Continuous.continuousOn (by unfold flowVal; fun_prop))
  exact ⟨x, hx, fun x' h1 h2 => hmax (a := x') ⟨h1, h2⟩⟩

/- English proof (translation)
Take `⟨h0, h2⟩` from `hx`. Establish `hl1 : (1 : ℝ) ≤ l` using `by exact_mod_cast (by omega : 1 ≤ l)`. Set `y : ZMod d → ℕ → ℝ` to `fun a i => if i0 ≤ i ∨ i ∉ oddLevels d then 0 else x a i`. Establish `hy : ∀ a i, y a i ≤ x a i` using `fun a i => by`. Simplify using `only [y]`.

Use `split_ifs`. Conclude with `h0 a i`. Conclude with `le_rfl`. Use `⟨y, ⟨fun a i => ?_, fun a => le_trans (add_le_add ?_ ?_) (h2 a)⟩, fun a i h => if_pos h, ?_⟩` and prove the remaining obligations. Simplify using `only [y]`.

Use `split_ifs`. Conclude with `le_rfl`. Conclude with `h0 a i`. Conclude with `Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hy a i) (by positivity)`. Conclude with `Finset.sum_le_sum fun i _ => hy _ i`.

Establish `hp : (0 : ℝ) < (l : ℝ) ^ i0` using `by positivity`. Rewrite using `[← sub_le_iff_le_add', le_div_iff₀ hp]`. Unfold `flowVal`. Rewrite using `[← Finset.sum_sub_distrib, Finset.sum_mul]`. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations.

Establish `e2 : 0 ≤ ∑ i ∈ oddLevels d, x (a - i) i` using `Finset.sum_nonneg fun j _ => h0 _ j`. Establish `e3 : (∑ i ∈ oddLevels d, x a i - ∑ i ∈ oddLevels d, y a i) * (l : ℝ) ^ i0 ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i`. Rewrite using `[← Finset.sum_sub_distrib, Finset.sum_mul]`. Use `Finset.sum_le_sum fun i hi => ?_` and prove the remaining obligations. Distinguish the cases in `h : i0 ≤ i`.

Establish `: y a i = 0` using `if_pos (Or.inl h)`. Rewrite using `[this, sub_zero, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl1 h) (h0 a i)`. Establish `: y a i = x a i` using `if_neg (by simp [h, hi])`. Rewrite using `[this, sub_self, zero_mul]`.

Conclude with `mul_nonneg (by positivity) (h0 a i)`. Use `h2 a` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma truncate (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (W : ZMod d → ℝ) (i0 : ℕ)
    (x : ZMod d → ℕ → ℝ) (hx : IsFlow l d W x) :
    ∃ x' : ZMod d → ℕ → ℝ, IsFlow l d W x' ∧
      (∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → x' a i = 0) ∧
      flowVal d x ≤ flowVal d x' + (∑ a, W a) / (l : ℝ) ^ i0 := by
  obtain ⟨h0, h2⟩ := hx
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  let y : ZMod d → ℕ → ℝ := fun a i => if i0 ≤ i ∨ i ∉ oddLevels d then 0 else x a i
  have hy : ∀ a i, y a i ≤ x a i := fun a i => by
    simp only [y]; split_ifs
    · exact h0 a i
    · exact le_rfl
  refine ⟨y, ⟨fun a i => ?_, fun a => le_trans (add_le_add ?_ ?_) (h2 a)⟩,
    fun a i h => if_pos h, ?_⟩
  · simp only [y]; split_ifs
    · exact le_rfl
    · exact h0 a i
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hy a i) (by positivity)
  · exact Finset.sum_le_sum fun i _ => hy _ i
  · have hp : (0 : ℝ) < (l : ℝ) ^ i0 := by positivity
    rw [← sub_le_iff_le_add', le_div_iff₀ hp]
    unfold flowVal
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    have e2 : 0 ≤ ∑ i ∈ oddLevels d, x (a - i) i := Finset.sum_nonneg fun j _ => h0 _ j
    have e3 : (∑ i ∈ oddLevels d, x a i - ∑ i ∈ oddLevels d, y a i) * (l : ℝ) ^ i0
        ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      by_cases h : i0 ≤ i
      · have : y a i = 0 := if_pos (Or.inl h)
        rw [this, sub_zero, mul_comm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl1 h) (h0 a i)
      · have : y a i = x a i := if_neg (by simp [h, hi])
        rw [this, sub_self, zero_mul]
        exact mul_nonneg (by positivity) (h0 a i)
    have := h2 a
    linarith

/- English proof (translation)
Introduce `l d _ hl W hW i0`. Take `⟨x, ⟨hx, hx0⟩, hmax⟩` from `low_optimum l d hl W hW i0`. Establish `hm : maxFlow l d W ≤ flowVal d x + (∑ a, W a) / (l : ℝ) ^ i0`. Use `csSup_le ⟨_, x, hx, rfl⟩ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`.

Take `⟨z', h1, h2, h3⟩` from `truncate l d hl W i0 z hz`. Combine the linear relations using `[hmax z' h1 h2]`. Set `T : (ZMod d × ℕ → ℝ) →ₗ[ℝ] (ZMod d → ℝ)` to `{ toFun := fun v s => (∑ i ∈ oddLevels d, (l : ℝ) ^ i * v (s, i)) + (∑ i ∈ oddLevels d, v (s - (i : ZMod d), i)) map_add' := fun v w => by`. Use extensionality with `s`. Simplify using `only [Pi.add_apply, mul_add, Finset.sum_add_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := fun c v => by`. Use extensionality with `s`. Simplify using `only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum, mul_left_comm c] }`. Set `φ : (ZMod d × ℕ → ℝ) →ₗ[ℝ] ℝ` to `{ toFun := fun v => ∑ s : ZMod d, ∑ i ∈ oddLevels d, v (s, i) map_add' := fun v w => by simp only [Pi.add_apply, Finset.sum_add_distrib] map_smul' := fun c v => by`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum] }`. Take `⟨y, h1, h2, h3, h4, h5⟩` from `basic ((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d) T φ (fun v hv hv0 hT => by`. Use extensionality with `⟨a, i⟩`. Distinguish the cases in `hi : i ∈ oddLevels d`. Use `le_antisymm ?_ (hv0 _)` and prove the remaining obligations.

Conclude with `entry_le l d hl 0 (fun a i => v (a, i)) ⟨fun a i => hv0 _, fun s => (congrFun hT s).le⟩ a i hi`. Conclude with `hv _ (by simp [hi]))`. Use the proof step `(fun p => x p.1 p.2) (fun p => hx.1 _ _)`. Use the proof step `(fun p hp => hx0 _ _ (Or.inr (by simpa using hp)))`. Use `⟨fun a i => y (a, i), ⟨fun a i => h1 _, fun s => ?_⟩, fun a i h => h4 (a, i) (hx0 a i h), ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(congrFun h2 s).le.trans (hx.2 s)`. Simplify `h5` using `[ZMod.card]`. Establish `: flowVal d x ≤ flowVal d (fun a i => y (a, i))` using `h3`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dropLevelsBasic : DropLevelsBasic := by
  intro l d _ hl W hW i0
  obtain ⟨x, ⟨hx, hx0⟩, hmax⟩ := low_optimum l d hl W hW i0
  have hm : maxFlow l d W ≤ flowVal d x + (∑ a, W a) / (l : ℝ) ^ i0 := by
    refine csSup_le ⟨_, x, hx, rfl⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2, h3⟩ := truncate l d hl W i0 z hz
    linarith [hmax z' h1 h2]
  let T : (ZMod d × ℕ → ℝ) →ₗ[ℝ] (ZMod d → ℝ) :=
    { toFun := fun v s => (∑ i ∈ oddLevels d, (l : ℝ) ^ i * v (s, i)) +
        (∑ i ∈ oddLevels d, v (s - (i : ZMod d), i))
      map_add' := fun v w => by
        ext s; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
      map_smul' := fun c v => by
        ext s
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum,
          mul_left_comm c] }
  let φ : (ZMod d × ℕ → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => ∑ s : ZMod d, ∑ i ∈ oddLevels d, v (s, i)
      map_add' := fun v w => by simp only [Pi.add_apply, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum] }
  obtain ⟨y, h1, h2, h3, h4, h5⟩ := basic ((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d) T φ
    (fun v hv hv0 hT => by
      ext ⟨a, i⟩
      by_cases hi : i ∈ oddLevels d
      · refine le_antisymm ?_ (hv0 _)
        exact entry_le l d hl 0 (fun a i => v (a, i))
          ⟨fun a i => hv0 _, fun s => (congrFun hT s).le⟩ a i hi
      · exact hv _ (by simp [hi]))
    (fun p => x p.1 p.2) (fun p => hx.1 _ _)
    (fun p hp => hx0 _ _ (Or.inr (by simpa using hp)))
  refine ⟨fun a i => y (a, i), ⟨fun a i => h1 _, fun s => ?_⟩,
    fun a i h => h4 (a, i) (hx0 a i h), ?_, ?_⟩
  · exact (congrFun h2 s).le.trans (hx.2 s)
  · simpa [ZMod.card] using h5
  · have : flowVal d x ≤ flowVal d (fun a i => y (a, i)) := h3
    linarith

/- English proof (translation)
Introduce `l n l1 W ys hn hl1 hl hy hW`. Take `⟨q, rfl⟩ : ∃ q, l = q + 1 + n` from `⟨l - 1 - n, by omega⟩`. Establish `hq : q + 1 + n - 1 - n = q` using `by omega`. Rewrite using `[hq]`. Establish `hq0 : 0 < q` using `by omega`.

Use `⟨(⌊ys⌋₊ % q) :: List.replicate (⌊ys⌋₊ / q) q, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Break down `List.mem_cons.1 hp with h | h` into its components or cases. Conclude with `h ▸ (Nat.mod_lt _ hq0).le`. Conclude with `(List.eq_of_mem_replicate h).le`.

Simplify using `only [List.sum_cons, List.sum_replicate, smul_eq_mul]`. Conclude with `Nat.mod_add_div' _ _`. Simplify using `only [List.length_cons, List.length_replicate]`. Move the coercions through the operations in `at *`. Use `set k : ℕ := ⌊ys⌋₊ / q with hk`.

Establish `h1 : (k : ℝ) * q ≤ ys`. Use `le_trans ?_ (Nat.floor_le hy)` and prove the remaining obligations. Conclude with `Nat.div_mul_le_self _ _` after adjusting the coercions. Establish `h2 : (n : ℝ) + 1 ≤ q` using `by exact_mod_cast (by omega : n + 1 ≤ q)`. Establish `hk0 : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`.

Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `h3 : (k : ℝ) ≤ 2 * W / l1 ^ 2`. Rewrite using `[le_div_iff₀ (by positivity)]`. Establish `h4 : l1 ^ 2 ≤ ((q : ℝ) + 1 + n + 1) * (2 * q)` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem splitLarge : SplitLarge := by
  intro l n l1 W ys hn hl1 hl hy hW
  obtain ⟨q, rfl⟩ : ∃ q, l = q + 1 + n := ⟨l - 1 - n, by omega⟩
  have hq : q + 1 + n - 1 - n = q := by omega
  rw [hq]
  have hq0 : 0 < q := by omega
  refine ⟨(⌊ys⌋₊ % q) :: List.replicate (⌊ys⌋₊ / q) q, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.1 hp with h | h
    · exact h ▸ (Nat.mod_lt _ hq0).le
    · exact (List.eq_of_mem_replicate h).le
  · simp only [List.sum_cons, List.sum_replicate, smul_eq_mul]
    exact Nat.mod_add_div' _ _
  · simp only [List.length_cons, List.length_replicate]
    push_cast at *
    set k : ℕ := ⌊ys⌋₊ / q with hk
    have h1 : (k : ℝ) * q ≤ ys := by
      refine le_trans ?_ (Nat.floor_le hy)
      exact_mod_cast Nat.div_mul_le_self _ _
    have h2 : (n : ℝ) + 1 ≤ q := by exact_mod_cast (by omega : n + 1 ≤ q)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h3 : (k : ℝ) ≤ 2 * W / l1 ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h4 : l1 ^ 2 ≤ ((q : ℝ) + 1 + n + 1) * (2 * q) := by nlinarith
      calc (k : ℝ) * l1 ^ 2 ≤ k * (((q : ℝ) + 1 + n + 1) * (2 * q)) :=
            mul_le_mul_of_nonneg_left h4 hk0
        _ = 2 * (((q : ℝ) + 1 + n + 1) * (k * q)) := by ring
        _ ≤ 2 * (((q : ℝ) + 1 + n + 1) * ys) := by gcongr
        _ ≤ 2 * W := by linarith
    linarith

/- English proof (translation)
Assemble the required witnesses or components as `⟨dropLevelsBasic, splitLarge⟩`.
-/
theorem main : DropLevelsBasic ∧ SplitLarge := ⟨dropLevelsBasic, splitLarge⟩

end GlobalTheory.BasicFlow
