import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.MemPolKIff

noncomputable section

open Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}

def Slope (TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop) (c : ℕ) (f : (σ →₀ ℕ) → K) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (lam : ι → K) (n : ι → ℕ) (b : ι → (σ →₀ ℕ) → K),
    (∀ k, ((n k : ℕ) : WithTop ℚ) ≤ v (lam k ^ 6)) ∧ (∀ k, TotallyRealRoots (n k) (b k)) ∧
    (∀ k α, 0 ≤ v (b k α)) ∧ ∀ α, (c : WithTop ℚ) ≤ v (f α - ∑ k, lam k * b k α)

structure CostOK (TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop) : Prop where
  one : TotallyRealRoots 0 (fun _ => 1)
  mul : ∀ m n f g, TotallyRealRoots m f → TotallyRealRoots n g → TotallyRealRoots (m + n) (fun α => f α * g α)
  add : ∀ n f g, TotallyRealRoots n f → TotallyRealRoots n g → TotallyRealRoots n (fun α => f α + g α)
  smul : ∀ n (a : K) f, TotallyRealRoots n f → TotallyRealRoots n (fun α => a * f α)
  mono : ∀ m n f, m ≤ n → TotallyRealRoots m f → TotallyRealRoots n f

variable {v}

/- English proof (translation)
Establish `h6 : v (x ^ 6) = 6 • v x` using `AddValuation.map_pow v x 6`. Rewrite `h` using `[h6]`. Distinguish the cases in `hv : v x = ⊤`. Rewrite using `[hv]`. Conclude with `le_top`.

Take `⟨q, hq⟩` from `WithTop.ne_top_iff_exists.mp hv`. Rewrite `h`, the goal using `[← hq]`. Rewrite `h` using `[← WithTop.coe_nsmul, ← WithTop.coe_natCast, WithTop.coe_le_coe, nsmul_eq_mul]`. Rewrite using `[← WithTop.coe_natCast, WithTop.coe_le_coe]`. Establish `h2 : ((6 * m : ℕ) : ℚ) ≤ n` using `by exact_mod_cast hmn`.

Move the coercions through the operations in `at h h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_val_of_le_pow_six (x : K) (m n : ℕ) (hmn : 6 * m ≤ n)
    (h : ((n : ℕ) : WithTop ℚ) ≤ v (x ^ 6)) : ((m : ℕ) : WithTop ℚ) ≤ v x := by
  have h6 : v (x ^ 6) = 6 • v x := AddValuation.map_pow v x 6
  rw [h6] at h
  by_cases hv : v x = ⊤
  · rw [hv]
    exact le_top
  · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hv
    rw [← hq] at h ⊢
    rw [← WithTop.coe_nsmul, ← WithTop.coe_natCast, WithTop.coe_le_coe, nsmul_eq_mul] at h
    rw [← WithTop.coe_natCast, WithTop.coe_le_coe]
    have h2 : ((6 * m : ℕ) : ℚ) ≤ n := by exact_mod_cast hmn
    push_cast at h h2
    linarith

/- English proof (translation)
Establish `h0` using `le_val_of_le_pow_six x 0 n (by omega) h`. Simplify using `using h0`.
-/
theorem val_nonneg_of_pow_six (x : K) (n : ℕ) (h : ((n : ℕ) : WithTop ℚ) ≤ v (x ^ 6)) : 0 ≤ v x := by
  have h0 := le_val_of_le_pow_six x 0 n (by omega) h
  simpa using h0

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [Nat.cast_zero, AddValuation.map_zero]`. Conclude with `le_top`. Consider the case `succ k ih`. Rewrite using `[Nat.cast_succ]`.

Conclude with `le_trans (le_min ih (le_of_eq (AddValuation.map_one v).symm)) (AddValuation.map_add v _ _)`.
-/
theorem v_natCast_nonneg_monomial_order_segments (n : ℕ) : 0 ≤ v (n : K) := by
  induction n with
  | zero => rw [Nat.cast_zero, AddValuation.map_zero]; exact le_top
  | succ k ih =>
    rw [Nat.cast_succ]
    exact le_trans (le_min ih (le_of_eq (AddValuation.map_one v).symm)) (AddValuation.map_add v _ _)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty, AddValuation.map_zero]`. Conclude with `le_top`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`.

Conclude with `le_trans (le_min (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))) (AddValuation.map_add v _ _)`.
-/
theorem v_sum_nonneg {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, 0 ≤ v (f i)) :
    0 ≤ v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, AddValuation.map_zero]; exact le_top
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))) (AddValuation.map_add v _ _)

/- English proof (translation)
Rewrite using `[AddValuation.map_mul]`. Conclude with `add_nonneg hx hy`.
-/
theorem v_mul_nonneg {x y : K} (hx : 0 ≤ v x) (hy : 0 ≤ v y) : 0 ≤ v (x * y) := by
  rw [AddValuation.map_mul]
  exact add_nonneg hx hy

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty, AddValuation.map_one]`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, AddValuation.map_mul]`. Conclude with `add_nonneg (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))`.
-/
theorem v_prod_nonneg {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, 0 ≤ v (f i)) :
    0 ≤ v (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, AddValuation.map_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, AddValuation.map_mul]
    exact add_nonneg (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/- English proof (translation)
Rewrite using `[AddValuation.map_mul]`. Conclude with `le_add_of_le_of_nonneg hx hy`.
-/
theorem v_mul_ge_left {x y : K} {c : WithTop ℚ} (hx : c ≤ v x) (hy : 0 ≤ v y) : c ≤ v (x * y) := by
  rw [AddValuation.map_mul]
  exact le_add_of_le_of_nonneg hx hy

/- English proof (translation)
Rewrite using `[AddValuation.map_mul]`. Conclude with `le_add_of_nonneg_of_le hx hy`.
-/
theorem v_mul_ge_right {x y : K} {c : WithTop ℚ} (hx : 0 ≤ v x) (hy : c ≤ v y) : c ≤ v (x * y) := by
  rw [AddValuation.map_mul]
  exact le_add_of_nonneg_of_le hx hy

/- English proof (translation)
Conclude with `le_trans (le_min hx hy) (AddValuation.map_add v x y)`.
-/
theorem v_add_ge {x y : K} {c : WithTop ℚ} (hx : c ≤ v x) (hy : c ≤ v y) : c ≤ v (x + y) := by
  exact le_trans (le_min hx hy) (AddValuation.map_add v x y)

namespace Slope

variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop} {c : ℕ}

/- English proof (translation)
Use `⟨Unit, inferInstance, fun _ => 1, fun _ => 0, fun _ _ => 1, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Simplify using the standard rewrite rules. Introduce `k`. Conclude with `h1`.

Introduce `k α`. Simplify using the standard rewrite rules. Introduce `α`. Simplify using the standard rewrite rules.
-/
theorem one (h1 : TotallyRealRoots 0 (fun _ => 1)) : Slope v TotallyRealRoots c (fun _ => 1) := by
  refine ⟨Unit, inferInstance, fun _ => 1, fun _ => 0, fun _ _ => 1, ?_, ?_, ?_, ?_⟩
  · intro k
    simp
  · intro k
    exact h1
  · intro k α
    simp
  · intro α
    simp

/- English proof (translation)
Take `⟨ι, hι, lam, n, b, h1, h2, h3, h4⟩` from `hf`. Use `⟨ι, hι, lam, n, b, h1, h2, h3, fun α => ?_⟩` and prove the remaining obligations. Establish `e : g α - ∑ k, lam k * b k α = (g α - f α) + (f α - ∑ k, lam k * b k α)` using `by ring`. Rewrite using `[e]`. Use `v_add_ge ?_ (h4 α)` and prove the remaining obligations.

Rewrite using `[AddValuation.map_sub_swap]`. Conclude with `h α`.
-/
theorem congr {f g : (σ →₀ ℕ) → K} (h : ∀ α, (c : WithTop ℚ) ≤ v (f α - g α))
    (hf : Slope v TotallyRealRoots c f) : Slope v TotallyRealRoots c g := by
  obtain ⟨ι, hι, lam, n, b, h1, h2, h3, h4⟩ := hf
  refine ⟨ι, hι, lam, n, b, h1, h2, h3, fun α => ?_⟩
  have e : g α - ∑ k, lam k * b k α = (g α - f α) + (f α - ∑ k, lam k * b k α) := by ring
  rw [e]
  refine v_add_ge ?_ (h4 α)
  rw [AddValuation.map_sub_swap]
  exact h α

/- English proof (translation)
Take `⟨ι, hι, lam, n, b, h1, h2, h3, h4⟩` from `sf`. Take `⟨ι', hι', mu, n', d, h1', h2', h3', h4'⟩` from `sg`. Use `⟨ι × ι', inferInstance, fun p => lam p.1 * mu p.2, fun p => n p.1 + n' p.2, fun p α => b p.1 α * d p.2 α, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `p show (((n p.1 + n' p.2 : ℕ)) : WithTop ℚ) ≤ v ((lam p.1 * mu p.2) ^ 6)`. Rewrite using `[mul_pow, AddValuation.map_mul, Nat.cast_add]`.

Conclude with `add_le_add (h1 p.1) (h1' p.2)`. Introduce `p`. Conclude with `hmul _ _ _ _ (h2 p.1) (h2' p.2)`. Introduce `p α`. Conclude with `v_mul_nonneg (h3 p.1 α) (h3' p.2 α)`.

Introduce `α show (c : WithTop ℚ) ≤ v (f α * g α - ∑ p : ι × ι', lam p.1 * mu p.2 * (b p.1 α * d p.2 α))`. Establish `hs : ∑ p : ι × ι', lam p.1 * mu p.2 * (b p.1 α * d p.2 α) = (∑ k, lam k * b k α) * (∑ l, mu l * d l α)`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_mul_sum]`. Conclude with `Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))`. Rewrite using `[hs]`.

Establish `hP : 0 ≤ v (∑ k, lam k * b k α)` using `v_sum_nonneg _ _ (fun k _ => v_mul_nonneg (val_nonneg_of_pow_six _ _ (h1 k)) (h3 k α))`. Establish `e : f α * g α - (∑ k, lam k * b k α) * (∑ l, mu l * d l α) = (f α - ∑ k, lam k * b k α) * g α + (∑ k, lam k * b k α) * (g α - ∑ l, mu l * d l α)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `v_add_ge (v_mul_ge_left (h4 α) (hg α)) (v_mul_ge_right hP (h4' α))`.
-/
theorem mul (hmul : ∀ m n f g, TotallyRealRoots m f → TotallyRealRoots n g → TotallyRealRoots (m + n) (fun α => f α * g α))
    {f g : (σ →₀ ℕ) → K} (_hf : ∀ α, 0 ≤ v (f α)) (hg : ∀ α, 0 ≤ v (g α))
    (sf : Slope v TotallyRealRoots c f) (sg : Slope v TotallyRealRoots c g) : Slope v TotallyRealRoots c (fun α => f α * g α) := by
  obtain ⟨ι, hι, lam, n, b, h1, h2, h3, h4⟩ := sf
  obtain ⟨ι', hι', mu, n', d, h1', h2', h3', h4'⟩ := sg
  refine ⟨ι × ι', inferInstance, fun p => lam p.1 * mu p.2, fun p => n p.1 + n' p.2,
    fun p α => b p.1 α * d p.2 α, ?_, ?_, ?_, ?_⟩
  · intro p
    show (((n p.1 + n' p.2 : ℕ)) : WithTop ℚ) ≤ v ((lam p.1 * mu p.2) ^ 6)
    rw [mul_pow, AddValuation.map_mul, Nat.cast_add]
    exact add_le_add (h1 p.1) (h1' p.2)
  · intro p
    exact hmul _ _ _ _ (h2 p.1) (h2' p.2)
  · intro p α
    exact v_mul_nonneg (h3 p.1 α) (h3' p.2 α)
  · intro α
    show (c : WithTop ℚ) ≤
      v (f α * g α - ∑ p : ι × ι', lam p.1 * mu p.2 * (b p.1 α * d p.2 α))
    have hs : ∑ p : ι × ι', lam p.1 * mu p.2 * (b p.1 α * d p.2 α) =
        (∑ k, lam k * b k α) * (∑ l, mu l * d l α) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
    rw [hs]
    have hP : 0 ≤ v (∑ k, lam k * b k α) :=
      v_sum_nonneg _ _ (fun k _ => v_mul_nonneg (val_nonneg_of_pow_six _ _ (h1 k)) (h3 k α))
    have e : f α * g α - (∑ k, lam k * b k α) * (∑ l, mu l * d l α) =
        (f α - ∑ k, lam k * b k α) * g α + (∑ k, lam k * b k α) * (g α - ∑ l, mu l * d l α) := by
      ring
    rw [e]
    exact v_add_ge (v_mul_ge_left (h4 α) (hg α)) (v_mul_ge_right hP (h4' α))

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty]`. Conclude with `Slope.one h1`. Consider the case `@insert a s ha ih`.

Establish `e : (fun α => ∏ i ∈ insert a s, f i α) = fun α => f a α * ∏ i ∈ s, f i α`. Use function extensionality and compare the values at `α`. Rewrite using `[Finset.prod_insert ha]`. Rewrite using `[e]`. Conclude with `Slope.mul hmul (hf a (Finset.mem_insert_self a s)) (fun α => v_prod_nonneg _ _ (fun i hi => hf i (Finset.mem_insert_of_mem hi) α)) (sf a (Finset.mem_insert_self a s)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => sf i (Finset.mem_insert_of_mem hi)))`.
-/
theorem prod (h1 : TotallyRealRoots 0 (fun _ => 1))
    (hmul : ∀ m n f g, TotallyRealRoots m f → TotallyRealRoots n g → TotallyRealRoots (m + n) (fun α => f α * g α))
    {κ : Type} (s : Finset κ) (f : κ → (σ →₀ ℕ) → K) (hf : ∀ i ∈ s, ∀ α, 0 ≤ v (f i α))
    (sf : ∀ i ∈ s, Slope v TotallyRealRoots c (f i)) : Slope v TotallyRealRoots c (fun α => ∏ i ∈ s, f i α) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Slope.one h1
  | @insert a s ha ih =>
    have e : (fun α => ∏ i ∈ insert a s, f i α) = fun α => f a α * ∏ i ∈ s, f i α := by
      funext α
      rw [Finset.prod_insert ha]
    rw [e]
    exact Slope.mul hmul (hf a (Finset.mem_insert_self a s))
      (fun α => v_prod_nonneg _ _ (fun i hi => hf i (Finset.mem_insert_of_mem hi) α))
      (sf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => sf i (Finset.mem_insert_of_mem hi)))

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty, AddValuation.map_zero]`. Conclude with `le_top`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`.

Conclude with `le_trans (le_min (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))) (AddValuation.map_add v _ _)`.
-/
private theorem le_valuation_finset_sum {ι : Type} (s : Finset ι) (f : ι → K) {t : WithTop ℚ}
    (h : ∀ i ∈ s, t ≤ v (f i)) : t ≤ v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, AddValuation.map_zero]; exact le_top
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))) (AddValuation.map_add v _ _)

/- English proof (translation)
Take `⟨ι, hι, lam, n, b, h1, h2, h3, h4⟩` from `sf`. Use `⟨{k // n k ≤ 6 * c}, inferInstance, fun k => lam k.1, fun k => n k.1, fun k => b k.1, fun k => val_nonneg_of_pow_six _ _ (h1 k.1), fun k => k.2, fun k => h2 k.1, fun k α => h3 k.1 α, fun α => ?_⟩` and prove the remaining obligations. Use `show (c : WithTop ℚ) ≤ v (f α - ∑ k : {k // n k ≤ 6 * c}, lam k.1 * b k.1 α)`. Establish `hsub : ∑ k : {k // n k ≤ 6 * c}, lam k.1 * b k.1 α = ∑ k ∈ Finset.univ.filter (fun k => n k ≤ 6 * c), lam k * b k α` using `(Finset.sum_subtype _ (fun x => by simp) (fun k => lam k * b k α)).symm`. Establish `e : f α - ∑ k : {k // n k ≤ 6 * c}, lam k.1 * b k.1 α = (f α - ∑ k, lam k * b k α) + ∑ k ∈ Finset.univ.filter (fun k => ¬ n k ≤ 6 * c), lam k * b k α`.

Rewrite using `[hsub, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => n k ≤ 6 * c)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `v_add_ge (h4 α) (le_valuation_finset_sum _ _ (fun k hk => ?_))` and prove the remaining obligations. Establish `hk'` using `(Finset.mem_filter.mp hk).2`.

Conclude with `v_mul_ge_left (le_val_of_le_pow_six (lam k) c (n k) (by omega) (h1 k)) (h3 k α)`.
-/
theorem trunc {f : (σ →₀ ℕ) → K} (sf : Slope v TotallyRealRoots c f) :
    ∃ (ι : Type) (_ : Fintype ι) (lam : ι → K) (n : ι → ℕ) (b : ι → (σ →₀ ℕ) → K),
      (∀ k, 0 ≤ v (lam k)) ∧ (∀ k, n k ≤ 6 * c) ∧ (∀ k, TotallyRealRoots (n k) (b k)) ∧
      (∀ k α, 0 ≤ v (b k α)) ∧ ∀ α, (c : WithTop ℚ) ≤ v (f α - ∑ k, lam k * b k α) := by
  classical
  obtain ⟨ι, hι, lam, n, b, h1, h2, h3, h4⟩ := sf
  refine ⟨{k // n k ≤ 6 * c}, inferInstance, fun k => lam k.1, fun k => n k.1, fun k => b k.1,
    fun k => val_nonneg_of_pow_six _ _ (h1 k.1), fun k => k.2, fun k => h2 k.1,
    fun k α => h3 k.1 α, fun α => ?_⟩
  show (c : WithTop ℚ) ≤ v (f α - ∑ k : {k // n k ≤ 6 * c}, lam k.1 * b k.1 α)
  have hsub : ∑ k : {k // n k ≤ 6 * c}, lam k.1 * b k.1 α =
      ∑ k ∈ Finset.univ.filter (fun k => n k ≤ 6 * c), lam k * b k α :=
    (Finset.sum_subtype _ (fun x => by simp) (fun k => lam k * b k α)).symm
  have e : f α - ∑ k : {k // n k ≤ 6 * c}, lam k.1 * b k.1 α =
      (f α - ∑ k, lam k * b k α) +
        ∑ k ∈ Finset.univ.filter (fun k => ¬ n k ≤ 6 * c), lam k * b k α := by
    rw [hsub, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => n k ≤ 6 * c)]
    ring
  rw [e]
  refine v_add_ge (h4 α) (le_valuation_finset_sum _ _ (fun k hk => ?_))
  have hk' := (Finset.mem_filter.mp hk).2
  exact v_mul_ge_left (le_val_of_le_pow_six (lam k) c (n k) (by omega) (h1 k)) (h3 k α)

end Slope

namespace CostOK

variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop}

/- English proof (translation)
Establish `h0` using `hC.smul 0 (0 : K) _ hC.one`. Simplify using `only [zero_mul] at h0`. Conclude with `hC.mono 0 n _ (Nat.zero_le n) h0`.
-/
theorem zero (hC : CostOK TotallyRealRoots) (n : ℕ) : TotallyRealRoots n (fun _ => 0) := by
  have h0 := hC.smul 0 (0 : K) _ hC.one
  simp only [zero_mul] at h0
  exact hC.mono 0 n _ (Nat.zero_le n) h0

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Conclude with `hC.zero n`. Consider the case `@insert a s ha ih`.

Establish `e : (fun α => ∑ i ∈ insert a s, f i α) = fun α => f a α + ∑ i ∈ s, f i α`. Use function extensionality and compare the values at `α`. Rewrite using `[Finset.sum_insert ha]`. Rewrite using `[e]`. Conclude with `hC.add n _ _ (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))`.
-/
theorem sum (hC : CostOK TotallyRealRoots) {κ : Type} (s : Finset κ) (n : ℕ) (f : κ → (σ →₀ ℕ) → K)
    (h : ∀ i ∈ s, TotallyRealRoots n (f i)) : TotallyRealRoots n (fun α => ∑ i ∈ s, f i α) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact hC.zero n
  | @insert a s ha ih =>
    have e : (fun α => ∑ i ∈ insert a s, f i α) = fun α => f a α + ∑ i ∈ s, f i α := by
      funext α
      rw [Finset.sum_insert ha]
    rw [e]
    exact hC.add n _ _ (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty, Finset.sum_empty]`. Conclude with `hC.one`. Consider the case `@insert a s ha ih`.

Establish `e : (fun α => ∏ i ∈ insert a s, f i α) = fun α => f a α * ∏ i ∈ s, f i α`. Use function extensionality and compare the values at `α`. Rewrite using `[Finset.prod_insert ha]`. Rewrite using `[e, Finset.sum_insert ha]`. Conclude with `hC.mul _ _ _ _ (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))`.
-/
theorem prod (hC : CostOK TotallyRealRoots) {κ : Type} (s : Finset κ) (n : κ → ℕ) (f : κ → (σ →₀ ℕ) → K)
    (h : ∀ i ∈ s, TotallyRealRoots (n i) (f i)) : TotallyRealRoots (∑ i ∈ s, n i) (fun α => ∏ i ∈ s, f i α) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact hC.one
  | @insert a s ha ih =>
    have e : (fun α => ∏ i ∈ insert a s, f i α) = fun α => f a α * ∏ i ∈ s, f i α := by
      funext α
      rw [Finset.prod_insert ha]
    rw [e, Finset.sum_insert ha]
    exact hC.mul _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end CostOK

/- English proof (translation)
Take `⟨ι, hι, lam, n, b, h0, hn, h2, h3, h4⟩` from `sf.trunc`. Use `⟨fun α => ∑ k, lam k * b k α, fun α => v_sum_nonneg _ _ (fun k _ => v_mul_nonneg (h0 k) (h3 k α)), h4, ?_⟩` and prove the remaining obligations. Conclude with `hC.sum Finset.univ (6 * c) (fun k α => lam k * b k α) (fun k _ => hC.smul _ (lam k) _ (hC.mono _ _ _ (hn k) (h2 k)))`.
-/
theorem Slope.exists_approx {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop} (hC : CostOK TotallyRealRoots) {c : ℕ}
    {f : (σ →₀ ℕ) → K} (sf : Slope v TotallyRealRoots c f) :
    ∃ g : (σ →₀ ℕ) → K, (∀ α, 0 ≤ v (g α)) ∧ (∀ α, (c : WithTop ℚ) ≤ v (f α - g α)) ∧
      TotallyRealRoots (6 * c) g := by
  obtain ⟨ι, hι, lam, n, b, h0, hn, h2, h3, h4⟩ := sf.trunc
  refine ⟨fun α => ∑ k, lam k * b k α,
    fun α => v_sum_nonneg _ _ (fun k _ => v_mul_nonneg (h0 k) (h3 k α)), h4, ?_⟩
  exact hC.sum Finset.univ (6 * c) (fun k α => lam k * b k α)
    (fun k _ => hC.smul _ (lam k) _ (hC.mono _ _ _ (hn k) (h2 k)))

/- English proof (translation)
Proceed by induction on `P with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ k ih`. Take `⟨Q, hQ⟩` from `ih`. Conclude with `⟨Q + 1 + Polynomial.X * Q, by rw [pow_succ, hQ]; ring⟩`.
-/
theorem one_add_X_pow_eq (P : ℕ) :
    ∃ Q : Polynomial ℕ, (1 + Polynomial.X : Polynomial ℕ) ^ P = 1 + Polynomial.X * Q := by
  induction P with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨Q, hQ⟩ := ih
    exact ⟨Q + 1 + Polynomial.X * Q, by rw [pow_succ, hQ]; ring⟩

/- English proof (translation)
Take `⟨Q, hQ⟩` from `one_add_X_pow_eq P`. Use `⟨fun i => (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i).coeff m, fun β => ?_⟩` and prove the remaining obligations. Establish `hz : ∀ i, m < i → (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i).coeff m = 0`. Introduce `i hi`. Rewrite using `[show ((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i = ((1 + Polynomial.X) ^ ρ * Q ^ i) * Polynomial.X ^ i by ring, Polynomial.coeff_mul_X_pow', if_neg (by omega)]`.

Establish `hL : ∀ i, (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * ((Polynomial.X * Q) ^ i * 1 ^ (β - i) * ((β.choose i : ℕ) : Polynomial ℕ))).coeff m = (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i).coeff m * β.choose i`. Introduce `i`. Rewrite using `[one_pow, mul_one, ← mul_assoc, Polynomial.coeff_mul_natCast, Nat.cast_id]`. Establish `h1 : (ρ + P * β).choose m = ((1 + Polynomial.X : Polynomial ℕ) ^ (ρ + P * β)).coeff m`. Rewrite using `[Polynomial.coeff_one_add_X_pow, Nat.cast_id]`.

Rewrite using `[h1, pow_add, pow_mul, hQ, add_comm (1 : Polynomial ℕ) (Polynomial.X * Q), add_pow (Polynomial.X * Q) 1 β, Finset.mul_sum, Polynomial.finset_sum_coeff]`. Repeatedly rewrite using `[hL]`. Use `show ∑ i ∈ Finset.range (β + 1), (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i).coeff m * β.choose i = ∑ i ∈ Finset.range (m + 1), (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i).coeff m * β.choose i`. Rewrite using `[Finset.sum_subset (Finset.range_mono (show β + 1 ≤ β + m + 1 by omega)) (fun i _ hi => by`. Rewrite `hi` using `[Finset.mem_range, not_lt]`.

Rewrite using `[Nat.choose_eq_zero_of_lt (by omega), mul_zero]),`. Use the proof step `Finset.sum_subset (Finset.range_mono (show m + 1 ≤ β + m + 1 by omega)) (fun i _ hi => by`. Rewrite `hi` using `[Finset.mem_range, not_lt]`. Rewrite using `[hz i (by omega), zero_mul])]`.
-/
theorem choose_affine (ρ P m : ℕ) : ∃ z : ℕ → ℕ, ∀ β : ℕ,
    (ρ + P * β).choose m = ∑ i ∈ range (m + 1), z i * β.choose i := by
  obtain ⟨Q, hQ⟩ := one_add_X_pow_eq P
  refine ⟨fun i => (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i).coeff m,
    fun β => ?_⟩
  have hz : ∀ i, m < i →
      (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i).coeff m = 0 := by
    intro i hi
    rw [show ((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i =
        ((1 + Polynomial.X) ^ ρ * Q ^ i) * Polynomial.X ^ i by ring,
      Polynomial.coeff_mul_X_pow', if_neg (by omega)]
  have hL : ∀ i, (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) *
      ((Polynomial.X * Q) ^ i * 1 ^ (β - i) * ((β.choose i : ℕ) : Polynomial ℕ))).coeff m =
      (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i).coeff m * β.choose i := by
    intro i
    rw [one_pow, mul_one, ← mul_assoc, Polynomial.coeff_mul_natCast, Nat.cast_id]
  have h1 : (ρ + P * β).choose m = ((1 + Polynomial.X : Polynomial ℕ) ^ (ρ + P * β)).coeff m := by
    rw [Polynomial.coeff_one_add_X_pow, Nat.cast_id]
  rw [h1, pow_add, pow_mul, hQ, add_comm (1 : Polynomial ℕ) (Polynomial.X * Q), add_pow (Polynomial.X * Q) 1 β,
    Finset.mul_sum, Polynomial.finset_sum_coeff]
  simp_rw [hL]
  show ∑ i ∈ Finset.range (β + 1),
      (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i).coeff m * β.choose i =
    ∑ i ∈ Finset.range (m + 1),
      (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i).coeff m * β.choose i
  rw [Finset.sum_subset (Finset.range_mono (show β + 1 ≤ β + m + 1 by omega))
      (fun i _ hi => by
        rw [Finset.mem_range, not_lt] at hi
        rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]),
    Finset.sum_subset (Finset.range_mono (show m + 1 ≤ β + m + 1 by omega))
      (fun i _ hi => by
        rw [Finset.mem_range, not_lt] at hi
        rw [hz i (by omega), zero_mul])]

section Binom

variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop}

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty, Finset.sum_empty]`. Conclude with `h1`. Consider the case `@insert a s ha ih`.

Establish `e : (fun α => ∏ i ∈ insert a s, f i α) = fun α => f a α * ∏ i ∈ s, f i α`. Use function extensionality and compare the values at `α`. Rewrite using `[Finset.prod_insert ha]`. Rewrite using `[e, Finset.sum_insert ha]`. Conclude with `hmul _ _ _ _ (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))`.
-/
theorem cost_prod (h1 : TotallyRealRoots 0 (fun _ => 1))
    (hmul : ∀ m n f g, TotallyRealRoots m f → TotallyRealRoots n g → TotallyRealRoots (m + n) (fun α => f α * g α))
    {κ : Type} (s : Finset κ) (n : κ → ℕ) (f : κ → (σ →₀ ℕ) → K)
    (h : ∀ i ∈ s, TotallyRealRoots (n i) (f i)) : TotallyRealRoots (∑ i ∈ s, n i) (fun α => ∏ i ∈ s, f i α) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact h1
  | @insert a s ha ih =>
    have e : (fun α => ∏ i ∈ insert a s, f i α) = fun α => f a α * ∏ i ∈ s, f i α := by
      funext α
      rw [Finset.prod_insert ha]
    rw [e, Finset.sum_insert ha]
    exact hmul _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/- English proof (translation)
Conclude with `cost_prod h1 hmul Finset.univ m (fun a α => ((u a α).choose (m a) : K)) (fun a _ => hu a (m a))`.
-/
theorem cost_prod_choose_gen (h1 : TotallyRealRoots 0 (fun _ => 1))
    (hmul : ∀ m n f g, TotallyRealRoots m f → TotallyRealRoots n g → TotallyRealRoots (m + n) (fun α => f α * g α))
    {κ : Type} [Fintype κ] (u : κ → (σ →₀ ℕ) → ℕ)
    (hu : ∀ a k, TotallyRealRoots k (fun α => ((u a α).choose k : K))) (m : κ → ℕ) :
    TotallyRealRoots (∑ a, m a) (fun α => ∏ a, ((u a α).choose (m a) : K)) := by
  exact cost_prod h1 hmul Finset.univ m (fun a α => ((u a α).choose (m a) : K))
    (fun a _ => hu a (m a))

/- English proof (translation)
Take `⟨z, hz⟩` from `choose_affine ρ P m`. Establish `e : (fun α => (((ρ + P * u α).choose m : ℕ) : K)) = fun α => ∑ i ∈ Finset.range (m + 1), (z i : K) * ((u α).choose i : K)`. Use function extensionality and compare the values at `α`. Rewrite using `[hz (u α)]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `hC.sum (Finset.range (m + 1)) m (fun i α => (z i : K) * ((u α).choose i : K)) (fun i hi => hC.smul m (z i : K) _ (hC.mono i m _ (by have := Finset.mem_range.mp hi; omega) (hu i)))`.
-/
theorem cost_choose_affine (hC : CostOK TotallyRealRoots) (u : (σ →₀ ℕ) → ℕ)
    (hu : ∀ k, TotallyRealRoots k (fun α => ((u α).choose k : K))) (ρ P m : ℕ) :
    TotallyRealRoots m (fun α => ((ρ + P * u α).choose m : K)) := by
  obtain ⟨z, hz⟩ := choose_affine ρ P m
  have e : (fun α => (((ρ + P * u α).choose m : ℕ) : K)) =
      fun α => ∑ i ∈ Finset.range (m + 1), (z i : K) * ((u α).choose i : K) := by
    funext α
    rw [hz (u α)]
    push_cast
    rfl
  rw [e]
  exact hC.sum (Finset.range (m + 1)) m (fun i α => (z i : K) * ((u α).choose i : K))
    (fun i hi => hC.smul m (z i : K) _
      (hC.mono i m _ (by have := Finset.mem_range.mp hi; omega) (hu i)))

/- English proof (translation)
Use `⟨fun α => binomComb T lam (fun a => u a α), fun α => ?_, hf, ?_⟩` and prove the remaining obligations. Use `show 0 ≤ v (∑ m ∈ T, lam m * ∏ a, ((u a α).choose (m a) : K))`. Conclude with `v_sum_nonneg _ _ (fun m hm => v_mul_nonneg (hlam m hm).1 (v_prod_nonneg _ _ (fun a _ => v_natCast_nonneg_monomial_order_segments _)))`. Conclude with `hC.sum T n (fun m α => lam m * ∏ a, ((u a α).choose (m a) : K)) (fun m hm => hC.smul n (lam m) _ (hC.mono _ n _ (hlam m hm).2 (cost_prod_choose_gen hC.one hC.mul u hu m)))`.
-/
theorem approx_of_trunc_gen (hC : CostOK TotallyRealRoots) {κ : Type} [Fintype κ] (u : κ → (σ →₀ ℕ) → ℕ)
    (hu : ∀ a k, TotallyRealRoots k (fun α => ((u a α).choose k : K)))
    (T : Finset (κ → ℕ)) (lam : (κ → ℕ) → K) {c n : ℕ}
    (hlam : ∀ m ∈ T, 0 ≤ v (lam m) ∧ ∑ a, m a ≤ n) (f : (σ →₀ ℕ) → K)
    (hf : ∀ α, (c : WithTop ℚ) ≤ v (f α - binomComb T lam (fun a => u a α))) :
    ∃ g : (σ →₀ ℕ) → K, (∀ α, 0 ≤ v (g α)) ∧ (∀ α, (c : WithTop ℚ) ≤ v (f α - g α)) ∧ TotallyRealRoots n g := by
  refine ⟨fun α => binomComb T lam (fun a => u a α), fun α => ?_, hf, ?_⟩
  · show 0 ≤ v (∑ m ∈ T, lam m * ∏ a, ((u a α).choose (m a) : K))
    exact v_sum_nonneg _ _ (fun m hm => v_mul_nonneg (hlam m hm).1
      (v_prod_nonneg _ _ (fun a _ => v_natCast_nonneg_monomial_order_segments _)))
  · exact hC.sum T n (fun m α => lam m * ∏ a, ((u a α).choose (m a) : K))
      (fun m hm => hC.smul n (lam m) _
        (hC.mono _ n _ (hlam m hm).2 (cost_prod_choose_gen hC.one hC.mul u hu m)))

/- English proof (translation)
Conclude with `approx_of_trunc_gen hC (fun x α => α x) hch T lam hlam f hf`.
-/
theorem approx_of_trunc [Fintype σ] (hC : CostOK TotallyRealRoots)
    (hch : ∀ x k, TotallyRealRoots k (fun α => ((α x).choose k : K)))
    (T : Finset (σ → ℕ)) (lam : (σ → ℕ) → K) {c n : ℕ}
    (hlam : ∀ m ∈ T, 0 ≤ v (lam m) ∧ ∑ x, m x ≤ n) (f : (σ →₀ ℕ) → K)
    (hf : ∀ α, (c : WithTop ℚ) ≤ v (f α - binomComb T lam (fun x => α x))) :
    ∃ g : (σ →₀ ℕ) → K, (∀ α, 0 ≤ v (g α)) ∧ (∀ α, (c : WithTop ℚ) ≤ v (f α - g α)) ∧ TotallyRealRoots n g := by
  exact approx_of_trunc_gen hC (fun x α => α x) hch T lam hlam f hf

end Binom

section DiagCost

open MvPolynomial

/- English proof (translation)
Establish `h1 : (monomial α c : MvPolynomial σ K) = c • monomial α (1 : K)`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Establish `h2 : dg f (monomial α (1 : K)) = monomial α (f α)`. Rewrite using `[show (monomial α (1 : K) : MvPolynomial σ K) = basisMonomials σ K α by`. Rewrite using `[coe_basisMonomials]]`.

Unfold `dg`. Rewrite using `[Module.Basis.constr_basis]`. Rewrite using `[h1, map_smul, h2, smul_monomial, smul_eq_mul]`.
-/
private theorem dg_monomial' (f : (σ →₀ ℕ) → K) (α : σ →₀ ℕ) (c : K) :
    dg f (monomial α c) = monomial α (c * f α) := by
  have h1 : (monomial α c : MvPolynomial σ K) = c • monomial α (1 : K) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  have h2 : dg f (monomial α (1 : K)) = monomial α (f α) := by
    rw [show (monomial α (1 : K) : MvPolynomial σ K) = basisMonomials σ K α by
      rw [coe_basisMonomials]]
    unfold dg
    rw [Module.Basis.constr_basis]
  rw [h1, map_smul, h2, smul_monomial, smul_eq_mul]

/- English proof (translation)
Use `conv_lhs => rw [F.as_sum]`. Rewrite using `[map_sum, coeff_sum]`. Simplify using `only [dg_monomial']`. Rewrite using `[Finset.sum_eq_single α]`. Rewrite using `[coeff_monomial, if_pos rfl]`.

Introduce `b _ hb`. Rewrite using `[coeff_monomial, if_neg hb]`. Introduce `hα`. Simplify using `only [mem_support_iff, not_not] at hα`. Rewrite using `[coeff_monomial, if_pos rfl, hα, zero_mul]`.
-/
private theorem coeff_dg_eq_coeff_mul (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) (α : σ →₀ ℕ) :
    coeff α (dg f F) = coeff α F * f α := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum, coeff_sum]
  simp only [dg_monomial']
  rw [Finset.sum_eq_single α]
  · rw [coeff_monomial, if_pos rfl]
  · intro b _ hb
    rw [coeff_monomial, if_neg hb]
  · intro hα
    simp only [mem_support_iff, not_not] at hα
    rw [coeff_monomial, if_pos rfl, hα, zero_mul]

/- English proof (translation)
Use extensionality with `α`. Simplify using `only [coeff_dg_eq_coeff_mul, coeff_add, coeff_sub, coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dg_one_fun (F : MvPolynomial σ K) : dg (fun _ => (1 : K)) F = F := by
  ext α
  simp only [coeff_dg_eq_coeff_mul, coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Use extensionality with `α`. Simplify using `only [coeff_dg_eq_coeff_mul, coeff_add, coeff_sub, coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dg_mul_fun (f g : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg (fun α => f α * g α) F = dg f (dg g F) := by
  ext α
  simp only [coeff_dg_eq_coeff_mul, coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Use extensionality with `α`. Simplify using `only [coeff_dg_eq_coeff_mul, coeff_add, coeff_sub, coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dg_add_fun (f g : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg (fun α => f α + g α) F = dg f F + dg g F := by
  ext α
  simp only [coeff_dg_eq_coeff_mul, coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Use extensionality with `α`. Simplify using `only [coeff_dg_eq_coeff_mul, coeff_add, coeff_sub, coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dg_smul_fun (a : K) (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg (fun α => a * f α) F = a • dg f F := by
  ext α
  simp only [coeff_dg_eq_coeff_mul, coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Use extensionality with `α`. Simplify using `only [coeff_dg_eq_coeff_mul, coeff_add, coeff_sub, coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dg_sub_fun (f g : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg (fun α => f α - g α) F = dg f F - dg g F := by
  ext α
  simp only [coeff_dg_eq_coeff_mul, coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
  ring

def CostV {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (fam : Set (Finset L)) (n : ℕ)
    (f : (L × Fin r →₀ ℕ) → K) : Prop :=
  ∀ S ∈ fam, ∀ (θ : ℝ) (F : MvPolynomial (L × Fin r) K), vala sg S θ F → vala sg S (θ - n) (dg f F)

/- English proof (translation)
Introduce `S _ θ F h`. Rewrite using `[dg_one_fun]`. Simplify using `using h`. Use `mul := by`. Introduce `m n f g hf hg S hS θ F h`.

Rewrite using `[dg_mul_fun]`. Use `hf S hS _ _ (hg S hS θ F h)` as an intermediate fact. Establish `e : θ - ((m + n : ℕ) : ℝ) = θ - n - m` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `this`.

Use `add := by`. Introduce `n f g hf hg S hS θ F h`. Rewrite using `[dg_add_fun]`. Conclude with `hadd S hS _ _ _ (hf S hS θ F h) (hg S hS θ F h)`. Use `smul := by`.

Introduce `n a f hf S hS θ F h`. Rewrite using `[dg_smul_fun]`. Conclude with `hsmul S hS _ _ _ (hf S hS θ F h)`. Use `mono := by`. Introduce `m n f hmn hf S hS θ F h`.

Establish `h1` using `hf S hS θ F h`. Unfold `vala at h1 ⊢`. Use `le_trans ?_ h1` and prove the remaining obligations. Establish `: θ - (n : ℝ) ≤ θ - (m : ℝ)`. Establish `: (m : ℝ) ≤ n` using `by exact_mod_cast hmn`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions.
-/
theorem costV_ok {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (fam : Set (Finset L))
    (hadd : ∀ S ∈ fam, ∀ (θ : ℝ) (F G : MvPolynomial (L × Fin r) K),
      vala sg S θ F → vala sg S θ G → vala sg S θ (F + G))
    (hsmul : ∀ S ∈ fam, ∀ (θ : ℝ) (a : K) (F : MvPolynomial (L × Fin r) K),
      vala sg S θ F → vala sg S θ (a • F)) :
    CostOK (CostV (K := K) (r := r) sg fam) where
  one := by
    intro S _ θ F h
    rw [dg_one_fun]; simpa using h
  mul := by
    intro m n f g hf hg S hS θ F h
    rw [dg_mul_fun]
    have := hf S hS _ _ (hg S hS θ F h)
    have e : θ - ((m + n : ℕ) : ℝ) = θ - n - m := by push_cast; ring
    rw [e]; exact this
  add := by
    intro n f g hf hg S hS θ F h
    rw [dg_add_fun]
    exact hadd S hS _ _ _ (hf S hS θ F h) (hg S hS θ F h)
  smul := by
    intro n a f hf S hS θ F h
    rw [dg_smul_fun]
    exact hsmul S hS _ _ _ (hf S hS θ F h)
  mono := by
    intro m n f hmn hf S hS θ F h
    have h1 := hf S hS θ F h
    unfold vala at h1 ⊢
    refine le_trans ?_ h1
    have : θ - (n : ℝ) ≤ θ - (m : ℝ) := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    exact_mod_cast this

end DiagCost

end Formalism.MainNotions.PlaneGram
