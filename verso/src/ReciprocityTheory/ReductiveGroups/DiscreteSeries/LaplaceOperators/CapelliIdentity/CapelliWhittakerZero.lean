import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.RowCol

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

variable {M R : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℂ R]

/- English proof (translation)
Use extensionality with `v`. Simplify using the standard rewrite rules.
-/
theorem whB_comp_sum {ι : Type*} (l : M →ₗ[ℂ] R) (s : Finset ι) (f : ι → Module.End ℂ M) :
    l ∘ₗ ∑ i ∈ s, f i = ∑ i ∈ s, l ∘ₗ f i := by
  ext v; simp

/- English proof (translation)
Establish `hab : a ≠ b` using `by rintro rfl; exact lt_irrefl _ h`. Apply the tactic sequence `have : capEntry E x a b = E a b := by simp [capEntry, hab]`. Rewrite using `[this, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hl a b h, LinearMap.smul_comp]`.
-/
theorem whB_l_entry {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (bl : Fin n → ℕ)
    (ψ : Fin n → Fin n → ℂ) (l : M →ₗ[ℂ] R) (hl : ∀ a b, bl a < bl b → l ∘ₗ E a b = ψ a b • l)
    {a b : Fin n} (h : bl a < bl b) (x : ℂ) (Y : Module.End ℂ M) :
    l ∘ₗ (capEntry E x a b * Y) = ψ a b • (l ∘ₗ Y) := by
  have hab : a ≠ b := by rintro rfl; exact lt_irrefl _ h
  have : capEntry E x a b = E a b := by simp [capEntry, hab]
  rw [this, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hl a b h, LinearMap.smul_comp]

/- English proof (translation)
Rewrite using `[cminor_col_at E ((isGlRep_iff_glRelR E).1 hE) Rs Cs (Fin.last p) x, whB_comp_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rw [LinearMap.comp_smul, whB_l_entry E bl ψ l hl (hR i), smul_smul, Fin.val_last, Fin.succAbove_last]`.
-/
theorem l_cminor_lastcol {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (bl : Fin n → ℕ)
    (ψ : Fin n → Fin n → ℂ) (l : M →ₗ[ℂ] R) (hl : ∀ a b, bl a < bl b → l ∘ₗ E a b = ψ a b • l)
    {p : ℕ} (Rs Cs : Fin (p + 1) → Fin n) (x : ℂ) (hR : ∀ i, bl (Rs i) < bl (Cs (Fin.last p))) :
    l ∘ₗ cminor E Rs Cs x = ∑ i : Fin (p + 1), ((-1 : ℂ) ^ ((i : ℕ) + p) * ψ (Rs i) (Cs (Fin.last p))) •
      (l ∘ₗ cminor E (Rs ∘ i.succAbove) (Cs ∘ Fin.castSucc) (x - 1)) := by
  rw [cminor_col_at E ((isGlRep_iff_glRelR E).1 hE) Rs Cs (Fin.last p) x, whB_comp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_smul, whB_l_entry E bl ψ l hl (hR i), smul_smul, Fin.val_last, Fin.succAbove_last]

/- English proof (translation)
Rewrite using `[cminor_succ_row E ((isGlRep_iff_glRelR E).1 hE) Rs Cs x, whB_comp_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rw [LinearMap.comp_smul, whB_l_entry E bl ψ l hl (hC j), smul_smul]`.
-/
theorem l_cminor_firstrow {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (bl : Fin n → ℕ)
    (ψ : Fin n → Fin n → ℂ) (l : M →ₗ[ℂ] R) (hl : ∀ a b, bl a < bl b → l ∘ₗ E a b = ψ a b • l)
    {p : ℕ} (Rs Cs : Fin (p + 1) → Fin n) (x : ℂ) (hC : ∀ j, bl (Rs 0) < bl (Cs j)) :
    l ∘ₗ cminor E Rs Cs x = ∑ j : Fin (p + 1), ((-1 : ℂ) ^ (j : ℕ) * ψ (Rs 0) (Cs j)) •
      (l ∘ₗ cminor E (Rs ∘ Fin.succ) (Cs ∘ j.succAbove) x) := by
  rw [cminor_succ_row E ((isGlRep_iff_glRelR E).1 hE) Rs Cs x, whB_comp_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.comp_smul, whB_l_entry E bl ψ l hl (hC j), smul_smul]

/- English proof (translation)
The claim follows from `cminor_intertwine E D Fin.castSucc (Fin.castSucc_injective k) l hD id id x`.
-/
theorem capelli_whittaker_zero (k : ℕ) (E : Fin (k + 1) → Fin (k + 1) → Module.End ℂ M)
    (D : Fin k → Fin k → Module.End ℂ R) (l : M →ₗ[ℂ] R) (x : ℂ)
    (hD : ∀ i j, l ∘ₗ E (Fin.castSucc i) (Fin.castSucc j) = D i j ∘ₗ l) :
    l ∘ₗ cminor E Fin.castSucc Fin.castSucc x = capelliC D x ∘ₗ l :=
  cminor_intertwine E D Fin.castSucc (Fin.castSucc_injective k) l hD id id x

def whB_c (N a : ℕ) [NeZero N] : Fin N := ⟨a % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩

/- English proof (translation)
The claim follows from `Fin.ext (Nat.mod_eq_of_lt a.isLt)`.
-/
theorem whB_c_val_self {N : ℕ} [NeZero N] (a : Fin N) : whB_c N (a : ℕ) = a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

def whB_seg (N s q : ℕ) [NeZero N] (i : Fin q) : Fin N := whB_c N (s + (i : ℕ))

/- English proof (translation)
The claim follows from `Nat.mod_eq_of_lt h`.
-/
theorem whB_cast_val {N : ℕ} [NeZero N] {a : ℕ} (h : a < N) : (whB_c N a : ℕ) = a :=
  Nat.mod_eq_of_lt h

/- English proof (translation)
Unfold `whB_seg; exact whB_cast_val (by omega)`.
-/
theorem whB_seg_val {N s q : ℕ} [NeZero N] (h : s + q ≤ N) (i : Fin q) :
    (whB_seg N s q i : ℕ) = s + i := by
  unfold whB_seg; exact whB_cast_val (by omega)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp, whB_seg, Fin.val_succ]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem whB_seg_succ (N s q : ℕ) [NeZero N] : whB_seg N s (q + 1) ∘ Fin.succ = whB_seg N (s + 1) q := by
  funext i; simp only [Function.comp, whB_seg, Fin.val_succ]; congr 1; omega

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[whB_seg]`.
-/
theorem whB_seg_castSucc (N s q : ℕ) [NeZero N] :
    whB_seg N s (q + 1) ∘ Fin.castSucc = whB_seg N s q := by
  funext i; simp [whB_seg]

/- English proof (translation)
Substitute `hq hs ht` using the available equality. Both sides reduce to the same expression.
-/
theorem whB_cminor_cast {N : ℕ} [NeZero N] (E : Fin N → Fin N → Module.End ℂ M) {s t q s' t' q' : ℕ}
    (hq : q = q') (hs : s = s') (ht : t = t') (y : ℂ) :
    cminor E (whB_seg N s q) (whB_seg N t q) y = cminor E (whB_seg N s' q') (whB_seg N t' q') y := by
  subst hq hs ht; rfl

def whB_g (k r : ℕ) (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ) (a : Fin (k + 2 * r + 1)) : ℂ :=
  ∏ b, if IsSimplePair k r a b then ψ a b else 1

/- English proof (translation)
Unfold `whB_g`. Rewrite using `[Finset.prod_eq_single b0 (fun b _ hb => ?_) (by simp), if_pos h]`. Rewrite using `[if_neg]`. Introduce `hb'`. Apply `hb` to reduce the goal to its premises.

Take `⟨h1, h2, h3⟩` from `h`. Take `⟨h1', h2', h3'⟩` from `hb'`. Simplify using `only [inW, blk] at h1 h2 h3 h1' h2' h3'`. Use `b.isLt` as an intermediate fact. Use `b0.isLt` as an intermediate fact.

Apply `Fin.ext` to reduce the goal to its premises. Apply the tactic sequence `split_ifs at h1 h1' <;> omega`.
-/
theorem whB_g_eq {k r : ℕ} (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ) {a b0 : Fin (k + 2 * r + 1)}
    (h : IsSimplePair k r a b0) : whB_g k r ψ a = ψ a b0 := by
  unfold whB_g
  rw [Finset.prod_eq_single b0 (fun b _ hb => ?_) (by simp), if_pos h]
  rw [if_neg]
  intro hb'
  apply hb
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := hb'
  simp only [inW, blk] at h1 h2 h3 h1' h2' h3'
  have := b.isLt; have := b0.isLt
  apply Fin.ext
  split_ifs at h1 h1' <;> omega

/- English proof (translation)
The claim follows from `Finset.prod_eq_one fun b _ => if_neg (h b)`.
-/
theorem whB_g_one {k r : ℕ} (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ) {a : Fin (k + 2 * r + 1)}
    (h : ∀ b, ¬ IsSimplePair k r a b) : whB_g k r ψ a = 1 :=
  Finset.prod_eq_one fun b _ => if_neg (h b)

/- English proof (translation)
Establish `e1 : kappa k r ψ = ∏ n ∈ range (k + 2 * r + 1), whB_g k r ψ (whB_c (k + 2 * r + 1) n)`. Rewrite using `[← Fin.prod_univ_eq_prod_range (fun n => whB_g k r ψ (whB_c (k + 2 * r + 1) n))]`. Simplify using `only [whB_c_val_self]`. Both sides reduce to the same expression. Rewrite using `[e1, show range (k + 2 * r + 1) = range (r + k + r + 1) by congr 1; ring, Finset.prod_range_succ, Finset.prod_range_add, Finset.prod_range_add]`.

Establish `hW : ∏ x ∈ range k, whB_g k r ψ (whB_c (k + 2 * r + 1) (r + x)) = 1`. Use `Finset.prod_eq_one fun x hx => whB_g_one ψ fun b hb => ?_` and prove the remaining obligations. Rewrite `hx` using `[Finset.mem_range]`. Take `⟨_, h2, _⟩` from `hb`. Conclude with `h2 ⟨by rw [whB_cast_val (by omega)]; omega, by rw [whB_cast_val (by omega)]; omega⟩`.

Establish `hL : whB_g k r ψ (whB_c (k + 2 * r + 1) (r + k + r)) = 1`. Use `whB_g_one ψ fun b hb => ?_` and prove the remaining obligations. Take `⟨h1, _, _⟩` from `hb`. Use `b.isLt` as an intermediate fact. Simplify using `only [blk, whB_cast_val (show r + k + r < k + 2 * r + 1 by omega)] at h1`.

Apply the tactic sequence `split_ifs at h1 <;> omega`. Establish `hE : ∏ x ∈ range r, whB_g k r ψ (whB_c (k + 2 * r + 1) (r + k + x)) = ∏ j ∈ range r, whB_g k r ψ (whB_c (k + 2 * r + 1) (k + r + j))`. Use `Finset.prod_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[show r + k + x = k + r + x by ring]`. Establish `hS : ∏ n ∈ range r, whB_g k r ψ (whB_c (k + 2 * r + 1) (n)) = (∏ i ∈ range (r - 1), whB_g k r ψ (whB_c (k + 2 * r + 1) (0 + i))) * whB_g k r ψ (whB_c (k + 2 * r + 1) (r - 1))`.

Take `⟨r', rfl⟩ : ∃ r', r = r' + 1` from `⟨r - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel, zero_add]`. Rewrite using `[Finset.prod_range_succ]`. Rewrite using `[hW, hL, hE, hS]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem whB_kappa (k r : ℕ) (hr : 0 < r) (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ) :
    kappa k r ψ = (∏ j ∈ range r, whB_g k r ψ (whB_c (k + 2 * r + 1) (k + r + j))) *
      ((∏ i ∈ range (r - 1), whB_g k r ψ (whB_c (k + 2 * r + 1) (0 + i))) *
        whB_g k r ψ (whB_c (k + 2 * r + 1) (r - 1))) := by
  have e1 : kappa k r ψ = ∏ n ∈ range (k + 2 * r + 1), whB_g k r ψ (whB_c (k + 2 * r + 1) n) := by
    rw [← Fin.prod_univ_eq_prod_range (fun n => whB_g k r ψ (whB_c (k + 2 * r + 1) n))]
    simp only [whB_c_val_self]; rfl
  rw [e1, show range (k + 2 * r + 1) = range (r + k + r + 1) by congr 1; ring,
    Finset.prod_range_succ, Finset.prod_range_add, Finset.prod_range_add]
  have hW : ∏ x ∈ range k, whB_g k r ψ (whB_c (k + 2 * r + 1) (r + x)) = 1 := by
    refine Finset.prod_eq_one fun x hx => whB_g_one ψ fun b hb => ?_
    rw [Finset.mem_range] at hx
    obtain ⟨_, h2, _⟩ := hb
    exact h2 ⟨by rw [whB_cast_val (by omega)]; omega, by rw [whB_cast_val (by omega)]; omega⟩
  have hL : whB_g k r ψ (whB_c (k + 2 * r + 1) (r + k + r)) = 1 := by
    refine whB_g_one ψ fun b hb => ?_
    obtain ⟨h1, _, _⟩ := hb
    have := b.isLt
    simp only [blk, whB_cast_val (show r + k + r < k + 2 * r + 1 by omega)] at h1
    split_ifs at h1 <;> omega
  have hE : ∏ x ∈ range r, whB_g k r ψ (whB_c (k + 2 * r + 1) (r + k + x)) =
      ∏ j ∈ range r, whB_g k r ψ (whB_c (k + 2 * r + 1) (k + r + j)) := by
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [show r + k + x = k + r + x by ring]
  have hS : ∏ n ∈ range r, whB_g k r ψ (whB_c (k + 2 * r + 1) (n)) =
      (∏ i ∈ range (r - 1), whB_g k r ψ (whB_c (k + 2 * r + 1) (0 + i))) *
        whB_g k r ψ (whB_c (k + 2 * r + 1) (r - 1)) := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel, zero_add]
    rw [Finset.prod_range_succ]
  rw [hW, hL, hE, hS]; ring

section Phases

variable (k r : ℕ) (E : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → Module.End ℂ M)
  (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ) (l : M →ₗ[ℂ] R) (hE : IsGlRep E)
  (hl : ∀ a b, blk k r a < blk k r b → l ∘ₗ E a b = ψ a b • l)
  (hψ : ∀ a b, blk k r a < blk k r b → ¬ IsSimplePair k r a b → ψ a b = 0)
include hE hl hψ

/- English proof (translation)
Proceed by induction on `m generalizing y with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Establish `hb0 : 0 + (k + r + m + 1) ≤ k + 2 * r + 1` using `by omega`. Establish `hb1 : 1 + (k + r + m + 1) ≤ k + 2 * r + 1` using `by omega`.

Establish `hR : ∀ i : Fin (k + r + m + 1), blk k r (whB_seg (k + 2 * r + 1) 0 (k + r + m + 1) i) < blk k r (whB_seg (k + 2 * r + 1) 1 (k + r + m + 1) (Fin.last (k + r + m)))`. Introduce `i`. Use `i.isLt` as an intermediate fact. Simplify using `only [blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_last]`. Apply the tactic sequence `split_ifs <;> omega`.

Establish `key` using `l_cminor_lastcol E hE (blk k r) ψ l hl _ _ y hR`. Use `key.trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (Fin.last (k + r + m))]`. Establish `hs : IsSimplePair k r (whB_seg (k + 2 * r + 1) 0 (k + r + m + 1) (Fin.last (k + r + m))) (whB_seg (k + 2 * r + 1) 1 (k + r + m + 1) (Fin.last (k + r + m)))`. Simplify using `only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_last]`.

Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[← whB_g_eq ψ hs, Fin.succAbove_last, whB_seg_castSucc, whB_seg_castSucc, ih (by omega) (y - 1), smul_smul, Finset.prod_range_succ]`. Establish `e : y - 1 - (m : ℂ) = y - ((m + 1 : ℕ) : ℂ)` using `by push_cast; ring`. Establish `e2 : (-1 : ℂ) ^ ((Fin.last (k + r + m) : ℕ) + (k + r + m)) = 1`. Rewrite using `[Fin.val_last]`.

Conclude with `Even.neg_one_pow ⟨_, rfl⟩`. Establish `e3 : whB_seg (k + 2 * r + 1) 0 (k + r + m + 1) (Fin.last (k + r + m)) = (whB_c (k + 2 * r + 1) (k + r + m))`. Simplify using `[whB_seg]`. Rewrite using `[e, e2, e3, one_mul, mul_comm]`. Introduce `i _ hi`.

Establish `hiv : (i : ℕ) < k + r + m`. Use `i.isLt` as an intermediate fact. Establish `: (i : ℕ) ≠ k + r + m` using `fun h => hi (Fin.ext (by simp [h]))`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hψ _ _ (hR i) ?_, mul_zero, zero_smul]`.

Simplify using `only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_last]`. Apply the tactic sequence `split_ifs <;> omega`. Simplify using the standard rewrite rules.
-/
theorem whB_phase1 (m : ℕ) (hm : m ≤ r) (y : ℂ) :
    l ∘ₗ cminor E (whB_seg (k + 2 * r + 1) 0 (k + r + m)) (whB_seg (k + 2 * r + 1) 1 (k + r + m)) y =
      (∏ j ∈ range m, whB_g k r ψ (whB_c (k + 2 * r + 1) (k + r + j))) •
        (l ∘ₗ cminor E (whB_seg (k + 2 * r + 1) 0 (k + r)) (whB_seg (k + 2 * r + 1) 1 (k + r))
          (y - m)) := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    have hb0 : 0 + (k + r + m + 1) ≤ k + 2 * r + 1 := by omega
    have hb1 : 1 + (k + r + m + 1) ≤ k + 2 * r + 1 := by omega
    have hR : ∀ i : Fin (k + r + m + 1), blk k r (whB_seg (k + 2 * r + 1) 0 (k + r + m + 1) i) <
        blk k r (whB_seg (k + 2 * r + 1) 1 (k + r + m + 1) (Fin.last (k + r + m))) := by
      intro i
      have := i.isLt
      simp only [blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_last]
      split_ifs <;> omega
    have key := l_cminor_lastcol E hE (blk k r) ψ l hl _ _ y hR
    refine key.trans ?_
    rw [Finset.sum_eq_single (Fin.last (k + r + m))]
    · have hs : IsSimplePair k r (whB_seg (k + 2 * r + 1) 0 (k + r + m + 1) (Fin.last (k + r + m)))
          (whB_seg (k + 2 * r + 1) 1 (k + r + m + 1) (Fin.last (k + r + m))) := by
        simp only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_last]
        split_ifs <;> omega
      rw [← whB_g_eq ψ hs, Fin.succAbove_last, whB_seg_castSucc, whB_seg_castSucc, ih (by omega) (y - 1),
        smul_smul, Finset.prod_range_succ]
      have e : y - 1 - (m : ℂ) = y - ((m + 1 : ℕ) : ℂ) := by push_cast; ring
      have e2 : (-1 : ℂ) ^ ((Fin.last (k + r + m) : ℕ) + (k + r + m)) = 1 := by
        rw [Fin.val_last]; exact Even.neg_one_pow ⟨_, rfl⟩
      have e3 : whB_seg (k + 2 * r + 1) 0 (k + r + m + 1) (Fin.last (k + r + m)) =
          (whB_c (k + 2 * r + 1) (k + r + m)) := by
        simp [whB_seg]
      rw [e, e2, e3, one_mul, mul_comm]
    · intro i _ hi
      have hiv : (i : ℕ) < k + r + m := by
        have := i.isLt
        have : (i : ℕ) ≠ k + r + m := fun h => hi (Fin.ext (by simp [h]))
        omega
      rw [hψ _ _ (hR i) ?_, mul_zero, zero_smul]
      simp only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_last]
      split_ifs <;> omega
    · simp

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Introduce `s hs y`. Rewrite using `[Finset.prod_range_zero, one_smul, whB_cminor_cast E rfl (show s = r - 1 by omega) (show s + 1 = r by omega)]`. Consider the case `succ j ih`.

Introduce `s hs y`. Establish `hb0 : s + (k + j + 1 + 1) ≤ k + 2 * r + 1` using `by omega`. Establish `hb1 : s + 1 + (k + j + 1 + 1) ≤ k + 2 * r + 1` using `by omega`. Establish `hC : ∀ c : Fin (k + j + 1 + 1), blk k r (whB_seg (k + 2 * r + 1) s (k + j + 1 + 1) 0) < blk k r (whB_seg (k + 2 * r + 1) (s + 1) (k + j + 1 + 1) c)`. Introduce `c`.

Use `c.isLt` as an intermediate fact. Simplify using `only [blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero]`. Apply the tactic sequence `split_ifs <;> omega`. Establish `key` using `l_cminor_firstrow E hE (blk k r) ψ l hl _ _ y hC`. Use `key.trans ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single (0 : Fin (k + j + 1 + 1))]`. Establish `hs' : IsSimplePair k r (whB_seg (k + 2 * r + 1) s (k + j + 1 + 1) 0) (whB_seg (k + 2 * r + 1) (s + 1) (k + j + 1 + 1) 0)`. Simplify using `only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero]`. Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[← whB_g_eq ψ hs', Fin.succAbove_zero, whB_seg_succ, whB_seg_succ, ih (s + 1) (by omega) y, smul_smul, Finset.prod_range_succ']`.

Establish `e3 : whB_seg (k + 2 * r + 1) s (k + j + 1 + 1) 0 = (whB_c (k + 2 * r + 1) (s))`. Simplify using `[whB_seg]`. Establish `hp : ∏ i ∈ range j, whB_g k r ψ (whB_c (k + 2 * r + 1) (s + 1 + i)) = ∏ i ∈ range j, whB_g k r ψ (whB_c (k + 2 * r + 1) (s + (i + 1)))`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[show s + 1 + i = s + (i + 1) by ring]`.

Rewrite using `[e3, hp, Fin.val_zero, pow_zero, one_mul, add_zero, mul_comm]`. Introduce `c _ hc`. Establish `hcv : 0 < (c : ℕ)`. Break down `Nat.eq_zero_or_pos (c : ℕ) with h | h` into its components or cases. Conclude with `absurd (Fin.ext (by simp [h])) hc`.

Conclude with `h`. Rewrite using `[hψ _ _ (hC c) ?_, mul_zero, zero_smul]`. Use `c.isLt` as an intermediate fact. Simplify using `only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero]`. Apply the tactic sequence `split_ifs <;> omega`.

Simplify using the standard rewrite rules.
-/
theorem whB_phase2a (j : ℕ) : ∀ (s : ℕ), s + j + 1 = r → ∀ y : ℂ,
    l ∘ₗ cminor E (whB_seg (k + 2 * r + 1) s (k + j + 1)) (whB_seg (k + 2 * r + 1) (s + 1) (k + j + 1)) y =
      (∏ i ∈ range j, whB_g k r ψ (whB_c (k + 2 * r + 1) (s + i))) •
        (l ∘ₗ cminor E (whB_seg (k + 2 * r + 1) (r - 1) (k + 1)) (whB_seg (k + 2 * r + 1) r (k + 1)) y) := by
  induction j with
  | zero =>
    intro s hs y
    rw [Finset.prod_range_zero, one_smul,
      whB_cminor_cast E rfl (show s = r - 1 by omega) (show s + 1 = r by omega)]
  | succ j ih =>
    intro s hs y
    have hb0 : s + (k + j + 1 + 1) ≤ k + 2 * r + 1 := by omega
    have hb1 : s + 1 + (k + j + 1 + 1) ≤ k + 2 * r + 1 := by omega
    have hC : ∀ c : Fin (k + j + 1 + 1), blk k r (whB_seg (k + 2 * r + 1) s (k + j + 1 + 1) 0) <
        blk k r (whB_seg (k + 2 * r + 1) (s + 1) (k + j + 1 + 1) c) := by
      intro c
      have := c.isLt
      simp only [blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero]
      split_ifs <;> omega
    have key := l_cminor_firstrow E hE (blk k r) ψ l hl _ _ y hC
    refine key.trans ?_
    rw [Finset.sum_eq_single (0 : Fin (k + j + 1 + 1))]
    · have hs' : IsSimplePair k r (whB_seg (k + 2 * r + 1) s (k + j + 1 + 1) 0)
          (whB_seg (k + 2 * r + 1) (s + 1) (k + j + 1 + 1) 0) := by
        simp only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero]
        split_ifs <;> omega
      rw [← whB_g_eq ψ hs', Fin.succAbove_zero, whB_seg_succ, whB_seg_succ, ih (s + 1) (by omega) y,
        smul_smul, Finset.prod_range_succ']
      have e3 : whB_seg (k + 2 * r + 1) s (k + j + 1 + 1) 0 = (whB_c (k + 2 * r + 1) (s)) := by
        simp [whB_seg]
      have hp : ∏ i ∈ range j, whB_g k r ψ (whB_c (k + 2 * r + 1) (s + 1 + i)) =
          ∏ i ∈ range j, whB_g k r ψ (whB_c (k + 2 * r + 1) (s + (i + 1))) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [show s + 1 + i = s + (i + 1) by ring]
      rw [e3, hp, Fin.val_zero, pow_zero, one_mul, add_zero, mul_comm]
    · intro c _ hc
      have hcv : 0 < (c : ℕ) := by
        rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
        · exact absurd (Fin.ext (by simp [h])) hc
        · exact h
      rw [hψ _ _ (hC c) ?_, mul_zero, zero_smul]
      have := c.isLt
      simp only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero]
      split_ifs <;> omega
    · simp

/- English proof (translation)
Establish `hb0 : r - 1 + (k + 1) ≤ k + 2 * r + 1` using `by omega`. Establish `hb1 : r + (k + 1) ≤ k + 2 * r + 1` using `by omega`. Establish `hC : ∀ c : Fin (k + 1), blk k r (whB_seg (k + 2 * r + 1) (r - 1) (k + 1) 0) < blk k r (whB_seg (k + 2 * r + 1) r (k + 1) c)`. Introduce `c`. Use `c.isLt` as an intermediate fact.

Simplify using `only [blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero]`. Apply the tactic sequence `split_ifs <;> omega`. Use `(l_cminor_firstrow E hE (blk k r) ψ l hl _ _ y hC).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (Fin.last k)]`. Establish `hs' : IsSimplePair k r (whB_seg (k + 2 * r + 1) (r - 1) (k + 1) 0) (whB_seg (k + 2 * r + 1) r (k + 1) (Fin.last k))`.

Simplify using `only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero, Fin.val_last]`. Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[← whB_g_eq ψ hs', Fin.succAbove_last, whB_seg_castSucc, whB_seg_succ, Fin.val_last, Nat.sub_add_cancel hr]`. Establish `e3 : whB_seg (k + 2 * r + 1) (r - 1) (k + 1) 0 = (whB_c (k + 2 * r + 1) (r - 1))`. Simplify using `[whB_seg]`.

Rewrite using `[e3]`. Introduce `c _ hc`. Establish `hcv : (c : ℕ) < k`. Use `c.isLt` as an intermediate fact. Establish `: (c : ℕ) ≠ k` using `fun h => hc (Fin.ext (by simp [h]))`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hψ _ _ (hC c) ?_, mul_zero, zero_smul]`. Simplify using `only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero]`. Apply the tactic sequence `split_ifs <;> omega`. Simplify using the standard rewrite rules.
-/
theorem whB_phase2b (hr : 0 < r) (y : ℂ) :
    l ∘ₗ cminor E (whB_seg (k + 2 * r + 1) (r - 1) (k + 1)) (whB_seg (k + 2 * r + 1) r (k + 1)) y =
      ((-1) ^ k * whB_g k r ψ (whB_c (k + 2 * r + 1) (r - 1))) •
        (l ∘ₗ cminor E (whB_seg (k + 2 * r + 1) r k) (whB_seg (k + 2 * r + 1) r k) y) := by
  have hb0 : r - 1 + (k + 1) ≤ k + 2 * r + 1 := by omega
  have hb1 : r + (k + 1) ≤ k + 2 * r + 1 := by omega
  have hC : ∀ c : Fin (k + 1), blk k r (whB_seg (k + 2 * r + 1) (r - 1) (k + 1) 0) <
      blk k r (whB_seg (k + 2 * r + 1) r (k + 1) c) := by
    intro c; have := c.isLt
    simp only [blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero]
    split_ifs <;> omega
  refine (l_cminor_firstrow E hE (blk k r) ψ l hl _ _ y hC).trans ?_
  rw [Finset.sum_eq_single (Fin.last k)]
  · have hs' : IsSimplePair k r (whB_seg (k + 2 * r + 1) (r - 1) (k + 1) 0)
        (whB_seg (k + 2 * r + 1) r (k + 1) (Fin.last k)) := by
      simp only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero, Fin.val_last]
      split_ifs <;> omega
    rw [← whB_g_eq ψ hs', Fin.succAbove_last, whB_seg_castSucc, whB_seg_succ, Fin.val_last,
      Nat.sub_add_cancel hr]
    have e3 : whB_seg (k + 2 * r + 1) (r - 1) (k + 1) 0 = (whB_c (k + 2 * r + 1) (r - 1)) := by
      simp [whB_seg]
    rw [e3]
  · intro c _ hc
    have hcv : (c : ℕ) < k := by
      have := c.isLt
      have : (c : ℕ) ≠ k := fun h => hc (Fin.ext (by simp [h]))
      omega
    rw [hψ _ _ (hC c) ?_, mul_zero, zero_smul]
    simp only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero]
    split_ifs <;> omega
  · simp

end Phases

/- English proof (translation)
Establish `hb : 0 + (k + 2 * r) ≤ k + 2 * r + 1` using `by omega`. Establish `hb' : 1 + (k + 2 * r) ≤ k + 2 * r + 1` using `by omega`. Establish `h1 : (Fin.castSucc : Fin (k + 2 * r) → Fin (k + 2 * r + 1)) = whB_seg (k + 2 * r + 1) 0 (k + 2 * r)`. Use function extensionality and compare the values at `i`. Apply `Fin.ext` to reduce the goal to its premises.

Rewrite using `[whB_seg_val hb]`. Simplify using the standard rewrite rules. Establish `h2 : (Fin.succ : Fin (k + 2 * r) → Fin (k + 2 * r + 1)) = whB_seg (k + 2 * r + 1) 1 (k + 2 * r)`. Use function extensionality and compare the values at `i`. Apply `Fin.ext` to reduce the goal to its premises.

Rewrite using `[whB_seg_val hb']`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `hW : whB_seg (k + 2 * r + 1) r k = wIdx k r ∘ id`. Use function extensionality and compare the values at `i; apply Fin.ext; rw [whB_seg_val (by omega)]; rfl`.

Establish `hinj : Function.Injective (wIdx k r)`. Introduce `a b h`. Apply `Fin.ext` to reduce the goal to its premises. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `[wIdx] at this`.

Conclude with `this`. Rewrite using `[h1, h2, whB_cminor_cast E (show k + 2 * r = k + r + r by ring) rfl rfl x, whB_phase1 k r E ψ l hE hl hψ r le_rfl x, whB_cminor_cast E (show k + r = k + (r - 1) + 1 by omega) rfl (show 1 = 0 + 1 from rfl) (x - r), whB_phase2a k r E ψ l hE hl hψ (r - 1) 0 (by omega) (x - r), whB_p …`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem capelli_whittaker (k r : ℕ) (E : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → Module.End ℂ M)
    (D : Fin k → Fin k → Module.End ℂ R) (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ)
    (l : M →ₗ[ℂ] R) (x : ℂ) (hE : IsGlRep E) (hr : 0 < r)
    (hl : ∀ a b, blk k r a < blk k r b → l ∘ₗ E a b = ψ a b • l)
    (hψ : ∀ a b, blk k r a < blk k r b → ¬ IsSimplePair k r a b → ψ a b = 0)
    (hD : ∀ i j, l ∘ₗ E (wIdx k r i) (wIdx k r j) = D i j ∘ₗ l) :
    l ∘ₗ cminor E Fin.castSucc Fin.succ x =
      ((-1) ^ k * kappa k r ψ) • (capelliC D (x - (r : ℂ)) ∘ₗ l) := by
  have hb : 0 + (k + 2 * r) ≤ k + 2 * r + 1 := by omega
  have hb' : 1 + (k + 2 * r) ≤ k + 2 * r + 1 := by omega
  have h1 : (Fin.castSucc : Fin (k + 2 * r) → Fin (k + 2 * r + 1)) =
      whB_seg (k + 2 * r + 1) 0 (k + 2 * r) := by
    funext i; apply Fin.ext; rw [whB_seg_val hb]; simp
  have h2 : (Fin.succ : Fin (k + 2 * r) → Fin (k + 2 * r + 1)) =
      whB_seg (k + 2 * r + 1) 1 (k + 2 * r) := by
    funext i; apply Fin.ext; rw [whB_seg_val hb']; simp; ring
  have hW : whB_seg (k + 2 * r + 1) r k = wIdx k r ∘ id := by
    funext i; apply Fin.ext; rw [whB_seg_val (by omega)]; rfl
  have hinj : Function.Injective (wIdx k r) := by
    intro a b h; apply Fin.ext; have := congrArg Fin.val h; simp [wIdx] at this; exact this
  rw [h1, h2, whB_cminor_cast E (show k + 2 * r = k + r + r by ring) rfl rfl x,
    whB_phase1 k r E ψ l hE hl hψ r le_rfl x,
    whB_cminor_cast E (show k + r = k + (r - 1) + 1 by omega) rfl (show 1 = 0 + 1 from rfl) (x - r),
    whB_phase2a k r E ψ l hE hl hψ (r - 1) 0 (by omega) (x - r),
    whB_phase2b k r E ψ l hE hl hψ hr (x - r), hW,
    cminor_intertwine E D (wIdx k r) hinj l hD id id (x - r), smul_smul, smul_smul, whB_kappa k r hr ψ]
  congr 1; ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
