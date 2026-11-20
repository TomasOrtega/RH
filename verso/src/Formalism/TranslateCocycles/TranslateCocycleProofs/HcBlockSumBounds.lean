import Formalism.TranslateCocycles.StatementHC

namespace Formalism.CG

open Finset

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[show a + (n + 1) = (a + n) + 1 by ring, Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hc_sumIcc (f : ℕ → ℚ) (a n : ℕ) :
    ∑ i ∈ Icc (a + 1) (a + n), f i = ∑ i ∈ range n, f (a + 1 + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show a + (n + 1) = (a + n) + 1 by ring, Finset.sum_Icc_succ_top (by omega), ih,
      Finset.sum_range_succ]
    congr 2; ring

/- English proof (translation)
Establish `h` using `hc_sumIcc f 0 n`. Simplify using `only [Nat.zero_add] at h`. Rewrite using `[h]; exact Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm])`.
-/
private lemma hc_sumIcc1 (f : ℕ → ℚ) (n : ℕ) :
    ∑ i ∈ Icc 1 n, f i = ∑ i ∈ range n, f (i + 1) := by
  have h := hc_sumIcc f 0 n
  simp only [Nat.zero_add] at h
  rw [h]; exact Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm])

/- English proof (translation)
Rewrite using `[Finset.sum_Ico_eq_sum_range]`. Simplify using `only [Nat.add_sub_cancel]`. Conclude with `Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm])`.
-/
private lemma hc_sumIco1 (f : ℕ → ℚ) (n : ℕ) :
    ∑ i ∈ Ico 1 (n + 1), f i = ∑ i ∈ range n, f (i + 1) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  exact Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm])

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[show a + (n + 1) = (a + n) + 1 by ring, Finset.sum_Ioc_succ_top (by omega), ih, Finset.sum_range_succ]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hc_sumIoc (f : ℕ → ℚ) (a n : ℕ) :
    ∑ i ∈ Ioc a (a + n), f i = ∑ i ∈ range n, f (a + 1 + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show a + (n + 1) = (a + n) + 1 by ring, Finset.sum_Ioc_succ_top (by omega), ih,
      Finset.sum_range_succ]
    congr 2; ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[show k + (n + 1) * c = (k + n * c) + c by ring, Finset.sum_range_add, ih, Finset.sum_range_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hc_sumBlocks (g : ℕ → ℚ) (k c n : ℕ) :
    ∑ l ∈ range (k + n * c), g l
      = ∑ l ∈ range k, g l + ∑ i ∈ range n, ∑ s ∈ range c, g (k + i * c + s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show k + (n + 1) * c = (k + n * c) + c by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ]
    ring

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro i _ hd`. Simplify using `at hd`. Substitute `hd` using the available equality.

Simplify using the standard rewrite rules. Consider the case `succ d ih`. Introduce `i hi hd`. Establish `h1` using `h i hi (by omega)`. Establish `h2` using `ih (i + 1) (by omega) (by omega)`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma hc_chain (f : ℕ → ℚ) (c : ℚ) (n : ℕ)
    (h : ∀ i, 1 ≤ i → i < n → f i + c ≤ f (i + 1)) :
    ∀ (d i : ℕ), 1 ≤ i → i + d = n → f i + d * c ≤ f n := by
  intro d
  induction d with
  | zero => intro i _ hd; simp at hd; subst hd; simp
  | succ d ih =>
    intro i hi hd
    have h1 := h i hi (by omega)
    have h2 := ih (i + 1) (by omega) (by omega)
    push_cast
    linarith

/- English proof (translation)
Simplify using `[HCparam, h]`.
-/
private lemma hc_param_head (k t : ℕ) (u e : ℕ → ℚ) (l : ℕ) (h : l ≤ k) :
    HCparam k t u e l = u l := by
  simp [HCparam, h]

/- English proof (translation)
Unfold `HCparam`. Establish `h1 : ¬ (k + i * (t + 1) + s + 1 ≤ k)` using `by omega`. Establish `h2 : k + i * (t + 1) + s + 1 - k - 1 = (t + 1) * i + s`. Rewrite using `[Nat.mul_comm]`. Use linear arithmetic over natural numbers and integers.

Establish `h3 : ((t + 1) * i + s) / (t + 1) = i`. Rewrite using `[Nat.mul_add_div (by omega), Nat.div_eq_of_lt hs]; simp`. Establish `h4 : ((t + 1) * i + s) % (t + 1) = s`. Rewrite using `[Nat.mul_add_mod, Nat.mod_eq_of_lt hs]`. Rewrite using `[if_neg h1, h2, h3, h4]`.
-/
private lemma hc_param_block (k t : ℕ) (u e : ℕ → ℚ) (i s : ℕ) (hs : s < t + 1) :
    HCparam k t u e (k + i * (t + 1) + s + 1) = -e (i + 1) + (t : ℚ) / 2 - (s : ℚ) := by
  unfold HCparam
  have h1 : ¬ (k + i * (t + 1) + s + 1 ≤ k) := by omega
  have h2 : k + i * (t + 1) + s + 1 - k - 1 = (t + 1) * i + s := by
    rw [Nat.mul_comm]; omega
  have h3 : ((t + 1) * i + s) / (t + 1) = i := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hs]; simp
  have h4 : ((t + 1) * i + s) % (t + 1) = s := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
  rw [if_neg h1, h2, h3, h4]

/- English proof (translation)
Establish `h1 : (l - k - 1) / (t + 1) * (t + 1) + (l - k - 1) % (t + 1) = l - k - 1` using `Nat.div_add_mod' _ _`. Use `⟨(l - k - 1) / (t + 1), (l - k - 1) % (t + 1), Nat.mod_lt _ (Nat.succ_pos t), ?_⟩` and prove the remaining obligations. Generalize the expression as in `(l - k - 1) / (t + 1) * (t + 1) = q at h1 ⊢`. Generalize the expression as in `(l - k - 1) % (t + 1) = r at h1 ⊢`. Use linear arithmetic over natural numbers and integers.
-/
private lemma hc_decomp (k t l : ℕ) (h : k < l) :
    ∃ i s, s < t + 1 ∧ l = k + i * (t + 1) + s + 1 := by
  have h1 : (l - k - 1) / (t + 1) * (t + 1) + (l - k - 1) % (t + 1) = l - k - 1 :=
    Nat.div_add_mod' _ _
  refine ⟨(l - k - 1) / (t + 1), (l - k - 1) % (t + 1), Nat.mod_lt _ (Nat.succ_pos t), ?_⟩
  generalize (l - k - 1) / (t + 1) * (t + 1) = q at h1 ⊢
  generalize (l - k - 1) % (t + 1) = r at h1 ⊢
  omega

/- English proof (translation)
Establish `: i * (t + 1) < n * (t + 1)` using `by omega`. Conclude with `Nat.lt_of_mul_lt_mul_right this`.
-/
private lemma hc_decomp_lt (k t i s n : ℕ) (h : k + i * (t + 1) + s + 1 ≤ k + n * (t + 1)) :
    i < n := by
  have : i * (t + 1) < n * (t + 1) := by omega
  exact Nat.lt_of_mul_lt_mul_right this

/- English proof (translation)
Unfold `HCnu HClam0 HCwG HCrank`. Rewrite using `[hc_param_head _ _ _ _ _ h]`. Simplify using `only [Nat.add_sub_cancel]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hc_nu_head (k t : ℕ) (u e : ℕ → ℚ) (j i : ℕ) (h : i + 1 ≤ k) :
    HCnu k t u e (j + 1) (i + 1) = HClam0 k u (i + 1) + HCwG k t e (j + 1) := by
  unfold HCnu HClam0 HCwG HCrank
  rw [hc_param_head _ _ _ _ _ h]
  simp only [Nat.add_sub_cancel]
  push_cast; ring

/- English proof (translation)
Unfold `HCnu HCrank`. Rewrite using `[hc_param_block _ _ _ _ _ _ hs]`. Simplify using `only [Nat.add_sub_cancel]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hc_nu_block (k t : ℕ) (u e : ℕ → ℚ) (j i s : ℕ) (hs : s < t + 1) :
    HCnu k t u e (j + 1) (k + i * (t + 1) + s + 1)
      = (e (j + 1) - e (i + 1)) - ((j : ℚ) - (i : ℚ)) * ((t : ℚ) + 1) := by
  unfold HCnu HCrank
  rw [hc_param_block _ _ _ _ _ _ hs]
  simp only [Nat.add_sub_cancel]
  push_cast; ring

/- English proof (translation)
Unfold `HCdeg HCblockSum`. Simplify using `only [Nat.add_sub_cancel]`. Rewrite using `[hc_sumIcc1, HCrank, hc_sumBlocks, hc_sumIcc1, hc_sumIco1]`. Establish `hhead : ∑ l ∈ range k, HCnu k t u e (j + 1) (l + 1) = ∑ l ∈ range k, HClam0 k u (l + 1) + (k : ℚ) * HCwG k t e (j + 1)`. Rewrite using `[Finset.sum_congr rfl (fun l hl => hc_nu_head k t u e j l (by have := Finset.mem_range.mp hl; omega)), Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`.

Establish `hblock : ∑ i ∈ range j, ∑ s ∈ range (t + 1), HCnu k t u e (j + 1) (k + i * (t + 1) + s + 1) = ((t : ℚ) + 1) * ∑ i ∈ range j, ((e (j + 1) - e (i + 1)) - (((j + 1 : ℕ) : ℚ) - ((i + 1 : ℕ) : ℚ)) * ((t : ℚ) + 1))`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (fun s hs => hc_nu_block k t u e j i s (Finset.mem_range.mp hs)), Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hhead, hblock]`.
-/
private lemma hc_degree (k t : ℕ) (u e : ℕ → ℚ) (j : ℕ) :
    HCdeg k t u e (j + 1)
      = ∑ i ∈ Icc 1 k, HClam0 k u i + (k : ℚ) * HCwG k t e (j + 1) + HCblockSum t e (j + 1) := by
  unfold HCdeg HCblockSum
  simp only [Nat.add_sub_cancel]
  rw [hc_sumIcc1, HCrank, hc_sumBlocks, hc_sumIcc1, hc_sumIco1]
  have hhead : ∑ l ∈ range k, HCnu k t u e (j + 1) (l + 1)
      = ∑ l ∈ range k, HClam0 k u (l + 1) + (k : ℚ) * HCwG k t e (j + 1) := by
    rw [Finset.sum_congr rfl (fun l hl => hc_nu_head k t u e j l
      (by have := Finset.mem_range.mp hl; omega)), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  have hblock : ∑ i ∈ range j, ∑ s ∈ range (t + 1), HCnu k t u e (j + 1) (k + i * (t + 1) + s + 1)
      = ((t : ℚ) + 1) * ∑ i ∈ range j,
          ((e (j + 1) - e (i + 1)) - (((j + 1 : ℕ) : ℚ) - ((i + 1 : ℕ) : ℚ)) * ((t : ℚ) + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_congr rfl (fun s hs => hc_nu_block k t u e j i s (Finset.mem_range.mp hs)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring
  rw [hhead, hblock]

/- English proof (translation)
Introduce `k t u e j hj`. Take `⟨j, rfl⟩ : ∃ j', j = j' + 1` from `⟨j - 1, by omega⟩`. Use `⟨?_, hc_degree k t u e j⟩` and prove the remaining obligations. Rewrite using `[hc_degree]`. Unfold `HCwG`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hCDegree : HCDegree := by
  intro k t u e j hj
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  refine ⟨?_, hc_degree k t u e j⟩
  rw [hc_degree]; unfold HCwG; ring

/- English proof (translation)
Introduce `k t u e b1 j hk hj hu huk he1 he`. Take `⟨j, rfl⟩ : ∃ j', j = j' + 1` from `⟨j - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Establish `hstep : ∀ l, 1 ≤ l → l < HCrank k t (j + 1) → HCparam k t u e (l + 1) + 1 ≤ HCparam k t u e l`. Introduce `l hl1 hl`.

Break down `Nat.lt_trichotomy l k with hlk | hlk | hlk` into its components or cases. Rewrite using `[hc_param_head _ _ _ _ _ (by omega : l + 1 ≤ k), hc_param_head _ _ _ _ _ hlk.le]`. Conclude with `hu l hl1 hlk`. Substitute `hlk` using the available equality. Establish `h0` using `hc_param_block l t u e 0 0 (by omega)`.

Simplify using `only [Nat.zero_mul, Nat.add_zero, Nat.zero_add] at h0`. Rewrite using `[h0, hc_param_head _ _ _ _ _ le_rfl]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨i, s, hs, rfl⟩` from `hc_decomp k t l hlk`.

Rewrite using `[hc_param_block _ _ _ _ _ _ hs]`. Distinguish the cases in `hst : s + 1 < t + 1`. Use `hc_param_block k t u e i (s + 1) hst` as an intermediate fact. Rewrite using `[show k + i * (t + 1) + s + 1 + 1 = k + i * (t + 1) + (s + 1) + 1 by ring, this]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hst' : s = t` using `by omega`. Substitute `hst'` using the available equality. Use `hc_param_block k s u e (i + 1) 0 (by omega)` as an intermediate fact. Rewrite using `[show k + i * (s + 1) + s + 1 + 1 = k + (i + 1) * (s + 1) + 0 + 1 by ring, this]`.

Establish `hij : i + 1 < j + 1`. Unfold `HCrank at hl`. Establish `h' : k + (i + 1) * (s + 1) + 0 + 1 ≤ k + (j + 1) * (s + 1)`. Establish `: (i + 1) * (s + 1) = i * (s + 1) + s + 1` using `by ring`. Use linear arithmetic over natural numbers and integers.

Conclude with `hc_decomp_lt k s (i + 1) 0 (j + 1) h'`. Use `he (i + 1) (by omega) hij` as an intermediate fact. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hrank : HCrank k t j ≤ HCrank k t (j + 1)`.

Unfold `HCrank`. Establish `: (j + 1) * (t + 1) = j * (t + 1) + (t + 1)` using `by ring`. Use linear arithmetic over natural numbers and integers. Establish `hej : ∀ i, i ≤ j → e (i + 1) + ((j : ℚ) - i) * ((t : ℚ) + 3) ≤ e (j + 1)`. Introduce `i hi`.

Use `hc_chain e ((t : ℚ) + 3) (j + 1) he (j - i) (i + 1) (by omega) (by omega)` as an intermediate fact. Rewrite `this` using `[Nat.cast_sub hi]`. Then use the resulting hypothesis. Establish `hnuk : 2 * ((j + 1 : ℕ) : ℚ) - 1 ≤ HCnu k t u e (j + 1) k`. Take `⟨k', rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[hc_nu_head _ _ _ _ _ _ le_rfl]`.

Unfold `HClam0 HCwG`. Use `hej 0 (by omega)` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Use the polynomial consequences of the given equalities and inequalities. Establish `hblk : ∀ i s, i < j → s < t + 1 → 2 * ((j : ℚ) - i) ≤ HCnu k t u e (j + 1) (k + i * (t + 1) + s + 1)`.

Introduce `i s hi hs`. Rewrite using `[hc_nu_block _ _ _ _ _ _ _ hs]`. Use `hej i hi.le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Use `⟨hstep, ?_, hnuk, ?_, ?_⟩` and prove the remaining obligations.

Introduce `l hl1 hl`. Use `hstep l hl1 (by omega)` as an intermediate fact. Unfold `HCnu`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `i s hi hij hs1 hs`. Take `⟨i, rfl⟩ : ∃ i', i = i' + 1` from `⟨i - 1, by omega⟩`. Take `⟨s, rfl⟩ : ∃ s', s = s' + 1` from `⟨s - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Rewrite using `[← Nat.add_assoc]`.

Use `hblk i s (by omega) (by omega)` as an intermediate fact. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `l hl1 hl`. Distinguish the cases in `hlk : l ≤ k`.

Take `⟨l, rfl⟩ : ∃ l', l = l' + 1` from `⟨l - 1, by omega⟩`. Take `⟨k', rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`. Rewrite `hnuk` using `[hc_nu_head _ _ _ _ _ _ le_rfl]`. Rewrite using `[hc_nu_head _ _ _ _ _ _ hlk]`. Establish `hc` using `hc_chain (fun i => -u i) 1 (k' + 1) (fun i h1 h2 => by`.

Use `hu i h1 h2; show -u i + 1 ≤ -u (i + 1); linarith) (k' - l) (l + 1) (by omega) (by omega)` as an intermediate fact. Rewrite `hc` using `[Nat.cast_sub (by omega)]`. Unfold `HClam0 at hnuk ⊢`. Move the coercions through the operations in `at hnuk hc ⊢`. Establish `hj0 : (0 : ℚ) ≤ j` using `Nat.cast_nonneg j`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨i, s, hs, rfl⟩` from `hc_decomp k t l (by omega)`. Establish `hij` using `hc_decomp_lt _ _ _ _ _ hl`. Establish `h1` using `hblk i s hij hs`. Establish `h2 : (i : ℚ) ≤ j` using `by exact_mod_cast hij.le`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hCPartition : HCPartition := by
  intro k t u e b1 j hk hj hu huk he1 he
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hstep : ∀ l, 1 ≤ l → l < HCrank k t (j + 1) →
      HCparam k t u e (l + 1) + 1 ≤ HCparam k t u e l := by
    intro l hl1 hl
    rcases Nat.lt_trichotomy l k with hlk | hlk | hlk
    · rw [hc_param_head _ _ _ _ _ (by omega : l + 1 ≤ k), hc_param_head _ _ _ _ _ hlk.le]
      exact hu l hl1 hlk
    · subst hlk
      have h0 := hc_param_block l t u e 0 0 (by omega)
      simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add] at h0
      rw [h0, hc_param_head _ _ _ _ _ le_rfl]
      push_cast; linarith
    · obtain ⟨i, s, hs, rfl⟩ := hc_decomp k t l hlk
      rw [hc_param_block _ _ _ _ _ _ hs]
      by_cases hst : s + 1 < t + 1
      · have := hc_param_block k t u e i (s + 1) hst
        rw [show k + i * (t + 1) + s + 1 + 1 = k + i * (t + 1) + (s + 1) + 1 by ring, this]
        push_cast; linarith
      · have hst' : s = t := by omega
        subst hst'
        have := hc_param_block k s u e (i + 1) 0 (by omega)
        rw [show k + i * (s + 1) + s + 1 + 1 = k + (i + 1) * (s + 1) + 0 + 1 by ring, this]
        have hij : i + 1 < j + 1 := by
          unfold HCrank at hl
          have h' : k + (i + 1) * (s + 1) + 0 + 1 ≤ k + (j + 1) * (s + 1) := by
            have : (i + 1) * (s + 1) = i * (s + 1) + s + 1 := by ring
            omega
          exact hc_decomp_lt k s (i + 1) 0 (j + 1) h'
        have := he (i + 1) (by omega) hij
        push_cast; linarith
  have hrank : HCrank k t j ≤ HCrank k t (j + 1) := by
    unfold HCrank
    have : (j + 1) * (t + 1) = j * (t + 1) + (t + 1) := by ring
    omega
  have hej : ∀ i, i ≤ j → e (i + 1) + ((j : ℚ) - i) * ((t : ℚ) + 3) ≤ e (j + 1) := by
    intro i hi
    have := hc_chain e ((t : ℚ) + 3) (j + 1) he (j - i) (i + 1) (by omega) (by omega)
    rwa [Nat.cast_sub hi] at this
  have hnuk : 2 * ((j + 1 : ℕ) : ℚ) - 1 ≤ HCnu k t u e (j + 1) k := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hc_nu_head _ _ _ _ _ _ le_rfl]
    unfold HClam0 HCwG
    have := hej 0 (by omega)
    push_cast at this ⊢
    nlinarith
  have hblk : ∀ i s, i < j → s < t + 1 →
      2 * ((j : ℚ) - i) ≤ HCnu k t u e (j + 1) (k + i * (t + 1) + s + 1) := by
    intro i s hi hs
    rw [hc_nu_block _ _ _ _ _ _ _ hs]
    have := hej i hi.le
    nlinarith
  refine ⟨hstep, ?_, hnuk, ?_, ?_⟩
  · intro l hl1 hl
    have := hstep l hl1 (by omega)
    unfold HCnu
    push_cast; linarith
  · intro i s hi hij hs1 hs
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [← Nat.add_assoc]
    have := hblk i s (by omega) (by omega)
    push_cast; linarith
  · intro l hl1 hl
    by_cases hlk : l ≤ k
    · obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [hc_nu_head _ _ _ _ _ _ le_rfl] at hnuk
      rw [hc_nu_head _ _ _ _ _ _ hlk]
      have hc := hc_chain (fun i => -u i) 1 (k' + 1) (fun i h1 h2 => by
        have := hu i h1 h2; show -u i + 1 ≤ -u (i + 1); linarith) (k' - l) (l + 1) (by omega) (by omega)
      rw [Nat.cast_sub (by omega)] at hc
      unfold HClam0 at hnuk ⊢
      push_cast at hnuk hc ⊢
      have hj0 : (0 : ℚ) ≤ j := Nat.cast_nonneg j
      linarith
    · obtain ⟨i, s, hs, rfl⟩ := hc_decomp k t l (by omega)
      have hij := hc_decomp_lt _ _ _ _ _ hl
      have h1 := hblk i s hij hs
      have h2 : (i : ℚ) ≤ j := by exact_mod_cast hij.le
      linarith

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Finset.sum_range_succ, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hc_halfsum (k : ℚ) (n : ℕ) :
    ∑ i ∈ range n, ((k + 1 - 2 * ((i + 1 : ℕ) : ℚ)) / 2) = n * (k - n) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/- English proof (translation)
Introduce `k u`. Establish `h1 : ∑ i ∈ Icc 1 k, HClam0 k u i = ∑ i ∈ Icc 1 k, u i`. Unfold `HClam0`. Rewrite using `[Finset.sum_sub_distrib, hc_sumIcc1 (fun i => ((k : ℚ) + 1 - 2 * (i : ℚ)) / 2), hc_halfsum]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Introduce `a b' hk hu1 huk`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `HClam0`. Rewrite using `[hu1]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Unfold `HClam0`. Rewrite using `[huk]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1]`. Take `⟨n, rfl⟩ : ∃ n, k = n + 2` from `⟨k - 2, by omega⟩`. Establish `hI : Ioo 1 (n + 2) = Icc (1 + 1) (1 + n)`. Use extensionality with `x`. Simplify using `only [Finset.mem_Ioo, Finset.mem_Icc]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hI, hc_sumIcc, hc_sumIcc1, Finset.sum_range_succ, Finset.sum_range_succ', huk]`. Simplify using `only [Nat.zero_add]`. Rewrite using `[hu1]`. Establish `: ∑ i ∈ range n, u (i + 1 + 1) = ∑ i ∈ range n, u (1 + 1 + i)` using `Finset.sum_congr rfl (fun i _ => by congr 1; ring)`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hCLamSum : HCLamSum := by
  intro k u
  have h1 : ∑ i ∈ Icc 1 k, HClam0 k u i = ∑ i ∈ Icc 1 k, u i := by
    unfold HClam0
    rw [Finset.sum_sub_distrib, hc_sumIcc1 (fun i => ((k : ℚ) + 1 - 2 * (i : ℚ)) / 2), hc_halfsum]
    ring
  refine ⟨h1, ?_⟩
  intro a b' hk hu1 huk
  refine ⟨?_, ?_, ?_⟩
  · unfold HClam0; rw [hu1]; push_cast; ring
  · unfold HClam0; rw [huk]; ring
  · rw [h1]
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    have hI : Ioo 1 (n + 2) = Icc (1 + 1) (1 + n) := by
      ext x; simp only [Finset.mem_Ioo, Finset.mem_Icc]; omega
    rw [hI, hc_sumIcc, hc_sumIcc1, Finset.sum_range_succ, Finset.sum_range_succ', huk]
    simp only [Nat.zero_add]
    rw [hu1]
    have : ∑ i ∈ range n, u (i + 1 + 1) = ∑ i ∈ range n, u (1 + 1 + i) :=
      Finset.sum_congr rfl (fun i _ => by congr 1; ring)
    rw [this]; ring

/- English proof (translation)
Establish `h` using `hc_chain e ((t : ℚ) + 3) j he (j - i) i hi (by omega)`. Rewrite `h` using `[Nat.cast_sub hij]`. Establish `h2 : (0 : ℚ) ≤ (j : ℚ) - i`. Establish `: (i : ℚ) ≤ j` using `by exact_mod_cast hij`. Combine the linear equalities and inequalities to obtain the conclusion.

Use the polynomial consequences of the given equalities and inequalities.
-/
private lemma hc_row_lower (t j : ℕ) (e : ℕ → ℚ)
    (he : ∀ i, 1 ≤ i → i < j → e i + ((t : ℚ) + 3) ≤ e (i + 1)) (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
    0 ≤ (e j - e i) - ((j : ℚ) - (i : ℚ)) * ((t : ℚ) + 1) := by
  have h := hc_chain e ((t : ℚ) + 3) j he (j - i) i hi (by omega)
  rw [Nat.cast_sub hij] at h
  have h2 : (0 : ℚ) ≤ (j : ℚ) - i := by
    have : (i : ℚ) ≤ j := by exact_mod_cast hij
    linarith
  nlinarith

/- English proof (translation)
Establish `ht : (0 : ℚ) ≤ (t : ℚ) + 1` using `by positivity`. Unfold `HCblockSum`. Use `⟨mul_nonneg ht (Finset.sum_nonneg fun i hi => ?_), ?_⟩` and prove the remaining obligations. Use `Finset.mem_Ico.mp hi` as an intermediate fact. Conclude with `hc_row_lower t j e he i this.1 this.2.le`.

Establish `h` using `Finset.sum_le_card_nsmul (Ico 1 j) (fun i => (e j - e i) - ((j : ℚ) - (i : ℚ)) * ((t : ℚ) + 1)) M (fun i hi => by`. Establish `hi'` using `Finset.mem_Ico.mp hi`. Establish `h1` using `hM i hi'.1 hi'.2`. Establish `h2 : (0 : ℚ) ≤ (j : ℚ) - i`. Establish `: (i : ℚ) ≤ j` using `by exact_mod_cast hi'.2.le`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `mul_nonneg h2 ht`. Use `show (e j - e i) - ((j : ℚ) - (i : ℚ)) * ((t : ℚ) + 1) ≤ M`. Use the proof step `linarith)`. Rewrite `h` using `[Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hj, Nat.cast_one]`.

Combine the equalities or inequalities in the displayed calculation.
-/
private lemma hc_blockSum_bounds (t j : ℕ) (e : ℕ → ℚ) (M : ℚ) (hj : 1 ≤ j)
    (he : ∀ i, 1 ≤ i → i < j → e i + ((t : ℚ) + 3) ≤ e (i + 1))
    (hM : ∀ i, 1 ≤ i → i < j → e j - e i ≤ M) :
    0 ≤ HCblockSum t e j ∧ HCblockSum t e j ≤ ((t : ℚ) + 1) * ((j : ℚ) - 1) * M := by
  have ht : (0 : ℚ) ≤ (t : ℚ) + 1 := by positivity
  unfold HCblockSum
  refine ⟨mul_nonneg ht (Finset.sum_nonneg fun i hi => ?_), ?_⟩
  · have := Finset.mem_Ico.mp hi
    exact hc_row_lower t j e he i this.1 this.2.le
  · have h := Finset.sum_le_card_nsmul (Ico 1 j)
      (fun i => (e j - e i) - ((j : ℚ) - (i : ℚ)) * ((t : ℚ) + 1)) M (fun i hi => by
        have hi' := Finset.mem_Ico.mp hi
        have h1 := hM i hi'.1 hi'.2
        have h2 : (0 : ℚ) ≤ (j : ℚ) - i := by
          have : (i : ℚ) ≤ j := by exact_mod_cast hi'.2.le
          linarith
        have h3 := mul_nonneg h2 ht
        show (e j - e i) - ((j : ℚ) - (i : ℚ)) * ((t : ℚ) + 1) ≤ M
        linarith)
    rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hj, Nat.cast_one] at h
    calc _ ≤ ((t : ℚ) + 1) * (((j : ℚ) - 1) * M) := mul_le_mul_of_nonneg_left h ht
      _ = _ := by ring

/- English proof (translation)
Introduce `k t m j u e b S η hj hjm ht hkS hkη he hb`. Establish `hk0 : (0 : ℚ) ≤ k` using `Nat.cast_nonneg k`. Establish `ht1 : (1 : ℚ) ≤ t` using `by exact_mod_cast ht`. Establish `hj1 : (1 : ℚ) ≤ j` using `by exact_mod_cast hj`. Establish `hjm' : (j : ℚ) ≤ m` using `by exact_mod_cast hjm`.

Establish `hη : 0 ≤ η` using `le_trans hk0 hkη`. Take `⟨hB0, hB1⟩` from `hc_blockSum_bounds t j e η hj he (fun i h1 h2 => by`. Use `hb i h1 h2` as an intermediate fact. Use the proof step `linarith)`. Establish `hB2 : ((t : ℚ) + 1) * ((j : ℚ) - 1) * η ≤ 2 * m * t * η`.

Apply `mul_le_mul_of_nonneg_right _ hη` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `hA1 : (k : ℚ) * ((k : ℚ) + (2 * (j : ℚ) - 1) * ((t : ℚ) + 1)) / 2 ≤ (k : ℚ) ^ 2 + k * m * ((t : ℚ) + 1)`. Establish `h1 : 0 ≤ (k : ℚ) * ((t : ℚ) + 1) * ((m : ℚ) - j)` using `mul_nonneg (mul_nonneg hk0 (by linarith)) (by linarith)`. Establish `h2 : 0 ≤ (k : ℚ) * ((t : ℚ) + 1)` using `mul_nonneg hk0 (by linarith)`.

Use polynomial arithmetic with `[sq_nonneg (k : ℚ)]`. Establish `hA2 : (k : ℚ) ^ 2 + k * m * ((t : ℚ) + 1) ≤ k * S + 2 * m * t * η`. Establish `hm0 : (0 : ℚ) ≤ m` using `Nat.cast_nonneg m`. Establish `h1 : 0 ≤ (k : ℚ) * (S - k)` using `mul_nonneg hk0 (by linarith)`. Establish `h2 : 0 ≤ (m : ℚ) * t * (η - k)` using `mul_nonneg (mul_nonneg hm0 (by linarith)) (by linarith)`.

Establish `h3 : 0 ≤ (k : ℚ) * m * ((t : ℚ) - 1)` using `mul_nonneg (mul_nonneg hk0 hm0) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hd` using `(hCDegree k t u e j hj).1`. Use `⟨hB0, hB1, hB2, hA1, hA2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hd]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hd]`. Establish `hA0 : 0 ≤ (k : ℚ) * ((k : ℚ) + (2 * (j : ℚ) - 1) * ((t : ℚ) + 1)) / 2`. Establish `: 0 ≤ (2 * (j : ℚ) - 1) * ((t : ℚ) + 1)` using `mul_nonneg (by linarith) (by linarith)`. Use `mul_nonneg hk0 (by linarith : 0 ≤ (k : ℚ) + (2 * (j : ℚ) - 1) * ((t : ℚ) + 1))` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hCSizesA : HCSizesA := by
  intro k t m j u e b S η hj hjm ht hkS hkη he hb
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have ht1 : (1 : ℚ) ≤ t := by exact_mod_cast ht
  have hj1 : (1 : ℚ) ≤ j := by exact_mod_cast hj
  have hjm' : (j : ℚ) ≤ m := by exact_mod_cast hjm
  have hη : 0 ≤ η := le_trans hk0 hkη
  obtain ⟨hB0, hB1⟩ := hc_blockSum_bounds t j e η hj he (fun i h1 h2 => by
    have := hb i h1 h2; linarith)
  have hB2 : ((t : ℚ) + 1) * ((j : ℚ) - 1) * η ≤ 2 * m * t * η := by
    apply mul_le_mul_of_nonneg_right _ hη
    nlinarith
  have hA1 : (k : ℚ) * ((k : ℚ) + (2 * (j : ℚ) - 1) * ((t : ℚ) + 1)) / 2
      ≤ (k : ℚ) ^ 2 + k * m * ((t : ℚ) + 1) := by
    have h1 : 0 ≤ (k : ℚ) * ((t : ℚ) + 1) * ((m : ℚ) - j) :=
      mul_nonneg (mul_nonneg hk0 (by linarith)) (by linarith)
    have h2 : 0 ≤ (k : ℚ) * ((t : ℚ) + 1) := mul_nonneg hk0 (by linarith)
    nlinarith [sq_nonneg (k : ℚ)]
  have hA2 : (k : ℚ) ^ 2 + k * m * ((t : ℚ) + 1) ≤ k * S + 2 * m * t * η := by
    have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
    have h1 : 0 ≤ (k : ℚ) * (S - k) := mul_nonneg hk0 (by linarith)
    have h2 : 0 ≤ (m : ℚ) * t * (η - k) := mul_nonneg (mul_nonneg hm0 (by linarith)) (by linarith)
    have h3 : 0 ≤ (k : ℚ) * m * ((t : ℚ) - 1) := mul_nonneg (mul_nonneg hk0 hm0) (by linarith)
    nlinarith
  have hd := (hCDegree k t u e j hj).1
  refine ⟨hB0, hB1, hB2, hA1, hA2, ?_, ?_⟩
  · rw [hd]; linarith
  · rw [hd]
    have hA0 : 0 ≤ (k : ℚ) * ((k : ℚ) + (2 * (j : ℚ) - 1) * ((t : ℚ) + 1)) / 2 := by
      have : 0 ≤ (2 * (j : ℚ) - 1) * ((t : ℚ) + 1) := mul_nonneg (by linarith) (by linarith)
      have := mul_nonneg hk0 (by linarith : 0 ≤ (k : ℚ) + (2 * (j : ℚ) - 1) * ((t : ℚ) + 1))
      linarith
    linarith

/- English proof (translation)
Introduce `k t m j u e b1 S η hj hjm hkt hkS he hb`. Establish `hk0 : (0 : ℚ) ≤ k` using `Nat.cast_nonneg k`. Establish `hm0 : (0 : ℚ) ≤ m` using `Nat.cast_nonneg m`. Establish `ht0 : (0 : ℚ) ≤ t` using `Nat.cast_nonneg t`. Establish `hkt' : (k : ℚ) ≤ t` using `by exact_mod_cast hkt.le`.

Establish `hj1 : (1 : ℚ) ≤ j` using `by exact_mod_cast hj`. Establish `hjm' : (j : ℚ) ≤ m` using `by exact_mod_cast hjm`. Establish `hη : 0 ≤ η` using `le_trans (abs_nonneg _) (hb j hj le_rfl)`. Establish `hM : ∀ i, 1 ≤ i → i < j → e j - e i ≤ 2 * η`. Introduce `i h1 h2`.

Establish `a1` using `abs_le.mp (hb i h1 h2.le)`. Establish `a2` using `abs_le.mp (hb j hj le_rfl)`. Combine the linear relations using `[a1.1, a2.2]`. Take `⟨hB0, hB1⟩` from `hc_blockSum_bounds t j e (2 * η) hj he hM`. Establish `c1 : (k : ℚ) * HCwG k t e j = k * e j - (k : ℚ) ^ 2 / 2 - k * (2 * (j : ℚ) - 1) * ((t : ℚ) + 1) / 2`.

Unfold `HCwG`. Expand and normalize the polynomial expressions, which then agree. Establish `c2 : (k : ℚ) ^ 2 / 2 ≤ k * S`. Establish `h1 : 0 ≤ (k : ℚ) * (S - k)` using `mul_nonneg hk0 (by linarith)`. Use polynomial arithmetic with `[sq_nonneg (k : ℚ)]`.

Establish `c3 : (k : ℚ) * (2 * (j : ℚ) - 1) * ((t : ℚ) + 1) / 2 ≤ k * m * ((t : ℚ) + 1)`. Establish `h1 : 0 ≤ (k : ℚ) * ((t : ℚ) + 1) * ((m : ℚ) - j)` using `mul_nonneg (mul_nonneg hk0 (by linarith)) (by linarith)`. Establish `h2 : 0 ≤ (k : ℚ) * ((t : ℚ) + 1)` using `mul_nonneg hk0 (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Establish `c4 : (k : ℚ) * m * ((t : ℚ) + 1) ≤ m * t * ((t : ℚ) + 1)`.

Establish `h1 : 0 ≤ (m : ℚ) * ((t : ℚ) + 1) * ((t : ℚ) - k)` using `mul_nonneg (mul_nonneg hm0 (by linarith)) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hd` using `(hCDegree k t u e j hj).2`. Use `⟨c1, c2, c3, c4, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `l hkl hl`.

Take `⟨j', rfl⟩ : ∃ j', j = j' + 1` from `⟨j - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel] at hl`. Take `⟨i, s, hs, rfl⟩` from `hc_decomp k t l hkl`. Establish `hij` using `hc_decomp_lt _ _ _ _ _ hl`. Rewrite using `[hc_nu_block _ _ _ _ _ _ _ hs]`.

Establish `l1` using `hc_row_lower t (j' + 1) e he (i + 1) (by omega) (by omega)`. Establish `l2` using `hM (i + 1) (by omega) (by omega)`. Establish `l3 : (0 : ℚ) ≤ ((j' : ℚ) - i) * ((t : ℚ) + 1)`. Establish `: (i : ℚ) ≤ j'` using `by exact_mod_cast hij.le`. Conclude with `mul_nonneg (by linarith) (by linarith)`.

Move the coercions through the operations in `at l1`. Prove the components needed by the constructor for the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hd, c1]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hd, c1]`. Establish `h1 : ((t : ℚ) + 1) * ((j : ℚ) - 1) * (2 * η) ≤ 2 * m * ((t : ℚ) + 1) * η`. Establish `: 0 ≤ ((t : ℚ) + 1) * η * ((m : ℚ) - j + 1)` using `mul_nonneg (mul_nonneg (by linarith) hη) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h2 : 0 ≤ (k : ℚ) * (2 * (j : ℚ) - 1) * ((t : ℚ) + 1) / 2`. Use `mul_nonneg (mul_nonneg hk0 (by linarith : 0 ≤ 2 * (j : ℚ) - 1)) (by linarith : 0 ≤ (t : ℚ) + 1)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use polynomial arithmetic with `[sq_nonneg (k : ℚ)]`.
-/
theorem hCSizesB : HCSizesB := by
  intro k t m j u e b1 S η hj hjm hkt hkS he hb
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg t
  have hkt' : (k : ℚ) ≤ t := by exact_mod_cast hkt.le
  have hj1 : (1 : ℚ) ≤ j := by exact_mod_cast hj
  have hjm' : (j : ℚ) ≤ m := by exact_mod_cast hjm
  have hη : 0 ≤ η := le_trans (abs_nonneg _) (hb j hj le_rfl)
  have hM : ∀ i, 1 ≤ i → i < j → e j - e i ≤ 2 * η := by
    intro i h1 h2
    have a1 := abs_le.mp (hb i h1 h2.le)
    have a2 := abs_le.mp (hb j hj le_rfl)
    linarith [a1.1, a2.2]
  obtain ⟨hB0, hB1⟩ := hc_blockSum_bounds t j e (2 * η) hj he hM
  have c1 : (k : ℚ) * HCwG k t e j
      = k * e j - (k : ℚ) ^ 2 / 2 - k * (2 * (j : ℚ) - 1) * ((t : ℚ) + 1) / 2 := by
    unfold HCwG; ring
  have c2 : (k : ℚ) ^ 2 / 2 ≤ k * S := by
    have h1 : 0 ≤ (k : ℚ) * (S - k) := mul_nonneg hk0 (by linarith)
    nlinarith [sq_nonneg (k : ℚ)]
  have c3 : (k : ℚ) * (2 * (j : ℚ) - 1) * ((t : ℚ) + 1) / 2 ≤ k * m * ((t : ℚ) + 1) := by
    have h1 : 0 ≤ (k : ℚ) * ((t : ℚ) + 1) * ((m : ℚ) - j) :=
      mul_nonneg (mul_nonneg hk0 (by linarith)) (by linarith)
    have h2 : 0 ≤ (k : ℚ) * ((t : ℚ) + 1) := mul_nonneg hk0 (by linarith)
    nlinarith
  have c4 : (k : ℚ) * m * ((t : ℚ) + 1) ≤ m * t * ((t : ℚ) + 1) := by
    have h1 : 0 ≤ (m : ℚ) * ((t : ℚ) + 1) * ((t : ℚ) - k) :=
      mul_nonneg (mul_nonneg hm0 (by linarith)) (by linarith)
    nlinarith
  have hd := (hCDegree k t u e j hj).2
  refine ⟨c1, c2, c3, c4, ?_, ?_, ?_⟩
  · intro l hkl hl
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hl
    obtain ⟨i, s, hs, rfl⟩ := hc_decomp k t l hkl
    have hij := hc_decomp_lt _ _ _ _ _ hl
    rw [hc_nu_block _ _ _ _ _ _ _ hs]
    have l1 := hc_row_lower t (j' + 1) e he (i + 1) (by omega) (by omega)
    have l2 := hM (i + 1) (by omega) (by omega)
    have l3 : (0 : ℚ) ≤ ((j' : ℚ) - i) * ((t : ℚ) + 1) := by
      have : (i : ℚ) ≤ j' := by exact_mod_cast hij.le
      exact mul_nonneg (by linarith) (by linarith)
    push_cast at l1
    constructor
    · linarith
    · linarith
  · rw [hd, c1]; linarith
  · rw [hd, c1]
    have h1 : ((t : ℚ) + 1) * ((j : ℚ) - 1) * (2 * η) ≤ 2 * m * ((t : ℚ) + 1) * η := by
      have : 0 ≤ ((t : ℚ) + 1) * η * ((m : ℚ) - j + 1) :=
        mul_nonneg (mul_nonneg (by linarith) hη) (by linarith)
      nlinarith
    have h2 : 0 ≤ (k : ℚ) * (2 * (j : ℚ) - 1) * ((t : ℚ) + 1) / 2 := by
      have := mul_nonneg (mul_nonneg hk0 (by linarith : 0 ≤ 2 * (j : ℚ) - 1))
        (by linarith : 0 ≤ (t : ℚ) + 1)
      linarith
    nlinarith [sq_nonneg (k : ℚ)]

/- English proof (translation)
Take `⟨-, -, -, -, -, h6, h7⟩` from `hCSizesA k t m j u e b S η hj hjm ht hkS hkη he hb`. Rewrite `h6`, `h7` using `[(hCLamSum k u).1]`. Establish `up` using `Finset.sum_le_card_nsmul (Icc 1 k) u ((C + 1) * S) (fun i hi => by`. Use `Finset.mem_Icc.mp hi` as an intermediate fact. Conclude with `(hu i this.1 this.2).2)`.

Establish `lo` using `Finset.card_nsmul_le_sum (Icc 1 k) u (-1) (fun i hi => by`. Use `Finset.mem_Icc.mp hi` as an intermediate fact. Conclude with `(hu i this.1 this.2).1)`. Rewrite `up`, `lo` using `[Nat.card_Icc, nsmul_eq_mul]`. Simplify using `only [Nat.add_sub_cancel] at up lo`.

Apply the tactic sequence `constructor <;> linarith`.
-/
private lemma hc_place_off (k t m j : ℕ) (u e b : ℕ → ℚ) (S η C : ℚ)
    (ht : 1 ≤ t) (hj : 1 ≤ j) (hjm : j ≤ m) (hkS : (k : ℚ) ≤ S) (hkη : (k : ℚ) ≤ η)
    (he : ∀ i, 1 ≤ i → i < j → e i + ((t : ℚ) + 3) ≤ e (i + 1))
    (hb : ∀ i, 1 ≤ i → i < j → b i ≤ e i ∧ e j - b i ≤ η)
    (hu : ∀ i, 1 ≤ i → i ≤ k → -1 ≤ u i ∧ u i ≤ (C + 1) * S) :
    HCdeg k t u e j ≤ k * e j + ((C + 1) * k * S + 2 * m * t * η) ∧
    k * e j - (k + k * S + 2 * m * t * η) ≤ HCdeg k t u e j := by
  obtain ⟨-, -, -, -, -, h6, h7⟩ := hCSizesA k t m j u e b S η hj hjm ht hkS hkη he hb
  rw [(hCLamSum k u).1] at h6 h7
  have up := Finset.sum_le_card_nsmul (Icc 1 k) u ((C + 1) * S) (fun i hi => by
    have := Finset.mem_Icc.mp hi; exact (hu i this.1 this.2).2)
  have lo := Finset.card_nsmul_le_sum (Icc 1 k) u (-1) (fun i hi => by
    have := Finset.mem_Icc.mp hi; exact (hu i this.1 this.2).1)
  rw [Nat.card_Icc, nsmul_eq_mul] at up lo
  simp only [Nat.add_sub_cancel] at up lo
  constructor <;> linarith

/- English proof (translation)
Take `⟨-, -, -, -, -, h6, h7⟩` from `hCSizesA k t m j u e b S η hj hjm ht hkS hkη he hb`. Rewrite `h6`, `h7` using `[((hCLamSum k u).2 a b' hk hu1 huk).2.2]`. Establish `hS : 0 ≤ S` using `le_trans (Nat.cast_nonneg k) hkS`. Establish `up` using `Finset.sum_le_card_nsmul (Ioo 1 k) u S (fun i hi => by`. Use `Finset.mem_Ioo.mp hi` as an intermediate fact.

Conclude with `(hu i this.1 this.2).2)`. Establish `lo : 0 ≤ ∑ i ∈ Ioo 1 k, u i` using `Finset.sum_nonneg (fun i hi => by`. Use `Finset.mem_Ioo.mp hi` as an intermediate fact. Conclude with `(hu i this.1 this.2).1)`. Rewrite `up` using `[Nat.card_Ioo, nsmul_eq_mul]`.

Establish `hc : ((k - 1 - 1 : ℕ) : ℚ) ≤ k` using `by exact_mod_cast (by omega : k - 1 - 1 ≤ k)`. Use `mul_le_mul_of_nonneg_right hc hS` as an intermediate fact. Apply the tactic sequence `constructor <;> linarith`.
-/
private lemma hc_place_top (k t m j : ℕ) (u e b : ℕ → ℚ) (a b' S η : ℚ)
    (hk : 2 ≤ k) (ht : 1 ≤ t) (hj : 1 ≤ j) (hjm : j ≤ m) (hkS : (k : ℚ) ≤ S) (hkη : (k : ℚ) ≤ η)
    (he : ∀ i, 1 ≤ i → i < j → e i + ((t : ℚ) + 3) ≤ e (i + 1))
    (hb : ∀ i, 1 ≤ i → i < j → b i ≤ e i ∧ e j - b i ≤ η)
    (hu1 : u 1 = a + ((k : ℚ) - 1) / 2) (huk : u k = -b' - ((k : ℚ) - 1) / 2)
    (hu : ∀ i, 1 < i → i < k → 0 ≤ u i ∧ u i ≤ S) :
    HCdeg k t u e j ≤ a - b' + k * e j + (k * S + 2 * m * t * η) ∧
    a - b' + k * e j - (k * S + 2 * m * t * η) ≤ HCdeg k t u e j := by
  obtain ⟨-, -, -, -, -, h6, h7⟩ := hCSizesA k t m j u e b S η hj hjm ht hkS hkη he hb
  rw [((hCLamSum k u).2 a b' hk hu1 huk).2.2] at h6 h7
  have hS : 0 ≤ S := le_trans (Nat.cast_nonneg k) hkS
  have up := Finset.sum_le_card_nsmul (Ioo 1 k) u S (fun i hi => by
    have := Finset.mem_Ioo.mp hi; exact (hu i this.1 this.2).2)
  have lo : 0 ≤ ∑ i ∈ Ioo 1 k, u i := Finset.sum_nonneg (fun i hi => by
    have := Finset.mem_Ioo.mp hi; exact (hu i this.1 this.2).1)
  rw [Nat.card_Ioo, nsmul_eq_mul] at up
  have hc : ((k - 1 - 1 : ℕ) : ℚ) ≤ k := by exact_mod_cast (by omega : k - 1 - 1 ≤ k)
  have := mul_le_mul_of_nonneg_right hc hS
  constructor <;> linarith

/- English proof (translation)
Introduce `k t m j P T u e b a b' S η C hk ht hj hjm hTP hkS hkη hC he hb hoff htop`. Establish `hS : 0 ≤ S` using `le_trans (Nat.cast_nonneg k) hkS`. Establish `hkS0 : 0 ≤ (k : ℚ) * S` using `mul_nonneg (Nat.cast_nonneg k) hS`. Establish `hite : ∀ f : ℕ → ℚ, ∑ τ ∈ P, (if τ ∈ T then f τ else 0) = ∑ τ ∈ T, f τ`. Introduce `f`.

Rewrite using `[Finset.sum_ite_mem, Finset.inter_eq_right.mpr hTP]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← hite a, ← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum (fun τ hτ => ?_)` and prove the remaining obligations. Distinguish the cases in `hT : τ ∈ T`.

Rewrite using `[if_pos hT]`. Take `⟨h1, h2, h3, h4⟩` from `htop τ hT`. Use `(hc_place_top k t m j (u τ) (e τ) (b τ) (a τ) (b' τ) S η hk ht hj hjm hkS hkη (he τ hτ) (hb τ hτ) h1 h2 h4).1` as an intermediate fact. Establish `hC' : 0 ≤ C * ((k : ℚ) * S)` using `mul_nonneg hC hkS0`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[if_neg hT]`. Use `(hc_place_off k t m j (u τ) (e τ) (b τ) S η C ht hj hjm hkS hkη (he τ hτ) (hb τ hτ) (hoff τ (Finset.mem_sdiff.mpr ⟨hτ, hT⟩))).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← hite (fun τ => a τ - b' τ), ← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum (fun τ hτ => ?_)` and prove the remaining obligations.

Establish `hk0 : (0 : ℚ) ≤ k` using `Nat.cast_nonneg k`. Distinguish the cases in `hT : τ ∈ T`. Rewrite using `[if_pos hT]`. Take `⟨h1, h2, h3, h4⟩` from `htop τ hT`. Use `(hc_place_top k t m j (u τ) (e τ) (b τ) (a τ) (b' τ) S η hk ht hj hjm hkS hkη (he τ hτ) (hb τ hτ) h1 h2 h4).2` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg hT]`. Use `(hc_place_off k t m j (u τ) (e τ) (b τ) S η C ht hj hjm hkS hkη (he τ hτ) (hb τ hτ) (hoff τ (Finset.mem_sdiff.mpr ⟨hτ, hT⟩))).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hCDpi : HCDpi := by
  intro k t m j P T u e b a b' S η C hk ht hj hjm hTP hkS hkη hC he hb hoff htop
  have hS : 0 ≤ S := le_trans (Nat.cast_nonneg k) hkS
  have hkS0 : 0 ≤ (k : ℚ) * S := mul_nonneg (Nat.cast_nonneg k) hS
  have hite : ∀ f : ℕ → ℚ, ∑ τ ∈ P, (if τ ∈ T then f τ else 0) = ∑ τ ∈ T, f τ := by
    intro f
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hTP]
  constructor
  · rw [← hite a, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun τ hτ => ?_)
    by_cases hT : τ ∈ T
    · rw [if_pos hT]
      obtain ⟨h1, h2, h3, h4⟩ := htop τ hT
      have := (hc_place_top k t m j (u τ) (e τ) (b τ) (a τ) (b' τ) S η hk ht hj hjm hkS hkη
        (he τ hτ) (hb τ hτ) h1 h2 h4).1
      have hC' : 0 ≤ C * ((k : ℚ) * S) := mul_nonneg hC hkS0
      nlinarith
    · rw [if_neg hT]
      have := (hc_place_off k t m j (u τ) (e τ) (b τ) S η C ht hj hjm hkS hkη
        (he τ hτ) (hb τ hτ) (hoff τ (Finset.mem_sdiff.mpr ⟨hτ, hT⟩))).1
      linarith
  · rw [← hite (fun τ => a τ - b' τ), ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun τ hτ => ?_)
    have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    by_cases hT : τ ∈ T
    · rw [if_pos hT]
      obtain ⟨h1, h2, h3, h4⟩ := htop τ hT
      have := (hc_place_top k t m j (u τ) (e τ) (b τ) (a τ) (b' τ) S η hk ht hj hjm hkS hkη
        (he τ hτ) (hb τ hτ) h1 h2 h4).2
      linarith
    · rw [if_neg hT]
      have := (hc_place_off k t m j (u τ) (e τ) (b τ) S η C ht hj hjm hkS hkη
        (he τ hτ) (hb τ hτ) (hoff τ (Finset.mem_sdiff.mpr ⟨hτ, hT⟩))).2
      linarith

/- English proof (translation)
Unfold `HCkap HCsparam`. Rewrite using `[if_pos (by omega), show 1 + i + 1 = 1 + 1 + i by ring]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hc_kapA (k t m j : ℕ) (v b e : ℕ → ℚ) (i : ℕ) (hi : i < k) :
    HCkap (k + 1) t m j v b e (1 + i)
      = e j + (v (1 + 1 + i) - ((t : ℚ) + 1) / 2 - (((k + 1 : ℕ) : ℚ) - ((1 + 1 + i : ℕ) : ℚ)) - j) := by
  unfold HCkap HCsparam
  rw [if_pos (by omega), show 1 + i + 1 = 1 + 1 + i by ring]
  push_cast; ring

/- English proof (translation)
Unfold `HCkap HCsparam`. Rewrite using `[if_neg (by omega), if_pos (by omega), show 1 + (k + i) + 1 - (k + 1) = 0 + 1 + i by omega]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hc_kapB (k t m j : ℕ) (v b e : ℕ → ℚ) (i : ℕ) (hi : i < j) :
    HCkap (k + 1) t m j v b e (1 + (k + i))
      = e j - b (0 + 1 + i) - ((t : ℚ) + 1) / 2 - ((j : ℚ) - ((0 + 1 + i : ℕ) : ℚ)) := by
  unfold HCkap HCsparam
  rw [if_neg (by omega), if_pos (by omega), show 1 + (k + i) + 1 - (k + 1) = 0 + 1 + i by omega]
  push_cast; ring

/- English proof (translation)
Unfold `HCkap HCsparam`. Rewrite using `[if_neg (by omega), if_neg (by omega), if_pos (by omega), show k + j + (s + 1) + 1 - (k + 1 + j) = s + 1 by omega]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hc_kapC (k t m j : ℕ) (v b e : ℕ → ℚ) (s : ℕ) (hs : s < t) :
    HCkap (k + 1) t m j v b e (k + j + (s + 1)) = 0 := by
  unfold HCkap HCsparam
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show k + j + (s + 1) + 1 - (k + 1 + j) = s + 1 by omega]
  push_cast; ring

/- English proof (translation)
Unfold `HCkap HCsparam`. Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg (by omega), show k + 1 + j + t + i + 1 - (k + 1) - t = j + 1 + i by omega]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hc_kapD (k t m j : ℕ) (v b e : ℕ → ℚ) (i : ℕ) :
    -HCkap (k + 1) t m j v b e (k + 1 + j + t + i)
      = b (j + 1 + i) - e j - ((t : ℚ) - 1) / 2 - (((j + 1 + i : ℕ) : ℚ) - j) := by
  unfold HCkap HCsparam
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show k + 1 + j + t + i + 1 - (k + 1) - t = j + 1 + i by omega]
  push_cast; ring

/- English proof (translation)
Introduce `k t m j v b e hk hj hjm`. Take `⟨k, rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i h2 hik`.

Take `⟨i, rfl⟩ : ∃ i', i = 1 + 1 + i'` from `⟨i - 2, by omega⟩`. Rewrite using `[show 1 + 1 + i - 1 = 1 + i by omega]`. Conclude with `hc_kapA k t m j v b e i (by omega)`. Introduce `i h1 hij`. Take `⟨i, rfl⟩ : ∃ i', i = 0 + 1 + i'` from `⟨i - 1, by omega⟩`.

Rewrite using `[show k + (0 + 1 + i) = 1 + (k + i) by ring]`. Conclude with `hc_kapB k t m j v b e i (by omega)`. Introduce `s h1 hs`. Take `⟨s, rfl⟩ : ∃ s', s = s' + 1` from `⟨s - 1, by omega⟩`. Conclude with `hc_kapC k t m j v b e s (by omega)`.

Introduce `i hji _`. Take `⟨i, rfl⟩ : ∃ i', i = j + 1 + i'` from `⟨i - j - 1, by omega⟩`. Rewrite using `[show k + t + (j + 1 + i) = k + 1 + j + t + i by ring]`. Conclude with `hc_kapD k t m j v b e i`.
-/
theorem hCSigmaRows : HCSigmaRows := by
  intro k t m j v b e hk hj hjm
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i h2 hik
    obtain ⟨i, rfl⟩ : ∃ i', i = 1 + 1 + i' := ⟨i - 2, by omega⟩
    rw [show 1 + 1 + i - 1 = 1 + i by omega]
    exact hc_kapA k t m j v b e i (by omega)
  · intro i h1 hij
    obtain ⟨i, rfl⟩ : ∃ i', i = 0 + 1 + i' := ⟨i - 1, by omega⟩
    rw [show k + (0 + 1 + i) = 1 + (k + i) by ring]
    exact hc_kapB k t m j v b e i (by omega)
  · intro s h1 hs
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    exact hc_kapC k t m j v b e s (by omega)
  · intro i hji _
    obtain ⟨i, rfl⟩ : ∃ i', i = j + 1 + i' := ⟨i - j - 1, by omega⟩
    rw [show k + t + (j + 1 + i) = k + 1 + j + t + i by ring]
    exact hc_kapD k t m j v b e i

/- English proof (translation)
Unfold `HCsparam`. Rewrite using `[if_pos h]`.
-/
private lemma hc_spA (k t j : ℕ) (v b e : ℕ → ℚ) (l : ℕ) (h : l + 1 ≤ k) :
    HCsparam k t j v b e l = v (l + 1) := by
  unfold HCsparam; rw [if_pos h]

/- English proof (translation)
Unfold `HCsparam; rw [if_neg (by omega), if_pos h2]`.
-/
private lemma hc_spB (k t j : ℕ) (v b e : ℕ → ℚ) (l : ℕ) (h1 : k < l + 1) (h2 : l + 1 ≤ k + j) :
    HCsparam k t j v b e l = -b (l + 1 - k) := by
  unfold HCsparam; rw [if_neg (by omega), if_pos h2]

/- English proof (translation)
Unfold `HCsparam; rw [if_neg (by omega), if_neg (by omega), if_pos h2]`.
-/
private lemma hc_spC (k t j : ℕ) (v b e : ℕ → ℚ) (l : ℕ) (h1 : k + j < l + 1)
    (h2 : l + 1 ≤ k + j + t) :
    HCsparam k t j v b e l = -e j + ((t : ℚ) - 1) / 2 - (((l + 1 - (k + j) : ℕ) : ℚ) - 1) := by
  unfold HCsparam; rw [if_neg (by omega), if_neg (by omega), if_pos h2]

/- English proof (translation)
Unfold `HCsparam; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]`.
-/
private lemma hc_spD (k t j : ℕ) (v b e : ℕ → ℚ) (l : ℕ) (h1 : k + j + t < l + 1) :
    HCsparam k t j v b e l = -b (l + 1 - k - t) := by
  unfold HCsparam; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/- English proof (translation)
Introduce `k t m j v b e hk ht hj hjm hv hvk hbe heb`. Establish `ht1 : (1 : ℚ) ≤ t` using `by exact_mod_cast ht`. Establish `hbb : ∀ i, 1 ≤ i → i < m → b i + 1 ≤ b (i + 1)`. Introduce `i h1 h2`. Use `hbe i h1 h2.le` as an intermediate fact.

Use `heb i h1 h2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hstep : ∀ l, 1 ≤ l → l + 1 < k + m + t → HCsparam k t j v b e (l + 1) + 1 ≤ HCsparam k t j v b e l`. Introduce `l hl1 hl`. Distinguish the cases in `c1 : l + 1 ≤ k`.

Rewrite using `[hc_spA _ _ _ _ _ _ _ c1]`. Distinguish the cases in `c1' : l + 1 + 1 ≤ k`. Rewrite using `[hc_spA _ _ _ _ _ _ _ c1']`. Conclude with `hv (l + 1) (by omega) (by omega)`. Rewrite using `[hc_spB _ _ _ _ _ _ _ (by omega) (by omega), show l + 1 + 1 - k = 1 by omega, show l + 1 = k by omega]`.

Conclude with `hvk (by omega)`. Distinguish the cases in `c2 : l + 1 ≤ k + j`. Rewrite using `[hc_spB _ _ _ _ _ _ _ (by omega) c2]`. Distinguish the cases in `c2' : l + 1 + 1 ≤ k + j`. Rewrite using `[hc_spB _ _ _ _ _ _ _ (by omega) c2', show l + 1 + 1 - k = (l + 1 - k) + 1 by omega]`.

Use `hbb (l + 1 - k) (by omega) (by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hc_spC _ _ _ _ _ _ _ (by omega) (by omega), show l + 1 + 1 - (k + j) = 1 by omega, show l + 1 - k = j by omega]`. Use `hbe j hj hjm` as an intermediate fact. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `c3 : l + 1 ≤ k + j + t`. Rewrite using `[hc_spC _ _ _ _ _ _ _ (by omega) c3]`. Distinguish the cases in `c3' : l + 1 + 1 ≤ k + j + t`. Rewrite using `[hc_spC _ _ _ _ _ _ _ (by omega) c3', show l + 1 + 1 - (k + j) = (l + 1 - (k + j)) + 1 by omega] push_cast; linarith`.

Rewrite using `[hc_spD _ _ _ _ _ _ _ (by omega), show l + 1 + 1 - k - t = j + 1 by omega, show l + 1 - (k + j) = t by omega]`. Use `heb j hj (by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hc_spD _ _ _ _ _ _ _ (by omega), hc_spD _ _ _ _ _ _ _ (by omega), show l + 1 + 1 - k - t = (l + 1 - k - t) + 1 by omega]`. Use `hbb (l + 1 - k - t) (by omega) (by omega)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hanti : ∀ l, 1 ≤ l → l + 1 < k + m + t → HCkap k t m j v b e (l + 1) ≤ HCkap k t m j v b e l`. Introduce `l hl1 hl`. Use `hstep l hl1 hl` as an intermediate fact. Unfold `HCkap`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨-, rB, -, rD⟩` from `hCSigmaRows k t m j v b e hk hj hjm`. Use `⟨hstep, hanti, ?_, ?_⟩` and prove the remaining obligations. Introduce `l hl1 hl`.

Establish `c` using `hc_chain (fun l => -HCkap k t m j v b e l) 0 (k - 1 + j) (fun i h1 h2 => by`. Use `hanti i h1 (by omega)` as an intermediate fact. Use `show -HCkap k t m j v b e i + 0 ≤ -HCkap k t m j v b e (i + 1)`. Use the proof step `linarith) (k - 1 + j - l) l hl1 (by omega)`. Establish `r` using `rB j hj le_rfl`.

Use `hbe j hj hjm` as an intermediate fact. Simplify using `only [mul_zero, add_zero] at c`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `l hl1 hl`. Establish `c` using `hc_chain (fun l => -HCkap k t m j v b e l) 0 l (fun i h1 h2 => by`.

Use `hanti i h1 (by omega)` as an intermediate fact. Use `show -HCkap k t m j v b e i + 0 ≤ -HCkap k t m j v b e (i + 1)`. Use the proof step `linarith) (l - (k + j + t)) (k + j + t) (by omega) (by omega)`. Establish `r` using `rD (j + 1) (by omega) (by omega)`. Rewrite `r` using `[show k - 1 + t + (j + 1) = k + j + t by omega]`.

Use `heb j hj (by omega)` as an intermediate fact. Simplify using `only [mul_zero, add_zero] at c`. Move the coercions through the operations in `at r`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hCSigmaPartition : HCSigmaPartition := by
  intro k t m j v b e hk ht hj hjm hv hvk hbe heb
  have ht1 : (1 : ℚ) ≤ t := by exact_mod_cast ht
  have hbb : ∀ i, 1 ≤ i → i < m → b i + 1 ≤ b (i + 1) := by
    intro i h1 h2
    have := hbe i h1 h2.le
    have := heb i h1 h2
    linarith
  have hstep : ∀ l, 1 ≤ l → l + 1 < k + m + t →
      HCsparam k t j v b e (l + 1) + 1 ≤ HCsparam k t j v b e l := by
    intro l hl1 hl
    by_cases c1 : l + 1 ≤ k
    · rw [hc_spA _ _ _ _ _ _ _ c1]
      by_cases c1' : l + 1 + 1 ≤ k
      · rw [hc_spA _ _ _ _ _ _ _ c1']
        exact hv (l + 1) (by omega) (by omega)
      · rw [hc_spB _ _ _ _ _ _ _ (by omega) (by omega), show l + 1 + 1 - k = 1 by omega,
          show l + 1 = k by omega]
        exact hvk (by omega)
    · by_cases c2 : l + 1 ≤ k + j
      · rw [hc_spB _ _ _ _ _ _ _ (by omega) c2]
        by_cases c2' : l + 1 + 1 ≤ k + j
        · rw [hc_spB _ _ _ _ _ _ _ (by omega) c2', show l + 1 + 1 - k = (l + 1 - k) + 1 by omega]
          have := hbb (l + 1 - k) (by omega) (by omega)
          linarith
        · rw [hc_spC _ _ _ _ _ _ _ (by omega) (by omega), show l + 1 + 1 - (k + j) = 1 by omega,
            show l + 1 - k = j by omega]
          have := hbe j hj hjm
          push_cast; linarith
      · by_cases c3 : l + 1 ≤ k + j + t
        · rw [hc_spC _ _ _ _ _ _ _ (by omega) c3]
          by_cases c3' : l + 1 + 1 ≤ k + j + t
          · rw [hc_spC _ _ _ _ _ _ _ (by omega) c3',
              show l + 1 + 1 - (k + j) = (l + 1 - (k + j)) + 1 by omega]
            push_cast; linarith
          · rw [hc_spD _ _ _ _ _ _ _ (by omega), show l + 1 + 1 - k - t = j + 1 by omega,
              show l + 1 - (k + j) = t by omega]
            have := heb j hj (by omega)
            linarith
        · rw [hc_spD _ _ _ _ _ _ _ (by omega), hc_spD _ _ _ _ _ _ _ (by omega),
            show l + 1 + 1 - k - t = (l + 1 - k - t) + 1 by omega]
          have := hbb (l + 1 - k - t) (by omega) (by omega)
          linarith
  have hanti : ∀ l, 1 ≤ l → l + 1 < k + m + t →
      HCkap k t m j v b e (l + 1) ≤ HCkap k t m j v b e l := by
    intro l hl1 hl
    have := hstep l hl1 hl
    unfold HCkap
    push_cast; linarith
  obtain ⟨-, rB, -, rD⟩ := hCSigmaRows k t m j v b e hk hj hjm
  refine ⟨hstep, hanti, ?_, ?_⟩
  · intro l hl1 hl
    have c := hc_chain (fun l => -HCkap k t m j v b e l) 0 (k - 1 + j) (fun i h1 h2 => by
      have := hanti i h1 (by omega)
      show -HCkap k t m j v b e i + 0 ≤ -HCkap k t m j v b e (i + 1)
      linarith) (k - 1 + j - l) l hl1 (by omega)
    have r := rB j hj le_rfl
    have := hbe j hj hjm
    simp only [mul_zero, add_zero] at c
    linarith
  · intro l hl1 hl
    have c := hc_chain (fun l => -HCkap k t m j v b e l) 0 l (fun i h1 h2 => by
      have := hanti i h1 (by omega)
      show -HCkap k t m j v b e i + 0 ≤ -HCkap k t m j v b e (i + 1)
      linarith) (l - (k + j + t)) (k + j + t) (by omega) (by omega)
    have r := rD (j + 1) (by omega) (by omega)
    rw [show k - 1 + t + (j + 1) = k + j + t by omega] at r
    have := heb j hj (by omega)
    simp only [mul_zero, add_zero] at c
    push_cast at r
    linarith

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`. Take `⟨n, rfl⟩ : ∃ n, m = j + n` from `⟨m - j, by omega⟩`. Unfold `HCDplus HCDminus`. Rewrite using `[Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range, show k + 1 + j - 1 = k + j by omega, show k + 1 + (j + n) + t - (k + 1 + j + t) = n by omega, Finset.sum_range_add, Finset.sum_congr rfl (fun i hi => hc_kapA k t (j + n) j v b e i (Finset.mem_range.mp hi)), Finset.sum_con …`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hc_sigma_sum (k t m j : ℕ) (v b e : ℕ → ℚ) (hk : 1 ≤ k) (hjm : j ≤ m) :
    HCDplus k t m j v b e + HCDminus k t m j v b e
      = ((k : ℚ) - 1) * e j + ∑ i ∈ Icc 2 k, (v i - ((t : ℚ) + 1) / 2 - ((k : ℚ) - i) - j)
        + ∑ i ∈ Icc 1 j, (e j - b i - ((t : ℚ) + 1) / 2 - ((j : ℚ) - i))
        + ∑ i ∈ Ioc j m, (b i - e j - ((t : ℚ) - 1) / 2 - ((i : ℚ) - j)) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = j + n := ⟨m - j, by omega⟩
  unfold HCDplus HCDminus
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
    show k + 1 + j - 1 = k + j by omega, show k + 1 + (j + n) + t - (k + 1 + j + t) = n by omega,
    Finset.sum_range_add,
    Finset.sum_congr rfl (fun i hi => hc_kapA k t (j + n) j v b e i (Finset.mem_range.mp hi)),
    Finset.sum_congr rfl (fun i hi => hc_kapB k t (j + n) j v b e i (Finset.mem_range.mp hi)),
    Finset.sum_congr rfl (fun i _ => hc_kapD k t (j + n) j v b e i),
    hc_sumIoc, show Icc 2 (k + 1) = Icc (1 + 1) (1 + k) by rw [Nat.add_comm k 1],
    hc_sumIcc, show Icc 1 j = Icc (0 + 1) (0 + j) by simp, hc_sumIcc,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; ring

/- English proof (translation)
Introduce `k t m j v b e S η hk ht hj hjm hv hbe heb hη`. Establish `hk1 : (1 : ℚ) ≤ k` using `by exact_mod_cast hk`. Establish `ht1 : (1 : ℚ) ≤ t` using `by exact_mod_cast ht`. Establish `hj1 : (1 : ℚ) ≤ j` using `by exact_mod_cast hj`. Establish `hjm' : (j : ℚ) ≤ m` using `by exact_mod_cast hjm`.

Establish `hm0 : (0 : ℚ) ≤ m` using `Nat.cast_nonneg m`. Establish `hη0 : 0 ≤ η` using `le_trans (abs_nonneg _) (hη j hj hjm)`. Establish `hgap : ∀ i, 1 ≤ i → i < m → e i + ((t : ℚ) + 3) ≤ e (i + 1)`. Introduce `i h1 h2`. Use `heb i h1 h2` as an intermediate fact.

Use `hbe (i + 1) (by omega) (by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum` using `hc_sigma_sum k t m j v b e hk hjm`. Establish `hup : ∀ i, 1 ≤ i → i ≤ j → 0 ≤ e j - b i - ((t : ℚ) + 1) / 2 - ((j : ℚ) - i) ∧ e j - b i - ((t : ℚ) + 1) / 2 - ((j : ℚ) - i) ≤ η`. Introduce `i h1 h2`.

Establish `c` using `hc_chain e ((t : ℚ) + 3) j (fun i a1 a2 => hgap i a1 (by omega)) (j - i) i h1 (by omega)`. Rewrite `c` using `[Nat.cast_sub h2]`. Establish `d : (0 : ℚ) ≤ (j : ℚ) - i`. Establish `: (i : ℚ) ≤ j` using `by exact_mod_cast h2`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `hbe i h1 (by omega)` as an intermediate fact. Establish `ab` using `abs_le.mp (hη i h1 (by omega))`. Establish `p` using `mul_nonneg d (by linarith : (0 : ℚ) ≤ (t : ℚ) + 2)`. Prove the components needed by the constructor for the conclusion. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear relations using `[ab.1]`. Establish `hdn : ∀ i, j < i → i ≤ m → 0 ≤ b i - e j - ((t : ℚ) - 1) / 2 - ((i : ℚ) - j) ∧ b i - e j - ((t : ℚ) - 1) / 2 - ((i : ℚ) - j) ≤ η`. Introduce `i h1 h2`. Take `⟨i, rfl⟩ : ∃ i', i = i' + 1` from `⟨i - 1, by omega⟩`. Establish `c` using `hc_chain e ((t : ℚ) + 3) i (fun i a1 a2 => hgap i a1 (by omega)) (i - j) j hj (by omega)`.

Rewrite `c` using `[Nat.cast_sub (by omega)]`. Establish `d : (0 : ℚ) ≤ (i : ℚ) - j`. Establish `: (j : ℚ) ≤ i` using `by exact_mod_cast (by omega : j ≤ i)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `heb i (by omega) (by omega)` as an intermediate fact.

Establish `ab` using `abs_le.mp (hη (i + 1) (by omega) h2)`. Establish `p` using `mul_nonneg d (by linarith : (0 : ℚ) ≤ (t : ℚ) + 2)`. Use `push_cast`. Prove the components needed by the constructor for the conclusion. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear relations using `[ab.2]`. Establish `s1lo` using `Finset.card_nsmul_le_sum (Icc 2 k) (fun i : ℕ => v i - ((t : ℚ) + 1) / 2 - ((k : ℚ) - i) - j) (-((k : ℚ) + m + t - 1)) (fun i hi => by`. Establish `hi'` using `Finset.mem_Icc.mp hi`. Establish `h2 : (2 : ℚ) ≤ i` using `by exact_mod_cast hi'.1`. Use `(hv i hi'.1 hi'.2).1` as an intermediate fact.

Use `show -((k : ℚ) + m + t - 1) ≤ v i - ((t : ℚ) + 1) / 2 - ((k : ℚ) - i) - j`. Use the proof step `linarith)`. Establish `s1up` using `Finset.sum_le_card_nsmul (Icc 2 k) (fun i : ℕ => v i - ((t : ℚ) + 1) / 2 - ((k : ℚ) - i) - j) S (fun i hi => by`. Establish `hi'` using `Finset.mem_Icc.mp hi`. Establish `h2 : (i : ℚ) ≤ k` using `by exact_mod_cast hi'.2`.

Use `(hv i hi'.1 hi'.2).2` as an intermediate fact. Use `show v i - ((t : ℚ) + 1) / 2 - ((k : ℚ) - i) - j ≤ S`. Use the proof step `linarith)`. Rewrite `s1lo`, `s1up` using `[Nat.card_Icc, nsmul_eq_mul, show k + 1 - 2 = k - 1 by omega, Nat.cast_sub hk, Nat.cast_one]`. Establish `s2lo : 0 ≤ ∑ i ∈ Icc 1 j, (e j - b i - ((t : ℚ) + 1) / 2 - ((j : ℚ) - i))` using `Finset.sum_nonneg (fun i hi => by`.

Establish `hi'` using `Finset.mem_Icc.mp hi`. Conclude with `(hup i hi'.1 hi'.2).1)`. Establish `s2up` using `Finset.sum_le_card_nsmul (Icc 1 j) (fun i : ℕ => e j - b i - ((t : ℚ) + 1) / 2 - ((j : ℚ) - i)) η (fun i hi => by`. Establish `hi'` using `Finset.mem_Icc.mp hi`. Conclude with `(hup i hi'.1 hi'.2).2)`.

Rewrite `s2up` using `[Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]`. Establish `s3lo : 0 ≤ ∑ i ∈ Ioc j m, (b i - e j - ((t : ℚ) - 1) / 2 - ((i : ℚ) - j))` using `Finset.sum_nonneg (fun i hi => by`. Establish `hi'` using `Finset.mem_Ioc.mp hi`. Conclude with `(hdn i hi'.1 hi'.2).1)`. Establish `s3up` using `Finset.sum_le_card_nsmul (Ioc j m) (fun i : ℕ => b i - e j - ((t : ℚ) - 1) / 2 - ((i : ℚ) - j)) η (fun i hi => by`.

Establish `hi'` using `Finset.mem_Ioc.mp hi`. Conclude with `(hdn i hi'.1 hi'.2).2)`. Rewrite `s3up` using `[Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub hjm]`. Use `⟨hsum, hup, hdn, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hsum]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hsum]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `hkS hmk`. Establish `hk0 : (0 : ℚ) ≤ k` using `by linarith`.

Establish `h1 : 0 ≤ (k : ℚ) * (S - k)` using `mul_nonneg hk0 (by linarith)`. Establish `hm1 : (1 : ℚ) ≤ m` using `by linarith`. Establish `h2 : 0 ≤ (m : ℚ) * (η - k * t)` using `mul_nonneg hm0 (by linarith)`. Establish `h3 : 0 ≤ (k : ℚ) * (((m : ℚ) - 1) * ((t : ℚ) - 1))` using `mul_nonneg hk0 (mul_nonneg (by linarith) (by linarith))`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem hCSigmaDegree : HCSigmaDegree := by
  intro k t m j v b e S η hk ht hj hjm hv hbe heb hη
  have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have ht1 : (1 : ℚ) ≤ t := by exact_mod_cast ht
  have hj1 : (1 : ℚ) ≤ j := by exact_mod_cast hj
  have hjm' : (j : ℚ) ≤ m := by exact_mod_cast hjm
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hη0 : 0 ≤ η := le_trans (abs_nonneg _) (hη j hj hjm)
  have hgap : ∀ i, 1 ≤ i → i < m → e i + ((t : ℚ) + 3) ≤ e (i + 1) := by
    intro i h1 h2
    have := heb i h1 h2
    have := hbe (i + 1) (by omega) (by omega)
    linarith
  have hsum := hc_sigma_sum k t m j v b e hk hjm
  have hup : ∀ i, 1 ≤ i → i ≤ j → 0 ≤ e j - b i - ((t : ℚ) + 1) / 2 - ((j : ℚ) - i) ∧
      e j - b i - ((t : ℚ) + 1) / 2 - ((j : ℚ) - i) ≤ η := by
    intro i h1 h2
    have c := hc_chain e ((t : ℚ) + 3) j (fun i a1 a2 => hgap i a1 (by omega)) (j - i) i h1 (by omega)
    rw [Nat.cast_sub h2] at c
    have d : (0 : ℚ) ≤ (j : ℚ) - i := by
      have : (i : ℚ) ≤ j := by exact_mod_cast h2
      linarith
    have := hbe i h1 (by omega)
    have ab := abs_le.mp (hη i h1 (by omega))
    have p := mul_nonneg d (by linarith : (0 : ℚ) ≤ (t : ℚ) + 2)
    constructor
    · nlinarith
    · linarith [ab.1]
  have hdn : ∀ i, j < i → i ≤ m → 0 ≤ b i - e j - ((t : ℚ) - 1) / 2 - ((i : ℚ) - j) ∧
      b i - e j - ((t : ℚ) - 1) / 2 - ((i : ℚ) - j) ≤ η := by
    intro i h1 h2
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have c := hc_chain e ((t : ℚ) + 3) i (fun i a1 a2 => hgap i a1 (by omega)) (i - j) j hj (by omega)
    rw [Nat.cast_sub (by omega)] at c
    have d : (0 : ℚ) ≤ (i : ℚ) - j := by
      have : (j : ℚ) ≤ i := by exact_mod_cast (by omega : j ≤ i)
      linarith
    have := heb i (by omega) (by omega)
    have ab := abs_le.mp (hη (i + 1) (by omega) h2)
    have p := mul_nonneg d (by linarith : (0 : ℚ) ≤ (t : ℚ) + 2)
    push_cast
    constructor
    · nlinarith
    · linarith [ab.2]

  have s1lo := Finset.card_nsmul_le_sum (Icc 2 k)
    (fun i : ℕ => v i - ((t : ℚ) + 1) / 2 - ((k : ℚ) - i) - j) (-((k : ℚ) + m + t - 1))
    (fun i hi => by
      have hi' := Finset.mem_Icc.mp hi
      have h2 : (2 : ℚ) ≤ i := by exact_mod_cast hi'.1
      have := (hv i hi'.1 hi'.2).1
      show -((k : ℚ) + m + t - 1) ≤ v i - ((t : ℚ) + 1) / 2 - ((k : ℚ) - i) - j
      linarith)
  have s1up := Finset.sum_le_card_nsmul (Icc 2 k)
    (fun i : ℕ => v i - ((t : ℚ) + 1) / 2 - ((k : ℚ) - i) - j) S
    (fun i hi => by
      have hi' := Finset.mem_Icc.mp hi
      have h2 : (i : ℚ) ≤ k := by exact_mod_cast hi'.2
      have := (hv i hi'.1 hi'.2).2
      show v i - ((t : ℚ) + 1) / 2 - ((k : ℚ) - i) - j ≤ S
      linarith)
  rw [Nat.card_Icc, nsmul_eq_mul, show k + 1 - 2 = k - 1 by omega, Nat.cast_sub hk, Nat.cast_one]
    at s1lo s1up
  have s2lo : 0 ≤ ∑ i ∈ Icc 1 j, (e j - b i - ((t : ℚ) + 1) / 2 - ((j : ℚ) - i)) :=
    Finset.sum_nonneg (fun i hi => by
      have hi' := Finset.mem_Icc.mp hi; exact (hup i hi'.1 hi'.2).1)
  have s2up := Finset.sum_le_card_nsmul (Icc 1 j)
    (fun i : ℕ => e j - b i - ((t : ℚ) + 1) / 2 - ((j : ℚ) - i)) η (fun i hi => by
      have hi' := Finset.mem_Icc.mp hi; exact (hup i hi'.1 hi'.2).2)
  rw [Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel] at s2up
  have s3lo : 0 ≤ ∑ i ∈ Ioc j m, (b i - e j - ((t : ℚ) - 1) / 2 - ((i : ℚ) - j)) :=
    Finset.sum_nonneg (fun i hi => by
      have hi' := Finset.mem_Ioc.mp hi; exact (hdn i hi'.1 hi'.2).1)
  have s3up := Finset.sum_le_card_nsmul (Ioc j m)
    (fun i : ℕ => b i - e j - ((t : ℚ) - 1) / 2 - ((i : ℚ) - j)) η (fun i hi => by
      have hi' := Finset.mem_Ioc.mp hi; exact (hdn i hi'.1 hi'.2).2)
  rw [Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub hjm] at s3up
  refine ⟨hsum, hup, hdn, ?_, ?_, ?_⟩
  · rw [hsum]; linarith
  · rw [hsum]; linarith
  · intro hkS hmk
    have hk0 : (0 : ℚ) ≤ k := by linarith
    have h1 : 0 ≤ (k : ℚ) * (S - k) := mul_nonneg hk0 (by linarith)
    have hm1 : (1 : ℚ) ≤ m := by linarith
    have h2 : 0 ≤ (m : ℚ) * (η - k * t) := mul_nonneg hm0 (by linarith)

    have h3 : 0 ≤ (k : ℚ) * (((m : ℚ) - 1) * ((t : ℚ) - 1)) :=
      mul_nonneg hk0 (mul_nonneg (by linarith) (by linarith))
    nlinarith

/- English proof (translation)
Introduce `k t m j u e b a bt b0 x S η hk ht hj hjm hkS hkη he hb hu1 huk hu hb0 hbt hx hw1 hw2`. Take `⟨p1, p2⟩` from `hc_place_top k t m j u e b a bt S η hk ht hj hjm hkS hkη he hb hu1 huk hu`. Establish `hx0 : (0 : ℚ) < x` using `by linarith`. Establish `hq0 : 0 ≤ b0 / x` using `div_nonneg hb0 hx0.le`. Establish `hq1 : b0 / x ≤ b0 / 2` using `div_le_div_of_nonneg_left hb0 (by norm_num) hx`.

Use `⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩` and prove the remaining obligations.
-/
theorem hCTopRow : HCTopRow := by
  intro k t m j u e b a bt b0 x S η hk ht hj hjm hkS hkη he hb hu1 huk hu hb0 hbt hx hw1 hw2
  obtain ⟨p1, p2⟩ := hc_place_top k t m j u e b a bt S η hk ht hj hjm hkS hkη he hb hu1 huk hu
  have hx0 : (0 : ℚ) < x := by linarith
  have hq0 : 0 ≤ b0 / x := div_nonneg hb0 hx0.le
  have hq1 : b0 / x ≤ b0 / 2 := div_le_div_of_nonneg_left hb0 (by norm_num) hx
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/- English proof (translation)
Introduce `k t m J P T u v e b a b' S η C hk ht hJ hTP hkS hmk hC hv hbe heb hη hoff htop`. Establish `hk0 : (0 : ℚ) ≤ k` using `Nat.cast_nonneg k`. Establish `ht1 : (1 : ℚ) ≤ t` using `by exact_mod_cast ht`. Prove the components needed by the constructor for the conclusion. Introduce `j hj`.

Take `⟨hj1, hjm⟩` from `hJ j hj`. Establish `hm1 : (1 : ℚ) ≤ m` using `by exact_mod_cast (by omega : 1 ≤ m)`. Establish `hkη : (k : ℚ) ≤ η`. Establish `h1 : 0 ≤ (k : ℚ) * ((t : ℚ) - 1)` using `mul_nonneg hk0 (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h` using `(hCDpi k t m j P T u e b a b' S η C hk ht hj1 hjm hTP hkS hkη hC (fun τ hτ i h1 h2 => by`. Use `heb τ hτ i h1 (by omega)` as an intermediate fact. Use `hbe τ hτ (i + 1) (by omega) (by omega)` as an intermediate fact. Use the proof step `linarith)`. Use the proof step `(fun τ hτ i h1 h2 => by`.

Use `hbe τ hτ i h1 (by omega)` as an intermediate fact. Establish `ab` using `abs_le.mp (hη τ hτ i j h1 (by omega) hj1 hjm)`. Prove the components needed by the constructor for the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear relations using `[ab.1]) hoff htop).1`.

Conclude with `h` after adjusting the coercions. Introduce `j hj`. Take `⟨hj1, hjm⟩` from `hJ j hj`. Establish `h : ∑ τ ∈ P, (((k : ℚ) - 1) * e τ j - (k * S + m * η)) ≤ ∑ τ ∈ P, HCDplus k t m j (v τ) (b τ) (e τ) + ∑ τ ∈ P, HCDminus k t m j (v τ) (b τ) (e τ)`. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_le_sum (fun τ hτ => ?_)` and prove the remaining obligations. Take `⟨-, -, -, h4, -, h6⟩` from `hCSigmaDegree k t m j (v τ) (b τ) (e τ) S η (by omega) ht hj1 hjm (hv τ hτ) (hbe τ hτ) (heb τ hτ) (fun i h1 h2 => hη τ hτ i j h1 h2 hj1 hjm)`. Establish `h6'` using `h6 hkS hmk`. Establish `hn : (0 : ℚ) ≤ (k : ℚ) + m + t - 1`. Establish `: (0 : ℚ) ≤ m` using `Nat.cast_nonneg m`.

Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities. Conclude with `h` after adjusting the coercions.
-/
theorem hCBalanceInputs : HCBalance := by
  intro k t m J P T u v e b a b' S η C hk ht hJ hTP hkS hmk hC hv hbe heb hη hoff htop
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have ht1 : (1 : ℚ) ≤ t := by exact_mod_cast ht
  constructor
  · intro j hj
    obtain ⟨hj1, hjm⟩ := hJ j hj
    have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have hkη : (k : ℚ) ≤ η := by
      have h1 : 0 ≤ (k : ℚ) * ((t : ℚ) - 1) := mul_nonneg hk0 (by linarith)
      nlinarith
    have h := (hCDpi k t m j P T u e b a b' S η C hk ht hj1 hjm hTP hkS hkη hC
      (fun τ hτ i h1 h2 => by
        have := heb τ hτ i h1 (by omega)
        have := hbe τ hτ (i + 1) (by omega) (by omega)
        linarith)
      (fun τ hτ i h1 h2 => by
        have := hbe τ hτ i h1 (by omega)
        have ab := abs_le.mp (hη τ hτ i j h1 (by omega) hj1 hjm)
        constructor
        · linarith
        · linarith [ab.1]) hoff htop).1
    exact_mod_cast h
  · intro j hj
    obtain ⟨hj1, hjm⟩ := hJ j hj
    have h : ∑ τ ∈ P, (((k : ℚ) - 1) * e τ j - (k * S + m * η))
        ≤ ∑ τ ∈ P, HCDplus k t m j (v τ) (b τ) (e τ)
          + ∑ τ ∈ P, HCDminus k t m j (v τ) (b τ) (e τ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun τ hτ => ?_)
      obtain ⟨-, -, -, h4, -, h6⟩ := hCSigmaDegree k t m j (v τ) (b τ) (e τ) S η (by omega) ht hj1
        hjm (hv τ hτ) (hbe τ hτ) (heb τ hτ) (fun i h1 h2 => hη τ hτ i j h1 h2 hj1 hjm)
      have h6' := h6 hkS hmk
      have hn : (0 : ℚ) ≤ (k : ℚ) + m + t - 1 := by
        have : (0 : ℚ) ≤ m := Nat.cast_nonneg m
        linarith
      nlinarith
    exact_mod_cast h

section Tests

private def tu : ℕ → ℕ → ℚ := fun τ i =>
  if τ = 0 then (if i = 1 then 21 / 2 else -3 / 2) else (if i = 1 then 3 / 2 else 1 / 2)
private def te : ℕ → ℚ := fun i => 4 * i
private def tb : ℕ → ℚ := fun i => 4 * i - 2
private def tv : ℕ → ℚ := fun _ => 1

/- English proof (translation)
Evaluate the numerical expressions using `[HCnu, HCparam, HCrank, tu, te]`.
-/
example : HCnu 2 1 (tu 0) te 2 1 = 14 ∧ HCnu 2 1 (tu 0) te 2 2 = 3 ∧ HCnu 2 1 (tu 0) te 2 3 = 2 ∧
    HCnu 2 1 (tu 0) te 2 4 = 2 := by
  norm_num [HCnu, HCparam, HCrank, tu, te]
/- English proof (translation)
Evaluate the numerical expressions using `[HCdeg, HCnu, HCparam, HCrank, tu, te, Finset.sum_Icc_succ_top]`.
-/
example : HCdeg 2 1 (tu 0) te 2 = 21 := by
  norm_num [HCdeg, HCnu, HCparam, HCrank, tu, te, Finset.sum_Icc_succ_top]
/- English proof (translation)
Evaluate the numerical expressions using `[HCDplus, HCDminus, HCkap, HCsparam, tv, tb, te, Finset.sum_Ico_succ_top]`.
-/
example : HCDplus 2 1 2 2 tv tb te = 11 ∧ HCDminus 2 1 2 2 tv tb te = 0 := by
  norm_num [HCDplus, HCDminus, HCkap, HCsparam, tv, tb, te, Finset.sum_Ico_succ_top]
/- English proof (translation)
Evaluate the numerical expressions using `[HCDplus, HCDminus, HCkap, HCsparam, tv, tb, te, Finset.sum_Ico_succ_top]`.
-/
example : HCDplus 2 1 2 1 tv tb te = 4 ∧ HCDminus 2 1 2 1 tv tb te = 1 := by
  norm_num [HCDplus, HCDminus, HCkap, HCsparam, tv, tb, te, Finset.sum_Ico_succ_top]

/- English proof (translation)
Use `(hCBalanceInputs 2 1 2 {1, 2} {0, 1} {0} tu (fun _ => tv) (fun _ => te) (fun _ => tb) (fun _ => 10) (fun _ => 1) 2 6 0 le_rfl le_rfl ?_ ?_ ?_ ?_ le_rfl ?_ ?_ ?_ ?_ ?_ ?_).1` and prove the remaining obligations. Introduce `j hj`. Simplify using `at hj`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.

Evaluate the numerical expressions. Evaluate the numerical expressions. Introduce `τ _ i _ _`. Evaluate the numerical expressions using `[tv]`. Introduce `τ _ i _ _`.

Simplify using `only [tb, te]`. Evaluate the numerical expressions. Introduce `τ _ i _ _`. Simplify using `only [tb, te]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Apply the tactic sequence `intro τ _ i j h1 h2 h3 h4 interval_cases i <;> interval_cases j <;> norm_num [tb, te, abs_le]`. Introduce `τ hτ i h1 h2`. Establish `: τ = 1` using `by simp at hτ; omega`. Substitute `this` using the available equality.

Apply the tactic sequence `interval_cases i <;> norm_num [tu]`. Introduce `τ hτ`. Establish `: τ = 0` using `by simpa using hτ`. Substitute `this` using the available equality. Use `⟨by norm_num [tu], by norm_num [tu], by norm_num, ?_⟩` and prove the remaining obligations.

Introduce `i h1 h2`. Use linear arithmetic over natural numbers and integers.
-/
example :
    (∀ j ∈ ({1, 2} : Finset ℕ), ((∑ τ ∈ ({0, 1} : Finset ℕ), HCdeg 2 1 (tu τ) te j : ℚ) : ℝ)
      ≤ ∑ _τ ∈ ({0} : Finset ℕ), ((10 : ℚ) : ℝ)
        + ∑ _τ ∈ ({0, 1} : Finset ℕ), (((2 : ℕ) : ℝ) * (te j : ℝ)
            + ((((0 : ℚ) + 1) * (2 : ℕ) * 2 + 2 * (2 : ℕ) * (1 : ℕ) * 6 : ℚ) : ℝ))) := by
  refine (hCBalanceInputs 2 1 2 {1, 2} {0, 1} {0} tu (fun _ => tv) (fun _ => te) (fun _ => tb)
    (fun _ => 10) (fun _ => 1) 2 6 0 le_rfl le_rfl ?_ ?_ ?_ ?_ le_rfl ?_ ?_ ?_ ?_ ?_ ?_).1
  · intro j hj; simp at hj; omega
  · simp
  · norm_num
  · norm_num
  · intro τ _ i _ _; norm_num [tv]
  · intro τ _ i _ _; simp only [tb, te]; norm_num
  · intro τ _ i _ _; simp only [tb, te]; push_cast; linarith
  · intro τ _ i j h1 h2 h3 h4
    interval_cases i <;> interval_cases j <;> norm_num [tb, te, abs_le]
  · intro τ hτ i h1 h2
    have : τ = 1 := by simp at hτ; omega
    subst this
    interval_cases i <;> norm_num [tu]
  · intro τ hτ
    have : τ = 0 := by simpa using hτ
    subst this
    refine ⟨by norm_num [tu], by norm_num [tu], by norm_num, ?_⟩
    intro i h1 h2; omega

/- English proof (translation)
Use `(hCPartition 2 1 (tu 0) te 2 2 (by norm_num) (by norm_num) ?_ ?_ ?_ ?_).2.2.2.2` and prove the remaining obligations. Introduce `i h1 h2`. Establish `: i = 1` using `by omega`. Substitute `this` using the available equality. Evaluate the numerical expressions using `[tu]`.

Evaluate the numerical expressions using `[tu]`. Evaluate the numerical expressions using `[te]`. Introduce `i _ _`. Simplify using `only [te]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
example : ∀ l, 1 ≤ l → l ≤ HCrank 2 1 (2 - 1) → 0 ≤ HCnu 2 1 (tu 0) te 2 l := by
  refine (hCPartition 2 1 (tu 0) te 2 2 (by norm_num) (by norm_num) ?_ ?_ ?_ ?_).2.2.2.2
  · intro i h1 h2
    have : i = 1 := by omega
    subst this; norm_num [tu]
  · norm_num [tu]
  · norm_num [te]
  · intro i _ _; simp only [te]; push_cast; linarith

/- English proof (translation)
Evaluate the numerical expressions using `[HCdeg, HCnu, HCparam, HCrank, tu, Finset.sum_Icc_succ_top]`.
-/
example : (10 : ℚ) + (2 - 1) * 1000 + (2 * 2 + 2 * 1 * 1 * 2)
    < HCdeg 2 1 (tu 0) (fun _ => 1000) 1 := by
  norm_num [HCdeg, HCnu, HCparam, HCrank, tu, Finset.sum_Icc_succ_top]

/- English proof (translation)
Evaluate the numerical expressions using `[HCnu, HCparam, HCrank, tu]`.
-/
example : HCnu 2 1 (tu 0) (fun i => i) 2 3 < 0 := by
  norm_num [HCnu, HCparam, HCrank, tu]

/- English proof (translation)
Use `(hCSizesB 1 2 2 2 (fun _ => 0) (fun i => 5 * i) 5 1 5 (by norm_num) le_rfl (by norm_num) (by norm_num) ?_ ?_).2.2.2.2.2.2` and prove the remaining obligations. Introduce `i _ _`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Apply the tactic sequence `intro i h1 h2 interval_cases i <;> norm_num [abs_le]`.
-/
example : HCdeg 1 2 (fun _ => 0) (fun i => 5 * i) 2 - ∑ i ∈ Icc 1 1, HClam0 1 (fun _ => 0) i
    - ((1 : ℕ) : ℚ) * (5 * ((2 : ℕ) : ℚ)) ≤ 2 * ((2 : ℕ) : ℚ) * (((2 : ℕ) : ℚ) + 1) * 5 := by
  refine (hCSizesB 1 2 2 2 (fun _ => 0) (fun i => 5 * i) 5 1 5 (by norm_num) le_rfl (by norm_num)
    (by norm_num) ?_ ?_).2.2.2.2.2.2
  · intro i _ _; push_cast; linarith
  · intro i h1 h2
    interval_cases i <;> norm_num [abs_le]

/- English proof (translation)
Use `(hCTopRow 2 1 1 1 (tu 0) te tb 10 1 1 2 2 6 le_rfl le_rfl le_rfl le_rfl (by norm_num) (by norm_num) ?_ ?_ (by norm_num [tu]) (by norm_num [tu]) ?_ (by norm_num) le_rfl le_rfl (by norm_num [te]) (by norm_num [te])).2.2.2.1` and prove the remaining obligations. Introduce `i h1 h2`. Use linear arithmetic over natural numbers and integers. Introduce `i h1 h2`. Use linear arithmetic over natural numbers and integers.

Introduce `i h1 h2`. Use linear arithmetic over natural numbers and integers.
-/
example : HCdeg 2 1 (tu 0) te 1 ≤ 10 + (((2 : ℕ) : ℚ) - 1) * te 1 + 1 / 2
    + (((2 : ℕ) : ℚ) * 2 + (2 * ((1 : ℕ) : ℚ) * ((1 : ℕ) : ℚ) + 1) * 6) := by
  refine (hCTopRow 2 1 1 1 (tu 0) te tb 10 1 1 2 2 6 le_rfl le_rfl le_rfl le_rfl (by norm_num)
    (by norm_num) ?_ ?_ (by norm_num [tu]) (by norm_num [tu]) ?_ (by norm_num) le_rfl le_rfl
    (by norm_num [te]) (by norm_num [te])).2.2.2.1
  · intro i h1 h2; omega
  · intro i h1 h2; omega
  · intro i h1 h2; omega

/- English proof (translation)
Use `(hCSigmaPartition 2 1 2 1 tv tb te (by norm_num) le_rfl le_rfl (by norm_num) ?_ ?_ ?_ ?_).2.2.1` and prove the remaining obligations. Introduce `i h1 h2`. Use linear arithmetic over natural numbers and integers. Introduce `_`. Evaluate the numerical expressions using `[tv, tb]`.

Introduce `i _ _`. Simplify using `only [tb, te]`. Evaluate the numerical expressions. Introduce `i _ _`. Simplify using `only [tb, te]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
example : ∀ l, 1 ≤ l → l < 2 + 1 → 1 ≤ HCkap 2 1 2 1 tv tb te l := by
  refine (hCSigmaPartition 2 1 2 1 tv tb te (by norm_num) le_rfl le_rfl (by norm_num) ?_ ?_ ?_ ?_).2.2.1
  · intro i h1 h2; omega
  · intro _; norm_num [tv, tb]
  · intro i _ _; simp only [tb, te]; norm_num
  · intro i _ _; simp only [tb, te]; push_cast; linarith

end Tests

end Formalism.CG
