import Formalism.LocalToGlobal.CharacterGerms.CoeffFirstPairingLinear

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace RootsP

variable {C : Type} [Field C] {V : VF C}

/- English proof (translation)
Simplify using `only [VF.MM, AddValuation.map_zero]`. Use `first`. Consider the case `exact WithTop.coe_lt_top 0`. Consider the case `exact WithTop.zero_lt_top`. Consider the case `simp`.
-/
private lemma mm_zero_lemma : V.MM (0 : C) := by
  simp only [VF.MM, AddValuation.map_zero]
  first
    | exact WithTop.coe_lt_top 0
    | exact WithTop.zero_lt_top
    | simp

/- English proof (translation)
Simplify using `only [VF.Ge, AddValuation.map_zero]`. Conclude with `le_top`.
-/
private lemma ge0_zero_lemma_2 : V.Ge 0 (0 : C) := by
  simp only [VF.Ge, AddValuation.map_zero]
  exact le_top

/- English proof (translation)
Simplify using `only [VF.MM] at hx hy ⊢`. Conclude with `lt_of_lt_of_le (lt_min hx hy) (V.v.map_add x y)`.
-/
private lemma mm_add_lemma_3 {x y : C} (hx : V.MM x) (hy : V.MM y) : V.MM (x + y) := by
  simp only [VF.MM] at hx hy ⊢
  exact lt_of_lt_of_le (lt_min hx hy) (V.v.map_add x y)

/- English proof (translation)
Simplify using `only [VF.Ge] at hx hy ⊢`. Conclude with `le_trans (le_min hx hy) (V.v.map_add x y)`.
-/
private lemma ge0_add_lemma_4 {x y : C} (hx : V.Ge 0 x) (hy : V.Ge 0 y) : V.Ge 0 (x + y) := by
  simp only [VF.Ge] at hx hy ⊢
  exact le_trans (le_min hx hy) (V.v.map_add x y)

/- English proof (translation)
Simplify using `only [VF.MM, VF.Ge, AddValuation.map_mul] at hx hy ⊢`. Establish `hy' : (0 : WithTop ℝ) ≤ V.v y` using `by simpa using hy`. Conclude with `lt_of_lt_of_le hx (le_add_of_nonneg_right hy')`.
-/
private lemma mm_mul_lemma_5 {x y : C} (hx : V.MM x) (hy : V.Ge 0 y) : V.MM (x * y) := by
  simp only [VF.MM, VF.Ge, AddValuation.map_mul] at hx hy ⊢
  have hy' : (0 : WithTop ℝ) ≤ V.v y := by simpa using hy
  exact lt_of_lt_of_le hx (le_add_of_nonneg_right hy')

/- English proof (translation)
Simplify using `only [VF.Ge, AddValuation.map_mul] at hx hy ⊢`. Establish `hx' : (0 : WithTop ℝ) ≤ V.v x` using `by simpa using hx`. Establish `hy' : (0 : WithTop ℝ) ≤ V.v y` using `by simpa using hy`. Establish `h` using `add_le_add hx' hy'`. Simplify using `using h`.
-/
private lemma ge0_mul_lemma_6 {x y : C} (hx : V.Ge 0 x) (hy : V.Ge 0 y) : V.Ge 0 (x * y) := by
  simp only [VF.Ge, AddValuation.map_mul] at hx hy ⊢
  have hx' : (0 : WithTop ℝ) ≤ V.v x := by simpa using hx
  have hy' : (0 : WithTop ℝ) ≤ V.v y := by simpa using hy
  have h := add_le_add hx' hy'
  simpa using h

/- English proof (translation)
Simplify using `[VF.Ge]`.
-/
private lemma ge0_one_lemma_7 : V.Ge 0 (1 : C) := by
  simp [VF.Ge]

/- English proof (translation)
Introduce `μ`. Rewrite using `[MvPowerSeries.coeff_mul]`. Conclude with `Finset.sum_induction _ (fun x => V.Ge 0 x) (fun a b ha hb => ge0_add_lemma_4 ha hb) ge0_zero_lemma_2 (fun p _ => ge0_mul_lemma_6 (hF p.1) (hG p.2))`.
-/
private lemma ints_mul_lemma_8 {σ : Type} {F G : MvPowerSeries σ C} (hF : IntS V F) (hG : IntS V G) :
    IntS V (F * G) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  exact Finset.sum_induction _ (fun x => V.Ge 0 x) (fun a b ha hb => ge0_add_lemma_4 ha hb) ge0_zero_lemma_2
    (fun p _ => ge0_mul_lemma_6 (hF p.1) (hG p.2))

/- English proof (translation)
Introduce `μ`. Rewrite using `[MvPowerSeries.coeff_one]`. Use `split_ifs`. Conclude with `ge0_one_lemma_7`. Conclude with `ge0_zero_lemma_2`.
-/
private lemma ints_one_lemma_9 {σ : Type} : IntS V (1 : MvPowerSeries σ C) := by
  intro μ
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact ge0_one_lemma_7
  · exact ge0_zero_lemma_2

/- English proof (translation)
Simplify using `only [VF.MM] at h`. Simplify using `only [VF.Ge]`. Establish `h'` using `le_of_lt h`. Simplify using `using h'`.
-/
private lemma ge_zero_of_mm {x : C} (h : V.MM x) : V.Ge 0 x := by
  simp only [VF.MM] at h
  simp only [VF.Ge]
  have h' := le_of_lt h
  simpa using h'

/- English proof (translation)
Establish `h1 : c = (c - 1) + 1` using `by ring`. Rewrite using `[h1]`. Conclude with `ge0_add_lemma_4 (ge_zero_of_mm h) ge0_one_lemma_7`.
-/
private lemma ge_zero_of_mm_sub_one {c : C} (h : V.MM (c - 1)) : V.Ge 0 c := by
  have h1 : c = (c - 1) + 1 := by ring
  rw [h1]
  exact ge0_add_lemma_4 (ge_zero_of_mm h) ge0_one_lemma_7

/- English proof (translation)
Introduce `μ`. Rewrite using `[MvPowerSeries.coeff_mul]`. Conclude with `Finset.sum_induction _ (fun x => V.MM x) (fun a b ha hb => mm_add_lemma_3 ha hb) mm_zero_lemma (fun p _ => mm_mul_lemma_5 (hA p.1) (hB p.2))`.
-/
theorem mm_mul_series {σ : Type} {A B : MvPowerSeries σ C} (hA : ∀ μ, V.MM (MvPowerSeries.coeff μ A))
    (hB : ∀ μ, V.Ge 0 (MvPowerSeries.coeff μ B)) : ∀ μ, V.MM (MvPowerSeries.coeff μ (A * B)) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  exact Finset.sum_induction _ (fun x => V.MM x) (fun a b ha hb => mm_add_lemma_3 ha hb) mm_zero_lemma
    (fun p _ => mm_mul_lemma_5 (hA p.1) (hB p.2))

/- English proof (translation)
Break down `V with ⟨v, l, hp, hv⟩` into its components or cases. Express the relevant statement in the definitionally equal form `ζ ^ l = 1 at hζ`. Express the relevant statement in the definitionally equal form `(0 : WithTop ℝ) < v (ζ - 1)`. Take `⟨l', rfl⟩ : ∃ l', l = l' + 1` from `⟨l - 1, by have := hp.pos; omega⟩`. Assume the negation of the conclusion as `hneg`.

Establish `hle : v (ζ - 1) ≤ 0` using `not_lt.mp hneg`. Establish `hne : v (ζ - 1) ≠ ⊤` using `ne_top_of_le_ne_top (by simp) hle`. Take `⟨r, hr⟩` from `WithTop.ne_top_iff_exists.mp hne`. Establish `hr0 : r ≤ 0`. Rewrite `hle` using `[← hr]`.

Conclude with `hle` after adjusting the coercions. Establish `hnat : ∀ q : ℕ, (0 : WithTop ℝ) ≤ v (q : C)`. Introduce `q`. Proceed by induction on `q with`. Consider the case `zero => simp`.

Consider the case `succ q ih`. Use `push_cast`. Conclude with `le_trans (le_min ih (by simp)) (v.map_add _ _)`. Establish `hpow : ∀ m : ℕ, v ((ζ - 1) ^ m) = (((m : ℝ) * r : ℝ) : WithTop ℝ)`. Introduce `m`.

Rewrite using `[AddValuation.map_pow, ← hr]`. Use `first`. Consider the case `rw [← WithTop.coe_nsmul, nsmul_eq_mul]`. Consider the case `(norm_cast; simp [nsmul_eq_mul])`. Establish `hbin : ∑ m ∈ Finset.range (l' + 1 + 1), (ζ - 1) ^ m * 1 ^ (l' + 1 - m) * ((l' + 1).choose m : C) = 1`.

Rewrite using `[← add_pow, sub_add_cancel, hζ]`. Rewrite `hbin` using `[Finset.sum_range_succ, Finset.sum_range_succ']`. Simplify using `only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one] at hbin`. Establish `hx : (ζ - 1) ^ (l' + 1) = -∑ m ∈ Finset.range l', (ζ - 1) ^ (m + 1) * ((l' + 1).choose (m + 1) : C)`. Take the linear combination `hbin`.

Establish `hterm : ∀ m ∈ Finset.range l', v ((ζ - 1) ^ (l' + 1)) < v ((ζ - 1) ^ (m + 1) * ((l' + 1).choose (m + 1) : C))`. Introduce `m hm`. Rewrite `hm` using `[Finset.mem_range]`. Take `⟨q, hq⟩` from `hp.dvd_choose_self (k := m + 1) (by omega) (by omega)`. Rewrite using `[AddValuation.map_mul, hq, Nat.cast_mul, AddValuation.map_mul, hv, hpow, hpow]`.

Establish `hq0` using `hnat q`. Establish `hm' : (m : ℝ) ≤ l'` using `by exact_mod_cast hm.le`. Establish `hreal : ((l' + 1 : ℕ) : ℝ) * r < ((m + 1 : ℕ) : ℝ) * r + 1`. Use `push_cast`. Use polynomial arithmetic with `[mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hm') hr0]`.

Establish `hA : ((((l' + 1 : ℕ) : ℝ) * r : ℝ) : WithTop ℝ) < ((((m + 1 : ℕ) : ℝ) * r + 1 : ℝ) : WithTop ℝ)` using `WithTop.coe_lt_coe.mpr hreal`. Establish `hB : ((((m + 1 : ℕ) : ℝ) * r + 1 : ℝ) : WithTop ℝ) ≤ ((((m + 1 : ℕ) : ℝ) * r : ℝ) : WithTop ℝ) + (1 + v (q : C))`. Rewrite using `[WithTop.coe_add, WithTop.coe_one]`. Conclude with `add_le_add le_rfl (le_add_of_nonneg_right hq0)`. Conclude with `lt_of_lt_of_le hA hB`.

Establish `hsum : v ((ζ - 1) ^ (l' + 1)) < v (∑ m ∈ Finset.range l', (ζ - 1) ^ (m + 1) * ((l' + 1).choose (m + 1) : C))`. Use `Finset.sum_induction _ (fun y => v ((ζ - 1) ^ (l' + 1)) < v y) ?_ ?_ hterm` and prove the remaining obligations. Introduce `a b ha hb`. Conclude with `lt_of_lt_of_le (lt_min ha hb) (v.map_add a b)`. Rewrite using `[AddValuation.map_zero, hpow]`.

Conclude with `WithTop.coe_lt_top _`. Establish `hx' : v ((ζ - 1) ^ (l' + 1)) = v (∑ m ∈ Finset.range l', (ζ - 1) ^ (m + 1) * ((l' + 1).choose (m + 1) : C))`. Rewrite using `[hx, AddValuation.map_neg]`. Rewrite `hsum` using `[← hx']`. Conclude with `lt_irrefl _ hsum`.
-/
theorem root_one {ζ : C} (hζ : ζ ^ V.l = 1) : V.MM (ζ - 1) := by
  rcases V with ⟨v, l, hp, hv⟩
  change ζ ^ l = 1 at hζ
  change (0 : WithTop ℝ) < v (ζ - 1)
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by have := hp.pos; omega⟩
  by_contra hneg
  have hle : v (ζ - 1) ≤ 0 := not_lt.mp hneg
  have hne : v (ζ - 1) ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  have hr0 : r ≤ 0 := by
    rw [← hr] at hle
    exact_mod_cast hle
  have hnat : ∀ q : ℕ, (0 : WithTop ℝ) ≤ v (q : C) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      push_cast
      exact le_trans (le_min ih (by simp)) (v.map_add _ _)
  have hpow : ∀ m : ℕ, v ((ζ - 1) ^ m) = (((m : ℝ) * r : ℝ) : WithTop ℝ) := by
    intro m
    rw [AddValuation.map_pow, ← hr]
    first
      | rw [← WithTop.coe_nsmul, nsmul_eq_mul]
      | (norm_cast; simp [nsmul_eq_mul])
  have hbin : ∑ m ∈ Finset.range (l' + 1 + 1), (ζ - 1) ^ m * 1 ^ (l' + 1 - m) * ((l' + 1).choose m : C) = 1 := by
    rw [← add_pow, sub_add_cancel, hζ]
  rw [Finset.sum_range_succ, Finset.sum_range_succ'] at hbin
  simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one] at hbin
  have hx : (ζ - 1) ^ (l' + 1) = -∑ m ∈ Finset.range l', (ζ - 1) ^ (m + 1) * ((l' + 1).choose (m + 1) : C) := by
    linear_combination hbin
  have hterm : ∀ m ∈ Finset.range l', v ((ζ - 1) ^ (l' + 1)) <
      v ((ζ - 1) ^ (m + 1) * ((l' + 1).choose (m + 1) : C)) := by
    intro m hm
    rw [Finset.mem_range] at hm
    obtain ⟨q, hq⟩ := hp.dvd_choose_self (k := m + 1) (by omega) (by omega)
    rw [AddValuation.map_mul, hq, Nat.cast_mul, AddValuation.map_mul, hv, hpow, hpow]
    have hq0 := hnat q
    have hm' : (m : ℝ) ≤ l' := by exact_mod_cast hm.le
    have hreal : ((l' + 1 : ℕ) : ℝ) * r < ((m + 1 : ℕ) : ℝ) * r + 1 := by
      push_cast
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hm') hr0]
    have hA : ((((l' + 1 : ℕ) : ℝ) * r : ℝ) : WithTop ℝ) < ((((m + 1 : ℕ) : ℝ) * r + 1 : ℝ) : WithTop ℝ) :=
      WithTop.coe_lt_coe.mpr hreal
    have hB : ((((m + 1 : ℕ) : ℝ) * r + 1 : ℝ) : WithTop ℝ) ≤
        ((((m + 1 : ℕ) : ℝ) * r : ℝ) : WithTop ℝ) + (1 + v (q : C)) := by
      rw [WithTop.coe_add, WithTop.coe_one]
      exact add_le_add le_rfl (le_add_of_nonneg_right hq0)
    exact lt_of_lt_of_le hA hB
  have hsum : v ((ζ - 1) ^ (l' + 1)) <
      v (∑ m ∈ Finset.range l', (ζ - 1) ^ (m + 1) * ((l' + 1).choose (m + 1) : C)) := by
    refine Finset.sum_induction _ (fun y => v ((ζ - 1) ^ (l' + 1)) < v y) ?_ ?_ hterm
    · intro a b ha hb
      exact lt_of_lt_of_le (lt_min ha hb) (v.map_add a b)
    · rw [AddValuation.map_zero, hpow]
      exact WithTop.coe_lt_top _
  have hx' : v ((ζ - 1) ^ (l' + 1)) =
      v (∑ m ∈ Finset.range l', (ζ - 1) ^ (m + 1) * ((l' + 1).choose (m + 1) : C)) := by
    rw [hx, AddValuation.map_neg]
  rw [← hx'] at hsum
  exact lt_irrefl _ hsum

end RootsP

/- English proof (translation)
Introduce `C _ V ζ hζ j f hf`. Establish `hc : ∀ (k : ℕ) (μ : Fin 2 →₀ ℕ), (μ.prod fun s m => (if s = j then ζ ^ k else 1) ^ m) ^ V.l = 1`. Introduce `k μ`. Establish `hk : (ζ ^ k) ^ V.l = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ, one_pow]`.

Unfold `Finsupp.prod`. Rewrite using `[← Finset.prod_pow]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `s _`. Rewrite using `[← pow_mul, mul_comm, pow_mul]`.

Use `split_ifs`. Rewrite using `[hk, one_pow]`. Simplify using the standard rewrite rules. Establish `hcoef : ∀ (k : ℕ) (μ : Fin 2 →₀ ℕ), MvPowerSeries.coeff μ (MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f) = (μ.prod fun s m => (if s = j then ζ ^ k else 1) ^ m) * MvPowerSeries.coeff μ f`. Introduce `k μ`.

Use `first`. Consider the case `exact MvPowerSeries.coeff_rescale _ _ _`. Consider the case `rw [MvPowerSeries.coeff_rescale]`. Consider the case `simp [MvPowerSeries.coeff_rescale]`. Establish `hE : ∀ (k : ℕ) (μ : Fin 2 →₀ ℕ), V.MM (MvPowerSeries.coeff μ (MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f - f))`.

Introduce `k μ`. Rewrite using `[map_sub, hcoef, ← sub_one_mul]`. Conclude with `RootsP.mm_mul_lemma_5 (RootsP.root_one (hc k μ)) (hf μ)`. Establish `hG : ∀ k : ℕ, IntS V (MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f)`. Introduce `k μ`.

Rewrite using `[hcoef]`. Conclude with `RootsP.ge0_mul_lemma_6 (RootsP.ge_zero_of_mm_sub_one (RootsP.root_one (hc k μ))) (hf μ)`. Establish `hpow : ∀ n : ℕ, IntS V (f ^ n)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Rewrite using `[pow_zero]`. Conclude with `RootsP.ints_one_lemma_9`. Consider the case `succ n ih`. Rewrite using `[pow_succ]`.

Conclude with `RootsP.ints_mul_lemma_8 ih hf`. Establish `key : ∀ n : ℕ, ∀ μ, V.MM (MvPowerSeries.coeff μ (∏ k ∈ Finset.range n, MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f - f ^ n))`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`.

Introduce `μ`. Simplify using `only [Finset.range_zero, Finset.prod_empty, pow_zero, sub_self, map_zero]`. Conclude with `RootsP.mm_zero_lemma`. Consider the case `succ n ih`. Introduce `μ`.

Establish `hid : ∏ k ∈ Finset.range (n + 1), MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f - f ^ (n + 1) = (∏ k ∈ Finset.range n, MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f - f ^ n) * MvPowerSeries.rescale (fun i => if i = j then ζ ^ n else 1) f + f ^ n * …`. Rewrite using `[Finset.prod_range_succ, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hid, map_add]`. Use `RootsP.mm_add_lemma_3 (RootsP.mm_mul_series ih (hG n) μ) ?_` and prove the remaining obligations.

Rewrite using `[mul_comm]`. Conclude with `RootsP.mm_mul_series (hE n) (hpow n) μ`. Conclude with `key V.l`.
-/
theorem rootsProd : ∀ (C : Type) [Field C] (V : VF C) (ζ : C), ζ ^ V.l = 1 → ∀ (j : Fin 2)
    (f : MvPowerSeries (Fin 2) C), IntS V f → ∀ μ, V.MM (MvPowerSeries.coeff μ
      (∏ k ∈ Finset.range V.l, MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f - f ^ V.l)) := by
  intro C _ V ζ hζ j f hf
  have hc : ∀ (k : ℕ) (μ : Fin 2 →₀ ℕ), (μ.prod fun s m => (if s = j then ζ ^ k else 1) ^ m) ^ V.l = 1 := by
    intro k μ
    have hk : (ζ ^ k) ^ V.l = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    unfold Finsupp.prod
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro s _
    rw [← pow_mul, mul_comm, pow_mul]
    split_ifs
    · rw [hk, one_pow]
    · simp
  have hcoef : ∀ (k : ℕ) (μ : Fin 2 →₀ ℕ),
      MvPowerSeries.coeff μ (MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f) =
        (μ.prod fun s m => (if s = j then ζ ^ k else 1) ^ m) * MvPowerSeries.coeff μ f := by
    intro k μ
    first
      | exact MvPowerSeries.coeff_rescale _ _ _
      | rw [MvPowerSeries.coeff_rescale]
      | simp [MvPowerSeries.coeff_rescale]
  have hE : ∀ (k : ℕ) (μ : Fin 2 →₀ ℕ), V.MM (MvPowerSeries.coeff μ
      (MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f - f)) := by
    intro k μ
    rw [map_sub, hcoef, ← sub_one_mul]
    exact RootsP.mm_mul_lemma_5 (RootsP.root_one (hc k μ)) (hf μ)
  have hG : ∀ k : ℕ, IntS V (MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f) := by
    intro k μ
    rw [hcoef]
    exact RootsP.ge0_mul_lemma_6 (RootsP.ge_zero_of_mm_sub_one (RootsP.root_one (hc k μ))) (hf μ)
  have hpow : ∀ n : ℕ, IntS V (f ^ n) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero]
      exact RootsP.ints_one_lemma_9
    | succ n ih =>
      rw [pow_succ]
      exact RootsP.ints_mul_lemma_8 ih hf
  have key : ∀ n : ℕ, ∀ μ, V.MM (MvPowerSeries.coeff μ
      (∏ k ∈ Finset.range n, MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f - f ^ n)) := by
    intro n
    induction n with
    | zero =>
      intro μ
      simp only [Finset.range_zero, Finset.prod_empty, pow_zero, sub_self, map_zero]
      exact RootsP.mm_zero_lemma
    | succ n ih =>
      intro μ
      have hid : ∏ k ∈ Finset.range (n + 1), MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f -
          f ^ (n + 1) =
          (∏ k ∈ Finset.range n, MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f - f ^ n) *
              MvPowerSeries.rescale (fun i => if i = j then ζ ^ n else 1) f +
            f ^ n * (MvPowerSeries.rescale (fun i => if i = j then ζ ^ n else 1) f - f) := by
        rw [Finset.prod_range_succ, pow_succ]
        ring
      rw [hid, map_add]
      refine RootsP.mm_add_lemma_3 (RootsP.mm_mul_series ih (hG n) μ) ?_
      rw [mul_comm]
      exact RootsP.mm_mul_series (hE n) (hpow n) μ
  exact key V.l

end Formalism.L2.FormalSeriesBounds
