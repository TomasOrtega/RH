import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.ShufStd
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.UnitPowerEqResiduePower

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F

namespace PositivityTheory.Rg.BcB.F.Choice.IndefiniteRowSideFullHecke

/- English proof (translation)
Introduce `n x _ hx`. Establish `hx' : ∀ i j : Fin n, i < j → x j + 2 ≤ x i` using `hx`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`.

Establish `h1` using `hx' ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ (by show i.val < j.val; omega)`. Establish `h2` using `hx' ⟨n - 1 - j.val, by omega⟩ ⟨n - 1 - i.val, by omega⟩ (by show n - 1 - j.val < n - 1 - i.val; omega)`. Simplify using `only [lOf]`. Use linear arithmetic over natural numbers and integers. Establish `hi` using `i.isLt`.

Establish `h1` using `hx' ⟨i.val, by omega⟩ ⟨n - 1 - i.val, by omega⟩ (by show i.val < n - 1 - i.val; omega)`. Simplify using `only [lOf]`. Use linear arithmetic over natural numbers and integers.
-/
theorem coneTwo' : ConeTwo := by
  intro n x _ hx
  have hx' : ∀ i j : Fin n, i < j → x j + 2 ≤ x i := hx
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hi := i.isLt
    have hj := j.isLt
    have h1 := hx' ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ (by show i.val < j.val; omega)
    have h2 := hx' ⟨n - 1 - j.val, by omega⟩ ⟨n - 1 - i.val, by omega⟩ (by show n - 1 - j.val < n - 1 - i.val; omega)
    simp only [lOf]
    omega
  · have hi := i.isLt
    have h1 := hx' ⟨i.val, by omega⟩ ⟨n - 1 - i.val, by omega⟩ (by show i.val < n - 1 - i.val; omega)
    simp only [lOf]
    omega

/- English proof (translation)
Introduce `E _ _ _ w n a s h e he k`. Both sides reduce to the same expression.
-/
theorem shufStd' : ShufStd := by
  intro E _ _ _ w n a s h e he k
  rfl

/- English proof (translation)
Introduce `n a s h`. Establish `hp` using `h.1.2.2`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Finset.disjoint_left]`. Introduce `k h1 h2`.

Simplify using `only [symIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl] at h1 h2`. Use `k.isLt` as an intermediate fact. Apply the tactic sequence `rcases h1 with ⟨p, hp1⟩ | ⟨p, hp1⟩ | ⟨m1, m2, m3⟩ <;> rcases h2 with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q1, q2, q3⟩ <;> first | omega | exact hq hp1`. Use extensionality with `k`. Simplify using `only [symIdx, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, iff_true]`.

Use `k.isLt` as an intermediate fact. Distinguish the cases in `h1 : k.val < n / 2`. Distinguish the cases in `h2 : (⟨k.val, h1⟩ : Fin (n / 2)) ∈ s`. Conclude with `Or.inl (Or.inl ⟨h1, h2⟩)`. Conclude with `Or.inr (Or.inl ⟨h1, h2⟩)`.

Distinguish the cases in `h3 : n - 1 - k.val < n / 2`. Distinguish the cases in `h2 : (⟨n - 1 - k.val, h3⟩ : Fin (n / 2)) ∈ s`. Conclude with `Or.inl (Or.inr (Or.inl ⟨h3, h2⟩))`. Conclude with `Or.inr (Or.inr (Or.inl ⟨h3, h2⟩))`. Establish `hk : k.val = n / 2` using `by omega`.

Establish `hn : n % 2 = 1` using `by omega`. Distinguish the cases in `ha : a % 2 = 1`. Conclude with `Or.inl (Or.inr (Or.inr ⟨ha, hn, hk⟩))`. Conclude with `Or.inr (Or.inr (Or.inr ⟨by omega, hn, hk⟩))`.
-/
theorem shufEx' : ShufEx := by
  intro n a s h
  have hp := h.1.2.2
  constructor
  · rw [Finset.disjoint_left]
    intro k h1 h2
    simp only [symIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl] at h1 h2
    have := k.isLt
    rcases h1 with ⟨p, hp1⟩ | ⟨p, hp1⟩ | ⟨m1, m2, m3⟩ <;> rcases h2 with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q1, q2, q3⟩ <;>
      first | omega | exact hq hp1
  · ext k
    simp only [symIdx, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, iff_true]
    have := k.isLt
    by_cases h1 : k.val < n / 2
    · by_cases h2 : (⟨k.val, h1⟩ : Fin (n / 2)) ∈ s
      · exact Or.inl (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · by_cases h3 : n - 1 - k.val < n / 2
      · by_cases h2 : (⟨n - 1 - k.val, h3⟩ : Fin (n / 2)) ∈ s
        · exact Or.inl (Or.inr (Or.inl ⟨h3, h2⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨h3, h2⟩))
      · have hk : k.val = n / 2 := by omega
        have hn : n % 2 = 1 := by omega
        by_cases ha : a % 2 = 1
        · exact Or.inl (Or.inr (Or.inr ⟨ha, hn, hk⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨by omega, hn, hk⟩))

def sgn2 {N : ℕ} (i j : Fin N) : ℤ := (if i < j then 1 else 0) - (if j < i then 1 else 0)

/- English proof (translation)
Unfold `sgn2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair_sign_antisymm {N : ℕ} (i j : Fin N) : sgn2 i j = - sgn2 j i := by
  unfold sgn2; ring

/- English proof (translation)
Unfold `sgn2 rh`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]`. Use `i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_pair_sign_eq_rho {N : ℕ} (i : Fin N) : ∑ j, sgn2 i j = rh N i := by
  unfold sgn2 rh
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio,
    Fin.card_Ioi, Fin.card_Iio]
  have := i.isLt
  omega

/- English proof (translation)
Unfold `sgn2`. Simplify using `only [hf.lt_iff_lt]`.
-/
theorem pair_sign_strictMono {N M : ℕ} {f : Fin N → Fin M} (hf : StrictMono f) (i j : Fin N) : sgn2 (f i) (f j) = sgn2 i j := by
  unfold sgn2; simp only [hf.lt_iff_lt]

def lo (n : ℕ) (i : Fin (n / 2)) : Fin n := ⟨i.val, by have := i.isLt; omega⟩
def hi (n : ℕ) (i : Fin (n / 2)) : Fin n := ⟨n - 1 - i.val, by have := i.isLt; omega⟩
def md (n : ℕ) (t : Fin (n % 2)) : Fin n := ⟨n / 2 + t.val, by have := t.isLt; omega⟩

/- English proof (translation)
Set `φ : Fin (n / 2) ⊕ (Fin (n / 2) ⊕ Fin (n % 2)) → Fin n` to `Sum.elim (lo n) (Sum.elim (hi n) (md n))`. Establish `hφ : Function.Bijective φ`. Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Use `⟨?_, by simp only [Fintype.card_sum, Fintype.card_fin]; omega⟩` and prove the remaining obligations. Apply the tactic sequence `rintro (i | i | t) (j | j | u) h <;>`.

Apply the tactic sequence `simp only [φ, Sum.elim_inl, Sum.elim_inr, lo, hi, md, Fin.ext_iff, Fin.val_mk, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h ⊢ <;>`. Use `first`. Consider the case `omega`. Consider the case `(have := i.isLt; have := j.isLt; omega)`. Consider the case `(have := i.isLt; have := u.isLt; omega)`.

Consider the case `(have := t.isLt; have := j.isLt; omega)`. Consider the case `(have := t.isLt; have := u.isLt; omega)`. Rewrite using `[← Fintype.sum_bijective φ hφ (fun p => f (φ p)) f (fun _ => rfl), Fintype.sum_sum_type, Fintype.sum_sum_type, Finset.sum_add_distrib, add_assoc]`. Both sides reduce to the same expression.
-/
theorem sum_split {n : ℕ} (f : Fin n → ℤ) :
    ∑ k, f k = ∑ i, (f (lo n i) + f (hi n i)) + ∑ t, f (md n t) := by
  let φ : Fin (n / 2) ⊕ (Fin (n / 2) ⊕ Fin (n % 2)) → Fin n := Sum.elim (lo n) (Sum.elim (hi n) (md n))
  have hφ : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp only [Fintype.card_sum, Fintype.card_fin]; omega⟩
    rintro (i | i | t) (j | j | u) h <;>
      simp only [φ, Sum.elim_inl, Sum.elim_inr, lo, hi, md, Fin.ext_iff, Fin.val_mk, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq] at h ⊢ <;>
      first
      | omega
      | (have := i.isLt; have := j.isLt; omega)
      | (have := i.isLt; have := u.isLt; omega)
      | (have := t.isLt; have := j.isLt; omega)
      | (have := t.isLt; have := u.isLt; omega)
  rw [← Fintype.sum_bijective φ hφ (fun p => f (φ p)) f (fun _ => rfl), Fintype.sum_sum_type, Fintype.sum_sum_type,
    Finset.sum_add_distrib, add_assoc]
  rfl

/- English proof (translation)
Use `i.isLt` as an intermediate fact. Simplify using `only [symIdx, lo, Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨_, h⟩ | ⟨h1, _⟩ | ⟨_, _, h⟩)`. Conclude with `h`.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Introduce `h`. Conclude with `Or.inl ⟨i.isLt, h⟩`.
-/
theorem mem_lo {n : ℕ} (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) (i : Fin (n / 2)) :
    lo n i ∈ symIdx n mid s ↔ i ∈ s := by
  have := i.isLt
  simp only [symIdx, lo, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨_, h⟩ | ⟨h1, _⟩ | ⟨_, _, h⟩)
    · exact h
    · omega
    · omega
  · intro h; exact Or.inl ⟨i.isLt, h⟩

/- English proof (translation)
Use `i.isLt` as an intermediate fact. Simplify using `only [symIdx, hi, Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨h1, _⟩ | ⟨h1, h⟩ | ⟨_, _, h⟩)`. Use linear arithmetic over natural numbers and integers.

Establish `e : (⟨n - 1 - (n - 1 - i.val), h1⟩ : Fin (n / 2)) = i` using `Fin.ext (by show n - 1 - (n - 1 - i.val) = i.val; omega)`. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Use linear arithmetic over natural numbers and integers. Introduce `h`. Use `Or.inr (Or.inl ⟨by omega, ?_⟩)` and prove the remaining obligations.

Use `h using 1` and compare the differences between its conclusion and the goal. Conclude with `Fin.ext (by show n - 1 - (n - 1 - i.val) = i.val; omega)`.
-/
theorem mem_hi {n : ℕ} (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) (i : Fin (n / 2)) :
    hi n i ∈ symIdx n mid s ↔ i ∈ s := by
  have := i.isLt
  simp only [symIdx, hi, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, h⟩ | ⟨_, _, h⟩)
    · omega
    · have e : (⟨n - 1 - (n - 1 - i.val), h1⟩ : Fin (n / 2)) = i := Fin.ext (by show n - 1 - (n - 1 - i.val) = i.val; omega)
      rwa [e] at h
    · omega
  · intro h
    refine Or.inr (Or.inl ⟨by omega, ?_⟩)
    convert h using 1
    exact Fin.ext (by show n - 1 - (n - 1 - i.val) = i.val; omega)

/- English proof (translation)
Use `t.isLt` as an intermediate fact. Simplify using `only [symIdx, md, Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h, _, _⟩)`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Conclude with `h`. Introduce `h; exact Or.inr (Or.inr ⟨h, by omega, by omega⟩)`.
-/
theorem mem_md {n : ℕ} (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) (t : Fin (n % 2)) :
    md n t ∈ symIdx n mid s ↔ mid := by
  have := t.isLt
  simp only [symIdx, md, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h, _, _⟩)
    · omega
    · omega
    · exact h
  · intro h; exact Or.inr (Or.inr ⟨h, by omega, by omega⟩)

/- English proof (translation)
Rewrite using `[← Finset.sum_coe_sort S g]`. Conclude with `Fintype.sum_equiv (S.orderIsoOfFin h).toEquiv _ _ (fun i => rfl)`.
-/
theorem sum_oe {n m : ℕ} (S : Finset (Fin n)) (h : S.card = m) (g : Fin n → ℤ) :
    ∑ i, g (S.orderEmbOfFin h i) = ∑ k ∈ S, g k := by
  rw [← Finset.sum_coe_sort S g]
  exact Fintype.sum_equiv (S.orderIsoOfFin h).toEquiv _ _ (fun i => rfl)

/- English proof (translation)
Establish `hn : ∀ k : Fin n, rh n k = ∑ i, sgn2 k (e (Sum.inl i)) + ∑ j, sgn2 k (e (Sum.inr j))`. Introduce `k`. Rewrite using `[← sum_pair_sign_eq_rho k, ← Fintype.sum_sum_type (f := fun p => sgn2 k (e p))]`. Conclude with `(Fintype.sum_equiv e (fun p => sgn2 k (e p)) (fun j => sgn2 k j) (fun _ => rfl)).symm`. Establish `ha : ∀ i : Fin a, rh a i = ∑ i', sgn2 (e (Sum.inl i)) (e (Sum.inl i'))` using `fun i => by`.

Rewrite using `[← sum_pair_sign_eq_rho i]`. Conclude with `Finset.sum_congr rfl (fun i' _ => (pair_sign_strictMono hL i i').symm)`. Establish `hb : ∀ j : Fin b, rh b j = ∑ j', sgn2 (e (Sum.inr j)) (e (Sum.inr j'))` using `fun j => by`. Rewrite using `[← sum_pair_sign_eq_rho j]`. Conclude with `Finset.sum_congr rfl (fun j' _ => (pair_sign_strictMono hR j j').symm)`.

Rewrite using `[← Fintype.sum_equiv e (fun p => (rh n (e p) - Sum.elim (fun i : Fin a => rh a i) (fun j : Fin b => rh b j) (e.symm (e p))) * x (e p)) (fun k : Fin n => (rh n k - Sum.elim (fun i : Fin a => rh a i) (fun j : Fin b => rh b j) (e.symm k)) * x k) (fun _ => rfl)]`. Simplify using `only [Equiv.symm_apply_apply]`. Rewrite using `[Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, hn, ha, hb, add_sub_cancel_left, add_sub_cancel_right, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm (s := (Finset.univ : Finset (Fin b))), ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[pair_sign_antisymm (e (Sum.inr j))]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem blocks {n a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) (hL : StrictMono fun i => e (Sum.inl i))
    (hR : StrictMono fun j => e (Sum.inr j)) (x : Fin n → ℤ) :
    ∑ k : Fin n, (rh n k - Sum.elim (fun i : Fin a => rh a i) (fun j : Fin b => rh b j) (e.symm k)) * x k =
      ∑ i, ∑ j, (x (e (Sum.inl i)) - x (e (Sum.inr j))) * sgn2 (e (Sum.inl i)) (e (Sum.inr j)) := by
  have hn : ∀ k : Fin n, rh n k = ∑ i, sgn2 k (e (Sum.inl i)) + ∑ j, sgn2 k (e (Sum.inr j)) := by
    intro k
    rw [← sum_pair_sign_eq_rho k, ← Fintype.sum_sum_type (f := fun p => sgn2 k (e p))]
    exact (Fintype.sum_equiv e (fun p => sgn2 k (e p)) (fun j => sgn2 k j) (fun _ => rfl)).symm
  have ha : ∀ i : Fin a, rh a i = ∑ i', sgn2 (e (Sum.inl i)) (e (Sum.inl i')) := fun i => by
    rw [← sum_pair_sign_eq_rho i]; exact Finset.sum_congr rfl (fun i' _ => (pair_sign_strictMono hL i i').symm)
  have hb : ∀ j : Fin b, rh b j = ∑ j', sgn2 (e (Sum.inr j)) (e (Sum.inr j')) := fun j => by
    rw [← sum_pair_sign_eq_rho j]; exact Finset.sum_congr rfl (fun j' _ => (pair_sign_strictMono hR j j').symm)
  rw [← Fintype.sum_equiv e (fun p => (rh n (e p) - Sum.elim (fun i : Fin a => rh a i) (fun j : Fin b => rh b j)
      (e.symm (e p))) * x (e p))
    (fun k : Fin n => (rh n k - Sum.elim (fun i : Fin a => rh a i) (fun j : Fin b => rh b j) (e.symm k)) * x k) (fun _ => rfl)]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, hn, ha, hb, add_sub_cancel_left, add_sub_cancel_right, Finset.sum_mul]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin b))), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pair_sign_antisymm (e (Sum.inr j))]; ring

/- English proof (translation)
Rewrite using `[Finset.sum_ite_mem, Finset.univ_inter]`.
-/
theorem sum_ind {α : Type} [Fintype α] [DecidableEq α] (S : Finset α) (g : α → ℤ) :
    ∑ k ∈ S, g k = ∑ k, if k ∈ S then g k else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/- English proof (translation)
Simplify using `only [Fin.lt_def, lo]`.
-/
theorem lo_lt_lo {n : ℕ} (i j : Fin (n / 2)) : lo n i < lo n j ↔ i < j := by
  simp only [Fin.lt_def, lo]

/- English proof (translation)
Use `i.isLt` as an intermediate fact. Use `j.isLt` as an intermediate fact. Simplify using `only [Fin.lt_def, hi]`. Use linear arithmetic over natural numbers and integers.
-/
theorem hi_lt_hi {n : ℕ} (i j : Fin (n / 2)) : hi n i < hi n j ↔ j < i := by
  have := i.isLt; have := j.isLt
  simp only [Fin.lt_def, hi]; omega

/- English proof (translation)
Use `i.isLt` as an intermediate fact. Use `j.isLt` as an intermediate fact. Simplify using `only [Fin.lt_def, lo, hi]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lo_lt_hi {n : ℕ} (i j : Fin (n / 2)) : lo n i < hi n j := by
  have := i.isLt; have := j.isLt
  simp only [Fin.lt_def, lo, hi]; omega

/- English proof (translation)
Use `i.isLt` as an intermediate fact. Use `j.isLt` as an intermediate fact. Simplify using `only [Fin.lt_def, lo, hi]`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_hi_lt_lo {n : ℕ} (i j : Fin (n / 2)) : ¬ hi n i < lo n j := by
  have := i.isLt; have := j.isLt
  simp only [Fin.lt_def, lo, hi]; omega

/- English proof (translation)
Use `i.isLt` as an intermediate fact. Use `t.isLt` as an intermediate fact. Simplify using `only [Fin.lt_def, lo, md]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lo_lt_md {n : ℕ} (i : Fin (n / 2)) (t : Fin (n % 2)) : lo n i < md n t := by
  have := i.isLt; have := t.isLt
  simp only [Fin.lt_def, lo, md]; omega

/- English proof (translation)
Use `i.isLt` as an intermediate fact. Use `t.isLt` as an intermediate fact. Simplify using `only [Fin.lt_def, lo, md]`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_md_lt_lo {n : ℕ} (i : Fin (n / 2)) (t : Fin (n % 2)) : ¬ md n t < lo n i := by
  have := i.isLt; have := t.isLt
  simp only [Fin.lt_def, lo, md]; omega

/- English proof (translation)
Use `i.isLt` as an intermediate fact. Use `t.isLt` as an intermediate fact. Simplify using `only [Fin.lt_def, hi, md]`. Use linear arithmetic over natural numbers and integers.
-/
theorem md_lt_hi {n : ℕ} (i : Fin (n / 2)) (t : Fin (n % 2)) : md n t < hi n i := by
  have := i.isLt; have := t.isLt
  simp only [Fin.lt_def, hi, md]; omega

/- English proof (translation)
Use `i.isLt` as an intermediate fact. Use `t.isLt` as an intermediate fact. Simplify using `only [Fin.lt_def, hi, md]`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_hi_lt_md {n : ℕ} (i : Fin (n / 2)) (t : Fin (n % 2)) : ¬ hi n i < md n t := by
  have := i.isLt; have := t.isLt
  simp only [Fin.lt_def, hi, md]; omega

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lOf_eq {n : ℕ} (x : Fin n → ℤ) (i : Fin (n / 2)) : lOf x i = x (lo n i) - x (hi n i) := rfl

/- English proof (translation)
Simplify using `only [sgn2, lo_lt_lo, hi_lt_hi, lo_lt_hi, not_hi_lt_lo, lOf_eq, ↓reduceIte]`. Break down `lt_or_gt_of_ne hij with h | h` into its components or cases. Establish `h1` using `hx _ _ ((lo_lt_lo i j).mpr h)`. Establish `h2` using `hx _ _ ((hi_lt_hi j i).mpr h)`. Simplify using `only [h, not_lt.mpr h.le, ↓reduceIte]`.

Rewrite using `[max_eq_left (by linarith)]; ring`. Establish `h1` using `hx _ _ ((lo_lt_lo j i).mpr h)`. Establish `h2` using `hx _ _ ((hi_lt_hi i j).mpr h)`. Simplify using `only [h, not_lt.mpr h.le, ↓reduceIte]`. Rewrite using `[max_eq_right (by linarith)]; ring`.
-/
theorem pt4 {n : ℕ} (x : Fin n → ℤ) (hx : ∀ i j : Fin n, i < j → x j + 2 ≤ x i) (i j : Fin (n / 2)) (hij : i ≠ j) :
    (x (lo n i) - x (lo n j)) * sgn2 (lo n i) (lo n j) + (x (lo n i) - x (hi n j)) * sgn2 (lo n i) (hi n j) +
      (x (hi n i) - x (lo n j)) * sgn2 (hi n i) (lo n j) + (x (hi n i) - x (hi n j)) * sgn2 (hi n i) (hi n j) =
      2 * max (lOf x i) (lOf x j) := by
  simp only [sgn2, lo_lt_lo, hi_lt_hi, lo_lt_hi, not_hi_lt_lo, lOf_eq, ↓reduceIte]
  rcases lt_or_gt_of_ne hij with h | h
  · have h1 := hx _ _ ((lo_lt_lo i j).mpr h)
    have h2 := hx _ _ ((hi_lt_hi j i).mpr h)
    simp only [h, not_lt.mpr h.le, ↓reduceIte]
    rw [max_eq_left (by linarith)]; ring
  · have h1 := hx _ _ ((lo_lt_lo j i).mpr h)
    have h2 := hx _ _ ((hi_lt_hi i j).mpr h)
    simp only [h, not_lt.mpr h.le, ↓reduceIte]
    rw [max_eq_right (by linarith)]; ring

/- English proof (translation)
Use `set T : Fin n → Fin n → ℤ := fun k k' => if k ∈ symIdx n (a % 2 = 1) s then (if k' ∈ symIdx n ((n - a) % 2 = 1) sᶜ then (x k - x k') * sgn2 k k' else 0) else 0 with hT`. Establish `s1 : ∑ k ∈ symIdx n (a % 2 = 1) s, ∑ k' ∈ symIdx n ((n - a) % 2 = 1) sᶜ, (x k - x k') * sgn2 k k' = ∑ k, ∑ k', T k k'`. Rewrite using `[sum_ind (symIdx n (a % 2 = 1) s)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[sum_ind (symIdx n ((n - a) % 2 = 1) sᶜ)]`.

Distinguish the cases in `hk : k ∈ symIdx n (a % 2 = 1) s`. Simplify using `only [hT, hk, ↓reduceIte]`. Simplify using `only [hT, hk, ↓reduceIte, Finset.sum_const_zero]`. Establish `s2 : ∑ k, ∑ k', T k k' = ∑ i, ∑ j, (T (lo n i) (lo n j) + T (lo n i) (hi n j) + T (hi n i) (lo n j) + T (hi n i) (hi n j)) + ∑ i, ∑ u, (T (lo n i) (md n u) + T (hi n i) (md n u) + T (md n u) (lo n i) + T (md n u) (hi n i)) + ∑ t, ∑ u, T (md n t) (md n u)`. Simplify using `only [sum_split (n := n)]`.

Simplify using `only [Finset.sum_add_distrib]`. Establish `c1 : ∑ t, ∑ j, T (md n t) (lo n j) = ∑ j, ∑ t, T (md n t) (lo n j)` using `Finset.sum_comm`. Establish `c2 : ∑ t, ∑ j, T (md n t) (hi n j) = ∑ j, ∑ t, T (md n t) (hi n j)` using `Finset.sum_comm`. Rewrite using `[c1, c2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `s3 : ∑ i, ∑ j, (T (lo n i) (lo n j) + T (lo n i) (hi n j) + T (hi n i) (lo n j) + T (hi n i) (hi n j)) = 2 * ∑ i ∈ s, ∑ j ∈ sᶜ, max (lOf x i) (lOf x j)`. Rewrite using `[Finset.mul_sum, sum_ind s]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `his : i ∈ s`. Rewrite using `[if_pos his, Finset.mul_sum, sum_ind sᶜ]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hjs : j ∈ sᶜ`. Establish `hij : i ≠ j` using `by rintro rfl; exact (Finset.mem_compl.mp hjs) his`. Simplify using `only [hT, mem_lo, mem_hi, his, hjs, ↓reduceIte]`. Conclude with `pt4 x hx i j hij`.

Simplify using `only [hT, mem_lo, mem_hi, his, hjs, ↓reduceIte, add_zero]`. Rewrite using `[if_neg his]`. Simplify using `only [hT, mem_lo, mem_hi, his, ↓reduceIte, add_zero, Finset.sum_const_zero]`. Establish `q : ∀ i u, T (lo n i) (md n u) + T (hi n i) (md n u) + T (md n u) (lo n i) + T (md n u) (hi n i) = if a % 2 = 1 then (if i ∈ sᶜ then lOf x i else 0) else (if i ∈ s then lOf x i else 0)`. Introduce `i u`.

Establish `hu` using `u.isLt`. Simplify using `only [hT, mem_lo, mem_hi, mem_md, sgn2, lo_lt_md, not_md_lt_lo, md_lt_hi, not_hi_lt_md, lOf_eq, ↓reduceIte]`. Distinguish the cases in `ha : a % 2 = 1`. Establish `hb : ¬ (n - a) % 2 = 1` using `by omega`. Apply the tactic sequence `by_cases his : i ∈ sᶜ <;> simp [ha, hb, his] <;> ring`.

Establish `hb : (n - a) % 2 = 1` using `by omega`. Apply the tactic sequence `by_cases his : i ∈ s <;> simp [ha, hb, his] <;> ring`. Establish `s4 : ∑ i, ∑ u, (T (lo n i) (md n u) + T (hi n i) (md n u) + T (md n u) (lo n i) + T (md n u) (hi n i)) = if n % 2 = 1 then (if a % 2 = 1 then ∑ j ∈ sᶜ, lOf x j else ∑ j ∈ s, lOf x j) else 0`. Simplify using `only [q, Finset.sum_const, Finset.card_univ, Fintype.card_fin]`. Break down `Nat.mod_two_eq_zero_or_one n with h | h` into its components or cases.

Simplify using `[h]`. Simplify using `only [h, one_smul, ↓reduceIte]`. Distinguish the cases in `ha : a % 2 = 1`. Simplify using `only [ha, ↓reduceIte]`. Rewrite using `[sum_ind sᶜ]`.

Simplify using `only [ha, ↓reduceIte]`. Rewrite using `[sum_ind s]`. Establish `s5 : ∑ t, ∑ u, T (md n t) (md n u) = 0`. Use `Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun u _ => ?_` and prove the remaining obligations. Establish `htu : md n t = md n u`.

Use `t.isLt` as an intermediate fact. Use `u.isLt` as an intermediate fact. Use `ext`. Simplify using `only [md]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [hT, htu, sub_self, zero_mul, ite_self]`. Rewrite using `[s1, s2, s3, s4, s5]`. Simplify using `only [vRes]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem half {n a : ℕ} (s : Finset (Fin (n / 2))) (hp : a % 2 + (n - a) % 2 = n % 2) (x : Fin n → ℤ)
    (hx : ∀ i j : Fin n, i < j → x j + 2 ≤ x i) :
    ∑ k ∈ symIdx n (a % 2 = 1) s, ∑ k' ∈ symIdx n ((n - a) % 2 = 1) sᶜ, (x k - x k') * sgn2 k k' =
      - vRes n a (lOf x) s := by
  set T : Fin n → Fin n → ℤ := fun k k' => if k ∈ symIdx n (a % 2 = 1) s then
    (if k' ∈ symIdx n ((n - a) % 2 = 1) sᶜ then (x k - x k') * sgn2 k k' else 0) else 0 with hT
  have s1 : ∑ k ∈ symIdx n (a % 2 = 1) s, ∑ k' ∈ symIdx n ((n - a) % 2 = 1) sᶜ, (x k - x k') * sgn2 k k' =
      ∑ k, ∑ k', T k k' := by
    rw [sum_ind (symIdx n (a % 2 = 1) s)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_ind (symIdx n ((n - a) % 2 = 1) sᶜ)]
    by_cases hk : k ∈ symIdx n (a % 2 = 1) s
    · simp only [hT, hk, ↓reduceIte]
    · simp only [hT, hk, ↓reduceIte, Finset.sum_const_zero]
  have s2 : ∑ k, ∑ k', T k k' =
      ∑ i, ∑ j, (T (lo n i) (lo n j) + T (lo n i) (hi n j) + T (hi n i) (lo n j) + T (hi n i) (hi n j)) +
      ∑ i, ∑ u, (T (lo n i) (md n u) + T (hi n i) (md n u) + T (md n u) (lo n i) + T (md n u) (hi n i)) +
      ∑ t, ∑ u, T (md n t) (md n u) := by
    simp only [sum_split (n := n)]
    simp only [Finset.sum_add_distrib]
    have c1 : ∑ t, ∑ j, T (md n t) (lo n j) = ∑ j, ∑ t, T (md n t) (lo n j) := Finset.sum_comm
    have c2 : ∑ t, ∑ j, T (md n t) (hi n j) = ∑ j, ∑ t, T (md n t) (hi n j) := Finset.sum_comm
    rw [c1, c2]; ring
  have s3 : ∑ i, ∑ j, (T (lo n i) (lo n j) + T (lo n i) (hi n j) + T (hi n i) (lo n j) + T (hi n i) (hi n j)) =
      2 * ∑ i ∈ s, ∑ j ∈ sᶜ, max (lOf x i) (lOf x j) := by
    rw [Finset.mul_sum, sum_ind s]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases his : i ∈ s
    · rw [if_pos his, Finset.mul_sum, sum_ind sᶜ]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hjs : j ∈ sᶜ
      · have hij : i ≠ j := by rintro rfl; exact (Finset.mem_compl.mp hjs) his
        simp only [hT, mem_lo, mem_hi, his, hjs, ↓reduceIte]
        exact pt4 x hx i j hij
      · simp only [hT, mem_lo, mem_hi, his, hjs, ↓reduceIte, add_zero]
    · rw [if_neg his]
      simp only [hT, mem_lo, mem_hi, his, ↓reduceIte, add_zero, Finset.sum_const_zero]
  have q : ∀ i u, T (lo n i) (md n u) + T (hi n i) (md n u) + T (md n u) (lo n i) + T (md n u) (hi n i) =
      if a % 2 = 1 then (if i ∈ sᶜ then lOf x i else 0) else (if i ∈ s then lOf x i else 0) := by
    intro i u
    have hu := u.isLt
    simp only [hT, mem_lo, mem_hi, mem_md, sgn2, lo_lt_md, not_md_lt_lo, md_lt_hi, not_hi_lt_md, lOf_eq, ↓reduceIte]
    by_cases ha : a % 2 = 1
    · have hb : ¬ (n - a) % 2 = 1 := by omega
      by_cases his : i ∈ sᶜ <;> simp [ha, hb, his] <;> ring
    · have hb : (n - a) % 2 = 1 := by omega
      by_cases his : i ∈ s <;> simp [ha, hb, his] <;> ring
  have s4 : ∑ i, ∑ u, (T (lo n i) (md n u) + T (hi n i) (md n u) + T (md n u) (lo n i) + T (md n u) (hi n i)) =
      if n % 2 = 1 then (if a % 2 = 1 then ∑ j ∈ sᶜ, lOf x j else ∑ j ∈ s, lOf x j) else 0 := by
    simp only [q, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · simp [h]
    · simp only [h, one_smul, ↓reduceIte]
      by_cases ha : a % 2 = 1
      · simp only [ha, ↓reduceIte]; rw [sum_ind sᶜ]
      · simp only [ha, ↓reduceIte]; rw [sum_ind s]
  have s5 : ∑ t, ∑ u, T (md n t) (md n u) = 0 := by
    refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun u _ => ?_
    have htu : md n t = md n u := by
      have := t.isLt; have := u.isLt
      ext; simp only [md]; omega
    simp only [hT, htu, sub_self, zero_mul, ite_self]
  rw [s1, s2, s3, s4, s5]
  simp only [vRes]
  ring

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[_root_.zpow_add, _root_.zpow_mul, zpow_natCast]`. Establish `h2 : ((-1 : ℂˣ) ^ (2 : ℤ)) = 1` using `by rw [zpow_two, neg_one_mul, neg_neg]`. Rewrite using `[h2, _root_.one_zpow, mul_one]`.
-/
theorem neg_one_pow_eq (N : ℕ) (d t : ℤ) (h : d = N + 2 * t) : ((-1 : ℂˣ) ^ N) = (-1) ^ d := by
  subst h
  rw [_root_.zpow_add, _root_.zpow_mul, zpow_natCast]
  have h2 : ((-1 : ℂˣ) ^ (2 : ℤ)) = 1 := by rw [zpow_two, neg_one_mul, neg_neg]
  rw [h2, _root_.one_zpow, mul_one]

/- English proof (translation)
Introduce `E _ _ _ w n a s h e he x hx`. Establish `hx' : ∀ i j : Fin n, i < j → x j + 2 ≤ x i` using `hx`. Establish `han : a ≤ n`. Establish `h1` using `h.2.1`. Establish `h2` using `Finset.card_le_univ (symIdx n (a % 2 = 1) s)`.

Rewrite `h2` using `[Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Use `⟨?_, funext fun i => congrArg x (he.1 i).symm, funext fun j => congrArg x (he.2 j).symm⟩` and prove the remaining obligations. Establish `heps : ∀ k, (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)).eps k = (-Units.mk0 (qh w) (qh_ne_zero' w)) ^ (rh n k - Sum.elim (fun i : Fin a => rh a i) (fun j : Fin (n - a) => rh (n - a) j) (e.symm k))`. Introduce `k`.

Use `show Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm k) * qU w (rh n k - Sum.elim (fun i : Fin a => rh a i) (fun j : Fin (n - a) => rh (n - a) j) (e.symm k)) = _`. Rewrite using `[unit_power_eq_residue_power, ← neg_one_mul (Units.mk0 (qh w) (qh_ne_zero' w)), mul_zpow]`. Use `congr 1`. Generalize the expression as in `e.symm k = p`. Break down `p with i | j` into its components or cases.

Simplify using `only [Sum.elim_inl]`. Conclude with `neg_one_pow_eq (n - a) _ (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) (by simp only [rh]; omega)`. Simplify using `only [Sum.elim_inr]`. Conclude with `neg_one_pow_eq a _ (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)) (by simp only [rh]; omega)`. Simplify using `only [heps, ← _root_.zpow_mul]`.

Rewrite using `[← zpow_finsum', Units.val_zpow_eq_zpow_val, Units.val_neg, Units.val_mk0]`. Use `congr 1`. Rewrite using `[blocks e (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)).monoL (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)).monoR x]`. Establish `hAB : ∑ i, ∑ j, (x (e (Sum.inl i)) - x (e (Sum.inr j))) * sgn2 (e (Sum.inl i)) (e (Sum.inr j)) = ∑ k ∈ symIdx n (a % 2 = 1) s, ∑ k' ∈ symIdx n ((n - a) % 2 = 1) sᶜ, (x k - x k') * sgn2 k k'`. Simplify using `only [he.1, he.2]`.

Rewrite using `[← sum_oe _ h.2.1 (fun k => ∑ k' ∈ symIdx n ((n - a) % 2 = 1) sᶜ, (x k - x k') * sgn2 k k')]`. Conclude with `Finset.sum_congr rfl fun i _ => sum_oe _ h.2.2 (fun k' => (x _ - x k') * sgn2 _ k')`. Rewrite using `[hAB, half s h.1.2.2 x hx']`.
-/
theorem vResStd' : VResStd := by
  intro E _ _ _ w n a s h e he x hx
  have hx' : ∀ i j : Fin n, i < j → x j + 2 ≤ x i := hx
  have han : a ≤ n := by
    have h1 := h.2.1
    have h2 := Finset.card_le_univ (symIdx n (a % 2 = 1) s)
    rw [Fintype.card_fin] at h2
    omega
  refine ⟨?_, funext fun i => congrArg x (he.1 i).symm, funext fun j => congrArg x (he.2 j).symm⟩
  have heps : ∀ k, (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)).eps k =
      (-Units.mk0 (qh w) (qh_ne_zero' w)) ^ (rh n k - Sum.elim (fun i : Fin a => rh a i)
        (fun j : Fin (n - a) => rh (n - a) j) (e.symm k)) := by
    intro k
    show Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm k) *
      qU w (rh n k - Sum.elim (fun i : Fin a => rh a i) (fun j : Fin (n - a) => rh (n - a) j) (e.symm k)) = _
    rw [unit_power_eq_residue_power, ← neg_one_mul (Units.mk0 (qh w) (qh_ne_zero' w)), mul_zpow]
    congr 1
    generalize e.symm k = p
    rcases p with i | j
    · simp only [Sum.elim_inl]
      exact neg_one_pow_eq (n - a) _ (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) (by simp only [rh]; omega)
    · simp only [Sum.elim_inr]
      exact neg_one_pow_eq a _ (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)) (by simp only [rh]; omega)
  simp only [heps, ← _root_.zpow_mul]
  rw [← zpow_finsum', Units.val_zpow_eq_zpow_val, Units.val_neg, Units.val_mk0]
  congr 1
  rw [blocks e (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)).monoL
    (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)).monoR x]
  have hAB : ∑ i, ∑ j, (x (e (Sum.inl i)) - x (e (Sum.inr j))) * sgn2 (e (Sum.inl i)) (e (Sum.inr j)) =
      ∑ k ∈ symIdx n (a % 2 = 1) s, ∑ k' ∈ symIdx n ((n - a) % 2 = 1) sᶜ, (x k - x k') * sgn2 k k' := by
    simp only [he.1, he.2]
    rw [← sum_oe _ h.2.1 (fun k => ∑ k' ∈ symIdx n ((n - a) % 2 = 1) sᶜ, (x k - x k') * sgn2 k k')]
    exact Finset.sum_congr rfl fun i _ => sum_oe _ h.2.2 (fun k' => (x _ - x k') * sgn2 _ k')
  rw [hAB, half s h.1.2.2 x hx']

end PositivityTheory.Rg.BcB.F.Choice.IndefiniteRowSideFullHecke

end
