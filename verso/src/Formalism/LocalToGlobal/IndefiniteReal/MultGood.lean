import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.HeckeThetaElements.DefsWt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta

namespace Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a => (L a : ℝ), s, ⟨fun _ _ h => by dsimp only; exact_mod_cast hL h, L, fun _ => rfl, rfl⟩, ⟨fun _ _ h => by dsimp only; exact_mod_cast hL h, hi⟩, hp, hq⟩`.
-/
theorem goodPar_of_enum {n p q : ℕ} (L : Fin n → ℚ) (s : Fin n → Bool) (hL : StrictAnti L)
    (hi : ∀ a, ∃ z : ℤ, (L a : ℝ) - ((n : ℝ) - 1) / 2 = z)
    (hp : (Finset.univ.filter fun a => s a = true).card = p)
    (hq : (Finset.univ.filter fun a => s a = false).card = q) :
    GoodPar n p q (Finset.univ.image fun a => (L a, s a)) :=
  ⟨fun a => (L a : ℝ), s, ⟨fun _ _ h => by dsimp only; exact_mod_cast hL h, L, fun _ => rfl, rfl⟩,
    ⟨fun _ _ h => by dsimp only; exact_mod_cast hL h, hi⟩, hp, hq⟩

/- English proof (translation)
Take `⟨lam, ε, ⟨hanti, Q, hQ, rfl⟩, ⟨_, hint⟩, hp, hq⟩` from `h`. Use `⟨fun a => -lam (Fin.rev a), fun a => ε (Fin.rev a), ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => -Q (Fin.rev a), fun a => by simp [hQ], ?_⟩, ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Unfold `dualPar`. Rewrite using `[Finset.image_image]`. Use extensionality with `⟨x, s⟩`.

Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Conclude with `⟨Fin.rev a, by simpa using ha⟩`. Introduce and unpack `⟨a, ha⟩`.

Conclude with `⟨_, ha⟩`. Take `⟨z, hz⟩` from `hint (Fin.rev a)`. Use `⟨-z - ((n : ℤ) - 1), ?_⟩` and prove the remaining obligations. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[← hp]`. Conclude with `Finset.card_equiv Fin.revPerm (by intro i; simp)`. Rewrite using `[← hq]`. Conclude with `Finset.card_equiv Fin.revPerm (by intro i; simp)`.
-/
theorem goodPar_dualPar {n p q : ℕ} {S : SPar} (h : GoodPar n p q S) : GoodPar n p q (dualPar S) := by
  obtain ⟨lam, ε, ⟨hanti, Q, hQ, rfl⟩, ⟨_, hint⟩, hp, hq⟩ := h
  refine ⟨fun a => -lam (Fin.rev a), fun a => ε (Fin.rev a),
    ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => -Q (Fin.rev a), fun a => by simp [hQ], ?_⟩,
    ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => ?_⟩, ?_, ?_⟩
  · unfold dualPar
    rw [Finset.image_image]
    ext ⟨x, s⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨Fin.rev a, by simpa using ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨_, ha⟩
  · obtain ⟨z, hz⟩ := hint (Fin.rev a)
    refine ⟨-z - ((n : ℤ) - 1), ?_⟩
    push_cast
    linarith
  · rw [← hp]
    exact Finset.card_equiv Fin.revPerm (by intro i; simp)
  · rw [← hq]
    exact Finset.card_equiv Fin.revPerm (by intro i; simp)

/- English proof (translation)
Use `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun a => s a = true)` as an intermediate fact. Simplify using `only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_false_eq {n : ℕ} (s : Fin n → Bool) :
    (Finset.univ.filter fun a => s a = false).card = n - (Finset.univ.filter fun a => s a = true).card := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun a => s a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at this
  omega

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `zero`. Simplify using `only [mul_zero, add_zero]`. Rewrite using `[Finset.sum_congr rfl (fun i hi => if_pos (Or.inl (Finset.mem_range.mp hi)))]`. Simplify using the standard rewrite rules.

Consider the case `succ c ih`. Apply the tactic sequence `rw [show K + 2 * (c + 1) = K + 2 * c + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih, if_pos (Or.inr ⟨c, by omega⟩), if_neg (by rintro (h | ⟨d, hd⟩) <;> omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_first_or_even (K c : ℕ) :
    ∑ i ∈ Finset.range (K + 2 * c), (if i < K ∨ Even (i - K) then 1 else 0) = K + c := by
  induction c with
  | zero =>
    simp only [mul_zero, add_zero]
    rw [Finset.sum_congr rfl (fun i hi => if_pos (Or.inl (Finset.mem_range.mp hi)))]
    simp
  | succ c ih =>
    rw [show K + 2 * (c + 1) = K + 2 * c + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      if_pos (Or.inr ⟨c, by omega⟩), if_neg (by rintro (h | ⟨d, hd⟩) <;> omega)]
    omega

/- English proof (translation)
Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]`. Establish `: (Finset.range (p + q)).filter (fun i => i < p) = Finset.range p`. Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[this, Finset.card_range]`.
-/
theorem sum_first (p q : ℕ) : ∑ i ∈ Finset.range (p + q), (if i < p then 1 else 0) = p := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
  have : (Finset.range (p + q)).filter (fun i => i < p) = Finset.range p := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

/- English proof (translation)
Introduce `a b hab`. Establish `hab' : (a : ℕ) < b` using `hab`. Use `lamAt_add_add_le h ((b : ℕ) - a) a (by omega)` as an intermediate fact. Rewrite `this` using `[show (a : ℕ) + ((b : ℕ) - a) = b by omega]`. Establish `h1 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ)`.

Establish `: 1 ≤ (b : ℕ) - a` using `by omega`. Conclude with `this` after adjusting the coercions. Use `show lamAt h b < lamAt h a`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lamAt_strictAnti {R : Ranks} (h : HCParam R) : StrictAnti fun a : Fin R.r => lamAt h a := by
  intro a b hab
  have hab' : (a : ℕ) < b := hab
  have := lamAt_add_add_le h ((b : ℕ) - a) a (by omega)
  rw [show (a : ℕ) + ((b : ℕ) - a) = b by omega] at this
  have h1 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by
    have : 1 ≤ (b : ℕ) - a := by omega
    exact_mod_cast this
  show lamAt h b < lamAt h a
  linarith

/- English proof (translation)
Take `⟨z, hz⟩` from `lamAt_int h a`. Take `⟨s, hs⟩` from `odd_r R`. Use `⟨z - s, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, hs]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamAt_half {R : Ranks} (h : HCParam R) (a : Fin R.r) :
    ∃ z : ℤ, ((lamAt h a : ℚ) : ℝ) - ((R.r : ℝ) - 1) / 2 = z := by
  obtain ⟨z, hz⟩ := lamAt_int h a
  obtain ⟨s, hs⟩ := odd_r R
  refine ⟨z - s, ?_⟩
  rw [hz, hs]
  push_cast
  ring

def sgA (R : Ranks) (a : ℕ) : Bool := decide (a < R.k - 1 ∨ Even (a - (R.k - 1)))

/- English proof (translation)
Establish `hk` using `D.R.m_add_three_le_k`. Establish `hrr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Unfold `parA TPar.Dpar`. Use extensionality with `⟨x, s⟩`. Simplify using `only [tparHC, Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and, Prod.mk.injEq, Finset.mem_biUnion, Finset.mem_filter, Nat.not_lt_zero, false_and, exists_false, or_false, Nat.not_odd_zero, if_false, add_zero]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨y, s'⟩, (⟨i, hi⟩ | ⟨i, hi⟩), rfl, rfl⟩`. Simplify using `only [Prod.mk.injEq] at hi`. Take `⟨rfl, rfl⟩` from `hi`. Use `⟨⟨i, by have := i.2; omega⟩, ?_, ?_⟩` and prove the remaining obligations.

Unfold `lamAt`. Rewrite using `[dif_pos i.2]`. Unfold `sgA`. Simplify using `[i.2]`. Simplify using `only [Prod.mk.injEq] at hi`.

Take `⟨rfl, rfl⟩` from `hi`. Use `⟨⟨D.R.k - 1 + i, by have := i.2; omega⟩, ?_, ?_⟩` and prove the remaining obligations. Unfold `lamAt`. Rewrite using `[dif_neg (show ¬ (D.R.k - 1 + (i : ℕ) < D.R.k - 1) by omega), dif_pos (show D.R.k - 1 + (i : ℕ) - (D.R.k - 1) < D.R.m by have := i.2; omega)]`. Simplify using `only [Nat.add_sub_cancel_left]`.

Unfold `sgA`. Simplify using `only [Nat.even_iff]`. Conclude with `decide_eq_decide.mpr (by omega)`. Introduce and unpack `⟨a, rfl, rfl⟩`. Establish `ha` using `a.2`.

Distinguish the cases in `c : (a : ℕ) < D.R.k - 1`. Use `⟨_, Or.inl ⟨⟨a, c⟩, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(D.hc τ).v ⟨a, c⟩ = lamAt (D.hc τ) a`. Unfold `lamAt`. Rewrite using `[dif_pos c]`.

Express the relevant statement in the definitionally equal form `true = sgA D.R a`. Unfold `sgA`. Simplify using `[c]`. Use `⟨_, Or.inr ⟨⟨(a : ℕ) - (D.R.k - 1), by omega⟩, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `-(D.hc τ).b _ = lamAt (D.hc τ) a`.

Unfold `lamAt; rw [dif_neg c, dif_pos (by omega)]`. Express the relevant statement in the definitionally equal form `decide _ = sgA D.R a`. Unfold `sgA`. Simplify using `only [Nat.even_iff]`. Conclude with `decide_eq_decide.mpr (by omega)`.
-/
theorem parA_eq (D : D7) (eta : D.what₂.Tau → ℚ) (h : ∀ τ, eta τ = 1 / 2 ∨ eta τ = -(1 / 2)) (τ : D.what₂.Tau) :
    parA (tparHC D eta h) 0 τ = Finset.univ.image fun a : Fin D.R.r => (lamAt (D.hc τ) a, sgA D.R a) := by
  have hk := D.R.m_add_three_le_k
  have hrr : D.R.r = D.R.k + D.R.m - 1 := rfl
  unfold parA TPar.Dpar
  ext ⟨x, s⟩
  simp only [tparHC, Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and, Prod.mk.injEq,
    Finset.mem_biUnion, Finset.mem_filter, Nat.not_lt_zero, false_and, exists_false, or_false,
    Nat.not_odd_zero, if_false, add_zero]
  constructor
  · rintro ⟨⟨y, s'⟩, (⟨i, hi⟩ | ⟨i, hi⟩), rfl, rfl⟩
    · simp only [Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      refine ⟨⟨i, by have := i.2; omega⟩, ?_, ?_⟩
      · unfold lamAt; rw [dif_pos i.2]
      · unfold sgA; simp [i.2]
    · simp only [Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      refine ⟨⟨D.R.k - 1 + i, by have := i.2; omega⟩, ?_, ?_⟩
      · unfold lamAt
        rw [dif_neg (show ¬ (D.R.k - 1 + (i : ℕ) < D.R.k - 1) by omega),
          dif_pos (show D.R.k - 1 + (i : ℕ) - (D.R.k - 1) < D.R.m by have := i.2; omega)]
        simp only [Nat.add_sub_cancel_left]
      · unfold sgA
        simp only [Nat.even_iff]
        exact decide_eq_decide.mpr (by omega)
  · rintro ⟨a, rfl, rfl⟩
    have ha := a.2
    by_cases c : (a : ℕ) < D.R.k - 1
    · refine ⟨_, Or.inl ⟨⟨a, c⟩, rfl⟩, ?_, ?_⟩
      · change (D.hc τ).v ⟨a, c⟩ = lamAt (D.hc τ) a
        unfold lamAt; rw [dif_pos c]
      · change true = sgA D.R a
        unfold sgA; simp [c]
    · refine ⟨_, Or.inr ⟨⟨(a : ℕ) - (D.R.k - 1), by omega⟩, rfl⟩, ?_, ?_⟩
      · change -(D.hc τ).b _ = lamAt (D.hc τ) a
        unfold lamAt; rw [dif_neg c, dif_pos (by omega)]
      · change decide _ = sgA D.R a
        unfold sgA
        simp only [Nat.even_iff]
        exact decide_eq_decide.mpr (by omega)

/- English proof (translation)
Rewrite using `[Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if sgA R i = true then 1 else 0) R.r]`. Establish `hr : R.r = (R.k - 1) + 2 * (R.m / 2)`. Use `R.m_add_three_le_k` as an intermediate fact. Take `⟨c, hc⟩` from `R.m_even`. Unfold `Ranks.r`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hr]`. Simplify using `only [sgA, decide_eq_true_eq]`. Conclude with `sum_first_or_even _ _`.
-/
theorem card_sgA (R : Ranks) :
    (Finset.univ.filter fun a : Fin R.r => sgA R a = true).card = R.k - 1 + R.m / 2 := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if sgA R i = true then 1 else 0) R.r]
  have hr : R.r = (R.k - 1) + 2 * (R.m / 2) := by
    have := R.m_add_three_le_k
    obtain ⟨c, hc⟩ := R.m_even
    unfold Ranks.r; omega
  rw [hr]
  simp only [sgA, decide_eq_true_eq]
  exact sum_first_or_even _ _

/- English proof (translation)
Rewrite using `[parA_eq]`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm` using `D.R.two_le_m`. Take `⟨c, hc⟩` from `D.R.m_even`. Use `goodPar_of_enum _ _ (lamAt_strictAnti _) (lamAt_half _) ?_ ?_` and prove the remaining obligations.

Rewrite using `[card_sgA]`. Simplify using `only [Ranks.sigY0, Ranks.rS]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[card_false_eq, card_sgA]`. Simplify using `only [Ranks.sigY0, Ranks.rS, Ranks.r]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem goodPar_parA (D : D7) (eta : D.what₂.Tau → ℚ) (h : ∀ τ, eta τ = 1 / 2 ∨ eta τ = -(1 / 2))
    (τ : D.what₂.Tau) : GoodPar D.R.r D.R.sigY0.1 D.R.sigY0.2 (parA (tparHC D eta h) 0 τ) := by
  rw [parA_eq]
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  obtain ⟨c, hc⟩ := D.R.m_even
  refine goodPar_of_enum _ _ (lamAt_strictAnti _) (lamAt_half _) ?_ ?_
  · rw [card_sgA]; simp only [Ranks.sigY0, Ranks.rS]; omega
  · rw [card_false_eq, card_sgA]; simp only [Ranks.sigY0, Ranks.rS, Ranks.r]; omega

/- English proof (translation)
Rewrite using `[D.sp.baseSpace_signature_eq, D.sp.Y_rank 0 (Nat.zero_le _)]`. Establish `: D.R.rankY 0 = D.R.r` using `by simp [Ranks.rankY]`. Rewrite using `[this]`. Conclude with `goodPar_parA D eta h τ`.
-/
theorem good_parameter_first_base_space (D : D7) (eta : D.what₂.Tau → ℚ) (h : ∀ τ, eta τ = 1 / 2 ∨ eta τ = -(1 / 2))
    (τ : D.what₂.Tau) :
    GoodPar (D.sp.Y 0).rank ((D.sp.Y 0).sig (tauE D τ)).1 ((D.sp.Y 0).sig (tauE D τ)).2
      (parA (tparHC D eta h) 0 τ) := by
  rw [D.sp.baseSpace_signature_eq, D.sp.Y_rank 0 (Nat.zero_le _)]
  have : D.R.rankY 0 = D.R.r := by simp [Ranks.rankY]
  rw [this]
  exact goodPar_parA D eta h τ

/- English proof (translation)
The claim follows from `goodPar_dualPar (good_parameter_first_base_space D eta h τ)`.
-/
theorem good_parameter_second_base_space (D : D7) (eta : D.what₂.Tau → ℚ) (h : ∀ τ, eta τ = 1 / 2 ∨ eta τ = -(1 / 2))
    (τ : D.what₂.Tau) :
    GoodPar (D.sp.Y 0).rank ((D.sp.Y 0).sig (tauE D τ)).1 ((D.sp.Y 0).sig (tauE D τ)).2
      (parB (tparHC D eta h) 0 τ) :=
  goodPar_dualPar (good_parameter_first_base_space D eta h τ)

/- English proof (translation)
The claim follows from `good_parameter_first_base_space D _ _`.
-/
theorem goodPar_parA_rec (D : D7) : ∀ τ, GoodPar (D.sp.Y 0).rank ((D.sp.Y 0).sig (tauE D τ)).1
    ((D.sp.Y 0).sig (tauE D τ)).2 (parA (tparRec D) 0 τ) :=
  good_parameter_first_base_space D _ _

/- English proof (translation)
The claim follows from `good_parameter_second_base_space D _ _`.
-/
theorem goodPar_parB_rec (D : D7) : ∀ τ, GoodPar (D.sp.Y 0).rank ((D.sp.Y 0).sig (tauE D τ)).1
    ((D.sp.Y 0).sig (tauE D τ)).2 (parB (tparRec D) 0 τ) :=
  good_parameter_second_base_space D _ _

/- English proof (translation)
Establish `ho : Odd (p + q)` using `hpq ▸ odd_r R`. Use extensionality with `⟨x, s⟩`. Simplify using `only [holPar, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq, holEnt_kapW h p q ho]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl, rfl⟩`.

Consider the cases of `a with`. Consider the case `inl i => exact ⟨⟨i, by have := i.2; omega⟩, rfl, by simp⟩`. Consider the case `inr c => exact ⟨⟨p + c, by have := c.2; omega⟩, rfl, by simp⟩`. Introduce and unpack `⟨a, rfl, rfl⟩`. Distinguish the cases in `hc : (a : ℕ) < p`.

Conclude with `⟨Sum.inl ⟨a, hc⟩, rfl, by simp [hc]⟩`. Use `⟨Sum.inr ⟨a - p, by have := a.2; omega⟩, ?_, by simp [hc]⟩` and prove the remaining obligations. Simplify using `only [Sum.elim_inr]`. Rewrite using `[show p + ((a : ℕ) - p) = a by omega]`.
-/
theorem holPar_kapW_eq {R : Ranks} (h : HCParam R) (p q : ℕ) (hpq : p + q = R.r) :
    holPar p q (kapW h p q) = Finset.univ.image fun a : Fin R.r => (lamAt h a, decide ((a : ℕ) < p)) := by
  have ho : Odd (p + q) := hpq ▸ odd_r R
  ext ⟨x, s⟩
  simp only [holPar, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq, holEnt_kapW h p q ho]
  constructor
  · rintro ⟨a, rfl, rfl⟩
    cases a with
    | inl i => exact ⟨⟨i, by have := i.2; omega⟩, rfl, by simp⟩
    | inr c => exact ⟨⟨p + c, by have := c.2; omega⟩, rfl, by simp⟩
  · rintro ⟨a, rfl, rfl⟩
    by_cases hc : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, hc⟩, rfl, by simp [hc]⟩
    · refine ⟨Sum.inr ⟨a - p, by have := a.2; omega⟩, ?_, by simp [hc]⟩
      simp only [Sum.elim_inr]
      rw [show p + ((a : ℕ) - p) = a by omega]

/- English proof (translation)
Rewrite using `[Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if decide (i < p) = true then 1 else 0) n, ← hpq]`. Simplify using `only [decide_eq_true_eq]`. Conclude with `sum_first p q`.
-/
theorem card_lt_first {n : ℕ} (p q : ℕ) (hpq : p + q = n) :
    (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = true).card = p := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if decide (i < p) = true then 1 else 0) n, ← hpq]
  simp only [decide_eq_true_eq]
  exact sum_first p q

/- English proof (translation)
Use `show GoodPar D.R.r _ _ (holPar _ _ (kapW (D.hc τ) _ _))`. Rewrite using `[holPar_kapW_eq _ _ _ hr]`. Use `goodPar_of_enum _ _ (lamAt_strictAnti _) (lamAt_half _) (card_lt_first _ _ hr) ?_` and prove the remaining obligations. Rewrite using `[card_false_eq, card_lt_first _ _ hr]`. Use linear arithmetic over natural numbers and integers.
-/
theorem goodPar_parW (D : D7) (W : HSp D) (τ : D.what₂.Tau)
    (hr : (W.sig (tauE D τ)).1 + (W.sig (tauE D τ)).2 = D.R.r) :
    GoodPar D.R.r (W.sig (tauE D τ)).1 (W.sig (tauE D τ)).2 (parW W (wtOf D W) τ) := by
  show GoodPar D.R.r _ _ (holPar _ _ (kapW (D.hc τ) _ _))
  rw [holPar_kapW_eq _ _ _ hr]
  refine goodPar_of_enum _ _ (lamAt_strictAnti _) (lamAt_half _) (card_lt_first _ _ hr) ?_
  rw [card_false_eq, card_lt_first _ _ hr]
  omega

/- English proof (translation)
Introduce `τ`. Rewrite using `[D.sp.W_rank j hj1 hjm]`. Use `goodPar_parW D _ τ ?_` and prove the remaining obligations. Rewrite using `[D.sp.W_sigval j hj1 hjm]`. Simplify using `only [Ranks.sigW, Ranks.r]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem goodPar_parW_rec (D : D7) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m) :
    ∀ τ, GoodPar (D.sp.W j).rank ((D.sp.W j).sig (tauE D τ)).1 ((D.sp.W j).sig (tauE D τ)).2
      (parW (D.sp.W j) (wtOf D (D.sp.W j)) τ) := by
  intro τ
  rw [D.sp.W_rank j hj1 hjm]
  refine goodPar_parW D _ τ ?_
  rw [D.sp.W_sigval j hj1 hjm]
  simp only [Ranks.sigW, Ranks.r]
  omega

end Formalism.IndefR.Mult
