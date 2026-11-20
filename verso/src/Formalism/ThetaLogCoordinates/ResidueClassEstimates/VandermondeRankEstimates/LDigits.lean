import Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementL

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

section Digits

variable {I1 I2 : Type}

def cTgt : CoarseVar I1 I2 → I1 ⊕ I2
  | Sum.inl i => Sum.inl i
  | Sum.inr (Sum.inl i) => Sum.inr i
  | Sum.inr (Sum.inr i) => Sum.inr i

def cWt (P : I1 ⊕ I2 → ℕ) (Q : I2 → ℕ) : CoarseVar I1 I2 → ℕ
  | Sum.inl i => P (Sum.inl i)
  | Sum.inr (Sum.inl i) => P (Sum.inr i)
  | Sum.inr (Sum.inr i) => P (Sum.inr i) * Q i

def cExp (P : I1 ⊕ I2 → ℕ) (Q : I2 → ℕ) : (CoarseVar I1 I2 →₀ ℕ) →+ ((I1 ⊕ I2) →₀ ℕ) :=
  Finsupp.liftAddHom fun x => (Finsupp.singleAddHom (cTgt x)).comp (AddMonoidHom.mulRight (cWt P Q x))

def digM (P : I1 ⊕ I2 → ℕ) (Q : I2 → ℕ) (e : (I1 ⊕ I2) →₀ ℕ) : CoarseVar I1 I2 →₀ ℕ :=
  Finsupp.sumElim
    (Finsupp.onFinset (e.comapDomain Sum.inl Sum.inl_injective.injOn).support
      (fun i => e (Sum.inl i) / P (Sum.inl i)) (by
        intro i hi
        rw [Finsupp.mem_support_iff, Finsupp.comapDomain_apply]
        intro h0; rw [h0] at hi; simp at hi))
    (Finsupp.sumElim
      (Finsupp.onFinset (e.comapDomain Sum.inr Sum.inr_injective.injOn).support
        (fun i => (e (Sum.inr i) / P (Sum.inr i)) % Q i) (by
          intro i hi
          rw [Finsupp.mem_support_iff, Finsupp.comapDomain_apply]
          intro h0; rw [h0] at hi; simp at hi))
      (Finsupp.onFinset (e.comapDomain Sum.inr Sum.inr_injective.injOn).support
        (fun i => (e (Sum.inr i) / P (Sum.inr i)) / Q i) (by
          intro i hi
          rw [Finsupp.mem_support_iff, Finsupp.comapDomain_apply]
          intro h0; rw [h0] at hi; simp at hi)))

def digL (P : I1 ⊕ I2 → ℕ) (e : (I1 ⊕ I2) →₀ ℕ) : (I1 ⊕ I2) →₀ ℕ :=
  Finsupp.onFinset e.support (fun i => e i % P i) (by
    intro i hi
    rw [Finsupp.mem_support_iff]
    intro h0; rw [h0] at hi; simp at hi)

end Digits

section Residue

def cnt (T Q r c : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin r → Fin T)).filter (fun u => (∑ l, (u l : ℕ)) % Q = c % Q)).card

/- English proof (translation)
Take `⟨R, rfl⟩ : ∃ R, Q = R + 1` from `⟨Q - 1, by omega⟩`. Rewrite using `[Nat.add_sub_cancel]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h0 : Nat.ModEq (R + 1) (a + s) c` using `h`.

Establish `h1 : Nat.ModEq (R + 1) (a + s + R * a) (c + R * a)` using `h0.add_right (R * a)`. Establish `h2 : a + s + R * a = s + (R + 1) * a` using `by ring`. Rewrite `h1` using `[h2]`. Establish `h3 : (s + (R + 1) * a) % (R + 1) = (c + R * a) % (R + 1)` using `h1`. Rewrite `h3` using `[Nat.add_mul_mod_self_left]`.

Conclude with `h3`. Introduce `h`. Establish `h0 : Nat.ModEq (R + 1) s (c + R * a)` using `h`. Establish `h1 : Nat.ModEq (R + 1) (a + s) (a + (c + R * a))` using `h0.add_left a`. Establish `h2 : a + (c + R * a) = c + (R + 1) * a` using `by ring`.

Rewrite `h1` using `[h2]`. Establish `h3 : (a + s) % (R + 1) = (c + (R + 1) * a) % (R + 1)` using `h1`. Rewrite `h3` using `[Nat.add_mul_mod_self_left]`. Conclude with `h3`.
-/
lemma shift_iff (Q a s c : ℕ) (hQ : 1 ≤ Q) :
    (a + s) % Q = c % Q ↔ s % Q = (c + (Q - 1) * a) % Q := by
  obtain ⟨R, rfl⟩ : ∃ R, Q = R + 1 := ⟨Q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  constructor
  · intro h
    have h0 : Nat.ModEq (R + 1) (a + s) c := h
    have h1 : Nat.ModEq (R + 1) (a + s + R * a) (c + R * a) := h0.add_right (R * a)
    have h2 : a + s + R * a = s + (R + 1) * a := by ring
    rw [h2] at h1
    have h3 : (s + (R + 1) * a) % (R + 1) = (c + R * a) % (R + 1) := h1
    rw [Nat.add_mul_mod_self_left] at h3
    exact h3
  · intro h
    have h0 : Nat.ModEq (R + 1) s (c + R * a) := h
    have h1 : Nat.ModEq (R + 1) (a + s) (a + (c + R * a)) := h0.add_left a
    have h2 : a + (c + R * a) = c + (R + 1) * a := by ring
    rw [h2] at h1
    have h3 : (a + s) % (R + 1) = (c + (R + 1) * a) % (R + 1) := h1
    rw [Nat.add_mul_mod_self_left] at h3
    exact h3

/- English proof (translation)
Establish `hbij : Function.Bijective (fun p : Fin T × (Fin r → Fin T) => (Fin.cons p.1 p.2 : Fin (r + 1) → Fin T))`. Use `Function.bijective_iff_has_inverse.2 ⟨fun u => (u 0, Fin.tail u), fun p => ?_, fun u => ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using `only [cnt, Finset.card_filter]`.

Rewrite using `[← Fintype.sum_prod_type']`. Use `symm`. Use `Fintype.sum_bijective _ hbij _ _ (fun p => ?_)` and prove the remaining obligations. Simplify using `only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]`. Conclude with `if_congr (shift_iff _ _ _ _ hQ).symm rfl rfl`.
-/
lemma cnt_succ (T Q r c : ℕ) (hQ : 1 ≤ Q) :
    cnt T Q (r + 1) c = ∑ a : Fin T, cnt T Q r (c + (Q - 1) * a) := by
  have hbij : Function.Bijective
      (fun p : Fin T × (Fin r → Fin T) => (Fin.cons p.1 p.2 : Fin (r + 1) → Fin T)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun u => (u 0, Fin.tail u), fun p => ?_, fun u => ?_⟩
    · simp
    · simp
  simp only [cnt, Finset.card_filter]
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective _ hbij _ _ (fun p => ?_)
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  exact if_congr (shift_iff _ _ _ _ hQ).symm rfl rfl

/- English proof (translation)
Establish `hbij : Function.Bijective (fun a : Fin T => (fun _ : Fin 1 => a))`. Use `Function.bijective_iff_has_inverse.2 ⟨fun u => u 0, fun a => rfl, fun u => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`. Establish `step : (∑ u : Fin 1 → Fin T, if (∑ l, (u l : ℕ)) % Q = c % Q then 1 else 0) = ∑ a : Fin T, if (a : ℕ) = c % Q then 1 else 0`.

Use `symm`. Use `Fintype.sum_bijective _ hbij _ _ (fun a => ?_)` and prove the remaining obligations. Simplify using `only [Fin.sum_univ_one]`. Rewrite using `[Nat.mod_eq_of_lt (lt_of_lt_of_le a.isLt hT)]`. Unfold `cnt`.

Rewrite using `[Finset.card_filter, step]`. Distinguish the cases in `h : c % Q < T`. Rewrite using `[if_pos h, Finset.sum_eq_single (⟨c % Q, h⟩ : Fin T)]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Conclude with `if_neg (fun e => hb (Fin.ext e))`. Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn`. Rewrite using `[if_neg h]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `a _`. Conclude with `if_neg (fun e => h (lt_of_eq_of_lt e.symm a.isLt))`.
-/
lemma cnt_one (T Q c : ℕ) (hT : T ≤ Q) : cnt T Q 1 c = if c % Q < T then 1 else 0 := by
  have hbij : Function.Bijective (fun a : Fin T => (fun _ : Fin 1 => a)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun u => u 0, fun a => rfl, fun u => ?_⟩
    funext i
    rw [Subsingleton.elim i 0]
  have step : (∑ u : Fin 1 → Fin T, if (∑ l, (u l : ℕ)) % Q = c % Q then 1 else 0) =
      ∑ a : Fin T, if (a : ℕ) = c % Q then 1 else 0 := by
    symm
    refine Fintype.sum_bijective _ hbij _ _ (fun a => ?_)
    simp only [Fin.sum_univ_one]
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le a.isLt hT)]
  unfold cnt
  rw [Finset.card_filter, step]
  by_cases h : c % Q < T
  · rw [if_pos h, Finset.sum_eq_single (⟨c % Q, h⟩ : Fin T)]
    · simp
    · intro b _ hb
      exact if_neg (fun e => hb (Fin.ext e))
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro a _
    exact if_neg (fun e => h (lt_of_eq_of_lt e.symm a.isLt))

/- English proof (translation)
Establish `h1 : (a + (c + (Q - 1) * a) % Q) % Q = c % Q` using `(shift_iff Q a _ c hQ).2 (Nat.mod_mod _ _)`. Establish `h2 : (b + (c + (Q - 1) * a) % Q) % Q = c % Q` using `(shift_iff Q b _ c hQ).2 (by rw [Nat.mod_mod, h])`. Establish `h3 : Nat.ModEq Q (a + (c + (Q - 1) * a) % Q) (b + (c + (Q - 1) * a) % Q)` using `h1.trans h2.symm`. Establish `h4 : Nat.ModEq Q a b` using `Nat.ModEq.add_right_cancel' _ h3`. Establish `h5 : a % Q = b % Q` using `h4`.

Rewrite `h5` using `[Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]`. Then use the resulting hypothesis.
-/
private theorem eq_of_add_pred_mul_mod_eq_of_lt (Q c a b : ℕ) (hQ : 1 ≤ Q) (ha : a < Q) (hb : b < Q)
    (h : (c + (Q - 1) * a) % Q = (c + (Q - 1) * b) % Q) : a = b := by
  have h1 : (a + (c + (Q - 1) * a) % Q) % Q = c % Q :=
    (shift_iff Q a _ c hQ).2 (Nat.mod_mod _ _)
  have h2 : (b + (c + (Q - 1) * a) % Q) % Q = c % Q :=
    (shift_iff Q b _ c hQ).2 (by rw [Nat.mod_mod, h])
  have h3 : Nat.ModEq Q (a + (c + (Q - 1) * a) % Q) (b + (c + (Q - 1) * a) % Q) :=
    h1.trans h2.symm
  have h4 : Nat.ModEq Q a b := Nat.ModEq.add_right_cancel' _ h3
  have h5 : a % Q = b % Q := h4
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h5

/- English proof (translation)
Establish `h2 : cnt T Q 2 c = ∑ a : Fin T, cnt T Q 1 (c + (Q - 1) * a)` using `cnt_succ T Q 1 c hQ`. Rewrite using `[h2]`. Simplify using `only [cnt_one T Q _ hT]`. Establish `hsplit : (∑ a : Fin T, if (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) + ((Finset.univ : Finset (Fin T)).filter (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card = T`. Rewrite using `[Finset.card_filter, ← Finset.sum_add_distrib]`.

Establish `hone : ∀ a : Fin T, ((if (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) + (if ¬ (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) : ℕ) = 1`. Introduce `a`. Apply the tactic sequence `by_cases h : (c + (Q - 1) * (a : ℕ)) % Q < T <;> simp [h]`. Simplify using `only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]`. Establish `hle : ((Finset.univ : Finset (Fin T)).filter (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card ≤ Q - T`.

Establish `hc : ((Finset.univ : Finset (Fin T)).filter (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card ≤ (Finset.Ico T Q).card`. Apply `Finset.card_le_card_of_injOn (fun a : Fin T => (c + (Q - 1) * (a : ℕ)) % Q)` to reduce the goal to its premises. Introduce `a ha`. Establish `ha' : T ≤ (c + (Q - 1) * (a : ℕ)) % Q` using `by simpa using ha`. Simplify using `only [Finset.mem_coe, Finset.mem_Ico]`.

Conclude with `⟨ha', Nat.mod_lt _ (by omega)⟩`. Introduce `a _ b _ hab`. Conclude with `Fin.ext (eq_of_add_pred_mul_mod_eq_of_lt Q c a b hQ (lt_of_lt_of_le a.isLt hT) (lt_of_lt_of_le b.isLt hT) hab)`. Rewrite `hc` using `[Nat.card_Ico]`. Conclude with `hc`.

Use linear arithmetic over natural numbers and integers.
-/
lemma cnt_two (T Q c : ℕ) (hQ : 1 ≤ Q) (hT : T ≤ Q) : T - (Q - T) ≤ cnt T Q 2 c := by
  have h2 : cnt T Q 2 c = ∑ a : Fin T, cnt T Q 1 (c + (Q - 1) * a) :=
    cnt_succ T Q 1 c hQ
  rw [h2]
  simp only [cnt_one T Q _ hT]
  have hsplit : (∑ a : Fin T, if (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) +
      ((Finset.univ : Finset (Fin T)).filter
        (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card = T := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    have hone : ∀ a : Fin T, ((if (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) +
        (if ¬ (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) : ℕ) = 1 := by
      intro a
      by_cases h : (c + (Q - 1) * (a : ℕ)) % Q < T <;> simp [h]
    simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have hle : ((Finset.univ : Finset (Fin T)).filter
      (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card ≤ Q - T := by
    have hc : ((Finset.univ : Finset (Fin T)).filter
        (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card ≤ (Finset.Ico T Q).card := by
      apply Finset.card_le_card_of_injOn (fun a : Fin T => (c + (Q - 1) * (a : ℕ)) % Q)
      · intro a ha
        have ha' : T ≤ (c + (Q - 1) * (a : ℕ)) % Q := by simpa using ha
        simp only [Finset.mem_coe, Finset.mem_Ico]
        exact ⟨ha', Nat.mod_lt _ (by omega)⟩
      · intro a _ b _ hab
        exact Fin.ext (eq_of_add_pred_mul_mod_eq_of_lt Q c a b hQ (lt_of_lt_of_le a.isLt hT)
          (lt_of_lt_of_le b.isLt hT) hab)
    rw [Nat.card_Ico] at hc
    exact hc
  omega

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero`. Introduce `c`. Rewrite using `[pow_zero, one_mul]`. Conclude with `cnt_two T Q c hQ hT`.

Consider the case `succ s ih`. Introduce `c`. Rewrite using `[show s + 1 + 2 = (s + 2) + 1 by omega, cnt_succ T Q (s + 2) c hQ]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ∑ a : Fin T, cnt T Q (s + 2) (c + (Q - 1) * a) := Finset.sum_le_sum (fun a _ => ih _)`.
-/
lemma cnt_ge (T Q : ℕ) (hQ : 1 ≤ Q) (hT : T ≤ Q) (s : ℕ) :
    ∀ c, T ^ s * (T - (Q - T)) ≤ cnt T Q (s + 2) c := by
  induction s with
  | zero =>
    intro c
    rw [pow_zero, one_mul]
    exact cnt_two T Q c hQ hT
  | succ s ih =>
    intro c
    rw [show s + 1 + 2 = (s + 2) + 1 by omega, cnt_succ T Q (s + 2) c hQ]
    calc T ^ (s + 1) * (T - (Q - T)) = ∑ _a : Fin T, T ^ s * (T - (Q - T)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring
      _ ≤ ∑ a : Fin T, cnt T Q (s + 2) (c + (Q - 1) * a) :=
          Finset.sum_le_sum (fun a _ => ih _)

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Establish `hq : 0 ≤ q` using `le_trans hb hbq`.

Establish `h1 : (q - b) * (q ^ m * (q - ((m : ℝ) + 2) * b)) ≤ (q - b) * ((q - b) ^ m * (q - 2 * b))` using `mul_le_mul_of_nonneg_left ih (by linarith)`. Establish `h2 : 0 ≤ q ^ m * (((m : ℝ) + 2) * b ^ 2)` using `mul_nonneg (pow_nonneg hq m) (by positivity)`. Combine the equalities or inequalities in the displayed calculation. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ (q - b) * ((q - b) ^ m * (q - 2 * b)) := by linarith`. Use `_ = (q - b) ^ (m + 1) * (q - 2 * b) := by ring`.
-/
private theorem pow_mul_sub_natCast_add_two_mul_le_sub_pow_mul (q b : ℝ) (hb : 0 ≤ b) (hbq : b ≤ q) :
    ∀ m : ℕ, q ^ m * (q - ((m : ℝ) + 2) * b) ≤ (q - b) ^ m * (q - 2 * b) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hq : 0 ≤ q := le_trans hb hbq
    have h1 : (q - b) * (q ^ m * (q - ((m : ℝ) + 2) * b)) ≤ (q - b) * ((q - b) ^ m * (q - 2 * b)) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h2 : 0 ≤ q ^ m * (((m : ℝ) + 2) * b ^ 2) :=
      mul_nonneg (pow_nonneg hq m) (by positivity)
    calc q ^ (m + 1) * (q - (((m + 1 : ℕ) : ℝ) + 2) * b)
        = (q - b) * (q ^ m * (q - ((m : ℝ) + 2) * b)) - q ^ m * (((m : ℝ) + 2) * b ^ 2) := by
          push_cast
          ring
      _ ≤ (q - b) * ((q - b) ^ m * (q - 2 * b)) := by linarith
      _ = (q - b) ^ (m + 1) * (q - 2 * b) := by ring

/- English proof (translation)
Introduce `r Q be c hr hQ`. Take `⟨m, rfl⟩ : ∃ m, r = m + 2` from `⟨r - 2, by omega⟩`. Establish `hQpos : (0 : ℝ) < (Q : ℝ)` using `by exact_mod_cast (show 0 < Q by omega)`. Establish `hQne : (Q : ℝ) ≠ 0` using `ne_of_gt hQpos`. Establish `key` using `cnt_ge (Q - 2 * be) Q (by omega) (by omega) m c`.

Establish `key'` using `(Nat.cast_le (α := ℝ)).mpr key`. Use `le_trans ?_ key'` and prove the remaining obligations. Establish `eq1 : (Q : ℝ) ^ (m + 1) * (1 - 2 * ((m + 2 : ℕ) : ℝ) * (be : ℝ) / (Q : ℝ)) = (Q : ℝ) ^ m * ((Q : ℝ) - ((m : ℝ) + 2) * (2 * (be : ℝ)))`. Establish `h : (Q : ℝ) ^ (m + 1) * (1 - 2 * ((m + 2 : ℕ) : ℝ) * (be : ℝ) / (Q : ℝ)) = (Q : ℝ) ^ m * (Q : ℝ) - (Q : ℝ) ^ m * (((m : ℝ) + 2) * (2 * (be : ℝ))) * ((Q : ℝ) / (Q : ℝ))`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, div_self hQne, mul_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[show m + 2 - 1 = m + 1 by omega]`. Use `le_trans (le_of_eq eq1) ?_` and prove the remaining obligations.

Distinguish the cases in `h4 : 2 * (2 * be) ≤ Q`. Establish `e1 : (Q - 2 * be) - (Q - (Q - 2 * be)) = Q - 2 * (2 * be)` using `by omega`. Establish `c1 : ((Q - 2 * be : ℕ) : ℝ) = (Q : ℝ) - 2 * (be : ℝ)`. Apply the tactic sequence `rw [Nat.cast_sub (show 2 * be ≤ Q by omega)] <;> push_cast <;> ring`. Establish `c2 : ((Q - 2 * (2 * be) : ℕ) : ℝ) = (Q : ℝ) - 2 * (2 * (be : ℝ))`.

Apply the tactic sequence `rw [Nat.cast_sub h4] <;> push_cast <;> ring`. Rewrite using `[Nat.cast_mul, Nat.cast_pow, e1, c1, c2]`. Conclude with `pow_mul_sub_natCast_add_two_mul_le_sub_pow_mul (Q : ℝ) (2 * (be : ℝ)) (by positivity) (by exact_mod_cast hQ.le) m`. Establish `hneg : (Q : ℝ) - ((m : ℝ) + 2) * (2 * (be : ℝ)) ≤ 0`. Establish `h1 : (Q : ℝ) ≤ 2 * (2 * (be : ℝ))`.

Conclude with `(show Q ≤ 2 * (2 * be) by omega)` after adjusting the coercions. Establish `h2 : (0 : ℝ) ≤ (m : ℝ) * (be : ℝ)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hp : (0 : ℝ) ≤ (Q : ℝ) ^ m` using `by positivity`. Establish `hle : (Q : ℝ) ^ m * ((Q : ℝ) - ((m : ℝ) + 2) * (2 * (be : ℝ))) ≤ 0`.

Use polynomial arithmetic with `[mul_nonneg hp (neg_nonneg.mpr hneg)]`. Conclude with `le_trans hle (Nat.cast_nonneg _)`.
-/
theorem residueClassLowerBound : ResidueClassLowerBound := by
  intro r Q be c hr hQ
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
  have key := cnt_ge (Q - 2 * be) Q (by omega) (by omega) m c
  have key' := (Nat.cast_le (α := ℝ)).mpr key
  refine le_trans ?_ key'
  have eq1 : (Q : ℝ) ^ (m + 1) * (1 - 2 * ((m + 2 : ℕ) : ℝ) * (be : ℝ) / (Q : ℝ)) =
      (Q : ℝ) ^ m * ((Q : ℝ) - ((m : ℝ) + 2) * (2 * (be : ℝ))) := by
    have h : (Q : ℝ) ^ (m + 1) * (1 - 2 * ((m + 2 : ℕ) : ℝ) * (be : ℝ) / (Q : ℝ)) =
        (Q : ℝ) ^ m * (Q : ℝ) - (Q : ℝ) ^ m * (((m : ℝ) + 2) * (2 * (be : ℝ))) * ((Q : ℝ) / (Q : ℝ)) := by
      push_cast
      ring
    rw [h, div_self hQne, mul_one]
    ring
  rw [show m + 2 - 1 = m + 1 by omega]
  refine le_trans (le_of_eq eq1) ?_
  by_cases h4 : 2 * (2 * be) ≤ Q
  · have e1 : (Q - 2 * be) - (Q - (Q - 2 * be)) = Q - 2 * (2 * be) := by omega
    have c1 : ((Q - 2 * be : ℕ) : ℝ) = (Q : ℝ) - 2 * (be : ℝ) := by
      rw [Nat.cast_sub (show 2 * be ≤ Q by omega)] <;> push_cast <;> ring
    have c2 : ((Q - 2 * (2 * be) : ℕ) : ℝ) = (Q : ℝ) - 2 * (2 * (be : ℝ)) := by
      rw [Nat.cast_sub h4] <;> push_cast <;> ring
    rw [Nat.cast_mul, Nat.cast_pow, e1, c1, c2]
    exact pow_mul_sub_natCast_add_two_mul_le_sub_pow_mul (Q : ℝ) (2 * (be : ℝ)) (by positivity) (by exact_mod_cast hQ.le) m
  · have hneg : (Q : ℝ) - ((m : ℝ) + 2) * (2 * (be : ℝ)) ≤ 0 := by
      have h1 : (Q : ℝ) ≤ 2 * (2 * (be : ℝ)) := by
        exact_mod_cast (show Q ≤ 2 * (2 * be) by omega)
      have h2 : (0 : ℝ) ≤ (m : ℝ) * (be : ℝ) := by positivity
      nlinarith
    have hp : (0 : ℝ) ≤ (Q : ℝ) ^ m := by positivity
    have hle : (Q : ℝ) ^ m * ((Q : ℝ) - ((m : ℝ) + 2) * (2 * (be : ℝ))) ≤ 0 := by
      nlinarith [mul_nonneg hp (neg_nonneg.mpr hneg)]
    exact le_trans hle (Nat.cast_nonneg _)

end Residue

section Exact

end Exact

end Formalism.InvariantFactorPaths.BranchingDimensions
