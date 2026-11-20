import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.ZetaHighest

open CompanionTheory.D.DSIC Formalism.REAL

variable {n : ℕ}

/- English proof (translation)
The claim follows from `((univ.filter fun a => ε a = s).orderEmbOfFin rfl).strictMono`.
-/
theorem blk_strictMono (ε : Fin n → Bool) (s : Bool) : StrictMono (blk ε s) :=
  ((univ.filter fun a => ε a = s).orderEmbOfFin rfl).strictMono

/- English proof (translation)
Establish `h` using `Finset.orderEmbOfFin_mem (univ.filter fun a => ε a = s) rfl i`. Conclude with `(Finset.mem_filter.1 h).2`.
-/
theorem blk_mem (ε : Fin n → Bool) (s : Bool) (i : Fin (nb ε s)) : ε (blk ε s i) = s := by
  have h := Finset.orderEmbOfFin_mem (univ.filter fun a => ε a = s) rfl i
  exact (Finset.mem_filter.1 h).2

/- English proof (translation)
Establish `h1 : a ∈ Set.range ((univ.filter fun a => ε a = s).orderEmbOfFin rfl)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Simplify using `using h`. Conclude with `h1`.
-/
theorem blk_surj (ε : Fin n → Bool) (s : Bool) (a : Fin n) (h : ε a = s) : ∃ i, blk ε s i = a := by
  have h1 : a ∈ Set.range ((univ.filter fun a => ε a = s).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    simpa using h
  exact h1

/- English proof (translation)
Use `Finset.prod_bij (fun i _ => blk ε s i) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `i _`. Simplify using `[blk_mem]`. Introduce `i _ j _ h`. Conclude with `(blk_strictMono ε s).injective h`.

Introduce `a ha`. Take `⟨i, hi⟩` from `blk_surj ε s a (Finset.mem_filter.1 ha).2`. Conclude with `⟨i, mem_univ _, hi⟩`. Introduce `i _`. Both sides reduce to the same expression.
-/
theorem prod_blk (ε : Fin n → Bool) (s : Bool) (f : Fin n → ℂ) :
    ∏ i, f (blk ε s i) = ∏ a ∈ univ.filter (fun a => ε a = s), f a := by
  refine Finset.prod_bij (fun i _ => blk ε s i) ?_ ?_ ?_ ?_
  · intro i _; simp [blk_mem]
  · intro i _ j _ h; exact (blk_strictMono ε s).injective h
  · intro a ha
    obtain ⟨i, hi⟩ := blk_surj ε s a (Finset.mem_filter.1 ha).2
    exact ⟨i, mem_univ _, hi⟩
  · intro i _; rfl

/- English proof (translation)
Rewrite using `[← Fin.card_Iio i]`. Use `symm`. Use `Finset.card_bij (fun j _ => blk ε s j) ?_ ?_ ?_` and prove the remaining obligations. Introduce `j hj`. Simplify using `only [mem_filter, mem_univ, true_and, blk_mem, and_true]`.

Conclude with `blk_strictMono ε s (Finset.mem_Iio.1 hj)`. Introduce `i _ j _ h`. Conclude with `(blk_strictMono ε s).injective h`. Introduce `a ha`. Establish `ha'` using `(Finset.mem_filter.1 ha).2`.

Take `⟨j, hj⟩` from `blk_surj ε s a (ha'.2.trans (blk_mem ε s i))`. Use `⟨j, Finset.mem_Iio.2 ?_, hj⟩` and prove the remaining obligations. Rewrite using `[← (blk_strictMono ε s).lt_iff_lt, hj]`. Conclude with `ha'.1`.
-/
theorem card_below (ε : Fin n → Bool) (s : Bool) (i : Fin (nb ε s)) :
    (univ.filter fun b => b < blk ε s i ∧ ε b = ε (blk ε s i)).card = i := by
  rw [← Fin.card_Iio i]
  symm
  refine Finset.card_bij (fun j _ => blk ε s j) ?_ ?_ ?_
  · intro j hj
    simp only [mem_filter, mem_univ, true_and, blk_mem, and_true]
    exact blk_strictMono ε s (Finset.mem_Iio.1 hj)
  · intro i _ j _ h; exact (blk_strictMono ε s).injective h
  · intro a ha
    have ha' := (Finset.mem_filter.1 ha).2
    obtain ⟨j, hj⟩ := blk_surj ε s a (ha'.2.trans (blk_mem ε s i))
    refine ⟨j, Finset.mem_Iio.2 ?_, hj⟩
    rw [← (blk_strictMono ε s).lt_iff_lt, hj]
    exact ha'.1

/- English proof (translation)
Establish `h1 : (1 : ℝ) = ∑ b : Fin n, if b = c then 1 else 0` using `by simp`. Establish `h2 : (n : ℝ) = ∑ _b : Fin n, (1 : ℝ)` using `by simp`. Rewrite using `[h2]`. Use `conv_lhs => rw [h1]`. Simplify using `only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Break down `lt_trichotomy b c with h | h | h` into its components or cases. Apply the tactic sequence `by_cases e : ε b = ε c <;> simp [h, h.ne, not_lt.2 h.le, e]`. Simplify using `[h]`. Apply the tactic sequence `by_cases e : ε b = ε c <;> simp [h, h.ne', not_lt.2 h.le, e]`.
-/
theorem card_total (ε : Fin n → Bool) (c : Fin n) :
    ((univ.filter fun b => c < b ∧ ε b = ε c).card : ℝ) + ((univ.filter fun b => b < c ∧ ε b = ε c).card : ℝ) +
      ((univ.filter fun b => c < b ∧ ε b ≠ ε c).card : ℝ) + ((univ.filter fun b => b < c ∧ ε b ≠ ε c).card : ℝ) + 1
      = n := by
  have h1 : (1 : ℝ) = ∑ b : Fin n, if b = c then 1 else 0 := by simp
  have h2 : (n : ℝ) = ∑ _b : Fin n, (1 : ℝ) := by simp
  rw [h2]
  conv_lhs => rw [h1]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy b c with h | h | h
  · by_cases e : ε b = ε c <;> simp [h, h.ne, not_lt.2 h.le, e]
  · simp [h]
  · by_cases e : ε b = ε c <;> simp [h, h.ne', not_lt.2 h.le, e]

/- English proof (translation)
Unfold `nb`. Simplify using `only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Break down `lt_trichotomy b c with h | h | h` into its components or cases. Apply the tactic sequence `cases e : ε b <;> simp [h, not_lt.2 h.le, hc]`.

Simplify using `[h, hc]`. Apply the tactic sequence `cases e : ε b <;> simp [h, not_lt.2 h.le, hc]`.
-/
theorem card_other (ε : Fin n → Bool) (c : Fin n) (hc : ε c = true) :
    ((univ.filter fun b => c < b ∧ ε b ≠ ε c).card : ℝ) + ((univ.filter fun b => b < c ∧ ε b ≠ ε c).card : ℝ)
      = nb ε false := by
  unfold nb
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy b c with h | h | h
  · cases e : ε b <;> simp [h, not_lt.2 h.le, hc]
  · simp [h, hc]
  · cases e : ε b <;> simp [h, not_lt.2 h.le, hc]

/- English proof (translation)
Establish `h1 : ((A1 ε).filter fun i => i.1.1 = c) = ∅`. Use `Finset.filter_eq_empty_iff.2 fun i _ h => ?_` and prove the remaining obligations. Use `i.2.1` as an intermediate fact. Rewrite `this` using `[h, hc]`. Conclude with `Bool.false_ne_true this`.

Establish `h2 : ((A1 ε).filter fun i => i.1.2 = c).card = (univ.filter fun b => c < b ∧ ε b ≠ ε c).card`. Use `Finset.card_bij (fun i _ => i.1.1) ?_ ?_ ?_` and prove the remaining obligations. Introduce `i hi`. Simplify using `only [A1, mem_filter, mem_univ, true_and] at hi ⊢`. Use `⟨hi.2 ▸ hi.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[i.2.1, hc]`. Simplify using the standard rewrite rules. Introduce `i hi j hj h`. Simplify using `only [A1, mem_filter, mem_univ, true_and] at hi hj`. Conclude with `Subtype.ext (Prod.ext h (hi.2.trans hj.2.symm))`.

Introduce `a ha`. Simplify using `only [mem_filter, mem_univ, true_and] at ha`. Use `⟨⟨(a, c), ?_, hc⟩, ?_, rfl⟩` and prove the remaining obligations. Use `ha.2` as an intermediate fact. Rewrite `this` using `[hc]`.

Simplify using `using this`. Simplify using `only [A1, mem_filter, mem_univ, true_and]`. Conclude with `⟨ha.1, trivial⟩`. Unfold `wtA`. Rewrite using `[h1, h2]`.

Simplify using the standard rewrite rules.
-/
theorem wt_false (ε : Fin n → Bool) (c : Fin n) (hc : ε c = false) :
    wtA (A1 ε) c = -((univ.filter fun b => c < b ∧ ε b ≠ ε c).card : ℝ) := by
  have h1 : ((A1 ε).filter fun i => i.1.1 = c) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun i _ h => ?_
    have := i.2.1
    rw [h, hc] at this
    exact Bool.false_ne_true this
  have h2 : ((A1 ε).filter fun i => i.1.2 = c).card = (univ.filter fun b => c < b ∧ ε b ≠ ε c).card := by
    refine Finset.card_bij (fun i _ => i.1.1) ?_ ?_ ?_
    · intro i hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi ⊢
      refine ⟨hi.2 ▸ hi.1, ?_⟩
      rw [i.2.1, hc]; simp
    · intro i hi j hj h
      simp only [A1, mem_filter, mem_univ, true_and] at hi hj
      exact Subtype.ext (Prod.ext h (hi.2.trans hj.2.symm))
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      refine ⟨⟨(a, c), ?_, hc⟩, ?_, rfl⟩
      · have := ha.2; rw [hc] at this; simpa using this
      · simp only [A1, mem_filter, mem_univ, true_and]
        exact ⟨ha.1, trivial⟩
  unfold wtA
  rw [h1, h2]; simp

/- English proof (translation)
Establish `h1 : ((A1 ε).filter fun i => i.1.2 = c) = ∅`. Use `Finset.filter_eq_empty_iff.2 fun i _ h => ?_` and prove the remaining obligations. Use `i.2.2` as an intermediate fact. Rewrite `this` using `[h, hc]`. Conclude with `Bool.false_ne_true this.symm`.

Establish `h2 : ((A1 ε).filter fun i => i.1.1 = c).card = (univ.filter fun b => b < c ∧ ε b ≠ ε c).card`. Use `Finset.card_bij (fun i _ => i.1.2) ?_ ?_ ?_` and prove the remaining obligations. Introduce `i hi`. Simplify using `only [A1, mem_filter, mem_univ, true_and] at hi ⊢`. Use `⟨hi.2 ▸ hi.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[i.2.2, hc]`. Simplify using the standard rewrite rules. Introduce `i hi j hj h`. Simplify using `only [A1, mem_filter, mem_univ, true_and] at hi hj`. Conclude with `Subtype.ext (Prod.ext (hi.2.trans hj.2.symm) h)`.

Introduce `a ha`. Simplify using `only [mem_filter, mem_univ, true_and] at ha`. Use `⟨⟨(c, a), hc, ?_⟩, ?_, rfl⟩` and prove the remaining obligations. Use `ha.2` as an intermediate fact. Rewrite `this` using `[hc]`.

Simplify using `using this`. Simplify using `only [A1, mem_filter, mem_univ, true_and]`. Conclude with `⟨ha.1, trivial⟩`. Unfold `wtA`. Rewrite using `[h1, h2]`.

Simplify using the standard rewrite rules.
-/
theorem wt_true (ε : Fin n → Bool) (c : Fin n) (hc : ε c = true) :
    wtA (A1 ε) c = ((univ.filter fun b => b < c ∧ ε b ≠ ε c).card : ℝ) := by
  have h1 : ((A1 ε).filter fun i => i.1.2 = c) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun i _ h => ?_
    have := i.2.2
    rw [h, hc] at this
    exact Bool.false_ne_true this.symm
  have h2 : ((A1 ε).filter fun i => i.1.1 = c).card = (univ.filter fun b => b < c ∧ ε b ≠ ε c).card := by
    refine Finset.card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · intro i hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi ⊢
      refine ⟨hi.2 ▸ hi.1, ?_⟩
      rw [i.2.2, hc]; simp
    · intro i hi j hj h
      simp only [A1, mem_filter, mem_univ, true_and] at hi hj
      exact Subtype.ext (Prod.ext (hi.2.trans hj.2.symm) h)
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      refine ⟨⟨(c, a), hc, ?_⟩, ?_, rfl⟩
      · have := ha.2; rw [hc] at this; simpa using this
      · simp only [A1, mem_filter, mem_univ, true_and]
        exact ⟨ha.1, trivial⟩
  unfold wtA
  rw [h1, h2]; simp

/- English proof (translation)
Establish `h1` using `card_total ε (blk ε false i)`. Establish `h2` using `wt_false ε _ (blk_mem ε false i)`. Establish `h3` using `card_below ε false i`. Simplify using `only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, Pi.add_apply, Pi.sub_apply]`. Rewrite using `[h2]`.

Rewrite `h1`, the goal using `[h3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gam_false (ε : Fin n → Bool) (lam : Fin n → ℝ) (i : Fin (nb ε false)) :
    gam ε lam (blk ε false i) = lam (blk ε false i) - ((n : ℝ) - 1) / 2 + (i : ℕ) := by
  have h1 := card_total ε (blk ε false i)
  have h2 := wt_false ε _ (blk_mem ε false i)
  have h3 := card_below ε false i
  simp only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, Pi.add_apply, Pi.sub_apply]
  rw [h2]
  rw [h3] at h1 ⊢
  linarith

/- English proof (translation)
Establish `h1` using `card_total ε (blk ε true i)`. Establish `h2` using `wt_true ε _ (blk_mem ε true i)`. Establish `h3` using `card_below ε true i`. Establish `h4` using `card_other ε _ (blk_mem ε true i)`. Simplify using `only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, Pi.add_apply, Pi.sub_apply]`.

Rewrite using `[h2]`. Rewrite `h1`, the goal using `[h3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gam_true (ε : Fin n → Bool) (lam : Fin n → ℝ) (i : Fin (nb ε true)) :
    gam ε lam (blk ε true i) = lam (blk ε true i) - ((n : ℝ) - 1) / 2 + (nb ε false : ℝ) + (i : ℕ) := by
  have h1 := card_total ε (blk ε true i)
  have h2 := wt_true ε _ (blk_mem ε true i)
  have h3 := card_below ε true i
  have h4 := card_other ε _ (blk_mem ε true i)
  simp only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, Pi.add_apply, Pi.sub_apply]
  rw [h2]
  rw [h3] at h1 ⊢
  linarith

/- English proof (translation)
Establish `inj : ∀ i j, blk ε s i = blk ε s j ↔ i = j` using `fun i j => (blk_strictMono ε s).injective.eq_iff`. Establish `hgl : GlRel (fun i j => F (blk ε s i) (blk ε s j))`. Introduce `a b c d`. Use `hF (blk ε s a) (blk ε s b) (blk ε s c) (blk ε s d) (by simp [blk_mem]) (by simp [blk_mem])` as an intermediate fact. Simplify `this` using `only [inj]`.

Establish `hw : IsHW (fun i j => F (blk ε s i) (blk ε s j)) (fun i => (μ (blk ε s i) : ℂ)) x` using `⟨fun a => hx.1 _, fun a b h => hx.2 _ _ (blk_strictMono ε s h) (by simp [blk_mem])⟩`. Establish `hq : qminor F (blk ε s) (blk ε s) u = qdet (fun i j => F (blk ε s i) (blk ε s j)) u`. Simplify using `only [qdet, qminor, Tm, inj, id]`. Rewrite using `[hq]`. Conclude with `qDetHW V _ _ _ x hgl hw u`.
-/
theorem block_eigen (ε : Fin n → Bool) (s : Bool) (μ : Fin n → ℝ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) (hF : KRel ε F) (hx : KHighest ε F μ x) (u : ℂ) :
    qminor F (blk ε s) (blk ε s) u x = (∏ i : Fin (nb ε s), (u - (i : ℂ) + (μ (blk ε s i) : ℂ))) • x := by
  have inj : ∀ i j, blk ε s i = blk ε s j ↔ i = j := fun i j => (blk_strictMono ε s).injective.eq_iff
  have hgl : GlRel (fun i j => F (blk ε s i) (blk ε s j)) := by
    intro a b c d
    have := hF (blk ε s a) (blk ε s b) (blk ε s c) (blk ε s d) (by simp [blk_mem]) (by simp [blk_mem])
    simpa only [inj] using this
  have hw : IsHW (fun i j => F (blk ε s i) (blk ε s j)) (fun i => (μ (blk ε s i) : ℂ)) x :=
    ⟨fun a => hx.1 _, fun a b h => hx.2 _ _ (blk_strictMono ε s h) (by simp [blk_mem])⟩
  have hq : qminor F (blk ε s) (blk ε s) u = qdet (fun i j => F (blk ε s i) (blk ε s j)) u := by
    simp only [qdet, qminor, Tm, inj, id]
  rw [hq]
  exact qDetHW V _ _ _ x hgl hw u

/- English proof (translation)
Introduce `n ε lam V _ _ F x hF hx Y`. Unfold `zeta`. Rewrite using `[Module.End.mul_apply, block_eigen ε true _ V F x hF hx, map_smul, block_eigen ε false _ V F x hF hx, smul_smul]`. Use `congr 1`. Establish `e1 : ∀ i : Fin (nb ε true), (Y + ((n : ℂ) - 1) / 2 - (nb ε false : ℂ) - (i : ℂ) + (gam ε lam (blk ε true i) : ℂ)) = Y + lam (blk ε true i)`.

Introduce `i`. Rewrite using `[gam_true]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∀ i : Fin (nb ε false), (Y + ((n : ℂ) - 1) / 2 - (i : ℂ) + (gam ε lam (blk ε false i) : ℂ)) = Y + lam (blk ε false i)`.

Introduce `i`. Rewrite using `[gam_false]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e1, e2]`.

Rewrite using `[prod_blk ε true fun a => Y + (lam a : ℂ), prod_blk ε false fun a => Y + (lam a : ℂ), Formalism.QuantumDeterminants.capP, ← Finset.prod_filter_mul_prod_filter_not univ (fun a => ε a = true)]`. Simplify using `only [Bool.not_eq_true]`.
-/
theorem zetaHW : CompanionTheory.D.DSIC.ZetaHW := by
  intro n ε lam V _ _ F x hF hx Y
  unfold zeta
  rw [Module.End.mul_apply, block_eigen ε true _ V F x hF hx, map_smul, block_eigen ε false _ V F x hF hx,
    smul_smul]
  congr 1
  have e1 : ∀ i : Fin (nb ε true), (Y + ((n : ℂ) - 1) / 2 - (nb ε false : ℂ) - (i : ℂ) +
      (gam ε lam (blk ε true i) : ℂ)) = Y + lam (blk ε true i) := by
    intro i; rw [gam_true]; push_cast; ring
  have e2 : ∀ i : Fin (nb ε false), (Y + ((n : ℂ) - 1) / 2 - (i : ℂ) +
      (gam ε lam (blk ε false i) : ℂ)) = Y + lam (blk ε false i) := by
    intro i; rw [gam_false]; push_cast; ring
  simp only [e1, e2]
  rw [prod_blk ε true fun a => Y + (lam a : ℂ), prod_blk ε false fun a => Y + (lam a : ℂ), Formalism.QuantumDeterminants.capP,
    ← Finset.prod_filter_mul_prod_filter_not univ (fun a => ε a = true)]
  simp only [Bool.not_eq_true]

end GlobalTheory.CompanionTheory.ZetaHighest
