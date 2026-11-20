import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.SummableTruncatedGeometric

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.InvariantFactorPaths.G7 (lgN)
open Formalism.MainNotions.OrbitPlaces (Pl orbMap orbLoc Ent Shape OrbOK)
open PI.OrbBoundFW

namespace GlobalTheory.KerStd.WordFree

variable {D : D7} {L : SizeData₂ D}

/- English proof (translation)
Introduce `h`. Establish `h2` using `hc.symm.trans h`. Consider the cases of `h2`.
-/
theorem not_signal {p : ℕ} (hc : IsResidueClassZero D p) : ¬ IsSg D p := by
  intro h
  have h2 := hc.symm.trans h
  cases h2

/- English proof (translation)
Unfold `partner`. Use `congr 1`. Conclude with `decide_eq_false (fun h => not_signal hc h.1)`.
-/
theorem partner_eq {p : ℕ} (hc : IsResidueClassZero D p) (t : HH D) (n : ℕ) :
    partner D p t n = (false, t + n • hP D p) := by
  unfold partner
  congr 1
  exact decide_eq_false (fun h => not_signal hc h.1)

/- English proof (translation)
Rewrite using `[positionPlace_conjugate_partner, partner_eq hc]`.
-/
theorem posPl_eq {p : ℕ} (hc : IsResidueClassZero D p) (t : HH D) (n : ℕ) :
    posPl D p (false, t) n = (false, t + n • hP D p) := by
  rw [positionPlace_conjugate_partner, partner_eq hc]

/- English proof (translation)
Establish `hst : stepP D p = hP D p` using `if_neg (not_signal hc)`. Establish `hb0 : X.bs (hP D p) t0 = t0`. Unfold `reps at ht0`. Rewrite `ht0` using `[hst]`. Take `⟨t', _, rfl⟩` from `Finset.mem_image.1 ht0`.

Conclude with `base_shift_idempotent X _ t'`. Use `symm`. Use `Finset.sum_nbij (fun s => (orbMap D p (false, t0) s).2) ?_ ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `s hs`. Establish `hT` using `(hTT s).1 hs`.

Establish `e1 : orbMap D p (false, t0) s = (false, t0 + s.val • hP D p)` using `posPl_eq hc t0 s.val`. Rewrite `hT`, the goal using `[e1]`. Simplify using `only [topsOn, Finset.mem_filter]`. Use `⟨hT.2, ?_⟩` and prove the remaining obligations. Rewrite using `[hst, base_shift_add_nsmul, hb0]`.

Introduce `s1 hs1 s2 hs2 heq`. Establish `hT1` using `(hTT s1).1 hs1`. Establish `hT2` using `(hTT s2).1 hs2`. Establish `: orbMap D p (false, t0) s1 = orbMap D p (false, t0) s2` using `Prod.ext (hT1.1.trans hT2.1.symm) heq`. Conclude with `ZMod.val_injective _ (posPl_inj D p (false, t0) _ _ (ZMod.val_lt s1) (ZMod.val_lt s2) this)`.

Introduce `t ht`. Establish `ht'` using `Finset.mem_coe.1 ht`. Simplify using `only [topsOn, Finset.mem_filter] at ht'`. Take `⟨hTT', hbt⟩` from `ht'`. Take `⟨m, hm⟩` from `X.bs_orb (stepP D p) t`.

Rewrite `hm` using `[hbt, hst]`. Establish `ho : orbMap D p (false, t0) ((m : ℕ) : ZMod (nP D p)) = (false, t)`. Unfold `orbMap`. Rewrite using `[ZMod.val_natCast, posPl_mod, posPl_eq hc, hm]`. Use `⟨((m : ℕ) : ZMod (nP D p)), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.mem_coe, hTT, ho]`. Conclude with `⟨rfl, hTT'⟩`. Use `show (orbMap D p (false, t0) _).2 = t`. Rewrite using `[ho]`.
-/
theorem sum_topsOn (X : Inst D L) {p : ℕ} (hc : IsResidueClassZero D p) {t0 : HH D} (ht0 : t0 ∈ reps X p)
    (TT : Finset (ZMod (nP D p))) (hTT : ∀ s, s ∈ TT ↔ IsTopPl D (orbMap D p (false, t0) s))
    (F : HH D → ℝ) :
    ∑ t ∈ topsOn X p t0, F t = ∑ s ∈ TT, F (orbMap D p (false, t0) s).2 := by
  have hst : stepP D p = hP D p := if_neg (not_signal hc)
  have hb0 : X.bs (hP D p) t0 = t0 := by
    unfold reps at ht0
    rw [hst] at ht0
    obtain ⟨t', _, rfl⟩ := Finset.mem_image.1 ht0
    exact base_shift_idempotent X _ t'
  symm
  refine Finset.sum_nbij (fun s => (orbMap D p (false, t0) s).2) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro s hs
    have hT := (hTT s).1 hs
    have e1 : orbMap D p (false, t0) s = (false, t0 + s.val • hP D p) := posPl_eq hc t0 s.val
    rw [e1] at hT ⊢
    simp only [topsOn, Finset.mem_filter]
    refine ⟨hT.2, ?_⟩
    rw [hst, base_shift_add_nsmul, hb0]
  · intro s1 hs1 s2 hs2 heq
    have hT1 := (hTT s1).1 hs1
    have hT2 := (hTT s2).1 hs2
    have : orbMap D p (false, t0) s1 = orbMap D p (false, t0) s2 :=
      Prod.ext (hT1.1.trans hT2.1.symm) heq
    exact ZMod.val_injective _ (posPl_inj D p (false, t0) _ _ (ZMod.val_lt s1) (ZMod.val_lt s2) this)
  · intro t ht
    have ht' := Finset.mem_coe.1 ht
    simp only [topsOn, Finset.mem_filter] at ht'
    obtain ⟨hTT', hbt⟩ := ht'
    obtain ⟨m, hm⟩ := X.bs_orb (stepP D p) t
    rw [hbt, hst] at hm
    have ho : orbMap D p (false, t0) ((m : ℕ) : ZMod (nP D p)) = (false, t) := by
      unfold orbMap
      rw [ZMod.val_natCast, posPl_mod, posPl_eq hc, hm]
    refine ⟨((m : ℕ) : ZMod (nP D p)), ?_, ?_⟩
    · rw [Finset.mem_coe, hTT, ho]
      exact ⟨rfl, hTT'⟩
    · show (orbMap D p (false, t0) _).2 = t
      rw [ho]

/- English proof (translation)
Establish `hpos : 0 < e` using `he.pos`. Establish `hp : partner D p t e = (false, (partner D p t e).2)` using `Prod.ext hT.1 rfl`. Use `⟨he, (partner D p t e).2, hT.2, ?_, hpos, hp, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `h1 : posPl D p (false, t) e = posPl D p (false, t) 0`.

Rewrite using `[posPl_zero, positionPlace_conjugate_partner, hp, h]`. Use `posPl_inj D p (false, t) _ _ hlt (by omega) h1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `e' _ h2 h`. Establish `h1 : posPl D p (false, t) e' = posPl D p (false, t) e`.

Rewrite using `[positionPlace_conjugate_partner, positionPlace_conjugate_partner, h, ← hp]`. Use `posPl_inj D p (false, t) _ _ (by omega) hlt h1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem excl_of_top {p : ℕ} (t : HH D) {e : ℕ} (he : Odd e) (hlt : e < nP D p)
    (hT : IsTopPl D (partner D p t e)) : Excl D p t e := by
  have hpos : 0 < e := he.pos
  have hp : partner D p t e = (false, (partner D p t e).2) := Prod.ext hT.1 rfl
  refine ⟨he, (partner D p t e).2, hT.2, ?_, hpos, hp, ?_⟩
  · intro h
    have h1 : posPl D p (false, t) e = posPl D p (false, t) 0 := by
      rw [posPl_zero, positionPlace_conjugate_partner, hp, h]
    have := posPl_inj D p (false, t) _ _ hlt (by omega) h1
    omega
  · intro e' _ h2 h
    have h1 : posPl D p (false, t) e' = posPl D p (false, t) e := by
      rw [positionPlace_conjugate_partner, positionPlace_conjugate_partner, h, ← hp]
    have := posPl_inj D p (false, t) _ _ (by omega) hlt h1
    omega

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp`. Unfold `lgN`. Use `split_ifs with h0`. Use `Real.logb_nonneg hp1 hy` as an intermediate fact. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `push_cast`. Establish `h1 : (p : ℝ) ^ (Nat.log p x) ≤ y`. Use `le_trans ?_ hx` and prove the remaining obligations. Conclude with `Nat.pow_log_le_self p h0` after adjusting the coercions.

Establish `h2 : ((Nat.log p x : ℕ) : ℝ) ≤ Real.logb p y`. Rewrite using `[Real.le_logb_iff_rpow_le hp1 (by linarith), Real.rpow_natCast]`. Conclude with `h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lgN_le {p x : ℕ} (hp : 1 < p) {y : ℝ} (hy : 1 ≤ y) (hx : (x : ℝ) ≤ y) :
    (lgN p x : ℝ) ≤ Real.logb p y + 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  unfold lgN
  split_ifs with h0
  · have := Real.logb_nonneg hp1 hy
    push_cast
    linarith
  · push_cast
    have h1 : (p : ℝ) ^ (Nat.log p x) ≤ y := by
      refine le_trans ?_ hx
      exact_mod_cast Nat.pow_log_le_self p h0
    have h2 : ((Nat.log p x : ℕ) : ℝ) ≤ Real.logb p y := by
      rw [Real.le_logb_iff_rpow_le hp1 (by linarith), Real.rpow_natCast]
      exact h1
    linarith

/- English proof (translation)
The claim follows from `Nat.cast_sub (ν.rowLen_anti 0 1 (by norm_num))`.
-/
theorem natSub_cast (ν : YoungDiagram) :
    ((ν.rowLen 0 - ν.rowLen 1 : ℕ) : ℝ) = (ν.rowLen 0 : ℝ) - (ν.rowLen 1 : ℝ) :=
  Nat.cast_sub (ν.rowLen_anti 0 1 (by norm_num))

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < Lc.l` using `by exact_mod_cast hl`. Use `set Λ := Real.logb Lc.l (2 * a) with hΛ`. Establish `hΛ1 : 1 ≤ Λ`. Rewrite using `[hΛ, Real.le_logb_iff_rpow_le hp1 (by linarith), Real.rpow_one]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hA : ∀ s, (lgN Lc.l (alLoc Lc s) : ℝ) ≤ 2 * Λ` using `fun s => by`. Use `lgN_le hl (y := 2 * a) (by linarith) (hal s)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB : ∀ s, (lgN Lc.l (Lc.size s - alLoc Lc s) : ℝ) ≤ 3 * Λ` using `fun s => by`. Establish `h3 : ((Lc.size s - alLoc Lc s : ℕ) : ℝ) ≤ (2 * a) ^ 2`.

Establish `: ((Lc.size s - alLoc Lc s : ℕ) : ℝ) ≤ (Lc.size s : ℝ)`. Conclude with `Nat.sub_le _ _` after adjusting the coercions. Use polynomial arithmetic with `[hsz s]`. Use `lgN_le hl (y := (2 * a) ^ 2) (by nlinarith) h3` as an intermediate fact. Rewrite `this` using `[Real.logb_pow]`.

Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Use `add_le_add ?_ ?_` and prove the remaining obligations. Establish `: ∀ s ∈ (Finset.univ : Finset (ZMod Lc.d)), ((Lc.N1 : ℝ) * lgN Lc.l (alLoc Lc s) + (Lc.N0 : ℝ) * Lc.N1 * lgN Lc.l (Lc.size s - alLoc Lc s)) ≤ c1 * M ^ 2 * Λ`. Introduce `s _`.

Establish `e1 : (Lc.N1 : ℝ) * lgN Lc.l (alLoc Lc s) ≤ M * (2 * Λ)` using `mul_le_mul hM1 (hA s) (Nat.cast_nonneg _) (by linarith)`. Establish `e2 : (Lc.N0 : ℝ) * Lc.N1 * lgN Lc.l (Lc.size s - alLoc Lc s) ≤ M * M * (3 * Λ)` using `mul_le_mul (mul_le_mul hM0 hM1 (Nat.cast_nonneg _) (by linarith)) (hB s) (Nat.cast_nonneg _) (by positivity)`. Establish `e3 : M * Λ ≤ M ^ 2 * Λ` using `mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)`. Establish `e4 : 5 * (M ^ 2 * Λ) ≤ c1 * (M ^ 2 * Λ)` using `mul_le_mul_of_nonneg_right h1 (by positivity)`. Use the polynomial consequences of the given equalities and inequalities.

Use `(Finset.sum_le_card_nsmul _ _ _ this).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.card_univ, ZMod.card, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `: ∀ s ∈ Lc.TT, ((lgN Lc.l (alLoc Lc s) : ℝ)) ^ 2 ≤ c2 * Λ ^ 2`. Introduce `s _`.

Establish `e1 : ((lgN Lc.l (alLoc Lc s) : ℝ)) ^ 2 ≤ (2 * Λ) ^ 2` using `pow_le_pow_left₀ (Nat.cast_nonneg _) (hA s) 2`. Establish `e4 : 4 * Λ ^ 2 ≤ c2 * Λ ^ 2` using `mul_le_mul_of_nonneg_right h2 (by positivity)`. Use the polynomial consequences of the given equalities and inequalities. Use `(Finset.sum_le_card_nsmul _ _ _ this).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem loss_le (Lc : product_zeroth_first_parts.Loc) {a M c1 c2 : ℝ} (ha : 1 < a) (hla : (Lc.l : ℝ) ≤ a)
    (hM0 : (Lc.N0 : ℝ) ≤ M) (hM1 : (Lc.N1 : ℝ) ≤ M) (hM : 1 ≤ M) (h1 : 5 ≤ c1) (h2 : 4 ≤ c2)
    (hl : 1 < Lc.l)
    (hal : ∀ s, (alLoc Lc s : ℝ) ≤ 2 * a) (hsz : ∀ s, (Lc.size s : ℝ) ≤ a ^ 2) :
    ((∑ s : ZMod Lc.d, ((Lc.N1 : ℝ) * lgN Lc.l (alLoc Lc s) +
        (Lc.N0 : ℝ) * Lc.N1 * lgN Lc.l (Lc.size s - alLoc Lc s))) +
      ∑ s ∈ Lc.TT, ((lgN Lc.l (alLoc Lc s) : ℝ)) ^ 2) ≤
    c1 * (Lc.d : ℝ) * M ^ 2 * Real.logb Lc.l (2 * a) +
      c2 * (Lc.TT.card : ℝ) * Real.logb Lc.l (2 * a) ^ 2 := by
  have hp1 : (1 : ℝ) < Lc.l := by exact_mod_cast hl
  set Λ := Real.logb Lc.l (2 * a) with hΛ
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ, Real.le_logb_iff_rpow_le hp1 (by linarith), Real.rpow_one]
    linarith
  have hA : ∀ s, (lgN Lc.l (alLoc Lc s) : ℝ) ≤ 2 * Λ := fun s => by
    have := lgN_le hl (y := 2 * a) (by linarith) (hal s)
    linarith
  have hB : ∀ s, (lgN Lc.l (Lc.size s - alLoc Lc s) : ℝ) ≤ 3 * Λ := fun s => by
    have h3 : ((Lc.size s - alLoc Lc s : ℕ) : ℝ) ≤ (2 * a) ^ 2 := by
      have : ((Lc.size s - alLoc Lc s : ℕ) : ℝ) ≤ (Lc.size s : ℝ) := by
        exact_mod_cast Nat.sub_le _ _
      nlinarith [hsz s]
    have := lgN_le hl (y := (2 * a) ^ 2) (by nlinarith) h3
    rw [Real.logb_pow] at this
    push_cast at this
    linarith
  refine add_le_add ?_ ?_
  · have : ∀ s ∈ (Finset.univ : Finset (ZMod Lc.d)), ((Lc.N1 : ℝ) * lgN Lc.l (alLoc Lc s) +
        (Lc.N0 : ℝ) * Lc.N1 * lgN Lc.l (Lc.size s - alLoc Lc s)) ≤ c1 * M ^ 2 * Λ := by
      intro s _
      have e1 : (Lc.N1 : ℝ) * lgN Lc.l (alLoc Lc s) ≤ M * (2 * Λ) :=
        mul_le_mul hM1 (hA s) (Nat.cast_nonneg _) (by linarith)
      have e2 : (Lc.N0 : ℝ) * Lc.N1 * lgN Lc.l (Lc.size s - alLoc Lc s) ≤ M * M * (3 * Λ) :=
        mul_le_mul (mul_le_mul hM0 hM1 (Nat.cast_nonneg _) (by linarith)) (hB s) (Nat.cast_nonneg _)
          (by positivity)
      have e3 : M * Λ ≤ M ^ 2 * Λ := mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
      have e4 : 5 * (M ^ 2 * Λ) ≤ c1 * (M ^ 2 * Λ) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      nlinarith
    refine (Finset.sum_le_card_nsmul _ _ _ this).trans (le_of_eq ?_)
    rw [Finset.card_univ, ZMod.card, nsmul_eq_mul]
    ring
  · have : ∀ s ∈ Lc.TT, ((lgN Lc.l (alLoc Lc s) : ℝ)) ^ 2 ≤ c2 * Λ ^ 2 := by
      intro s _
      have e1 : ((lgN Lc.l (alLoc Lc s) : ℝ)) ^ 2 ≤ (2 * Λ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (hA s) 2
      have e4 : 4 * Λ ^ 2 ≤ c2 * Λ ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
      nlinarith
    refine (Finset.sum_le_card_nsmul _ _ _ this).trans (le_of_eq ?_)
    rw [nsmul_eq_mul]
    ring

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `refl => exact le_rfl`. Consider the case `step _ ih => exact ih.trans (product_zeroth_first_parts.N_pred_lt D.R _ (Nat.le_add_left 1 _)).le`.
-/
theorem N_mono (D : D7) {i j : ℕ} (h : i ≤ j) : D.R.N i ≤ D.R.N j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (product_zeroth_first_parts.N_pred_lt D.R _ (Nat.le_add_left 1 _)).le

/- English proof (translation)
Introduce `D L X K E hS hα hK1 hK2 p _ h hc _ hpX u i hi t0 ht0 Th`. Establish `hp1n : 1 < p` using `lt_of_lt_of_le (by norm_num) h.five`. Establish `hp1 : (1 : ℝ) < (p : ℝ)` using `by exact_mod_cast hp1n`. Establish `ha : 1 < L.sc.a` using `hS.xa.2`. Establish `hTT` using `mem_top_orbit_set_iff E p h u i (false, t0) Th`.

Establish `halTop : ∀ s ∈ (orbLoc E p h u i (false, t0) Th).TT, (alLoc (orbLoc E p h u i (false, t0) Th) s : ℝ) = E.row u i (false, (orbMap D p (false, t0) s).2) 0 - E.row u i (false, (orbMap D p (false, t0) s).2) 1`. Introduce `s hs`. Establish `hom : orbMap D p (false, t0) s = (false, (orbMap D p (false, t0) s).2)` using `Prod.ext ((hTT s).1 hs).1 rfl`. Unfold `alLoc`. Rewrite using `[if_pos hs, natSub_cast, ← hom]`.

Both sides reduce to the same expression. Establish `hcard : (Nv X p t0 : ℝ) = ((orbLoc E p h u i (false, t0) Th).TT.card : ℝ)`. Use `sum_topsOn X hc ht0 _ hTT (fun _ => 1)` as an intermediate fact. Unfold `Nv`. Rewrite using `[Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]`.

Use `push_cast`. Conclude with `this`. Establish `hN1 : D.R.N (i + 1) ≤ D.R.N D.R.m` using `N_mono D hi`. Establish `hN01 : D.R.N i < D.R.N (i + 1)` using `product_zeroth_first_parts.N_pred_lt D.R (i + 1) (Nat.le_add_left 1 i)`. Establish `hloss` using `loss_le (orbLoc E p h u i (false, t0) Th) (a := L.sc.a) (M := Nm D) ha (hpX.trans hS.xa.1) (show ((D.R.N i : ℕ) : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) by exact_mod_cast hN01.le.trans hN1) (show ((D.R.N (i + 1) : ℕ) : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) by exact_mod_cast hN1) (show (1 : ℝ) ≤ ((D …`.

Distinguish the cases in `hs : s ∈ (orbLoc E p h u i (false, t0) Th).TT`. Rewrite using `[halTop s hs]`. Conclude with `hα u i hi _ ((hTT s).1 hs).2`. Unfold `alLoc`. Rewrite using `[if_neg hs]`.

Use `push_cast`. Use the proof step `linarith)`. Use the proof step `(fun s => hS.sizeA u i hi (orbMap D p (false, t0) s))`. Unfold `g0 gainA`. Use `sub_le_sub ?_ ?_` and prove the remaining obligations.

Use `swap`. Unfold `dl`. Rewrite using `[hcard]`. Conclude with `hloss`. Rewrite using `[sum_topsOn X hc ht0 _ hTT]`.

Use `Finset.sum_le_sum fun s hs => ?_` and prove the remaining obligations. Establish `hs' : IsTopPl D (orbMap D p (false, t0) s)` using `(hTT s).1 hs`. Establish `hrow` using `halTop s hs`. Use `set t := (orbMap D p (false, t0) s).2 with ht`. Establish `hom : orbMap D p (false, t0) s = (false, t)` using `Prod.ext hs'.1 rfl`.

Establish `htT : t ∈ D.host.TT` using `hs'.2`. Establish `hpart : ∀ e : ℕ, orbMap D p (false, t0) (s + (e : ZMod (nP D p))) = partner D p t e`. Introduce `e`. Rewrite using `[orbit_map_add_natCast, hom, positionPlace_conjugate_partner]`. Establish `hl : ((orbLoc E p h u i (false, t0) Th).l : ℝ) = (p : ℝ)` using `rfl`.

Apply `tsum_le_tsum_of_nonneg_le` to reduce the goal to its premises. Introduce `e split_ifs`. Conclude with `le_max_left _ _`. Conclude with `le_refl 0`. Introduce `e`.

Distinguish the cases in `he : Odd e ∧ ¬ Excl D p t e`. Establish `hne : ¬ (e < (orbLoc E p h u i (false, t0) Th).d ∧ s + (e : ZMod (nP D p)) ∈ (orbLoc E p h u i (false, t0) Th).TT)`. Introduce and unpack `⟨h1, h2⟩`. Establish `hT0` using `(hTT _).1 h2`. Establish `hT : IsTopPl D (partner D p t e)` using `by rw [← hpart e]; exact hT0`.

Conclude with `he.2 (excl_of_top t he.1 h1 hT)`. Rewrite using `[if_pos he, if_pos ⟨he.1, hne⟩, max_comm]`. Use `max_le_max ?_ le_rfl` and prove the remaining obligations. Establish `hal` using `hS.alG u i hi t htT`. Establish `hcap` using `hS.capG u i hi (orbMap D p (false, t0) (s + (e : ZMod (nP D p))))`.

Rewrite `hcap` using `[← orbit_local_capacity_eq E p h u i (false, t0) Th, hpart]`. Establish `hpe : (0 : ℝ) < (p : ℝ) ^ e` using `pow_pos (by linarith) e`. Rewrite using `[hl, hrow]`. Unfold `capU`. Conclude with `sub_le_sub (div_le_div_of_nonneg_right hal hpe.le) hcap`.

Rewrite using `[if_neg he] split_ifs`. Conclude with `le_max_right _ _`. Conclude with `le_refl 0`. Conclude with `summable_truncated_geometric _ _ (by rw [hl]; exact hp1) _ (fun e => Nat.cast_nonneg _) _`.
-/
theorem wordFreeNumber_le_orbitBound : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (E : OrbitPlaces.Ent D), OrbitPlaces.Shape D L X E → (∀ u, ∀ i < D.R.m, ∀ t ∈ D.host.TT, E.row u i (false, t) 0 - E.row u i (false, t) 1 ≤ 2 * L.sc.a) → 5 ≤ K.dl1 → 4 ≤ K.dl2 → ∀ (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p), IsResidueClassZero D p → hP D p ≠ 0 → (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m, ∀ t0 ∈ reps X p, ∀ Th, g0 X K (aL L) (bL L) p (i + 1) t0 ≤ gainA (OrbitPlaces.orbLoc E p h u i (false, t0) Th) := by
  intro D L X K E hS hα hK1 hK2 p _ h hc _ hpX u i hi t0 ht0 Th
  have hp1n : 1 < p := lt_of_lt_of_le (by norm_num) h.five
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp1n
  have ha : 1 < L.sc.a := hS.xa.2
  have hTT := mem_top_orbit_set_iff E p h u i (false, t0) Th
  have halTop : ∀ s ∈ (orbLoc E p h u i (false, t0) Th).TT,
      (alLoc (orbLoc E p h u i (false, t0) Th) s : ℝ) =
        E.row u i (false, (orbMap D p (false, t0) s).2) 0 - E.row u i (false, (orbMap D p (false, t0) s).2) 1 := by
    intro s hs
    have hom : orbMap D p (false, t0) s = (false, (orbMap D p (false, t0) s).2) :=
      Prod.ext ((hTT s).1 hs).1 rfl
    unfold alLoc
    rw [if_pos hs, natSub_cast, ← hom]
    rfl
  have hcard : (Nv X p t0 : ℝ) = ((orbLoc E p h u i (false, t0) Th).TT.card : ℝ) := by
    have := sum_topsOn X hc ht0 _ hTT (fun _ => 1)
    unfold Nv
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
    push_cast
    exact this
  have hN1 : D.R.N (i + 1) ≤ D.R.N D.R.m := N_mono D hi
  have hN01 : D.R.N i < D.R.N (i + 1) := product_zeroth_first_parts.N_pred_lt D.R (i + 1) (Nat.le_add_left 1 i)
  have hloss := loss_le (orbLoc E p h u i (false, t0) Th) (a := L.sc.a) (M := Nm D) ha
    (hpX.trans hS.xa.1)
    (show ((D.R.N i : ℕ) : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) by exact_mod_cast hN01.le.trans hN1)
    (show ((D.R.N (i + 1) : ℕ) : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) by exact_mod_cast hN1)
    (show (1 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) by exact_mod_cast (by omega : 1 ≤ D.R.N D.R.m))
    hK1 hK2 hp1n
    (fun s => by
      by_cases hs : s ∈ (orbLoc E p h u i (false, t0) Th).TT
      · rw [halTop s hs]
        exact hα u i hi _ ((hTT s).1 hs).2
      · unfold alLoc
        rw [if_neg hs]
        push_cast
        linarith)
    (fun s => hS.sizeA u i hi (orbMap D p (false, t0) s))
  unfold g0 gainA
  refine sub_le_sub ?_ ?_
  swap
  · unfold dl
    rw [hcard]
    exact hloss
  rw [sum_topsOn X hc ht0 _ hTT]
  refine Finset.sum_le_sum fun s hs => ?_
  have hs' : IsTopPl D (orbMap D p (false, t0) s) := (hTT s).1 hs
  have hrow := halTop s hs
  set t := (orbMap D p (false, t0) s).2 with ht
  have hom : orbMap D p (false, t0) s = (false, t) := Prod.ext hs'.1 rfl
  have htT : t ∈ D.host.TT := hs'.2
  have hpart : ∀ e : ℕ, orbMap D p (false, t0) (s + (e : ZMod (nP D p))) = partner D p t e := by
    intro e; rw [orbit_map_add_natCast, hom, positionPlace_conjugate_partner]
  have hl : ((orbLoc E p h u i (false, t0) Th).l : ℝ) = (p : ℝ) := rfl
  apply tsum_le_tsum_of_nonneg_le
  · intro e
    split_ifs
    · exact le_max_left _ _
    · exact le_refl 0
  · intro e
    by_cases he : Odd e ∧ ¬ Excl D p t e
    · have hne : ¬ (e < (orbLoc E p h u i (false, t0) Th).d ∧
          s + (e : ZMod (nP D p)) ∈ (orbLoc E p h u i (false, t0) Th).TT) := by
        rintro ⟨h1, h2⟩
        have hT0 := (hTT _).1 h2
        have hT : IsTopPl D (partner D p t e) := by rw [← hpart e]; exact hT0
        exact he.2 (excl_of_top t he.1 h1 hT)
      rw [if_pos he, if_pos ⟨he.1, hne⟩, max_comm]
      refine max_le_max ?_ le_rfl
      have hal := hS.alG u i hi t htT
      have hcap := hS.capG u i hi (orbMap D p (false, t0) (s + (e : ZMod (nP D p))))
      rw [← orbit_local_capacity_eq E p h u i (false, t0) Th, hpart] at hcap
      have hpe : (0 : ℝ) < (p : ℝ) ^ e := pow_pos (by linarith) e
      rw [hl, hrow]
      unfold capU
      exact sub_le_sub (div_le_div_of_nonneg_right hal hpe.le) hcap
    · rw [if_neg he]
      split_ifs
      · exact le_max_right _ _
      · exact le_refl 0
  · exact summable_truncated_geometric _ _ (by rw [hl]; exact hp1) _ (fun e => Nat.cast_nonneg _) _

end GlobalTheory.KerStd.WordFree
