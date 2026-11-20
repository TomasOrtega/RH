import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FTDefs
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.OtherStart

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

/- English proof (translation)
Establish `h` using `prod_tops TT h2 (fun s => (f s : ℝ))`. Rewrite `h` using `[Finset.prod_mul_distrib, ← prod_next TT (fun s => (f s : ℝ)), ← Finset.prod_mul_distrib]`. Conclude with `h` after adjusting the coercions.
-/
theorem natPart {n' : ℕ} (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (f : Fin n' → ℕ) :
    ∏ s ∈ TT, f s = ∏ j, (f (segNext TT j) * ∏ i, f (segPos TT j i)) := by
  have h := prod_tops TT h2 (fun s => (f s : ℝ))
  rw [Finset.prod_mul_distrib, ← prod_next TT (fun s => (f s : ℝ)), ← Finset.prod_mul_distrib] at h
  exact_mod_cast h

/- English proof (translation)
Establish `h` using `natPart TT h2 (fun s => 2 ^ g s)`. Simplify using `only [Finset.prod_pow_eq_pow_sum, ← pow_add] at h`. Conclude with `Nat.pow_right_injective (le_refl 2) h`.
-/
theorem natPartSum {n' : ℕ} (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (g : Fin n' → ℕ) :
    ∑ s ∈ TT, g s = ∑ j, (g (segNext TT j) + ∑ i, g (segPos TT j i)) := by
  have h := natPart TT h2 (fun s => 2 ^ g s)
  simp only [Finset.prod_pow_eq_pow_sum, ← pow_add] at h
  exact Nat.pow_right_injective (le_refl 2) h

/- English proof (translation)
Rewrite using `[Fintype.prod_prod_type, ← Finset.prod_coe_sort TT]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_bool]`. Unfold `hhDegs hhDeg`. Distinguish the cases in `he : Even s.val.val`.

Simplify using `[he]`. Simplify using `[he, mul_comm]`.
-/
theorem ft_prod_letters {n' : ℕ} {M : Type} [CommMonoid M] (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (F : ℕ → M) :
    ∏ x : TT × Bool, F (hhDegs TT aT bT x) = ∏ s ∈ TT, (F (aT s) * F (bT s)) := by
  rw [Fintype.prod_prod_type, ← Finset.prod_coe_sort TT]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Fintype.prod_bool]
  unfold hhDegs hhDeg
  by_cases he : Even s.val.val
  · simp [he]
  · simp [he, mul_comm]

/- English proof (translation)
Rewrite using `[ft_prod_letters X.TT X.aT X.bT Nat.factorial, natPart X.TT h2]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Unfold `facSeg`. Rewrite using `[Finset.prod_congr rfl fun i _ => mul_comm ((X.bT (segPos X.TT j i)).factorial) _]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem facSeg_prod (X : Loc) (h2 : 2 ≤ numSeg X.TT) :
    ∏ x : X.TT × Bool, (hhDegs X.TT X.aT X.bT x).factorial = ∏ j, facSeg X j := by
  rw [ft_prod_letters X.TT X.aT X.bT Nat.factorial, natPart X.TT h2]
  refine Finset.prod_congr rfl fun j _ => ?_
  unfold facSeg
  rw [Finset.prod_congr rfl fun i _ => mul_comm ((X.bT (segPos X.TT j i)).factorial) _]
  ring

/- English proof (translation)
Rewrite using `[natPartSum X.TT h2]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Unfold `lgSeg`. Rewrite using `[Finset.sum_congr rfl fun i _ => add_comm (Nat.log X.p (X.bT (segPos X.TT j i))) _]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lgSeg_sum (X : Loc) (h2 : 2 ≤ numSeg X.TT) :
    ∑ j, lgSeg X j = ∑ s ∈ X.TT, (Nat.log X.p (X.aT s) + Nat.log X.p (X.bT s)) := by
  rw [natPartSum X.TT h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold lgSeg
  rw [Finset.sum_congr rfl fun i _ => add_comm (Nat.log X.p (X.bT (segPos X.TT j i))) _]
  ring

/- English proof (translation)
Rewrite using `[← Finset.mul_sum, lgSeg_sum X h2]`. Unfold `kapZ`. Rewrite using `[← Finset.mul_sum]`. Use `congr 1`. Use `ft_prod_letters (M := Multiplicative ℕ) X.TT X.aT X.bT (fun d => Multiplicative.ofAdd (Nat.log X.p d))` as an intermediate fact.

Conclude with `this`.
-/
theorem kapZ_sum (X : Loc) (h2 : 2 ≤ numSeg X.TT) :
    kapZ X.p X.m X.TT X.aT X.bT = ∑ j, (X.m + 1) * lgSeg X j := by
  rw [← Finset.mul_sum, lgSeg_sum X h2]
  unfold kapZ
  rw [← Finset.mul_sum]
  congr 1
  have := ft_prod_letters (M := Multiplicative ℕ) X.TT X.aT X.bT (fun d => Multiplicative.ofAdd (Nat.log X.p d))
  exact this

/- English proof (translation)
Introduce `X K _ h2`. Unfold `zTen zSeg`. Rewrite using `[Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, ← kapZ_sum X h2]`. Use `congr 1`. Use `congrArg (Nat.cast (R := K)) (facSeg_prod X h2)` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`.
-/
theorem zProdAt : ZProdAt := by
  intro X K _ h2
  unfold zTen zSeg
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, ← kapZ_sum X h2]
  congr 1
  have := congrArg (Nat.cast (R := K)) (facSeg_prod X h2)
  push_cast at this
  exact this

/- English proof (translation)
Establish `hp' : (1 : ℝ) < (p : ℝ)` using `by exact_mod_cast hp`. Establish `ha' : (1 : ℝ) ≤ (a : ℝ)` using `by exact_mod_cast ha`. Establish `hnn : 0 ≤ Real.logb p a` using `Real.logb_nonneg hp' ha'`. Break down `Nat.eq_zero_or_pos d with h0 | h0` into its components or cases. Substitute `h0` using the available equality.

Simplify using `only [Nat.log_zero_right, Nat.cast_zero]`. Check the signs of the components of the expression. Establish `h1 : (Nat.log p d : ℝ) ≤ Real.logb p d` using `Real.natLog_le_logb d p`. Establish `h2 : Real.logb p d ≤ Real.logb p ((a : ℝ) ^ 2)` using `Real.logb_le_logb_of_le hp' (by exact_mod_cast h0) (by exact_mod_cast hd)`. Rewrite `h2` using `[Real.logb_pow]`.

Move the coercions through the operations in `at h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_le_of_le_sq {p a d : ℕ} (hp : 1 < p) (ha : 1 ≤ a) (hd : d ≤ a ^ 2) :
    (Nat.log p d : ℝ) ≤ 2 * Real.logb p a := by
  have hp' : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have ha' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hnn : 0 ≤ Real.logb p a := Real.logb_nonneg hp' ha'
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · subst h0
    simp only [Nat.log_zero_right, Nat.cast_zero]
    positivity
  · have h1 : (Nat.log p d : ℝ) ≤ Real.logb p d := Real.natLog_le_logb d p
    have h2 : Real.logb p d ≤ Real.logb p ((a : ℝ) ^ 2) :=
      Real.logb_le_logb_of_le hp' (by exact_mod_cast h0) (by exact_mod_cast hd)
    rw [Real.logb_pow] at h2
    push_cast at h2
    linarith

/- English proof (translation)
Introduce `X St`. Establish `hp1 : 1 < X.p` using `by have := St.p5; omega`. Establish `hk : (1 : ℝ) ≤ X.k` using `by unfold Loc.k; have : (0 : ℝ) ≤ (X.m : ℝ) := Nat.cast_nonneg _; linarith`. Establish `ha0 : 0 < (X.a : ℝ)`. Break down `Nat.eq_zero_or_pos X.a with h | h` into its components or cases.

Use `St.loga` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h` after adjusting the coercions.

Establish `hae : Real.exp 1 ≤ (X.a : ℝ)` using `(Real.le_log_iff_exp_le ha0).1 St.loga`. Establish `ha3 : 3 ≤ X.a`. Assume the negation of the conclusion as `hlt`. Establish `: X.a ≤ 2` using `by omega`. Establish `h2 : (X.a : ℝ) ≤ 2` using `by exact_mod_cast this`.

Use `Real.exp_one_gt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha3' : (3 : ℝ) ≤ (X.a : ℝ)` using `by exact_mod_cast ha3`. Establish `hA : ∀ s ∈ X.TT, X.aT s ≤ X.a ^ 2`. Introduce `s hs`.

Establish `h1` using `(St.winA s hs).2`. Establish `hkY : 1 ≤ X.k * X.Y` using `by nlinarith [St.Y1]`. Establish `h2 : 2 / (X.k * X.Y) ≤ 2`. Rewrite using `[div_le_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h3 : (X.aT s : ℝ) ≤ (X.a : ℝ) ^ 2` using `by nlinarith`. Conclude with `h3` after adjusting the coercions. Establish `hB : ∀ s ∈ X.TT, X.bT s ≤ X.a ^ 2`. Introduce `s hs`. Establish `h1` using `(St.winB s hs).2`.

Establish `hN1 : (0 : ℝ) ≤ 18 * X.N1 * X.La C0 / X.k`. Establish `: (0 : ℝ) ≤ (X.N1 : ℝ)` using `Nat.cast_nonneg _`. Establish `h'` using `St.La1`. Check the signs of the components of the expression. Establish `hbe : be X C0 ≤ 1`.

Use `St.beLe` as an intermediate fact. Use `St.de6` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb : X.b' * (X.p : ℝ) < X.a`. Use `St.pab` as an intermediate fact.

Rewrite `this` using `[lt_div_iff₀ St.bpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp5 : (5 : ℝ) ≤ (X.p : ℝ)` using `by exact_mod_cast St.p5`. Establish `hb2 : 2 * X.b' ≤ X.a` using `by nlinarith [St.bpos]`. Establish `h3 : (X.bT s : ℝ) ≤ (X.a : ℝ) ^ 2` using `by nlinarith [St.bpos]`.

Conclude with `h3` after adjusting the coercions. Establish `hnn : 0 ≤ Real.logb X.p X.a` using `Real.logb_nonneg (by exact_mod_cast hp1) (by linarith)`. Establish `hsum : ((∑ j, lgSeg X j : ℕ) : ℝ) ≤ X.N * (4 * Real.logb X.p X.a)`. Rewrite using `[lgSeg_sum X St.seg2]`. Use `push_cast`.

Unfold `Loc.N`. Rewrite using `[← nsmul_eq_mul]`. Use `Finset.sum_le_card_nsmul _ _ _ fun s hs => ?_` and prove the remaining obligations. Establish `h1` using `log_le_of_le_sq hp1 (by omega : 1 ≤ X.a) (hA s hs)`. Establish `h2` using `log_le_of_le_sq hp1 (by omega : 1 ≤ X.a) (hB s hs)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e1 : ∑ j : Fin (numSeg X.TT), (((X.m + 2) * lgSeg X j : ℕ) : ℝ) = ((X.m : ℝ) + 2) * ((∑ j, lgSeg X j : ℕ) : ℝ)`. Use `push_cast`. Rewrite using `[Finset.mul_sum]`. Rewrite using `[e1]`.

Unfold `Loc.kap0 kap0G4`. Establish `hN : 0 ≤ X.N` using `by unfold Loc.N; positivity`. Establish `hm : (X.m : ℝ) + 2 ≤ 2 * X.k` using `by unfold Loc.k; have : (0 : ℝ) ≤ (X.m : ℝ) := Nat.cast_nonneg _; linarith`. Establish `hm0 : (0 : ℝ) ≤ (X.m : ℝ) + 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem numAt (C0 Cde CE1 CE2 : ℝ) : NumAt C0 Cde CE1 CE2 := by
  intro X St
  have hp1 : 1 < X.p := by have := St.p5; omega
  have hk : (1 : ℝ) ≤ X.k := by unfold Loc.k; have : (0 : ℝ) ≤ (X.m : ℝ) := Nat.cast_nonneg _; linarith

  have ha0 : 0 < (X.a : ℝ) := by
    rcases Nat.eq_zero_or_pos X.a with h | h
    · have := St.loga
      rw [h] at this
      simp at this
      linarith
    · exact_mod_cast h
  have hae : Real.exp 1 ≤ (X.a : ℝ) := (Real.le_log_iff_exp_le ha0).1 St.loga
  have ha3 : 3 ≤ X.a := by
    by_contra hlt
    have : X.a ≤ 2 := by omega
    have h2 : (X.a : ℝ) ≤ 2 := by exact_mod_cast this
    have := Real.exp_one_gt_d9
    linarith
  have ha3' : (3 : ℝ) ≤ (X.a : ℝ) := by exact_mod_cast ha3
  have hA : ∀ s ∈ X.TT, X.aT s ≤ X.a ^ 2 := by
    intro s hs
    have h1 := (St.winA s hs).2
    have hkY : 1 ≤ X.k * X.Y := by nlinarith [St.Y1]
    have h2 : 2 / (X.k * X.Y) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have h3 : (X.aT s : ℝ) ≤ (X.a : ℝ) ^ 2 := by nlinarith
    exact_mod_cast h3
  have hB : ∀ s ∈ X.TT, X.bT s ≤ X.a ^ 2 := by
    intro s hs
    have h1 := (St.winB s hs).2
    have hN1 : (0 : ℝ) ≤ 18 * X.N1 * X.La C0 / X.k := by
      have : (0 : ℝ) ≤ (X.N1 : ℝ) := Nat.cast_nonneg _
      have h' := St.La1
      positivity
    have hbe : be X C0 ≤ 1 := by
      have := St.beLe
      have := St.de6
      linarith
    have hb : X.b' * (X.p : ℝ) < X.a := by
      have := St.pab
      rw [lt_div_iff₀ St.bpos] at this
      linarith
    have hp5 : (5 : ℝ) ≤ (X.p : ℝ) := by exact_mod_cast St.p5
    have hb2 : 2 * X.b' ≤ X.a := by nlinarith [St.bpos]
    have h3 : (X.bT s : ℝ) ≤ (X.a : ℝ) ^ 2 := by nlinarith [St.bpos]
    exact_mod_cast h3
  have hnn : 0 ≤ Real.logb X.p X.a :=
    Real.logb_nonneg (by exact_mod_cast hp1) (by linarith)
  have hsum : ((∑ j, lgSeg X j : ℕ) : ℝ) ≤ X.N * (4 * Real.logb X.p X.a) := by
    rw [lgSeg_sum X St.seg2]
    push_cast
    unfold Loc.N
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun s hs => ?_
    have h1 := log_le_of_le_sq hp1 (by omega : 1 ≤ X.a) (hA s hs)
    have h2 := log_le_of_le_sq hp1 (by omega : 1 ≤ X.a) (hB s hs)
    linarith
  have e1 : ∑ j : Fin (numSeg X.TT), (((X.m + 2) * lgSeg X j : ℕ) : ℝ) = ((X.m : ℝ) + 2) * ((∑ j, lgSeg X j : ℕ) : ℝ) := by
    push_cast
    rw [Finset.mul_sum]
  rw [e1]
  unfold Loc.kap0 kap0G4
  have hN : 0 ≤ X.N := by unfold Loc.N; positivity
  have hm : (X.m : ℝ) + 2 ≤ 2 * X.k := by unfold Loc.k; have : (0 : ℝ) ≤ (X.m : ℝ) := Nat.cast_nonneg _; linarith
  have hm0 : (0 : ℝ) ≤ (X.m : ℝ) + 2 := by positivity
  calc ((X.m : ℝ) + 2) * ((∑ j, lgSeg X j : ℕ) : ℝ) ≤ ((X.m : ℝ) + 2) * (X.N * (4 * Real.logb X.p X.a)) :=
        mul_le_mul_of_nonneg_left hsum hm0
    _ ≤ (2 * X.k) * (X.N * (4 * Real.logb X.p X.a)) := mul_le_mul_of_nonneg_right hm (by positivity)
    _ = 4 * (2 * X.N * X.k * Real.logb X.p X.a) := by ring

end Formalism.MainNotions.ColumnSystems.Pf
