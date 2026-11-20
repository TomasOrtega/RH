import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversalLaw
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementT

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Split

open Formalism.L2.Th1.C Formalism.L2.Th1.C.Pts Formalism.L2.Th1.C.Calc

variable {K : Type} [Field K] [CharZero K] {R : Subring K} {l linv ph : PowerSeries K}

/- English proof (translation)
Use `lGBinom K R σ z hz _ h` as an intermediate fact. Unfold `Cong`. Rewrite using `[← smul_sub]` and apply the resulting hypothesis.
-/
theorem cong_smul {σ : Type} {z : K} (hz : IsBinomScalar R z) {f g : MvPowerSeries σ K}
    (h : Cong R f g) : Cong R (z • f) (z • g) := by
  have := lGBinom K R σ z hz _ h
  unfold Cong
  rwa [← smul_sub]

/- English proof (translation)
Use `lGBinom K R σ _ hz _ h` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hc, one_smul]`. Then use the resulting hypothesis.
-/
theorem lg_of_smul {σ : Type} {c : K} (hc : c ≠ 0) (hz : IsBinomScalar R c⁻¹)
    {f : MvPowerSeries σ K} (h : LG R (c • f)) : LG R f := by
  have := lGBinom K R σ _ hz _ h
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/- English proof (translation)
Establish `e1` using `phNorm_pt hF.1 hN (isPt_fadd hF.1 hF.2.1 hx hy)`. Establish `e2` using `phNorm_pt hF.1 hN hx`. Establish `e3` using `phNorm_pt hF.1 hN hy`. Rewrite `e1` using `[fmul_fadd hF.1 a hx.1 hy.1]`. Use `cong_sub (cong_sub e1 e2) e3` as an intermediate fact.

Rewrite `this` using `[← smul_sub, ← smul_sub]`. Conclude with `this`.
-/
theorem biextension_formal_mul_mul (hF : Frame R l linv ph) {a b : K} (hN : PhNormAt R l linv ph a b)
    {σ : Type} {x y : MvPowerSeries σ K} (hx : IsPt R x) (hy : IsPt R y) :
    Cong R (be0 l linv ph (fmul l linv a x) (fmul l linv a y)) ((a * b) • be0 l linv ph x y) := by
  have e1 := phNorm_pt hF.1 hN (isPt_fadd hF.1 hF.2.1 hx hy)
  have e2 := phNorm_pt hF.1 hN hx
  have e3 := phNorm_pt hF.1 hN hy
  rw [fmul_fadd hF.1 a hx.1 hy.1] at e1
  have := cong_sub (cong_sub e1 e2) e3
  rw [← smul_sub, ← smul_sub] at this
  exact this

/- English proof (translation)
Establish `hax : IsPt R (fmul l linv a x)` using `isPt_fmul hF.1 ha hx`. Establish `e1 : Cong R (be0 l linv ph (fmul l linv a x) (fmul l linv a y)) (a • be0 l linv ph (fmul l linv a x) y)` using `hZ σ _ _ hax hy`. Establish `e2 : Cong R (be0 l linv ph (fmul l linv a x) y) (a • be0 l linv ph x y)`. Use `hZ σ y x hy hx` as an intermediate fact. Rewrite `this` using `[addDefect_comm ph y (fmul l linv a x), addDefect_comm ph y x]`. Then use the resulting hypothesis.

Establish `e3 : Cong R (a • a • be0 l linv ph x y) ((a * b) • be0 l linv ph x y)` using `cong_trans (cong_symm (cong_trans e1 (cong_smul hB e2))) (biextension_formal_mul_mul hF hN hx hy)`. Use `lg_of_smul hc hinv ?_` and prove the remaining obligations. Establish `e : (a * (a - b)) • be0 l linv ph x y = a • a • be0 l linv ph x y - (a * b) • be0 l linv ph x y`. Rewrite using `[smul_smul, ← sub_smul, mul_sub]`. Rewrite using `[e]`.

Conclude with `e3`.
-/
theorem biextension_vanishes_split (hF : Frame R l linv ph) {a b : K} (ha : EndInt R l linv a)
    (hB : IsBinomScalar R a) (hZ : ZLinAt R l linv ph a) (hN : PhNormAt R l linv ph a b)
    (hc : a * (a - b) ≠ 0) (hinv : IsBinomScalar R (a * (a - b))⁻¹)
    {σ : Type} {x y : MvPowerSeries σ K} (hx : IsPt R x) (hy : IsPt R y) :
    LG R (be0 l linv ph x y) := by
  have hax : IsPt R (fmul l linv a x) := isPt_fmul hF.1 ha hx
  have e1 : Cong R (be0 l linv ph (fmul l linv a x) (fmul l linv a y))
      (a • be0 l linv ph (fmul l linv a x) y) := hZ σ _ _ hax hy
  have e2 : Cong R (be0 l linv ph (fmul l linv a x) y) (a • be0 l linv ph x y) := by
    have := hZ σ y x hy hx
    rwa [addDefect_comm ph y (fmul l linv a x), addDefect_comm ph y x] at this
  have e3 : Cong R (a • a • be0 l linv ph x y) ((a * b) • be0 l linv ph x y) :=
    cong_trans (cong_symm (cong_trans e1 (cong_smul hB e2))) (biextension_formal_mul_mul hF hN hx hy)
  refine lg_of_smul hc hinv ?_
  have e : (a * (a - b)) • be0 l linv ph x y =
      a • a • be0 l linv ph x y - (a * b) • be0 l linv ph x y := by
    rw [smul_smul, ← sub_smul, mul_sub]
  rw [e]
  exact e3

/- English proof (translation)
Rewrite using `[PhNormAt, mulBy_eq_fmul, mul_one]`.
-/
theorem phNorm_one_iff (c : K) :
    PhNormAt R l linv ph c 1 ↔
      Cong R (PowerSeries.subst (fmul l linv c (PowerSeries.X : MvPowerSeries Unit K)) ph)
        (c • (ph : MvPowerSeries Unit K)) := by
  rw [PhNormAt, mulBy_eq_fmul, mul_one]

/- English proof (translation)
Establish `hX : IsPt R (PowerSeries.X : MvPowerSeries Unit K)` using `isPt_X`. Establish `hXs : PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K) ph = ph` using `PowerSeries.X_subst ph`. Rewrite using `[phNorm_one_iff]`. Proceed by induction on `n with`. Consider the case `zero`.

Rewrite using `[Nat.cast_zero, fmul_zero_left hF.1, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2, zero_smul]`. Conclude with `cong_refl _`. Consider the case `succ n ih`. Establish `k` using `key _ _ (isPt_fmul hF.1 (Clo.endInt_natCast hF.1 hF.2.1 n) hX) hX`. Rewrite `k` using `[be0, hXs]`.

Rewrite using `[Nat.cast_succ, fmul_add hF.1 _ _ hX.1, fmul_one hF.1 hX.1, add_smul, one_smul]`. Use `lg_add k ih` as an intermediate fact. Unfold `Cong`. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.
-/
theorem phNorm_natCast (hF : Frame R l linv ph)
    (key : ∀ x y : MvPowerSeries Unit K, IsPt R x → IsPt R y → LG R (be0 l linv ph x y)) (n : ℕ) :
    PhNormAt R l linv ph (n : K) 1 := by
  have hX : IsPt R (PowerSeries.X : MvPowerSeries Unit K) := isPt_X
  have hXs : PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K) ph = ph :=
    PowerSeries.X_subst ph
  rw [phNorm_one_iff]
  induction n with
  | zero =>
    rw [Nat.cast_zero, fmul_zero_left hF.1, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2,
      zero_smul]
    exact cong_refl _
  | succ n ih =>
    have k := key _ _ (isPt_fmul hF.1 (Clo.endInt_natCast hF.1 hF.2.1 n) hX) hX
    rw [be0, hXs] at k
    rw [Nat.cast_succ, fmul_add hF.1 _ _ hX.1, fmul_one hF.1 hX.1, add_smul, one_smul]
    have := lg_add k ih
    unfold Cong
    convert this using 1
    abel

/- English proof (translation)
Establish `hX : IsPt R (PowerSeries.X : MvPowerSeries Unit K)` using `isPt_X`. Take `⟨m, rfl | rfl⟩` from `n.eq_nat_or_neg`. Rewrite using `[Int.cast_natCast]`. Conclude with `phNorm_natCast hF key m`. Rewrite using `[Int.cast_neg, Int.cast_natCast]`.

Establish `hm` using `Clo.endInt_natCast (R := R) hF.1 hF.2.1 m`. Establish `k` using `key _ _ (isPt_fmul hF.1 hm hX) (isPt_fmul hF.1 (endInt_neg hF.1 hF.2.1 hm) hX)`. Rewrite `k` using `[be0, fadd_fmul_neg hF.1 _ hX.1, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2]`. Establish `h1` using `(phNorm_one_iff (R := R) (l := l) (linv := linv) (ph := ph) (m : K)).1 (phNorm_natCast hF key m)`. Rewrite using `[phNorm_one_iff, neg_smul]`.

Use `lg_neg (lg_add k h1)` as an intermediate fact. Unfold `Cong`. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.
-/
theorem phNorm_intCast (hF : Frame R l linv ph)
    (key : ∀ x y : MvPowerSeries Unit K, IsPt R x → IsPt R y → LG R (be0 l linv ph x y)) (n : ℤ) :
    PhNormAt R l linv ph (n : K) 1 := by
  have hX : IsPt R (PowerSeries.X : MvPowerSeries Unit K) := isPt_X
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [Int.cast_natCast]
    exact phNorm_natCast hF key m
  · rw [Int.cast_neg, Int.cast_natCast]
    have hm := Clo.endInt_natCast (R := R) hF.1 hF.2.1 m
    have k := key _ _ (isPt_fmul hF.1 hm hX) (isPt_fmul hF.1 (endInt_neg hF.1 hF.2.1 hm) hX)
    rw [be0, fadd_fmul_neg hF.1 _ hX.1, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2] at k
    have h1 := (phNorm_one_iff (R := R) (l := l) (linv := linv) (ph := ph) (m : K)).1
      (phNorm_natCast hF key m)
    rw [phNorm_one_iff, neg_smul]
    have := lg_neg (lg_add k h1)
    unfold Cong
    convert this using 1
    abel

/- English proof (translation)
Introduce `K _ _ _ _ R hR l linv ph a b hF hF1 ha hcl hN ha0 hab hb1 hi1 hi2`. Establish `hl` using `hF.1.1`. Establish `hli` using `hF.1.2.2.1`. Establish `hph` using `hF.2.2`. Establish `hB : IsBinomScalar R a`.

Use `closure_minimal ?_ (binomClosed K R hR) hcl` and prove the remaining obligations. Introduce and unpack `_ ⟨n, rfl⟩`. Conclude with `intBinomScalar K R n`. Establish `hZ : ZLinAt R l linv ph a`. Use `closure_minimal ?_ (zLinClosed K R hR l linv ph hl hli hph) hcl` and prove the remaining obligations.

Introduce and unpack `_ ⟨n, rfl⟩`. Conclude with `zLinInt K R l linv ph hF hF1 n`. Establish `key : ∀ x y : MvPowerSeries Unit K, IsPt R x → IsPt R y → LG R (be0 l linv ph x y)` using `fun x y hx hy => biextension_vanishes_split hF ha hB hZ hN (mul_ne_zero ha0 (sub_ne_zero.2 hab)) hi1 hx hy`. Establish `hA : PhNormAt R l linv ph a 1`. Establish `hc : IsClosed {c : K | PhNormAt R l linv ph c 1}` using `(phNormClosed K R hR l linv ph hl hli hph).preimage (continuous_id.prodMk continuous_const)`.

Use `closure_minimal ?_ hc hcl` and prove the remaining obligations. Introduce and unpack `_ ⟨n, rfl⟩`. Conclude with `phNorm_intCast hF key n`. Use `lg_of_smul (mul_ne_zero ha0 (sub_ne_zero.2 (Ne.symm hb1))) hi2 ?_` and prove the remaining obligations. Establish `e3 : Cong R ((a * 1) • (ph : MvPowerSeries Unit K)) ((a * b) • ph)` using `cong_trans (cong_symm hA) hN`.

Establish `e : (a * (1 - b)) • (ph : MvPowerSeries Unit K) = (a * 1) • ph - (a * b) • ph`. Rewrite using `[← sub_smul, mul_sub]`. Rewrite using `[e]`. Conclude with `e3`.
-/
theorem split_vanishing_at_two : Formalism.L2.Th1.G.SplitVanishTwo := by
  intro K _ _ _ _ R hR l linv ph a b hF hF1 ha hcl hN ha0 hab hb1 hi1 hi2
  have hl := hF.1.1
  have hli := hF.1.2.2.1
  have hph := hF.2.2
  have hB : IsBinomScalar R a := by
    refine closure_minimal ?_ (binomClosed K R hR) hcl
    rintro _ ⟨n, rfl⟩
    exact intBinomScalar K R n
  have hZ : ZLinAt R l linv ph a := by
    refine closure_minimal ?_ (zLinClosed K R hR l linv ph hl hli hph) hcl
    rintro _ ⟨n, rfl⟩
    exact zLinInt K R l linv ph hF hF1 n
  have key : ∀ x y : MvPowerSeries Unit K, IsPt R x → IsPt R y → LG R (be0 l linv ph x y) :=
    fun x y hx hy =>
      biextension_vanishes_split hF ha hB hZ hN (mul_ne_zero ha0 (sub_ne_zero.2 hab)) hi1 hx hy
  have hA : PhNormAt R l linv ph a 1 := by
    have hc : IsClosed {c : K | PhNormAt R l linv ph c 1} :=
      (phNormClosed K R hR l linv ph hl hli hph).preimage
        (continuous_id.prodMk continuous_const)
    refine closure_minimal ?_ hc hcl
    rintro _ ⟨n, rfl⟩
    exact phNorm_intCast hF key n
  refine lg_of_smul (mul_ne_zero ha0 (sub_ne_zero.2 (Ne.symm hb1))) hi2 ?_
  have e3 : Cong R ((a * 1) • (ph : MvPowerSeries Unit K)) ((a * b) • ph) :=
    cong_trans (cong_symm hA) hN
  have e : (a * (1 - b)) • (ph : MvPowerSeries Unit K) = (a * 1) • ph - (a * b) • ph := by
    rw [← sub_smul, mul_sub]
  rw [e]
  exact e3

end Formalism.L2.Th1.B.Split
