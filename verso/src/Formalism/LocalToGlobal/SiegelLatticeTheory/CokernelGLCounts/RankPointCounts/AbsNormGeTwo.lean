import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SummableLogAlpD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvOfVolLocPos

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol
  Formalism.L2.SG.DataInst Formalism.L2.SG.Pf.ProdConvCut Formalism.L2.SG.Pf.AlTie

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)

/- English proof (translation)
Unfold `etaV`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem etaV_pm (v : PlX X) :
    ((etaV (E := X.B.I.E) v : ℤ) : ℝ) = 1 ∨ ((etaV (E := X.B.I.E) v : ℤ) : ℝ) = -1 := by
  unfold etaV
  split_ifs <;> simp

/- English proof (translation)
Establish `h0 : Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Establish `h1 : Ideal.absNorm v.asIdeal ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`.

Conclude with `v.isPrime.ne_top`. Establish `h2 : 2 ≤ Ideal.absNorm v.asIdeal` using `by omega`. Conclude with `h2` after adjusting the coercions.
-/
theorem absNorm_ge_two (v : PlX X) : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast h2

/- English proof (translation)
Establish `hq0 : 0 < q` using `by linarith`. Establish `hx0 : 0 ≤ q⁻¹` using `inv_nonneg.mpr hq0.le`. Establish `hxq : q⁻¹ * q = 1` using `inv_mul_cancel₀ hq0.ne'`. Establish `hx2 : q⁻¹ ≤ 1 / 2` using `by nlinarith [mul_le_mul_of_nonneg_left hq hx0]`. Establish `hterm : ∀ i : ℕ, |η ^ i / q ^ i| = q⁻¹ ^ i`.

Introduce `i`. Rewrite using `[abs_div, abs_pow, abs_pow, abs_of_pos hq0, inv_pow]`. Apply the tactic sequence `rcases hη with rfl | rfl <;> simp`. Establish `hsum : ∑ i ∈ Finset.Icc a N, q⁻¹ ^ i ≤ 2 * q⁻¹ ^ k`. Establish `h1 : ∑ i ∈ Finset.Icc a N, q⁻¹ ^ i ≤ q⁻¹ ^ a / (1 - q⁻¹)`.

Establish `hI : Finset.Icc a N = Finset.Ico a (N + 1)`. Use extensionality with `i`. Simplify using `only [Finset.mem_Icc, Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hI]`.

Conclude with `geom_sum_Ico_le_of_lt_one hx0 (by linarith)`. Establish `h2 : q⁻¹ ^ a / (1 - q⁻¹) ≤ 2 * q⁻¹ ^ a`. Rewrite using `[div_le_iff₀ (by linarith)]`. Use polynomial arithmetic with `[mul_nonneg (pow_nonneg hx0 a) (by linarith : (0 : ℝ) ≤ 1 / 2 - q⁻¹)]`. Establish `h3 : q⁻¹ ^ a ≤ q⁻¹ ^ k` using `pow_le_pow_of_le_one hx0 (by linarith) ha`.

Combine the linear equalities and inequalities to obtain the conclusion. Prove the components needed by the constructor for the conclusion. Establish `hfac : ∀ i ∈ Finset.Icc a N, Real.exp (-(2 * q⁻¹ ^ i)) ≤ 1 - η ^ i / q ^ i`. Introduce `i hi`. Establish `hi1 : i ≠ 0`.

Use `(Finset.mem_Icc.mp hi).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hy0 : 0 ≤ q⁻¹ ^ i` using `pow_nonneg hx0 i`. Establish `hy : q⁻¹ ^ i ≤ 1 / 2` using `le_trans (pow_le_of_le_one hx0 (by linarith) hi1) hx2`. Establish `hle : η ^ i / q ^ i ≤ q⁻¹ ^ i` using `(abs_le.mp (le_of_eq (hterm i))).2`.

Establish `he : 1 + 2 * q⁻¹ ^ i ≤ Real.exp (2 * q⁻¹ ^ i)`. Combine the linear relations using `[Real.add_one_le_exp (2 * q⁻¹ ^ i)]`. Establish `hEF : Real.exp (-(2 * q⁻¹ ^ i)) * Real.exp (2 * q⁻¹ ^ i) = 1`. Rewrite using `[← Real.exp_add]`. Simplify using the standard rewrite rules.

Establish `hE0 : 0 < Real.exp (-(2 * q⁻¹ ^ i))` using `Real.exp_pos _`. Establish `hE12 : Real.exp (-(2 * q⁻¹ ^ i)) * (1 + 2 * q⁻¹ ^ i) ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hc : 1 ≤ (1 + 2 * q⁻¹ ^ i) * (1 - q⁻¹ ^ i)` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Rewrite using `[Finset.sum_neg_distrib, ← Finset.mul_sum]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = ∏ i ∈ Finset.Icc a N, Real.exp (-(2 * q⁻¹ ^ i)) := Real.exp_sum _ _`.

Use `_ ≤ ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i) := Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) hfac`. Establish `hfac : ∀ i ∈ Finset.Icc a N, 1 - η ^ i / q ^ i ≤ Real.exp (q⁻¹ ^ i)`. Introduce `i _`. Use `(abs_le.mp (le_of_eq (hterm i))).1` as an intermediate fact. Combine the linear relations using `[Real.add_one_le_exp (q⁻¹ ^ i)]`.

Establish `hnn : ∀ i ∈ Finset.Icc a N, 0 ≤ 1 - η ^ i / q ^ i`. Introduce `i _`. Use `(abs_le.mp (le_of_eq (hterm i))).2` as an intermediate fact. Establish `hy : q⁻¹ ^ i ≤ 1` using `pow_le_one₀ hx0 (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem exp_bounds_prod_one_sub_pow_div (q η : ℝ) (hq : 2 ≤ q) (hη : η = 1 ∨ η = -1) (k a N : ℕ) (hk : 1 ≤ k)
    (ha : k ≤ a) :
    Real.exp (-(4 * q⁻¹ ^ k)) ≤ ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i) ∧
      ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i) ≤ Real.exp (2 * q⁻¹ ^ k) := by
  have hq0 : 0 < q := by linarith
  have hx0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hxq : q⁻¹ * q = 1 := inv_mul_cancel₀ hq0.ne'
  have hx2 : q⁻¹ ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_left hq hx0]
  have hterm : ∀ i : ℕ, |η ^ i / q ^ i| = q⁻¹ ^ i := by
    intro i
    rw [abs_div, abs_pow, abs_pow, abs_of_pos hq0, inv_pow]
    rcases hη with rfl | rfl <;> simp
  have hsum : ∑ i ∈ Finset.Icc a N, q⁻¹ ^ i ≤ 2 * q⁻¹ ^ k := by
    have h1 : ∑ i ∈ Finset.Icc a N, q⁻¹ ^ i ≤ q⁻¹ ^ a / (1 - q⁻¹) := by
      have hI : Finset.Icc a N = Finset.Ico a (N + 1) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hI]
      exact geom_sum_Ico_le_of_lt_one hx0 (by linarith)
    have h2 : q⁻¹ ^ a / (1 - q⁻¹) ≤ 2 * q⁻¹ ^ a := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (pow_nonneg hx0 a) (by linarith : (0 : ℝ) ≤ 1 / 2 - q⁻¹)]
    have h3 : q⁻¹ ^ a ≤ q⁻¹ ^ k := pow_le_pow_of_le_one hx0 (by linarith) ha
    linarith
  constructor
  · have hfac : ∀ i ∈ Finset.Icc a N, Real.exp (-(2 * q⁻¹ ^ i)) ≤ 1 - η ^ i / q ^ i := by
      intro i hi
      have hi1 : i ≠ 0 := by
        have := (Finset.mem_Icc.mp hi).1
        omega
      have hy0 : 0 ≤ q⁻¹ ^ i := pow_nonneg hx0 i
      have hy : q⁻¹ ^ i ≤ 1 / 2 := le_trans (pow_le_of_le_one hx0 (by linarith) hi1) hx2
      have hle : η ^ i / q ^ i ≤ q⁻¹ ^ i := (abs_le.mp (le_of_eq (hterm i))).2
      have he : 1 + 2 * q⁻¹ ^ i ≤ Real.exp (2 * q⁻¹ ^ i) := by
        linarith [Real.add_one_le_exp (2 * q⁻¹ ^ i)]
      have hEF : Real.exp (-(2 * q⁻¹ ^ i)) * Real.exp (2 * q⁻¹ ^ i) = 1 := by
        rw [← Real.exp_add]
        simp
      have hE0 : 0 < Real.exp (-(2 * q⁻¹ ^ i)) := Real.exp_pos _
      have hE12 : Real.exp (-(2 * q⁻¹ ^ i)) * (1 + 2 * q⁻¹ ^ i) ≤ 1 := by
        calc Real.exp (-(2 * q⁻¹ ^ i)) * (1 + 2 * q⁻¹ ^ i)
            ≤ Real.exp (-(2 * q⁻¹ ^ i)) * Real.exp (2 * q⁻¹ ^ i) := mul_le_mul_of_nonneg_left he hE0.le
          _ = 1 := hEF
      have hc : 1 ≤ (1 + 2 * q⁻¹ ^ i) * (1 - q⁻¹ ^ i) := by nlinarith
      calc Real.exp (-(2 * q⁻¹ ^ i))
          ≤ Real.exp (-(2 * q⁻¹ ^ i)) * ((1 + 2 * q⁻¹ ^ i) * (1 - q⁻¹ ^ i)) := le_mul_of_one_le_right hE0.le hc
        _ = (Real.exp (-(2 * q⁻¹ ^ i)) * (1 + 2 * q⁻¹ ^ i)) * (1 - q⁻¹ ^ i) := by ring
        _ ≤ 1 * (1 - q⁻¹ ^ i) := mul_le_mul_of_nonneg_right hE12 (by linarith)
        _ ≤ 1 - η ^ i / q ^ i := by linarith
    calc Real.exp (-(4 * q⁻¹ ^ k))
        ≤ Real.exp (∑ i ∈ Finset.Icc a N, -(2 * q⁻¹ ^ i)) := by
          apply Real.exp_le_exp.mpr
          rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
          linarith
      _ = ∏ i ∈ Finset.Icc a N, Real.exp (-(2 * q⁻¹ ^ i)) := Real.exp_sum _ _
      _ ≤ ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i) :=
          Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) hfac
  · have hfac : ∀ i ∈ Finset.Icc a N, 1 - η ^ i / q ^ i ≤ Real.exp (q⁻¹ ^ i) := by
      intro i _
      have := (abs_le.mp (le_of_eq (hterm i))).1
      linarith [Real.add_one_le_exp (q⁻¹ ^ i)]
    have hnn : ∀ i ∈ Finset.Icc a N, 0 ≤ 1 - η ^ i / q ^ i := by
      intro i _
      have := (abs_le.mp (le_of_eq (hterm i))).2
      have hy : q⁻¹ ^ i ≤ 1 := pow_le_one₀ hx0 (by linarith)
      linarith
    calc ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i)
        ≤ ∏ i ∈ Finset.Icc a N, Real.exp (q⁻¹ ^ i) := Finset.prod_le_prod hnn hfac
      _ = Real.exp (∑ i ∈ Finset.Icc a N, q⁻¹ ^ i) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (2 * q⁻¹ ^ k) := Real.exp_le_exp.mpr hsum

/- English proof (translation)
Unfold `aP`. Apply the tactic sequence `exact exp_bounds_prod_one_sub_pow_div _ _ (absNorm_ge_two X v) (etaV_pm X v) _ _ _ hk (by split_ifs <;> omega)`.
-/
theorem aP_bounds (hk : 1 ≤ D.R.k) (v : PlX X) (T : ℕ) :
    Real.exp (-(4 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k)) ≤ aP (E := X.B.I.E) v D.R.k X.B.I.n T ∧
      aP (E := X.B.I.E) v D.R.k X.B.I.n T ≤ Real.exp (2 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k) := by
  unfold aP
  exact exp_bounds_prod_one_sub_pow_div _ _ (absNorm_ge_two X v) (etaV_pm X v) _ _ _ hk (by split_ifs <;> omega)

/- English proof (translation)
Establish `ha0 : 0 ≤ a` using `le_trans (Real.exp_pos _).le ha.1`. Establish `hb0 : 0 ≤ b` using `le_trans (Real.exp_pos _).le hb.1`. Use `⟨⟨le_trans (Real.exp_le_exp.mpr (by linarith)) ha.1, le_trans ha.2 (Real.exp_le_exp.mpr (by linarith))⟩, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_add]`.

Put the polynomial expressions in normal form. Use `_ ≤ a * b := mul_le_mul ha.1 hb.1 (Real.exp_pos _).le ha0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form.
-/
private theorem exp_bounds_mul_of_exp_bounds (a b y : ℝ) (hy : 0 ≤ y)
    (ha : Real.exp (-(4 * y)) ≤ a ∧ a ≤ Real.exp (2 * y)) (hb : Real.exp (-(4 * y)) ≤ b ∧ b ≤ Real.exp (2 * y)) :
    (Real.exp (-(8 * y)) ≤ a ∧ a ≤ Real.exp (4 * y)) ∧
      (Real.exp (-(8 * y)) ≤ a * b ∧ a * b ≤ Real.exp (4 * y)) := by
  have ha0 : 0 ≤ a := le_trans (Real.exp_pos _).le ha.1
  have hb0 : 0 ≤ b := le_trans (Real.exp_pos _).le hb.1
  refine ⟨⟨le_trans (Real.exp_le_exp.mpr (by linarith)) ha.1, le_trans ha.2 (Real.exp_le_exp.mpr (by linarith))⟩, ?_, ?_⟩
  · calc Real.exp (-(8 * y)) = Real.exp (-(4 * y)) * Real.exp (-(4 * y)) := by
          rw [← Real.exp_add]
          ring_nf
      _ ≤ a * b := mul_le_mul ha.1 hb.1 (Real.exp_pos _).le ha0
  · calc a * b ≤ Real.exp (2 * y) * Real.exp (2 * y) := mul_le_mul ha.2 hb.2 hb0 (Real.exp_pos _).le
      _ = Real.exp (4 * y) := by
          rw [← Real.exp_add]
          ring_nf

/- English proof (translation)
Establish `h` using `exp_bounds_mul_of_exp_bounds _ _ ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k) (by positivity) (aP_bounds X hk v (Tw u)) (aP_bounds X hk v (Tw u'))`. Unfold `alX`. Use `split_ifs`. Conclude with `h.1`. Conclude with `h.2`.
-/
theorem alX_bounds (hk : 1 ≤ D.R.k) (v : PlX X) :
    Real.exp (-(8 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k)) ≤ alX X u u' v ∧
      alX X u u' v ≤ Real.exp (4 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k) := by
  have h := exp_bounds_mul_of_exp_bounds _ _ ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k) (by positivity)
    (aP_bounds X hk v (Tw u)) (aP_bounds X hk v (Tw u'))
  unfold alX
  split_ifs
  · exact h.1
  · exact h.2

/- English proof (translation)
Establish `hP` using `Formalism.L2.SG.Pf.placesOver_holds D`. Use `set s := D.R.k with hs`. Use `set a : PlF D → ℝ := fun p => (Formalism.L2.SG.DataCut.qP p ^ s)⁻¹ with ha`. Establish `ha0 : ∀ p, 0 ≤ a p` using `fun p => inv_nonneg.2 (pow_nonneg (Formalism.L2.SG.DataCut.qP_nonneg p) _)`. Establish `hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, a p ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ s)⁻¹`.

Introduce `S`. Conclude with `Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S Formalism.L2.SG.DataCut.qP Loc.resChar D.R.f s hk2 (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩) (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))`. Establish `haS : Summable a` using `summable_of_sum_le ha0 hsum`. Establish `h1 : Summable fun v : PlX X => a (plEquiv X v)` using `(plEquiv X).summable_iff.2 haS`. Use `h1.congr fun v => ?_` and prove the remaining obligations.

Use `show (Formalism.L2.SG.DataCut.qP (plEquiv X v) ^ s)⁻¹ = _`. Establish `hq : Formalism.L2.SG.DataCut.qP (plEquiv X v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)`. Rewrite using `[← absNorm_plEquiv X v]`. Conclude with `Formalism.L2.SG.Pf.LocModel.qPl_eq _`. Rewrite using `[hq, inv_pow]`.
-/
theorem summable_qk (hk2 : 2 ≤ D.R.k) :
    Summable fun v : PlX X => (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k := by
  have hP := Formalism.L2.SG.Pf.placesOver_holds D
  set s := D.R.k with hs
  set a : PlF D → ℝ := fun p => (Formalism.L2.SG.DataCut.qP p ^ s)⁻¹ with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => inv_nonneg.2 (pow_nonneg (Formalism.L2.SG.DataCut.qP_nonneg p) _)
  have hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, a p ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    intro S
    exact Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S Formalism.L2.SG.DataCut.qP Loc.resChar D.R.f s hk2
      (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩)
      (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))
  have haS : Summable a := summable_of_sum_le ha0 hsum
  have h1 : Summable fun v : PlX X => a (plEquiv X v) := (plEquiv X).summable_iff.2 haS
  refine h1.congr fun v => ?_
  show (Formalism.L2.SG.DataCut.qP (plEquiv X v) ^ s)⁻¹ = _
  have hq : Formalism.L2.SG.DataCut.qP (plEquiv X v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    rw [← absNorm_plEquiv X v]
    exact Formalism.L2.SG.Pf.LocModel.qPl_eq _
  rw [hq, inv_pow]

/- English proof (translation)
Establish `hk2 : 2 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `hk1 : 1 ≤ D.R.k` using `by omega`. Establish `hpos : ∀ v, 0 < alX X u u' v` using `fun v => lt_of_lt_of_le (Real.exp_pos _) (alX_bounds X u u' hk1 v).1`. Establish `hlog : Summable fun v : PlX X => Real.log (alX X u u' v)`. Use `Summable.of_norm_bounded ((summable_qk X hk2).mul_left 8) fun v => ?_` and prove the remaining obligations.

Rewrite using `[Real.norm_eq_abs, abs_le]`. Take `⟨b1, b2⟩` from `alX_bounds X u u' hk1 v`. Establish `h1` using `Real.log_le_log (Real.exp_pos _) b1`. Establish `h2` using `Real.log_le_log (hpos v) b2`. Rewrite `h1`, `h2` using `[Real.log_exp]`.

Establish `hy0 : 0 ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k` using `pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _`. Apply the tactic sequence `constructor <;> linarith`. Establish `hlogO : Summable fun v : OrdX X => Real.log (alX X u u' v.1)` using `hlog.comp_injective (i := fun v : OrdX X => v.1) Subtype.val_injective`. Establish `hposO : ∀ v : OrdX X, 0 < alX X u u' v.1` using `fun v => hpos v.1`. Use `⟨Real.multipliable_of_summable_log hposO hlogO, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Real.rexp_tsum_eq_tprod hposO hlogO]`. Conclude with `Real.exp_pos _`.
-/
theorem AlConvC_holds : AlConvC X u u' := by
  have hk2 : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk1 : 1 ≤ D.R.k := by omega
  have hpos : ∀ v, 0 < alX X u u' v := fun v => lt_of_lt_of_le (Real.exp_pos _) (alX_bounds X u u' hk1 v).1
  have hlog : Summable fun v : PlX X => Real.log (alX X u u' v) := by
    refine Summable.of_norm_bounded ((summable_qk X hk2).mul_left 8) fun v => ?_
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨b1, b2⟩ := alX_bounds X u u' hk1 v
    have h1 := Real.log_le_log (Real.exp_pos _) b1
    have h2 := Real.log_le_log (hpos v) b2
    rw [Real.log_exp] at h1 h2
    have hy0 : 0 ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k :=
      pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _
    constructor <;> linarith
  have hlogO : Summable fun v : OrdX X => Real.log (alX X u u' v.1) :=
    hlog.comp_injective (i := fun v : OrdX X => v.1) Subtype.val_injective
  have hposO : ∀ v : OrdX X, 0 < alX X u u' v.1 := fun v => hpos v.1
  refine ⟨Real.multipliable_of_summable_log hposO hlogO, ?_⟩
  rw [← Real.rexp_tsum_eq_tprod hposO hlogO]
  exact Real.exp_pos _

end Formalism.L2.SG.Pf.ProdConvCut2
