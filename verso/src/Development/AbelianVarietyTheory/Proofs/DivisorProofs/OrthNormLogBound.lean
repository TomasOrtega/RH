import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthNormLogBoundIffOrthBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingListCharacterProduct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InitMinorNeZeroOfStrictMono

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.BrCompare GlobalTheory.BrCompare.Shift

noncomputable section

namespace GlobalTheory.BranchLogBound

variable {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n}

def sgN (lam : DomWeight (n + 1)) (sg : DomWeight n) : Fin n → ℕ := fun i => (sg.w i - lam.w (Fin.last n)).toNat

/- English proof (translation)
Introduce `i`. Establish `: 0 ≤ sg.w i - lam.w i.succ ∧ 0 ≤ lam.w i.castSucc - sg.w i` using `h i`. Use linear arithmetic over natural numbers and integers.
-/
theorem interlace_w (h : Br.Interlace rfl lam sg) : Formalism.BranchingDeterminantCap.Interlace lam.w sg.w := by
  intro i
  have : 0 ≤ sg.w i - lam.w i.succ ∧ 0 ≤ lam.w i.castSucc - sg.w i := h i
  omega

/- English proof (translation)
Establish `h1` using `(interlace_w h i).2`. Establish `h2` using `lam.anti (Fin.le_last i.succ)`. Unfold `sgN`. Use linear arithmetic over natural numbers and integers.
-/
theorem sgN_cast (h : Br.Interlace rfl lam sg) (i : Fin n) : (sgN lam sg i : ℤ) = sg.w i - lam.w (Fin.last n) := by
  have h1 := (interlace_w h i).2
  have h2 := lam.anti (Fin.le_last i.succ)
  unfold sgN
  omega

/- English proof (translation)
Introduce `i`. Use `interlace_w h i` as an intermediate fact. Simplify using `only [lamZ_lamN, sgN_cast h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem interlace_N (h : Br.Interlace rfl lam sg) : Formalism.BranchingDeterminantCap.Interlace (lamZ (lamN lam)) (fun i => (sgN lam sg i : ℤ)) := by
  intro i
  have := interlace_w h i
  simp only [lamZ_lamN, sgN_cast h]
  omega

/- English proof (translation)
Establish `hb : ∀ s, (Br.bBr rfl lam sg s).toNat = lamN lam s - sgN lam sg s`. Introduce `s`. Establish `h1` using `lamN_cast lam s`. Establish `h2` using `sgN_cast h s`. Establish `h3 : Br.bBr rfl lam sg s = lam.w s.castSucc - sg.w s` using `rfl`.

Rewrite using `[h3]`. Use linear arithmetic over natural numbers and integers. Establish `ha : ∀ s, (Br.aBr rfl lam sg s).toNat = sgN lam sg s - nuNext (lamN lam) s`. Introduce `s`. Establish `h1` using `nuNext_cast lam s`.

Establish `h2` using `sgN_cast h s`. Establish `h3 : Br.aBr rfl lam sg s = sg.w s - lam.w s.succ` using `rfl`. Rewrite using `[h3]`. Use linear arithmetic over natural numbers and integers. Unfold `Br.xiBr xiB`.

Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, map_pow, rename_initMinor, rename_initMinor, ha, hb]`. Use `congr 2`.
-/
theorem xiBr_eq (h : Br.Interlace rfl lam sg) (K : Type) [Field K] :
    Br.xiBr K rfl lam sg = incl K n (xiB K (lamN lam) (sgN lam sg)) := by
  have hb : ∀ s, (Br.bBr rfl lam sg s).toNat = lamN lam s - sgN lam sg s := by
    intro s
    have h1 := lamN_cast lam s
    have h2 := sgN_cast h s
    have h3 : Br.bBr rfl lam sg s = lam.w s.castSucc - sg.w s := rfl
    rw [h3]
    omega
  have ha : ∀ s, (Br.aBr rfl lam sg s).toNat = sgN lam sg s - nuNext (lamN lam) s := by
    intro s
    have h1 := nuNext_cast lam s
    have h2 := sgN_cast h s
    have h3 : Br.aBr rfl lam sg s = sg.w s - lam.w s.succ := rfl
    rw [h3]
    omega
  unfold Br.xiBr xiB
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_pow, rename_initMinor, rename_initMinor, ha, hb]
  congr 2

/- English proof (translation)
Unfold `extremal hw`. Rewrite using `[map_prod, Fin.prod_univ_castSucc]`. Establish `h0 : lam.natW (Fin.last n) = 0`. Use `natW_top lam (Fin.last n)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[h0, Nat.zero_sub, pow_zero, mul_one]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow]`. Use `congr 1`. Conclude with `(rename_initMinor K (Fin.castLE (by have := i.2; omega) : Fin (i.val + 1) → Fin (n + 1)) (by have := i.2; omega)).symm`.

Establish `h1` using `nuNext_cast lam i`. Establish `h2` using `natW_top lam i.succ`. Establish `h3 : nuNext lam.natW i.castSucc = lam.natW i.succ`. Unfold `nuNext`. Rewrite using `[dif_pos (by simp)]`.

Both sides reduce to the same expression. Rewrite using `[h3]`. Establish `h4 : lamN lam i = lam.natW i.castSucc` using `rfl`. Use linear arithmetic over natural numbers and integers.
-/
theorem extremal_eq (lam : DomWeight (n + 1)) (K : Type) [Field K] :
    extremal K (n + 1) lam = incl K n (hw K (Nat.le_succ n) (lamN lam)) := by
  unfold extremal hw
  rw [map_prod, Fin.prod_univ_castSucc]
  have h0 : lam.natW (Fin.last n) = 0 := by
    have := natW_top lam (Fin.last n)
    omega
  rw [h0, Nat.zero_sub, pow_zero, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow]
  congr 1
  · exact (rename_initMinor K (Fin.castLE (by have := i.2; omega) : Fin (i.val + 1) → Fin (n + 1)) (by have := i.2; omega)).symm
  · have h1 := nuNext_cast lam i
    have h2 := natW_top lam i.succ
    have h3 : nuNext lam.natW i.castSucc = lam.natW i.succ := by
      unfold nuNext
      rw [dif_pos (by simp)]
      rfl
    rw [h3]
    have h4 : lamN lam i = lam.natW i.castSucc := rfl
    omega

/- English proof (translation)
Unfold `Formalism.REAL.fockF fockB`. Rewrite using `[support_map_of_injective _ (algebraMap ℝ ℂ).injective, Complex.re_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `: ∀ (x : ℝ) (k : ℕ), ((algebraMap ℝ ℂ x) * (starRingEnd ℂ) (algebraMap ℝ ℂ x) * (k : ℂ)).re = x * x * k`. Introduce `x k`.

Simplify using the standard rewrite rules. Rewrite using `[coeff_map]`. Conclude with `this _ _`.
-/
theorem fockF_map {σ : Type} (f : MvPolynomial σ ℝ) :
    (Formalism.REAL.fockF (map (algebraMap ℝ ℂ) f) (map (algebraMap ℝ ℂ) f)).re = fockB f f := by
  unfold Formalism.REAL.fockF fockB
  rw [support_map_of_injective _ (algebraMap ℝ ℂ).injective, Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : ∀ (x : ℝ) (k : ℕ), ((algebraMap ℝ ℂ x) * (starRingEnd ℂ) (algebraMap ℝ ℂ x) * (k : ℂ)).re = x * x * k := by
    intro x k
    simp
  rw [coeff_map]
  exact this _ _

/- English proof (translation)
Simplify using `only [xiB, map_prod, map_mul, map_pow, initMinor, RingHom.map_det]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `congr 3 <;> ext1 a b <;> simp`.
-/
theorem map_xiB (l s : Fin n → ℕ) : map (algebraMap ℝ ℂ) (xiB ℝ l s) = xiB ℂ l s := by
  simp only [xiB, map_prod, map_mul, map_pow, initMinor, RingHom.map_det]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 3 <;> ext1 a b <;> simp

/- English proof (translation)
Establish `h1` using `xiNorm n (lamN lam) (sgN lam sg) (interlace_N h)`. Establish `h2` using `(fockPos _ _ (GlobalTheory.Branching.xiB_ne_zero (lamN lam) (sgN lam sg))).1`. Establish `h3` using `(fockPos _ _ (hwNe ℂ (n + 1) n (Nat.le_succ n) (lamN lam))).1`. Establish `e : hw ℂ (Nat.le_succ n) (lamN lam) = map (algebraMap ℝ ℂ) (hw ℝ (Nat.le_succ n) (lamN lam))` using `(lclosedeq_hw_map _ _ _).symm`. Rewrite `h1`, `h2` using `[← map_xiB, fockF_map]`.

Rewrite `h1`, `h3` using `[e, fockF_map]`. Unfold `Br.kapBr`. Rewrite using `[xiBr_eq h, extremal_eq, fockB_incl, fockB_incl]`. Conclude with `⟨div_pos h2 h3, (div_le_iff₀ h3).2 h1⟩`.
-/
theorem kap_bounds (h : Br.Interlace rfl lam sg) :
    0 < Br.kapBr ℝ rfl lam sg ∧ Br.kapBr ℝ rfl lam sg ≤ weylProd (lamZ (lamN lam)) := by
  have h1 := xiNorm n (lamN lam) (sgN lam sg) (interlace_N h)
  have h2 := (fockPos _ _ (GlobalTheory.Branching.xiB_ne_zero (lamN lam) (sgN lam sg))).1
  have h3 := (fockPos _ _ (hwNe ℂ (n + 1) n (Nat.le_succ n) (lamN lam))).1
  have e : hw ℂ (Nat.le_succ n) (lamN lam) = map (algebraMap ℝ ℂ) (hw ℝ (Nat.le_succ n) (lamN lam)) :=
    (lclosedeq_hw_map _ _ _).symm
  rw [← map_xiB, fockF_map] at h1 h2
  rw [e, fockF_map] at h1 h3
  unfold Br.kapBr
  rw [xiBr_eq h, extremal_eq, fockB_incl, fockB_incl]
  exact ⟨div_pos h2 h3, (div_le_iff₀ h3).2 h1⟩

/- English proof (translation)
Unfold `DomWeight.spread`. Rewrite using `[dif_pos (Nat.succ_pos n)]`. Both sides reduce to the same expression.
-/
theorem spread_eq (lam : DomWeight (n + 1)) : lam.spread = lam.w 0 - lam.w (Fin.last n) + (n + 1 : ℕ) := by
  unfold DomWeight.spread
  rw [dif_pos (Nat.succ_pos n)]
  rfl

/- English proof (translation)
Establish `ha : Antitone (lamZ (lamN lam))` using `fun a b hab => by`. Use `lam.anti hab` as an intermediate fact. Simplify using `only [lamZ_lamN]`. Use linear arithmetic over natural numbers and integers. Use `(kap_bounds h).2.trans ((weylDimBound n _ ha).2.trans ?_)` and prove the remaining obligations.

Establish `h0` using `ha (Fin.zero_le (Fin.last n))`. Use `pow_le_pow_left₀ (add_nonneg (by exact_mod_cast sub_nonneg.2 h0) (Nat.cast_nonneg n)) ?_ _` and prove the remaining obligations. Rewrite `hA` using `[spread_eq]`. Simplify using `only [lamZ_lamN]`. Move the coercions through the operations in `at hA ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem kap_le (h : Br.Interlace rfl lam sg) {A : ℝ} (hA : ((lam.spread : ℤ) : ℝ) ≤ A) :
    Br.kapBr ℝ rfl lam sg ≤ A ^ ((n + 1) * n / 2) := by
  have ha : Antitone (lamZ (lamN lam)) := fun a b hab => by
    have := lam.anti hab
    simp only [lamZ_lamN]
    omega
  refine (kap_bounds h).2.trans ((weylDimBound n _ ha).2.trans ?_)
  have h0 := ha (Fin.zero_le (Fin.last n))
  refine pow_le_pow_left₀ (add_nonneg (by exact_mod_cast sub_nonneg.2 h0) (Nat.cast_nonneg n)) ?_ _
  rw [spread_eq] at hA
  simp only [lamZ_lamN]
  push_cast at hA ⊢
  linarith

/- English proof (translation)
Use `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cBr_eq (lam : DomWeight (n + 1)) (sg : DomWeight n) : Br.cBr rfl lam sg = cCap lam.w sg.w := by
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Take `⟨h1, h2⟩` from `capConst n lam.w sg.w (interlace_w h)`. Rewrite using `[cBr_eq]`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `e : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg = d1 lam.w sg.w` using `rfl`. Rewrite using `[e]`.

Establish `h3 : |((cCap lam.w sg.w : ℤ) : ℝ)| ≤ ((lam.w 0 - lam.w (Fin.last n) + (n : ℤ) - 1 : ℤ) : ℝ) ^ (n * (d1 lam.w sg.w).toNat)` using `by exact_mod_cast h2`. Use `h3.trans ?_` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Establish `h0` using `lam.anti (Fin.zero_le (Fin.last n))`.

Use `pow_le_pow_left₀ (by exact_mod_cast (by omega : (0 : ℤ) ≤ lam.w 0 - lam.w (Fin.last n) + (n : ℤ) - 1)) ?_ _` and prove the remaining obligations. Rewrite `hA` using `[spread_eq]`. Move the coercions through the operations in `at hA ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem c_bounds (h : Br.Interlace rfl lam sg) {A : ℝ} (hA : ((lam.spread : ℤ) : ℝ) ≤ A) :
    Br.cBr rfl lam sg ≠ 0 ∧ |((Br.cBr rfl lam sg : ℤ) : ℝ)| ≤ A ^ (n * (GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg).toNat) := by
  obtain ⟨h1, h2⟩ := capConst n lam.w sg.w (interlace_w h)
  rw [cBr_eq]
  refine ⟨h1, ?_⟩
  have e : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg = d1 lam.w sg.w := rfl
  rw [e]
  have h3 : |((cCap lam.w sg.w : ℤ) : ℝ)| ≤
      ((lam.w 0 - lam.w (Fin.last n) + (n : ℤ) - 1 : ℤ) : ℝ) ^ (n * (d1 lam.w sg.w).toNat) := by exact_mod_cast h2
  refine h3.trans ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h0 := lam.anti (Fin.zero_le (Fin.last n))
  refine pow_le_pow_left₀ (by exact_mod_cast (by omega : (0 : ℤ) ≤ lam.w 0 - lam.w (Fin.last n) + (n : ℤ) - 1)) ?_ _
  rw [spread_eq] at hA
  push_cast at hA ⊢
  linarith

/- English proof (translation)
Take `⟨c1, c2⟩` from `c_bounds h hA`. Establish `k1` using `(kap_bounds h).1`. Establish `k2` using `kap_le h hA`. Establish `c0 : ((Br.cBr rfl lam sg : ℤ) : ℝ) ≠ 0` using `by exact_mod_cast c1`. Establish `hd : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg` using `(interlaceIdent n lam.w sg.w (interlace_w h)).2.2.2.1`.

Establish `hd' : (((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg).toNat : ℕ) : ℝ) = ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg : ℤ) : ℝ)`. Conclude with `congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg hd)` after adjusting the coercions. Establish `he : (((n + 1) * n / 2 : ℕ) : ℝ) = ((n : ℝ) + 1) * n / 2`. Rewrite using `[Nat.cast_div (by rw [mul_comm]; exact (Nat.even_mul_succ_self n).two_dvd) (by norm_num)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨by positivity, ?_⟩` and prove the remaining obligations. Establish `l1` using `Real.log_le_log (abs_pos.2 c0) c2`. Establish `l2` using `Real.log_le_log k1 k2`. Rewrite `l1` using `[Real.log_pow, Real.log_abs, Nat.cast_mul, hd']`.

Rewrite `l2` using `[Real.log_pow, he]`. Rewrite using `[Real.log_mul (pow_ne_zero 2 c0) k1.ne', Real.log_pow]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_position (h : Br.Interlace rfl lam sg) {A : ℝ} (hA : ((lam.spread : ℤ) : ℝ) ≤ A) :
    0 < ((Br.cBr rfl lam sg : ℤ) : ℝ) ^ 2 * Br.kapBr ℝ rfl lam sg ∧
    Real.log (((Br.cBr rfl lam sg : ℤ) : ℝ) ^ 2 * Br.kapBr ℝ rfl lam sg) ≤
      (2 * (((n + 1 : ℕ) : ℝ) - 1) * ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg : ℤ) : ℝ) +
        ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) / 2) * Real.log A := by
  obtain ⟨c1, c2⟩ := c_bounds h hA
  have k1 := (kap_bounds h).1
  have k2 := kap_le h hA
  have c0 : ((Br.cBr rfl lam sg : ℤ) : ℝ) ≠ 0 := by exact_mod_cast c1
  have hd : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg := (interlaceIdent n lam.w sg.w (interlace_w h)).2.2.2.1
  have hd' : (((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg).toNat : ℕ) : ℝ) = ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg : ℤ) : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg hd)
  have he : (((n + 1) * n / 2 : ℕ) : ℝ) = ((n : ℝ) + 1) * n / 2 := by
    rw [Nat.cast_div (by rw [mul_comm]; exact (Nat.even_mul_succ_self n).two_dvd) (by norm_num)]
    push_cast
    ring
  refine ⟨by positivity, ?_⟩
  have l1 := Real.log_le_log (abs_pos.2 c0) c2
  have l2 := Real.log_le_log k1 k2
  rw [Real.log_pow, Real.log_abs, Nat.cast_mul, hd'] at l1
  rw [Real.log_pow, he] at l2
  rw [Real.log_mul (pow_ne_zero 2 c0) k1.ne', Real.log_pow]
  push_cast
  linarith

/- English proof (translation)
Use `⟨2, fun ι _ N n hN lam sg h1 a ha => ?_⟩` and prove the remaining obligations. Use `⟨?_, ?_, GlobalTheory.BrNormCompare.last_ineq hN lam sg h1 a ha⟩` and prove the remaining obligations. Substitute `hN` using the available equality. Conclude with `Finset.prod_pos fun τ _ => (one_position (h1 τ) (ha τ)).1`. Substitute `hN` using the available equality.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.orthNormSq`. Rewrite using `[Real.log_prod fun τ _ => (one_position (h1 τ) (ha τ)).1.ne']`. Conclude with `Finset.sum_le_sum fun τ _ => (one_position (h1 τ) (ha τ)).2`.
-/
theorem orthNormLogBound : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.OrthNormLogBound := by
  refine ⟨2, fun ι _ N n hN lam sg h1 a ha => ?_⟩
  refine ⟨?_, ?_, GlobalTheory.BrNormCompare.last_ineq hN lam sg h1 a ha⟩
  · subst hN
    exact Finset.prod_pos fun τ _ => (one_position (h1 τ) (ha τ)).1
  · subst hN
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.orthNormSq
    rw [Real.log_prod fun τ _ => (one_position (h1 τ) (ha τ)).1.ne']
    exact Finset.sum_le_sum fun τ _ => (one_position (h1 τ) (ha τ)).2

end GlobalTheory.BranchLogBound
