import Formalism.HermitianCurvature.BigCellVanishingOfCommute

open Formalism.FourierDecayAlt Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.GeometricRayBounds

/- English proof (translation)
Take `⟨t, ht⟩ : ∃ t : ℝ, t ∉ S.image (fun i => (c i).re / (c i).im)` from `by first`. Consider the case `exact Infinite.exists_not_mem_finset _`. Consider the case `exact Infinite.exists_notMem_finset _`. Use `⟨1 + (t : ℂ) * Complex.I, ?_, fun i hi => ?_⟩` and prove the remaining obligations. Introduce `h`.

Establish `h1` using `congrArg Complex.re h`. Simplify using `at h1`. Introduce `h0`. Establish `h0' : (c i).re = (c i).im * t`. Simplify using `at h0`.

Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `him : (c i).im = 0`. Conclude with `hc i hi (Complex.ext (by rw [h0', him, zero_mul, Complex.zero_re]) (by rw [him, Complex.zero_im]))`. Conclude with `ht (Finset.mem_image.2 ⟨i, hi, by rw [h0']; exact mul_div_cancel_left₀ t him⟩)`.
-/
theorem exists_dir {ι : Type*} (S : Finset ι) (c : ι → ℂ) (hc : ∀ i ∈ S, c i ≠ 0) :
    ∃ u : ℂ, u ≠ 0 ∧ ∀ i ∈ S, (c i * u).re ≠ 0 := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∉ S.image (fun i => (c i).re / (c i).im) := by
    first
    | exact Infinite.exists_not_mem_finset _
    | exact Infinite.exists_notMem_finset _
  refine ⟨1 + (t : ℂ) * Complex.I, ?_, fun i hi => ?_⟩
  · intro h
    have h1 := congrArg Complex.re h
    simp at h1
  · intro h0
    have h0' : (c i).re = (c i).im * t := by
      simp at h0
      linarith
    by_cases him : (c i).im = 0
    · exact hc i hi (Complex.ext (by rw [h0', him, zero_mul, Complex.zero_re])
        (by rw [him, Complex.zero_im]))
    · exact ht (Finset.mem_image.2 ⟨i, hi, by rw [h0']; exact mul_div_cancel_left₀ t him⟩)

/- English proof (translation)
Proceed by induction on `S using Finset.cons_induction with`. Consider the case `empty => simp`. Consider the case `cons a S ha ih`. Rewrite using `[Finset.sum_cons, Finset.sum_cons]`. Conclude with `(map_add_le_add p _ _).trans (add_le_add_right ih _)`.
-/
theorem p_sum_le {V : Type*} [AddCommGroup V] [Module ℂ V] (p : Seminorm ℂ V) {ι : Type*} (S : Finset ι)
    (f : ι → V) : p (∑ i ∈ S, f i) ≤ ∑ i ∈ S, p (f i) := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact (map_add_le_add p _ _).trans (add_le_add_right ih _)

/- English proof (translation)
Rewrite using `[mul_comm]`. Conclude with `Complex.norm_exp_ofReal_mul_I x`.
-/
theorem nexp (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I x

/- English proof (translation)
Establish `hne : 0 < ‖q - 1‖` using `norm_pos_iff.2 (sub_ne_zero.2 hq1)`. Rewrite using `[geom_sum_eq hq1, norm_div]`. Apply `div_le_div_of_nonneg_right _ hne.le` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_pow, hq, one_pow, norm_one]`.

Evaluate the numerical expressions.
-/
theorem geom_bound (q : ℂ) (hq : ‖q‖ = 1) (hq1 : q ≠ 1) (M : ℕ) :
    ‖∑ m ∈ range M, q ^ m‖ ≤ 2 / ‖q - 1‖ := by
  have hne : 0 < ‖q - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hq1)
  rw [geom_sum_eq hq1, norm_div]
  apply div_le_div_of_nonneg_right _ hne.le
  calc ‖q ^ M - 1‖ ≤ ‖q ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      rw [norm_pow, hq, one_pow, norm_one]
      norm_num

/- English proof (translation)
Introduce `h`. Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.1 h`. Establish `h2` using `congrArg Complex.im hn`. Simplify using `at h2`. Establish `hx : x = n * (2 * Real.pi)` using `by linarith`.

Establish `hpi` using `Real.pi_pos`. Rewrite `h1` using `[hx, abs_lt]`. Break down `lt_trichotomy n 0 with hn0 | hn0 | hn0` into its components or cases. Establish `h3 : (n : ℝ) ≤ -1` using `by exact_mod_cast Int.le_sub_one_of_lt hn0`. Use the polynomial consequences of the given equalities and inequalities.

Substitute `hn0` using the available equality. Simplify using `at hx`. Conclude with `h0 hx`. Establish `h3 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn0`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exp_ne_one {x : ℝ} (h0 : x ≠ 0) (h1 : |x| < 2 * Real.pi) :
    Complex.exp (Complex.I * (x : ℂ)) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  have h2 := congrArg Complex.im hn
  simp at h2
  have hx : x = n * (2 * Real.pi) := by linarith
  have hpi := Real.pi_pos
  rw [hx, abs_lt] at h1
  rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
  · have h3 : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn0
    nlinarith
  · subst hn0
    simp at hx
    exact h0 hx
  · have h3 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    nlinarith

end Formalism.FourierDecayAlt.P.GeometricRayBounds

namespace Formalism.FourierDecayAlt.P

open GeometricRayBounds

/- English proof (translation)
Introduce `β hβ V _ _ p s w a C' x₁ hw H j0`. Use `set c : Fin s → ℂ := fun j => β * (w j - w j0) with hcdef`. Establish `hc : ∀ j ∈ Finset.univ.erase j0, c j ≠ 0`. Introduce `j hj`. Establish `hj' : j ≠ j0` using `Finset.ne_of_mem_erase hj`.

Conclude with `mul_ne_zero hβ (sub_ne_zero.2 fun h => hj' (hw h))`. Take `⟨u, hu0, hu⟩` from `exists_dir (Finset.univ.erase j0) c hc`. Establish `hunorm : 0 < ‖u‖` using `norm_pos_iff.2 hu0`. Establish `hsum0 : 0 ≤ ∑ j, |(c j * u).re|` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Use `set K0 : ℝ := 1 + ∑ j, |(c j * u).re| with hK0`.

Establish `hK0pos : 0 < K0` using `by linarith`. Use `set t : ℝ := Real.pi / K0 with ht`. Establish `htpos : 0 < t` using `div_pos Real.pi_pos hK0pos`. Establish `hphase : ∀ j, |t * (c j * u).re| < 2 * Real.pi`. Introduce `j`.

Establish `hle : |(c j * u).re| ≤ ∑ j, |(c j * u).re|` using `Finset.single_le_sum (f := fun j => |(c j * u).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)`. Rewrite using `[abs_mul, abs_of_pos htpos, ht, div_mul_eq_mul_div, div_lt_iff₀ hK0pos]`. Use polynomial arithmetic with `[Real.pi_pos]`. Use `set q : Fin s → ℂ := fun j => Complex.exp (Complex.I * ((t * (c j * u).re : ℝ) : ℂ)) with hqdef`. Establish `hq1 : ∀ j ∈ Finset.univ.erase j0, q j ≠ 1` using `fun j hj => exp_ne_one (mul_ne_zero htpos.ne' (hu j hj)) (hphase j)`.

Establish `hqn : ∀ j, ‖q j‖ = 1` using `fun j => nexp _`. Establish `hpsi : ∀ j (x : ℂ), G.psi β (-(w j0) * x) * G.psi β (w j * x) = Complex.exp (Complex.I * (((c j * x).re : ℝ) : ℂ))`. Introduce `j x`. Rewrite using `[show c j * x = β * (-(w j0) * x) + β * (w j * x) by simp only [hcdef]; ring, Complex.add_re, Complex.ofReal_add, mul_add, Complex.exp_add]`. Both sides reduce to the same expression.

Establish `hpsin : ∀ x : ℂ, ‖G.psi β x‖ = 1` using `fun x => nexp _`. Use `set Kc : ℝ := ∑ j ∈ Finset.univ.erase j0, 2 / ‖q j - 1‖ * p (a j) with hKc`. Establish `hC' : 0 ≤ C'`. Take `⟨N, hN⟩` from `exists_nat_gt (|x₁| / ‖u‖ + 1)`. Establish `hq0 : 0 ≤ |x₁| / ‖u‖` using `div_nonneg (abs_nonneg _) hunorm.le`.

Establish `hNu : 0 < (N : ℝ) * ‖u‖` using `mul_pos (by linarith) hunorm`. Establish `hx : x₁ ≤ ‖((N : ℝ) : ℂ) * u‖`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]`. Establish `h2` using `(div_lt_iff₀ hunorm).1 (by linarith : |x₁| / ‖u‖ < N)`. Combine the linear relations using `[le_abs_self x₁]`.

Establish `h1` using `(apply_nonneg p _).trans (H _ hx)`. Rewrite `h1` using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]`. Conclude with `(div_nonneg_iff.1 h1).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hNu))`. Establish `hmain : ∀ N : ℕ, 0 < N → x₁ ≤ N * ‖u‖ → p (a j0) ≤ (C' / ‖u‖ + Kc) / N`. Introduce `N hN hx₁`.

Establish `hNpos : (0 : ℝ) < N` using `by exact_mod_cast hN`. Use `set x : ℕ → ℂ := fun m => (((N : ℝ) + m * t : ℝ) : ℂ) * u with hxdef`. Establish `hxn : ∀ m : ℕ, (N : ℝ) * ‖u‖ ≤ ‖x m‖`. Introduce `m`. Establish `hmt : 0 ≤ (m : ℝ) * t` using `mul_nonneg (Nat.cast_nonneg _) htpos.le`.

Simplify using `only [hxdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[abs_of_nonneg (add_nonneg (Nat.cast_nonneg _) hmt)]`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT : ∀ m : ℕ, p (∑ j, G.psi β (w j * x m) • a j) ≤ C' / (N * ‖u‖)`.

Introduce `m`. Combine the equalities or inequalities in the displayed calculation. Use `set coef : Fin s → ℂ := fun j => ∑ m ∈ Finset.range N, G.psi β (-(w j0) * x m) * G.psi β (w j * x m) with hcoef`. Establish `hid : ∑ m ∈ Finset.range N, G.psi β (-(w j0) * x m) • ∑ j, G.psi β (w j * x m) • a j = ∑ j, coef j • a j`. Simplify using `only [Finset.smul_sum, smul_smul, hcoef, Finset.sum_smul]`.

Conclude with `Finset.sum_comm`. Establish `hc0 : coef j0 = N`. Establish `h0 : c j0 = 0` using `by simp only [hcdef, sub_self, mul_zero]`. Simplify using `only [hcoef, hpsi, h0, zero_mul, Complex.zero_re, Complex.ofReal_zero, mul_zero, Complex.exp_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`. Establish `hcj : ∀ j ∈ Finset.univ.erase j0, ‖coef j‖ ≤ 2 / ‖q j - 1‖`.

Introduce `j hj`. Establish `hterm : ∀ m : ℕ, G.psi β (-(w j0) * x m) * G.psi β (w j * x m) = Complex.exp (Complex.I * (((N : ℝ) * (c j * u).re : ℝ) : ℂ)) * q j ^ m`. Introduce `m`. Rewrite using `[hpsi, show c j * x m = (((N : ℝ) + m * t : ℝ) : ℂ) * (c j * u) by simp only [hxdef]; ring, Complex.re_ofReal_mul]`. Simplify using `only [hqdef]`.

Rewrite using `[← Complex.exp_nat_mul, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hcoef, hterm, ← Finset.mul_sum, norm_mul, nexp, one_mul]`.

Conclude with `geom_bound (q j) (hqn j) (hq1 j hj) N`. Establish `hsplit : ∑ j, coef j • a j = coef j0 • a j0 + ∑ j ∈ Finset.univ.erase j0, coef j • a j` using `(Finset.add_sum_erase _ _ (Finset.mem_univ j0)).symm`. Establish `hpa : (N : ℝ) * p (a j0) ≤ N * (C' / (N * ‖u‖)) + Kc`. Establish `e1 : (N : ℝ) * p (a j0) = p (coef j0 • a j0)`. Rewrite using `[hc0, map_smul_eq_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[e1]`. Establish `e2 : coef j0 • a j0 = (∑ m ∈ Finset.range N, G.psi β (-(w j0) * x m) • ∑ j, G.psi β (w j * x m) • a j) - ∑ j ∈ Finset.univ.erase j0, coef j • a j`. Rewrite using `[hid, hsplit]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e2]`. Use `(map_sub_le_add p _ _).trans (add_le_add ?_ ?_)` and prove the remaining obligations. Use `(p_sum_le p _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul_eq_mul, hpsin, one_mul]`. Use `_ ≤ ∑ m ∈ Finset.range N, C' / (N * ‖u‖) := Finset.sum_le_sum fun m _ => hT m`. Use `_ = N * (C' / (N * ‖u‖)) := by simp`. Use `(p_sum_le p _ _).trans ?_` and prove the remaining obligations. Use `Finset.sum_le_sum fun j hj => ?_` and prove the remaining obligations.

Rewrite using `[map_smul_eq_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hcj j hj) (apply_nonneg p _)`. Establish `e3 : (N : ℝ) * (C' / (N * ‖u‖)) = C' / ‖u‖`. Clear the denominators using the available nonvanishing facts. Rewrite `hpa` using `[e3]`.

Rewrite using `[le_div_iff₀ hNpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnn` using `apply_nonneg p (a j0)`. Assume the negation of the conclusion as `hne`. Establish `hδ : 0 < p (a j0)` using `lt_of_le_of_ne hnn (Ne.symm hne)`.

Take `⟨N, hN⟩` from `exists_nat_gt (max (|x₁| / ‖u‖) ((C' / ‖u‖ + Kc) / p (a j0)))`. Establish `hN1 : |x₁| / ‖u‖ < N` using `lt_of_le_of_lt (le_max_left _ _) hN`. Establish `hN2 : (C' / ‖u‖ + Kc) / p (a j0) < N` using `lt_of_le_of_lt (le_max_right _ _) hN`. Establish `hNpos : (0 : ℝ) < N` using `lt_of_le_of_lt (div_nonneg (abs_nonneg _) hunorm.le) hN1`. Establish `hx₁ : x₁ ≤ N * ‖u‖`.

Establish `h2` using `(div_lt_iff₀ hunorm).1 hN1`. Combine the linear relations using `[le_abs_self x₁]`. Establish `hb` using `hmain N (by exact_mod_cast hNpos) hx₁`. Rewrite `hN2` using `[div_lt_iff₀ hδ]`. Rewrite `hb` using `[le_div_iff₀ hNpos]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem averaging_vanishes : C6.AveragingZero := by
  intro β hβ V _ _ p s w a C' x₁ hw H j0
  classical
  set c : Fin s → ℂ := fun j => β * (w j - w j0) with hcdef
  have hc : ∀ j ∈ Finset.univ.erase j0, c j ≠ 0 := by
    intro j hj
    have hj' : j ≠ j0 := Finset.ne_of_mem_erase hj
    exact mul_ne_zero hβ (sub_ne_zero.2 fun h => hj' (hw h))
  obtain ⟨u, hu0, hu⟩ := exists_dir (Finset.univ.erase j0) c hc
  have hunorm : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hsum0 : 0 ≤ ∑ j, |(c j * u).re| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set K0 : ℝ := 1 + ∑ j, |(c j * u).re| with hK0
  have hK0pos : 0 < K0 := by linarith
  set t : ℝ := Real.pi / K0 with ht
  have htpos : 0 < t := div_pos Real.pi_pos hK0pos
  have hphase : ∀ j, |t * (c j * u).re| < 2 * Real.pi := by
    intro j
    have hle : |(c j * u).re| ≤ ∑ j, |(c j * u).re| :=
      Finset.single_le_sum (f := fun j => |(c j * u).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    rw [abs_mul, abs_of_pos htpos, ht, div_mul_eq_mul_div, div_lt_iff₀ hK0pos]
    nlinarith [Real.pi_pos]
  set q : Fin s → ℂ := fun j => Complex.exp (Complex.I * ((t * (c j * u).re : ℝ) : ℂ)) with hqdef
  have hq1 : ∀ j ∈ Finset.univ.erase j0, q j ≠ 1 := fun j hj =>
    exp_ne_one (mul_ne_zero htpos.ne' (hu j hj)) (hphase j)
  have hqn : ∀ j, ‖q j‖ = 1 := fun j => nexp _
  have hpsi : ∀ j (x : ℂ), G.psi β (-(w j0) * x) * G.psi β (w j * x) =
      Complex.exp (Complex.I * (((c j * x).re : ℝ) : ℂ)) := by
    intro j x
    rw [show c j * x = β * (-(w j0) * x) + β * (w j * x) by simp only [hcdef]; ring, Complex.add_re,
      Complex.ofReal_add, mul_add, Complex.exp_add]
    rfl
  have hpsin : ∀ x : ℂ, ‖G.psi β x‖ = 1 := fun x => nexp _
  set Kc : ℝ := ∑ j ∈ Finset.univ.erase j0, 2 / ‖q j - 1‖ * p (a j) with hKc
  have hC' : 0 ≤ C' := by
    obtain ⟨N, hN⟩ := exists_nat_gt (|x₁| / ‖u‖ + 1)
    have hq0 : 0 ≤ |x₁| / ‖u‖ := div_nonneg (abs_nonneg _) hunorm.le
    have hNu : 0 < (N : ℝ) * ‖u‖ := mul_pos (by linarith) hunorm
    have hx : x₁ ≤ ‖((N : ℝ) : ℂ) * u‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]
      have h2 := (div_lt_iff₀ hunorm).1 (by linarith : |x₁| / ‖u‖ < N)
      linarith [le_abs_self x₁]
    have h1 := (apply_nonneg p _).trans (H _ hx)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)] at h1
    exact (div_nonneg_iff.1 h1).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hNu))
  have hmain : ∀ N : ℕ, 0 < N → x₁ ≤ N * ‖u‖ → p (a j0) ≤ (C' / ‖u‖ + Kc) / N := by
    intro N hN hx₁
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    set x : ℕ → ℂ := fun m => (((N : ℝ) + m * t : ℝ) : ℂ) * u with hxdef
    have hxn : ∀ m : ℕ, (N : ℝ) * ‖u‖ ≤ ‖x m‖ := by
      intro m
      have hmt : 0 ≤ (m : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) htpos.le
      simp only [hxdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (Nat.cast_nonneg _) hmt)]
      gcongr
      linarith
    have hT : ∀ m : ℕ, p (∑ j, G.psi β (w j * x m) • a j) ≤ C' / (N * ‖u‖) := by
      intro m
      calc _ ≤ C' / ‖x m‖ := H _ (hx₁.trans (hxn m))
        _ ≤ C' / (N * ‖u‖) := div_le_div_of_nonneg_left hC' (mul_pos hNpos hunorm) (hxn m)
    set coef : Fin s → ℂ := fun j =>
      ∑ m ∈ Finset.range N, G.psi β (-(w j0) * x m) * G.psi β (w j * x m) with hcoef
    have hid : ∑ m ∈ Finset.range N, G.psi β (-(w j0) * x m) • ∑ j, G.psi β (w j * x m) • a j =
        ∑ j, coef j • a j := by
      simp only [Finset.smul_sum, smul_smul, hcoef, Finset.sum_smul]
      exact Finset.sum_comm
    have hc0 : coef j0 = N := by
      have h0 : c j0 = 0 := by simp only [hcdef, sub_self, mul_zero]
      simp only [hcoef, hpsi, h0, zero_mul, Complex.zero_re, Complex.ofReal_zero, mul_zero,
        Complex.exp_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hcj : ∀ j ∈ Finset.univ.erase j0, ‖coef j‖ ≤ 2 / ‖q j - 1‖ := by
      intro j hj
      have hterm : ∀ m : ℕ, G.psi β (-(w j0) * x m) * G.psi β (w j * x m) =
          Complex.exp (Complex.I * (((N : ℝ) * (c j * u).re : ℝ) : ℂ)) * q j ^ m := by
        intro m
        rw [hpsi, show c j * x m = (((N : ℝ) + m * t : ℝ) : ℂ) * (c j * u) by simp only [hxdef]; ring,
          Complex.re_ofReal_mul]
        simp only [hqdef]
        rw [← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      simp only [hcoef, hterm, ← Finset.mul_sum, norm_mul, nexp, one_mul]
      exact geom_bound (q j) (hqn j) (hq1 j hj) N
    have hsplit : ∑ j, coef j • a j = coef j0 • a j0 + ∑ j ∈ Finset.univ.erase j0, coef j • a j :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ j0)).symm
    have hpa : (N : ℝ) * p (a j0) ≤ N * (C' / (N * ‖u‖)) + Kc := by
      have e1 : (N : ℝ) * p (a j0) = p (coef j0 • a j0) := by
        rw [hc0, map_smul_eq_mul]
        simp
      rw [e1]
      have e2 : coef j0 • a j0 =
          (∑ m ∈ Finset.range N, G.psi β (-(w j0) * x m) • ∑ j, G.psi β (w j * x m) • a j) -
            ∑ j ∈ Finset.univ.erase j0, coef j • a j := by
        rw [hid, hsplit]
        abel
      rw [e2]
      refine (map_sub_le_add p _ _).trans (add_le_add ?_ ?_)
      · refine (p_sum_le p _ _).trans ?_
        calc ∑ m ∈ Finset.range N, p (G.psi β (-(w j0) * x m) • ∑ j, G.psi β (w j * x m) • a j)
            = ∑ m ∈ Finset.range N, p (∑ j, G.psi β (w j * x m) • a j) := by
              refine Finset.sum_congr rfl fun m _ => ?_
              rw [map_smul_eq_mul, hpsin, one_mul]
          _ ≤ ∑ m ∈ Finset.range N, C' / (N * ‖u‖) := Finset.sum_le_sum fun m _ => hT m
          _ = N * (C' / (N * ‖u‖)) := by simp
      · refine (p_sum_le p _ _).trans ?_
        refine Finset.sum_le_sum fun j hj => ?_
        rw [map_smul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hcj j hj) (apply_nonneg p _)
    have e3 : (N : ℝ) * (C' / (N * ‖u‖)) = C' / ‖u‖ := by
      field_simp
    rw [e3] at hpa
    rw [le_div_iff₀ hNpos]
    linarith
  have hnn := apply_nonneg p (a j0)
  by_contra hne
  have hδ : 0 < p (a j0) := lt_of_le_of_ne hnn (Ne.symm hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (|x₁| / ‖u‖) ((C' / ‖u‖ + Kc) / p (a j0)))
  have hN1 : |x₁| / ‖u‖ < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : (C' / ‖u‖ + Kc) / p (a j0) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (abs_nonneg _) hunorm.le) hN1
  have hx₁ : x₁ ≤ N * ‖u‖ := by
    have h2 := (div_lt_iff₀ hunorm).1 hN1
    linarith [le_abs_self x₁]
  have hb := hmain N (by exact_mod_cast hNpos) hx₁
  rw [div_lt_iff₀ hδ] at hN2
  rw [le_div_iff₀ hNpos] at hb
  nlinarith

/- English proof (translation)
Introduce `_` and use `averaging_vanishes`.
-/
theorem averaging_of_parts : C6.AveragingOfParts := fun _ => averaging_vanishes

end Formalism.FourierDecayAlt.P
