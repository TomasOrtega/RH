import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial

noncomputable section

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p n hp`. Simplify using `only [pderiv_mul, map_add, hp, pderiv_X, Pi.single_apply]`.

Apply the tactic sequence `split_ifs <;> (try simp) <;> ring`.
-/
theorem pderiv_comm_two_variables (i j : Fin 2) (P : MvPolynomial (Fin 2) ℝ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
    simp only [pderiv_mul, map_add, hp, pderiv_X, Pi.single_apply]
    split_ifs <;> (try simp) <;> ring

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using `only [eval_C, pderiv_C, map_zero]`. Conclude with `hasDerivAt_const s a`. Consider the case `add p q hp hq`.

Simplify using `only [map_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p n hp`. Establish `hX : HasDerivAt (fun u : ℝ => (![u, t] : Fin 2 → ℝ) n) (eval ![s, t] (pderiv 0 (X n))) s` using `by fin_cases n`. Simplify using `using hasDerivAt_id' s`.

Simplify using `using hasDerivAt_const s t`. Simplify using `only [map_mul, eval_X, pderiv_mul, map_add]`. Conclude with `hp.mul hX`.
-/
theorem hasDerivAt_eval_fst (P : MvPolynomial (Fin 2) ℝ) (s t : ℝ) :
    HasDerivAt (fun u => eval ![u, t] P) (eval ![s, t] (pderiv 0 P)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero]
    exact hasDerivAt_const s a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p n hp =>
    have hX : HasDerivAt (fun u : ℝ => (![u, t] : Fin 2 → ℝ) n) (eval ![s, t] (pderiv 0 (X n))) s := by
      fin_cases n
      · simpa using hasDerivAt_id' s
      · simpa using hasDerivAt_const s t
    simp only [map_mul, eval_X, pderiv_mul, map_add]
    exact hp.mul hX

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using `only [eval_C, pderiv_C, map_zero]`. Conclude with `hasDerivAt_const t a`. Consider the case `add p q hp hq`.

Simplify using `only [map_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p n hp`. Establish `hX : HasDerivAt (fun u : ℝ => (![s, u] : Fin 2 → ℝ) n) (eval ![s, t] (pderiv 1 (X n))) t` using `by fin_cases n`. Simplify using `using hasDerivAt_const t s`.

Simplify using `using hasDerivAt_id' t`. Simplify using `only [map_mul, eval_X, pderiv_mul, map_add]`. Conclude with `hp.mul hX`.
-/
theorem hasDerivAt_eval_snd (P : MvPolynomial (Fin 2) ℝ) (s t : ℝ) :
    HasDerivAt (fun u => eval ![s, u] P) (eval ![s, t] (pderiv 1 P)) t := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero]
    exact hasDerivAt_const t a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p n hp =>
    have hX : HasDerivAt (fun u : ℝ => (![s, u] : Fin 2 → ℝ) n) (eval ![s, t] (pderiv 1 (X n))) t := by
      fin_cases n
      · simpa using hasDerivAt_const t s
      · simpa using hasDerivAt_id' t
    simp only [map_mul, eval_X, pderiv_mul, map_add]
    exact hp.mul hX

/- English proof (translation)
The claim follows from `continuous_iff_continuousAt.2 fun u => (hasDerivAt_eval_fst P u t).continuousAt`.
-/
theorem continuous_eval_fst (P : MvPolynomial (Fin 2) ℝ) (t : ℝ) :
    Continuous fun u => eval ![u, t] P :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_eval_fst P u t).continuousAt

/- English proof (translation)
The claim follows from `continuous_iff_continuousAt.2 fun u => (hasDerivAt_eval_snd P s u).continuousAt`.
-/
theorem continuous_eval_snd (P : MvPolynomial (Fin 2) ℝ) (s : ℝ) :
    Continuous fun u => eval ![s, u] P :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_eval_snd P s u).continuousAt

/- English proof (translation)
The claim follows from `intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_eval_fst P u t) ((continuous_eval_fst _ t).intervalIntegrable a b)`.
-/
theorem integral_eval_pderiv_fst (P : MvPolynomial (Fin 2) ℝ) (t a b : ℝ) :
    ∫ u in a..b, eval ![u, t] (pderiv 0 P) = eval ![b, t] P - eval ![a, t] P :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_eval_fst P u t)
    ((continuous_eval_fst _ t).intervalIntegrable a b)

/- English proof (translation)
The claim follows from `intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_eval_snd P s u) ((continuous_eval_snd _ s).intervalIntegrable a b)`.
-/
theorem integral_eval_pderiv_snd (P : MvPolynomial (Fin 2) ℝ) (s a b : ℝ) :
    ∫ u in a..b, eval ![s, u] (pderiv 1 P) = eval ![s, b] P - eval ![s, a] P :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_eval_snd P s u)
    ((continuous_eval_snd _ s).intervalIntegrable a b)

/- English proof (translation)
Unfold `gKernel`. Simplify using `only [map_sum, map_sub, map_mul, map_pow, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]`. Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Establish `hj' : j < k` using `Finset.mem_range.1 hj`. Establish `h : 2 * j + 1 + (2 * k - 1 - 2 * j) = 2 * j + (2 * k - 2 * j)` using `by omega`.

Rewrite using `[← pow_add, ← pow_add, h, sub_self]`.
-/
theorem gKernel_eval_diag (k : ℕ) (c : ℝ) : eval ![c, c] (gKernel ℝ k) = 0 := by
  unfold gKernel
  simp only [map_sum, map_sub, map_mul, map_pow, eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : j < k := Finset.mem_range.1 hj
  have h : 2 * j + 1 + (2 * k - 1 - 2 * j) = 2 * j + (2 * k - 2 * j) := by omega
  rw [← pow_add, ← pow_add, h, sub_self]

/- English proof (translation)
Introduce `k`. Take `⟨-, -, h11, hmm, h1m, hm1, hc⟩` from `h0 ℝ k`. Use `set G := gKernel ℝ k with hGdef`. Establish `hg : gMixed k = pderiv 0 (pderiv 1 G)` using `rfl`. Establish `hg' : gMixed k = pderiv 1 (pderiv 0 G)` using `by rw [hg, pderiv_comm_two_variables]`.

Establish `hI1 : ∀ t : ℝ, ∫ x in (-1 : ℝ)..1, eval ![x, t] (gMixed k) = eval ![1, t] (pderiv 1 G) - eval ![-1, t] (pderiv 1 G)` using `fun t => by`. Rewrite using `[hg]`. Conclude with `integral_eval_pderiv_fst _ _ _ _`. Establish `hI2 : ∀ s : ℝ, ∫ y in (-1 : ℝ)..1, eval ![s, y] (gMixed k) = eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)` using `fun s => by`. Rewrite using `[hg']`.

Conclude with `integral_eval_pderiv_snd _ _ _ _`. Establish `hsq : squareMean (gMixed k) = k`. Unfold `squareMean`. Simplify using `only [hI2]`. Rewrite using `[intervalIntegral.integral_sub ((continuous_eval_fst _ _).intervalIntegrable _ _) ((continuous_eval_fst _ _).intervalIntegrable _ _), integral_eval_pderiv_fst, integral_eval_pderiv_fst, h11, hmm, h1m, hm1]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨hsq, fun c => ?_⟩` and prove the remaining obligations. Take `⟨e1, e2, e3, e4⟩` from `hc c`. Establish `hdiag` using `gKernel_eval_diag k c`. Rewrite `hdiag` using `[← hGdef]`.

Unfold `doublyCentred`. Simplify using `only [hI1, hI2, hsq]`. Establish `hin : ∀ s : ℝ, ∫ t in (-1 : ℝ)..c, (eval ![s, t] (gMixed k) - 1 / 2 * (eval ![1, t] (pderiv 1 G) - eval ![-1, t] (pderiv 1 G)) - 1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) + (k : ℝ)) = (eval ![s, c] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) - 1 / 2 * ((eval …`. Introduce `s`. Rewrite using `[intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => eval ![s, t] (pderiv 0 G) - 1 / 2 * (eval ![1, t] G - eval ![-1, t] G) - (1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) - k) * t)]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `t _`. Use `((hasDerivAt_eval_snd (pderiv 0 G) s t).sub (((hasDerivAt_eval_snd G 1 t).sub (hasDerivAt_eval_snd G (-1) t)).const_mul (1 / 2))).sub ((hasDerivAt_id t).const_mul (1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) - k))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `u`.

Simplify using `only [Pi.sub_apply, id]`. Rewrite using `[hg']`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(((continuous_eval_snd _ s).sub (continuous_const.mul ((continuous_eval_snd _ 1).sub (continuous_eval_snd _ (-1))))).sub continuous_const |>.add continuous_const).intervalIntegrable _ _`. Simplify using `only [hin]`.

Rewrite using `[intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => eval ![s, c] G - eval ![s, -1] G - 1 / 2 * ((eval ![1, c] G - eval ![1, -1] G) - (eval ![-1, c] G - eval ![-1, -1] G)) * s - (c + 1) * (1 / 2 * (eval ![s, 1] G - eval ![s, -1] G) - k * s))]`. Take the linear combination `(1 / 2 : ℝ) * e1 + (1 / 2 : ℝ) * e2 - (1 / 2 : ℝ) * e3 - (1 / 2 : ℝ) * e4 + hdiag + (1 + c) / 2 * h1m - c * hmm + (1 + c) / 2 * hm1`. Introduce `s _`. Use `(((hasDerivAt_eval_fst G s c).sub (hasDerivAt_eval_fst G s (-1))).sub ((hasDerivAt_id s).const_mul (1 / 2 * ((eval ![1, c] G - eval ![1, -1] G) - (eval ![-1, c] G - eval ![-1, -1] G))))).sub ((((hasDerivAt_eval_fst G s 1).sub (hasDerivAt_eval_fst G s (-1))).const_mul (1 / 2)).sub …` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `u`. Simplify using `only [Pi.sub_apply, id]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `((((continuous_eval_fst _ c).sub (continuous_eval_fst _ (-1))).sub continuous_const).sub (continuous_const.mul ((continuous_const.mul ((continuous_eval_fst _ 1).sub (continuous_eval_fst _ (-1)))).sub continuous_const))).intervalIntegrable _ _`.
-/
theorem GHatIdentity.proof (h0 : GKernelIdentity.Statement) : GHatIdentity.Statement := by
  intro k
  obtain ⟨-, -, h11, hmm, h1m, hm1, hc⟩ := h0 ℝ k
  set G := gKernel ℝ k with hGdef
  have hg : gMixed k = pderiv 0 (pderiv 1 G) := rfl
  have hg' : gMixed k = pderiv 1 (pderiv 0 G) := by rw [hg, pderiv_comm_two_variables]
  have hI1 : ∀ t : ℝ, ∫ x in (-1 : ℝ)..1, eval ![x, t] (gMixed k) =
      eval ![1, t] (pderiv 1 G) - eval ![-1, t] (pderiv 1 G) := fun t => by
    rw [hg]; exact integral_eval_pderiv_fst _ _ _ _
  have hI2 : ∀ s : ℝ, ∫ y in (-1 : ℝ)..1, eval ![s, y] (gMixed k) =
      eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G) := fun s => by
    rw [hg']; exact integral_eval_pderiv_snd _ _ _ _
  have hsq : squareMean (gMixed k) = k := by
    unfold squareMean
    simp only [hI2]
    rw [intervalIntegral.integral_sub ((continuous_eval_fst _ _).intervalIntegrable _ _)
      ((continuous_eval_fst _ _).intervalIntegrable _ _), integral_eval_pderiv_fst,
      integral_eval_pderiv_fst, h11, hmm, h1m, hm1]
    ring
  refine ⟨hsq, fun c => ?_⟩
  obtain ⟨e1, e2, e3, e4⟩ := hc c
  have hdiag := gKernel_eval_diag k c
  rw [← hGdef] at hdiag
  unfold doublyCentred
  simp only [hI1, hI2, hsq]
  have hin : ∀ s : ℝ, ∫ t in (-1 : ℝ)..c,
      (eval ![s, t] (gMixed k) - 1 / 2 * (eval ![1, t] (pderiv 1 G) - eval ![-1, t] (pderiv 1 G)) -
        1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) + (k : ℝ)) =
      (eval ![s, c] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) -
        1 / 2 * ((eval ![1, c] G - eval ![1, -1] G) - (eval ![-1, c] G - eval ![-1, -1] G)) -
        (c + 1) * (1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) - k) := by
    intro s
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => eval ![s, t] (pderiv 0 G) - 1 / 2 * (eval ![1, t] G - eval ![-1, t] G) -
        (1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) - k) * t)]
    · ring
    · intro t _
      have := ((hasDerivAt_eval_snd (pderiv 0 G) s t).sub
        (((hasDerivAt_eval_snd G 1 t).sub (hasDerivAt_eval_snd G (-1) t)).const_mul (1 / 2))).sub
        ((hasDerivAt_id t).const_mul
          (1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) - k))
      convert this using 1
      · funext u; simp only [Pi.sub_apply, id]
      · rw [hg']; ring
    · exact (((continuous_eval_snd _ s).sub (continuous_const.mul
        ((continuous_eval_snd _ 1).sub (continuous_eval_snd _ (-1))))).sub
        continuous_const |>.add continuous_const).intervalIntegrable _ _
  simp only [hin]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => eval ![s, c] G - eval ![s, -1] G -
      1 / 2 * ((eval ![1, c] G - eval ![1, -1] G) - (eval ![-1, c] G - eval ![-1, -1] G)) * s -
      (c + 1) * (1 / 2 * (eval ![s, 1] G - eval ![s, -1] G) - k * s))]
  · linear_combination (1 / 2 : ℝ) * e1 + (1 / 2 : ℝ) * e2 - (1 / 2 : ℝ) * e3 - (1 / 2 : ℝ) * e4 +
      hdiag + (1 + c) / 2 * h1m - c * hmm + (1 + c) / 2 * hm1
  · intro s _
    have := (((hasDerivAt_eval_fst G s c).sub (hasDerivAt_eval_fst G s (-1))).sub
      ((hasDerivAt_id s).const_mul
        (1 / 2 * ((eval ![1, c] G - eval ![1, -1] G) - (eval ![-1, c] G - eval ![-1, -1] G))))).sub
      ((((hasDerivAt_eval_fst G s 1).sub (hasDerivAt_eval_fst G s (-1))).const_mul (1 / 2)).sub
        ((hasDerivAt_id s).const_mul (k : ℝ)) |>.const_mul (c + 1))
    convert this using 1
    · funext u
      simp only [Pi.sub_apply, id]
    · ring
  · exact ((((continuous_eval_fst _ c).sub (continuous_eval_fst _ (-1))).sub continuous_const).sub
      (continuous_const.mul ((continuous_const.mul ((continuous_eval_fst _ 1).sub
        (continuous_eval_fst _ (-1)))).sub continuous_const))).intervalIntegrable _ _

end

end GroundTheory.Heights₂.Heights.FlagBundles
