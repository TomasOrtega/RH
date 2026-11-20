import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Complexify
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionDiagonalIdentityStatement
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

open Polynomial

variable {m : ℕ}

noncomputable def pfPoly (x : ℝ) (r d' : Fin m → ℝ) : ℝ[X] :=
  (X - C x) * ∏ j, (X - C (d' j)) + ∑ j, C (r j) * ∏ k ∈ univ.erase j, (X - C (d' k))

/- English proof (translation)
Establish `hj : ∀ j, (∏ k ∈ univ.erase j, (s - d' k)) = (∏ k, (s - d' k)) / (s - d' j)`. Introduce `j`. Rewrite using `[eq_div_iff (hs j), mul_comm, Finset.mul_prod_erase univ (fun k => s - d' k) (mem_univ j)]`. Simplify using `only [pfPoly, eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_prod, eval_finset_sum]`. Rewrite using `[mul_add, Finset.mul_sum, mul_comm]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hj j]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma eval_pfPoly (x : ℝ) (r d' : Fin m → ℝ) (s : ℝ) (hs : ∀ j, s - d' j ≠ 0) :
    (pfPoly x r d').eval s =
      (∏ j, (s - d' j)) * (s - x + ∑ j, r j / (s - d' j)) := by
  have hj : ∀ j, (∏ k ∈ univ.erase j, (s - d' k)) = (∏ k, (s - d' k)) / (s - d' j) := by
    intro j
    rw [eq_div_iff (hs j), mul_comm, Finset.mul_prod_erase univ (fun k => s - d' k) (mem_univ j)]
  simp only [pfPoly, eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_prod, eval_finset_sum]
  rw [mul_add, Finset.mul_sum, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hj j]
  ring

/- English proof (translation)
Establish `hdd' : ∀ i j, d i - d' j ≠ 0`. Introduce `i j hij`. Establish `: Sum.elim d d' (Sum.inl i) = Sum.elim d d' (Sum.inr j)`. Simplify using `using sub_eq_zero.mp hij`. Conclude with `absurd (h this) (by simp)`.

Establish `hinj : Function.Injective d` using `fun a b hab => by`. Establish `: Sum.elim d d' (Sum.inl a) = Sum.elim d d' (Sum.inl b)` using `by simpa using hab`. Simplify using `using h this`. Establish `hP : (∏ i, (X - C (d i)) : ℝ[X]).Monic` using `monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _`. Establish `hQ : (∏ j, (X - C (d' j)) : ℝ[X]).Monic` using `monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _`.

Establish `hPd : (∏ i, (X - C (d i)) : ℝ[X]).degree = (m + 1 : ℕ)`. Rewrite using `[degree_eq_natDegree hP.ne_zero, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]`. Simplify using the standard rewrite rules. Establish `hQd : (∏ j, (X - C (d' j)) : ℝ[X]).natDegree = m`. Rewrite using `[natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]`.

Simplify using the standard rewrite rules. Establish `hL : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).Monic` using `(monic_X_sub_C _).mul hQ`. Establish `hLd : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).degree = (m + 1 : ℕ)`. Rewrite using `[degree_eq_natDegree hL.ne_zero, (monic_X_sub_C _).natDegree_mul hQ, hQd]`. Simplify using `[add_comm]`.

Establish `hsub : ((∏ i, (X - C (d i)) : ℝ[X]) - (X - C (pfX d d')) * ∏ j, (X - C (d' j))).degree < ((m + 1 : ℕ) : WithBot ℕ)`. Use `degree_sub_lt (hPd.trans hLd.symm) hP.ne_zero (hP.leadingCoeff.trans hL.leadingCoeff.symm)` as an intermediate fact. Rewrite `this` using `[hPd]`. Then use the resulting hypothesis. Establish `hterm : ∀ j : Fin m, (C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).degree < ((m + 1 : ℕ) : WithBot ℕ)`. Introduce `j`.

Rewrite using `[← smul_eq_C_mul]`. Use `(degree_smul_le _ _).trans_lt ?_` and prove the remaining obligations. Establish `hM : (∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).Monic` using `monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _`. Rewrite using `[degree_eq_natDegree hM.ne_zero, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]`. Simplify using the standard rewrite rules.

Conclude with `(by omega : m - 1 < m + 1)` after adjusting the coercions. Establish `hsum : (∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).degree < ((m + 1 : ℕ) : WithBot ℕ)`. Use `(degree_sum_le _ _).trans_lt ?_` and prove the remaining obligations. Conclude with `(Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => hterm j`. Establish `hdeg : ((∏ i, (X - C (d i)) : ℝ[X]) - pfPoly (pfX d d') (pfR d d') d').degree < (univ : Finset (Fin (m + 1))).card`.

Establish `: ((∏ i, (X - C (d i)) : ℝ[X]) - pfPoly (pfX d d') (pfR d d') d') = ((∏ i, (X - C (d i)) : ℝ[X]) - (X - C (pfX d d')) * ∏ j, (X - C (d' j))) - ∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k))`. Simplify using `only [pfPoly]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Simplify using `using (degree_sub_le _ _).trans_lt (max_lt hsub hsum)`.

Use `sub_eq_zero.mp (eq_zero_of_degree_lt_of_eval_index_eq_zero univ hinj.injOn hdeg ?_)` and prove the remaining obligations. Introduce `i _`. Establish `hz` using `GlobalTheory.T.partial_fraction_diagonal_identity d d' h i`. Rewrite using `[eval_sub, eval_pfPoly _ _ _ _ (hdd' i), hz, mul_zero, eval_prod]`. Simplify using `only [eval_sub, eval_X, eval_C, sub_zero]`.

Conclude with `Finset.prod_eq_zero (mem_univ i) (sub_self _)`.
-/
lemma prod_eq_pfPoly (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (h : Function.Injective (Sum.elim d d')) :
    (∏ i, (X - C (d i)) : ℝ[X]) = pfPoly (pfX d d') (pfR d d') d' := by
  have hdd' : ∀ i j, d i - d' j ≠ 0 := by
    intro i j hij
    have : Sum.elim d d' (Sum.inl i) = Sum.elim d d' (Sum.inr j) := by
      simpa using sub_eq_zero.mp hij
    exact absurd (h this) (by simp)
  have hinj : Function.Injective d := fun a b hab => by
    have : Sum.elim d d' (Sum.inl a) = Sum.elim d d' (Sum.inl b) := by simpa using hab
    simpa using h this
  have hP : (∏ i, (X - C (d i)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hQ : (∏ j, (X - C (d' j)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hPd : (∏ i, (X - C (d i)) : ℝ[X]).degree = (m + 1 : ℕ) := by
    rw [degree_eq_natDegree hP.ne_zero, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp
  have hQd : (∏ j, (X - C (d' j)) : ℝ[X]).natDegree = m := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp
  have hL : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).Monic := (monic_X_sub_C _).mul hQ
  have hLd : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).degree = (m + 1 : ℕ) := by
    rw [degree_eq_natDegree hL.ne_zero, (monic_X_sub_C _).natDegree_mul hQ, hQd]
    simp [add_comm]
  have hsub : ((∏ i, (X - C (d i)) : ℝ[X]) -
      (X - C (pfX d d')) * ∏ j, (X - C (d' j))).degree < ((m + 1 : ℕ) : WithBot ℕ) := by
    have := degree_sub_lt (hPd.trans hLd.symm) hP.ne_zero (hP.leadingCoeff.trans hL.leadingCoeff.symm)
    rwa [hPd] at this
  have hterm : ∀ j : Fin m, (C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).degree
      < ((m + 1 : ℕ) : WithBot ℕ) := by
    intro j
    rw [← smul_eq_C_mul]
    refine (degree_smul_le _ _).trans_lt ?_
    have hM : (∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).Monic :=
      monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
    rw [degree_eq_natDegree hM.ne_zero, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp
    exact_mod_cast (by omega : m - 1 < m + 1)
  have hsum : (∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).degree
      < ((m + 1 : ℕ) : WithBot ℕ) := by
    refine (degree_sum_le _ _).trans_lt ?_
    exact (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => hterm j
  have hdeg : ((∏ i, (X - C (d i)) : ℝ[X]) - pfPoly (pfX d d') (pfR d d') d').degree
      < (univ : Finset (Fin (m + 1))).card := by
    have : ((∏ i, (X - C (d i)) : ℝ[X]) - pfPoly (pfX d d') (pfR d d') d') =
        ((∏ i, (X - C (d i)) : ℝ[X]) - (X - C (pfX d d')) * ∏ j, (X - C (d' j))) -
          ∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) := by
      simp only [pfPoly]; ring
    rw [this]
    simpa using (degree_sub_le _ _).trans_lt (max_lt hsub hsum)
  refine sub_eq_zero.mp (eq_zero_of_degree_lt_of_eval_index_eq_zero univ hinj.injOn hdeg ?_)
  intro i _
  have hz := GlobalTheory.T.partial_fraction_diagonal_identity d d' h i
  rw [eval_sub, eval_pfPoly _ _ _ _ (hdd' i), hz, mul_zero, eval_prod]
  simp only [eval_sub, eval_X, eval_C, sub_zero]
  exact Finset.prod_eq_zero (mem_univ i) (sub_self _)

/- English proof (translation)
Introduce `m d d' h i`. Establish `hdd' : ∀ j, d i - d' j ≠ 0`. Introduce `j hij`. Establish `: Sum.elim d d' (Sum.inl i) = Sum.elim d d' (Sum.inr j)`. Simplify using `using sub_eq_zero.mp hij`.

Conclude with `absurd (h this) (by simp)`. Use `set Q : ℝ[X] := ∏ j, (X - C (d' j)) with hQdef`. Establish `hQe : ∀ s, Q.eval s = ∏ j, (s - d' j)` using `fun s => by simp [hQdef, eval_prod]`. Establish `hQ0 : Q.eval (d i) ≠ 0`. Rewrite using `[hQe]`.

Conclude with `Finset.prod_ne_zero_iff.2 fun j _ => hdd' j`. Set `f : ℝ → ℝ` to `fun s => s - pfX d d' + ∑ j, pfR d d' j / (s - d' j)`. Establish `hterm : ∀ j ∈ (univ : Finset (Fin m)), HasDerivAt (fun s => pfR d d' j / (s - d' j)) (-(pfR d d' j / (d i - d' j) ^ 2)) (d i)`. Introduce `j _`. Establish `h1 : HasDerivAt (fun s : ℝ => s - d' j) 1 (d i)` using `(hasDerivAt_id _).sub_const _`.

Establish `h2` using `(hasDerivAt_const (d i) (pfR d d' j)).fun_div h1 (hdd' j)`. Conclude with `h2.congr_deriv (by simp [neg_div])`. Establish `hf : HasDerivAt f (1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2) (d i)`. Establish `h3` using `HasDerivAt.fun_sum hterm`. Establish `h4` using `((hasDerivAt_id (d i)).sub_const (pfX d d')).fun_add h3`.

Conclude with `h4.congr_deriv (by simp [sub_eq_add_neg])`. Establish `hf0 : f (d i) = 0` using `GlobalTheory.T.partial_fraction_diagonal_identity d d' h i`. Establish `hprod : HasDerivAt (fun s => Q.eval s * f s) (Q.eval (d i) * (1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2)) (d i)`. Use `(Q.hasDerivAt (d i)).fun_mul hf` as an intermediate fact. Conclude with `this.congr_deriv (by simp [hf0])`.

Use `set P : ℝ[X] := ∏ k, (X - C (d k)) with hPdef`. Establish `hPfac : P = (X - C (d i)) * ∏ k ∈ univ.erase i, (X - C (d k))` using `(Finset.mul_prod_erase univ (fun k => (X - C (d k) : ℝ[X])) (mem_univ i)).symm`. Establish `hPder : P.derivative.eval (d i) = ∏ k ∈ univ.erase i, (d i - d k)`. Rewrite using `[hPfac, derivative_mul]`. Simplify using `[eval_prod]`.

Establish `hev : (fun s => P.eval s) =ᶠ[nhds (d i)] fun s => Q.eval s * f s`. Establish `hopen : ∀ᶠ s in nhds (d i), ∀ j, s - d' j ≠ 0`. Use `Filter.eventually_all.2 fun j => ?_` and prove the remaining obligations. Establish `hc : ContinuousAt (fun s : ℝ => s - d' j) (d i)` using `by fun_prop`. Conclude with `hc.eventually_ne (hdd' j)`.

Use `filter_upwards [hopen] with s hs`. Rewrite using `[hPdef, prod_eq_pfPoly d d' h, eval_pfPoly _ _ _ _ hs, hQe]`. Establish `huniq` using `(P.hasDerivAt (d i)).unique (hprod.congr_of_eventuallyEq hev)`. Rewrite `huniq` using `[hPder]`. Unfold `pfD`.

Rewrite using `[← hQe (d i), huniq]`. Clear the denominators using the available nonvanishing facts.
-/
theorem pfDer : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ),
    Function.Injective (Sum.elim d d') →
      ∀ i, 1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2 = pfD d d' i := by
  intro m d d' h i
  have hdd' : ∀ j, d i - d' j ≠ 0 := by
    intro j hij
    have : Sum.elim d d' (Sum.inl i) = Sum.elim d d' (Sum.inr j) := by
      simpa using sub_eq_zero.mp hij
    exact absurd (h this) (by simp)
  set Q : ℝ[X] := ∏ j, (X - C (d' j)) with hQdef
  have hQe : ∀ s, Q.eval s = ∏ j, (s - d' j) := fun s => by simp [hQdef, eval_prod]
  have hQ0 : Q.eval (d i) ≠ 0 := by
    rw [hQe]; exact Finset.prod_ne_zero_iff.2 fun j _ => hdd' j

  let f : ℝ → ℝ := fun s => s - pfX d d' + ∑ j, pfR d d' j / (s - d' j)
  have hterm : ∀ j ∈ (univ : Finset (Fin m)), HasDerivAt (fun s => pfR d d' j / (s - d' j))
      (-(pfR d d' j / (d i - d' j) ^ 2)) (d i) := by
    intro j _
    have h1 : HasDerivAt (fun s : ℝ => s - d' j) 1 (d i) := (hasDerivAt_id _).sub_const _
    have h2 := (hasDerivAt_const (d i) (pfR d d' j)).fun_div h1 (hdd' j)
    exact h2.congr_deriv (by simp [neg_div])
  have hf : HasDerivAt f (1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2) (d i) := by
    have h3 := HasDerivAt.fun_sum hterm
    have h4 := ((hasDerivAt_id (d i)).sub_const (pfX d d')).fun_add h3
    exact h4.congr_deriv (by simp [sub_eq_add_neg])
  have hf0 : f (d i) = 0 := GlobalTheory.T.partial_fraction_diagonal_identity d d' h i
  have hprod : HasDerivAt (fun s => Q.eval s * f s)
      (Q.eval (d i) * (1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2)) (d i) := by
    have := (Q.hasDerivAt (d i)).fun_mul hf
    exact this.congr_deriv (by simp [hf0])

  set P : ℝ[X] := ∏ k, (X - C (d k)) with hPdef
  have hPfac : P = (X - C (d i)) * ∏ k ∈ univ.erase i, (X - C (d k)) :=
    (Finset.mul_prod_erase univ (fun k => (X - C (d k) : ℝ[X])) (mem_univ i)).symm
  have hPder : P.derivative.eval (d i) = ∏ k ∈ univ.erase i, (d i - d k) := by
    rw [hPfac, derivative_mul]
    simp [eval_prod]
  have hev : (fun s => P.eval s) =ᶠ[nhds (d i)] fun s => Q.eval s * f s := by
    have hopen : ∀ᶠ s in nhds (d i), ∀ j, s - d' j ≠ 0 := by
      refine Filter.eventually_all.2 fun j => ?_
      have hc : ContinuousAt (fun s : ℝ => s - d' j) (d i) := by fun_prop
      exact hc.eventually_ne (hdd' j)
    filter_upwards [hopen] with s hs
    rw [hPdef, prod_eq_pfPoly d d' h, eval_pfPoly _ _ _ _ hs, hQe]
  have huniq := (P.hasDerivAt (d i)).unique (hprod.congr_of_eventuallyEq hev)
  rw [hPder] at huniq
  unfold pfD
  rw [← hQe (d i), huniq]
  field_simp

end GlobalTheory.CompanionTheory.RgHeFrame
