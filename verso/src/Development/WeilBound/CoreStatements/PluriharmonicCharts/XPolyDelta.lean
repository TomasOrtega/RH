import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace PositivityTheory.Xgp.poly_delta

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C a => simp [toWt]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p n hp => simp only [map_mul, hp, toWt, aeval_X] at *`. Rewrite using `[eval_X]`.
-/
theorem eval_toWt {Ψ : Type} {N : ℕ} (lam : Ψ × Fin N → ℝ) (Q : MvPolynomial (Ψ × Fin N) ℝ) :
    eval lam (toWt Q) = eval (fun p => eval lam (gapX p)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [toWt]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, toWt, aeval_X] at *; rw [eval_X]

/- English proof (translation)
Proceed by induction on `l, h using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ l h ih => rw [Finset.sum_Ico_succ_top h, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tele_nat (f : ℕ → ℝ) (i l : ℕ) (h : i ≤ l) :
    ∑ m ∈ Finset.Ico i l, (f m - f (m + 1)) = f i - f l := by
  induction l, h using Nat.le_induction with
  | base => simp
  | succ l h ih => rw [Finset.sum_Ico_succ_top h, ih]; ring

/- English proof (translation)
Set `f : ℕ → ℝ` to `fun n => if hn : n < N then lam (τ, ⟨n, hn⟩) else 0`. Establish `hg : ∀ m : Fin N, eval lam (gapX (τ, m)) = f m - f ((m : ℕ) + 1)`. Introduce `m`. Distinguish the cases in `hm : (m : ℕ) + 1 < N`. Simplify using `[gapX, f, hm, m.isLt]`.

Simplify using `[gapX, f, hm, m.isLt]`. Rewrite using `[Finset.sum_congr rfl (fun m _ => hg m)]`. Rewrite using `[show ∑ m ∈ Finset.Ico i l, (f m - f ((m : ℕ) + 1)) = ∑ n ∈ Finset.Ico (i : ℕ) (l : ℕ), (f n - f (n + 1)) by`. Rewrite using `[← Fin.map_valEmbedding_Ico, Finset.sum_map]`. Use the proof step `rfl]`.

Rewrite using `[tele_nat f i l (by exact_mod_cast h)]`. Simplify using `[f, i.isLt, l.isLt]`.
-/
theorem tele {Ψ : Type} {N : ℕ} (lam : Ψ × Fin N → ℝ) (τ : Ψ) (i l : Fin N) (h : i ≤ l) :
    ∑ m ∈ Finset.Ico i l, eval lam (gapX (τ, m)) = lam (τ, i) - lam (τ, l) := by
  classical
  let f : ℕ → ℝ := fun n => if hn : n < N then lam (τ, ⟨n, hn⟩) else 0
  have hg : ∀ m : Fin N, eval lam (gapX (τ, m)) = f m - f ((m : ℕ) + 1) := by
    intro m
    by_cases hm : (m : ℕ) + 1 < N
    · simp [gapX, f, hm, m.isLt]
    · simp [gapX, f, hm, m.isLt]
  rw [Finset.sum_congr rfl (fun m _ => hg m)]
  rw [show ∑ m ∈ Finset.Ico i l, (f m - f ((m : ℕ) + 1))
      = ∑ n ∈ Finset.Ico (i : ℕ) (l : ℕ), (f n - f (n + 1)) by
    rw [← Fin.map_valEmbedding_Ico, Finset.sum_map]
    rfl]
  rw [tele_nat f i l (by exact_mod_cast h)]
  simp [f, i.isLt, l.isLt]

end PositivityTheory.Xgp.poly_delta

/- English proof (translation)
Introduce `Ψ _ _ N Q v h`. Prove the components needed by the constructor for the conclusion. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `lam`. Rewrite using `[PositivityTheory.Xgp.poly_delta.eval_toWt, h]`.

Simplify using `only [antisymDelta, map_mul, map_prod, eval_C, map_sub, eval_X]`. Use `congr 1`. Use `Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun l hl => ?_` and prove the remaining obligations. Conclude with `PositivityTheory.Xgp.poly_delta.tele lam τ i l (Finset.mem_Ioi.mp hl).le`. Simplify using `only [antisymDelta, map_prod, map_sub, eval_X, rhoWt]`.

Use `Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun l hl => ?_` and prove the remaining obligations. Establish `: (i : ℕ) < l` using `Fin.lt_def.mp (Finset.mem_Ioi.mp hl)`. Establish `: ((i : ℕ) : ℝ) < (l : ℕ)` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem PositivityTheory.Xgp.t_poly_delta : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (Q : MvPolynomial (Ψ × Fin N) ℝ) (v : ℝ), (∀ c : Ψ × Fin N → ℝ, eval c Q = v * ∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, c (τ, m)) → toWt Q = C v * antisymDelta Ψ N ∧ 0 < eval (rhoWt Ψ N) (antisymDelta Ψ N) := by
  intro Ψ _ _ N Q v h
  constructor
  · apply MvPolynomial.funext
    intro lam
    rw [PositivityTheory.Xgp.poly_delta.eval_toWt, h]
    simp only [antisymDelta, map_mul, map_prod, eval_C, map_sub, eval_X]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ =>
      Finset.prod_congr rfl fun l hl => ?_
    exact PositivityTheory.Xgp.poly_delta.tele lam τ i l (Finset.mem_Ioi.mp hl).le
  · simp only [antisymDelta, map_prod, map_sub, eval_X, rhoWt]
    refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun l hl => ?_
    have : (i : ℕ) < l := Fin.lt_def.mp (Finset.mem_Ioi.mp hl)
    have : ((i : ℕ) : ℝ) < (l : ℕ) := by exact_mod_cast this
    linarith
