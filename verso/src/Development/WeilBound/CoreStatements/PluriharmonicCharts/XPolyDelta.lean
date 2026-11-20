import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace PositivityTheory.Xgp.poly_delta

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem eval_toWt {Ψ : Type} {N : ℕ} (lam : Ψ × Fin N → ℝ) (Q : MvPolynomial (Ψ × Fin N) ℝ) :
    eval lam (toWt Q) = eval (fun p => eval lam (gapX p)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [toWt]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, toWt, aeval_X] at *; rw [eval_X]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tele_nat (f : ℕ → ℝ) (i l : ℕ) (h : i ≤ l) :
    ∑ m ∈ Finset.Ico i l, (f m - f (m + 1)) = f i - f l := by
  induction l, h using Nat.le_induction with
  | base => simp
  | succ l h ih => rw [Finset.sum_Ico_succ_top h, ih]; ring

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
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
