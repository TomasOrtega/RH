import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix GlobalTheory.AlgWtHW

namespace GlobalTheory

/- English proof (translation)
Simplify using `only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem eval_transvection_polynomial_X_entry {n : ℕ} (i j : Fin n) (c : ℂ) (a b : Fin n) :
    Polynomial.eval c ((transvection i j (Polynomial.X : Polynomial ℂ)) a b) = transvection i j c a b := by
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all

/- English proof (translation)
Simplify using `only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem eval_transvection_polynomial_neg_X_entry {n : ℕ} (i j : Fin n) (c : ℂ) (a b : Fin n) :
    Polynomial.eval c ((transvection i j (-Polynomial.X : Polynomial ℂ)) a b) = transvection i j (-c) a b := by
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p v hp => simp [hp]`.
-/
theorem eval_aeval_mv {σ : Type} (g : σ → Polynomial ℂ) (Q : MvPolynomial σ ℂ) (s : ℂ) :
    Polynomial.eval s (MvPolynomial.aeval g Q) = MvPolynomial.eval (fun v => (g v).eval s) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp => simp [hp]

/- English proof (translation)
Introduce `n ι _ _ Φ hΦ i j hij`. Use `choose Q hQ using hΦ.poly`. Set `g : (Fin n × Fin n) ⊕ (Fin n × Fin n) → Polynomial ℂ` to `Sum.elim (fun p => transvection i j (Polynomial.X : Polynomial ℂ) p.1 p.2) (fun p => transvection i j (-Polynomial.X : Polynomial ℂ) p.1 p.2)`. Use `⟨fun a b => MvPolynomial.aeval g (Q a b), ?_⟩` and prove the remaining obligations. Introduce `s B hB a b`.

Establish `hinv : (B⁻¹).val = transvection i j (-s)`. Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[hB]`. Use `transvection_mul_transvection_same (R := ℂ) i j hij s (-s)` as an intermediate fact. Rewrite using `[this, add_neg_cancel, transvection_zero]`.

Rewrite using `[hQ a b B, eval_aeval_mv]`. Use `congr 2`. Use function extensionality and compare the values at `v`. Break down `v with p | p` into its components or cases. Simplify using `[g, eval_transvection_polynomial_X_entry, hB]`.

Simplify using `[g, eval_transvection_polynomial_neg_X_entry, hinv]`.
-/
theorem polyRep_transvection_entries_poly :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ →
      ∀ (i j : Fin n), i ≠ j → ∃ P : ι → ι → Polynomial ℂ, ∀ (s : ℂ) (B : GL (Fin n) ℂ),
        B.val = transvection i j s → ∀ a b, Φ B a b = (P a b).eval s := by
  intro n ι _ _ Φ hΦ i j hij
  choose Q hQ using hΦ.poly
  let g : (Fin n × Fin n) ⊕ (Fin n × Fin n) → Polynomial ℂ :=
    Sum.elim (fun p => transvection i j (Polynomial.X : Polynomial ℂ) p.1 p.2)
      (fun p => transvection i j (-Polynomial.X : Polynomial ℂ) p.1 p.2)
  refine ⟨fun a b => MvPolynomial.aeval g (Q a b), ?_⟩
  intro s B hB a b
  have hinv : (B⁻¹).val = transvection i j (-s) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hB]
    have := transvection_mul_transvection_same (R := ℂ) i j hij s (-s)
    rw [this, add_neg_cancel, transvection_zero]
  rw [hQ a b B, eval_aeval_mv]
  congr 2
  funext v
  rcases v with p | p
  · simp [g, eval_transvection_polynomial_X_entry, hB]
  · simp [g, eval_transvection_polynomial_neg_X_entry, hinv]

end GlobalTheory
