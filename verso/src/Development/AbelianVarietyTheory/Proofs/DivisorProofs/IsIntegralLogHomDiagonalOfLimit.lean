import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPolyCoeff

set_option autoImplicit false

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.DiagLimit

/- English proof (translation)
Introduce `C _ _ v d G κ _ _ U L hU hL hUL t h`. Take `⟨φ, h1, h2, h3⟩` from `GlobalTheory.IntegralEndLimit.integral_of_limit C v d G (U * Matrix.diagonal t * L) (fun r => by`. Take `⟨t', A, φ, hφ, hA, ht⟩` from `h r`. Use `⟨A, fun a b => ?_, φ, hφ.2.1, hφ.1, hφ.2.2⟩` and prove the remaining obligations. Establish `e1 : A * U = U * Matrix.diagonal t'`.

Use extensionality with `e ℓ`. Use `congrFun (hA ℓ) e` as an intermediate fact. Rewrite using `[Matrix.mul_diagonal, mul_comm]`. Conclude with `this`. Establish `e2 : A = U * Matrix.diagonal t' * L`.

Rewrite using `[← e1, Matrix.mul_assoc, hUL, Matrix.mul_one]`. Establish `e3 : (U * Matrix.diagonal t * L) a b - A a b = ∑ ℓ, U a ℓ * -(t' ℓ - t ℓ) * L ℓ b`. Rewrite using `[e2, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun ℓ _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_diagonal, Matrix.mul_diagonal]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3]`. Use `v.map_le_sum fun ℓ _ => ?_` and prove the remaining obligations. Rewrite using `[v.map_mul, v.map_mul, v.map_neg]`. Use `add_le_add (add_le_add (show (0 : WithTop ℝ) ≤ v (U a ℓ) from hU a ℓ) (ht ℓ)) (show (0 : WithTop ℝ) ≤ v (L ℓ b) from hL ℓ b)` as an intermediate fact.

Rewrite using `[zero_add, add_zero] at this)` and apply the resulting hypothesis. Conclude with `⟨φ, h2, h1, h3⟩`.
-/
theorem isIntHom_diagonal_of_limit :
    ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d : ℕ) (G : LogFGL v d) (κ : Type) [Fintype κ] [DecidableEq κ] (U : Matrix (Fin d) κ C) (L : Matrix κ (Fin d) C), (∀ a b, IsIntV v (U a b)) → (∀ a b, IsIntV v (L a b)) → U * L = 1 → ∀ t : κ → C, (∀ r : ℝ, ∃ (t' : κ → C) (A : Matrix (Fin d) (Fin d) C) (φ : Fin d → MvPowerSeries (Fin d) C), IsIntHom G G φ A ∧ (∀ ℓ, A.mulVec (fun e => U e ℓ) = t' ℓ • fun e => U e ℓ) ∧ ∀ ℓ, (r : WithTop ℝ) ≤ v (t' ℓ - t ℓ)) → ∃ φ, IsIntHom G G φ (U * Matrix.diagonal t * L) := by
  intro C _ _ v d G κ _ _ U L hU hL hUL t h
  obtain ⟨φ, h1, h2, h3⟩ := GlobalTheory.IntegralEndLimit.integral_of_limit C v d G
    (U * Matrix.diagonal t * L) (fun r => by
      obtain ⟨t', A, φ, hφ, hA, ht⟩ := h r
      refine ⟨A, fun a b => ?_, φ, hφ.2.1, hφ.1, hφ.2.2⟩
      have e1 : A * U = U * Matrix.diagonal t' := by
        ext e ℓ
        have := congrFun (hA ℓ) e
        rw [Matrix.mul_diagonal, mul_comm]
        exact this
      have e2 : A = U * Matrix.diagonal t' * L := by
        rw [← e1, Matrix.mul_assoc, hUL, Matrix.mul_one]
      have e3 : (U * Matrix.diagonal t * L) a b - A a b =
          ∑ ℓ, U a ℓ * -(t' ℓ - t ℓ) * L ℓ b := by
        rw [e2, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
        ring
      rw [e3]
      refine v.map_le_sum fun ℓ _ => ?_
      rw [v.map_mul, v.map_mul, v.map_neg]
      have := add_le_add (add_le_add (show (0 : WithTop ℝ) ≤ v (U a ℓ) from hU a ℓ) (ht ℓ))
        (show (0 : WithTop ℝ) ≤ v (L ℓ b) from hL ℓ b)
      rwa [zero_add, add_zero] at this)
  exact ⟨φ, h2, h1, h3⟩

end GlobalTheory.DiagLimit
