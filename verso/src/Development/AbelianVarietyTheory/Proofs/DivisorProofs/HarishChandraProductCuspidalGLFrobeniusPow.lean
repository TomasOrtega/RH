import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldFrobeniusPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLFieldAutomorphismStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem hc_congr_deg {F : Type} [Field F] (a b b' : ℕ) (α : GL (Fin a) F → ℂ)
    (β : (m : ℕ) → GL (Fin m) F → ℂ) (n : ℕ) (h : b = b') :
    hc a b α (β b) n = hc a b' α (β b') n := by
  subst h; rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem deg_map_mul (L : List (ℕ × ℕ)) (c : ℕ) :
    deg (L.map fun p => (p.1, p.2 * c)) = deg L := by
  unfold deg
  rw [List.map_map]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Both sides reduce to the same expression. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem J_gal : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ),
    (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (L : List (ℕ × ℕ)) (n : ℕ) (x : GL (Fin n) F),
    J θ L n (gal (t : F →+* F) n x) = J θ (L.map fun p => (p.1, p.2 * ringChar F ^ j)) n x := by
  intro F _ _ θ t j ht L
  induction L with
  | nil => intro n x; rfl
  | cons p L ih =>
    intro n x
    rw [List.map_cons, J_cons, J_cons, GlobalTheory.T.harishChandraInductionGL_fieldAutomorphism F t]
    have h1 : (fun y => cusp θ p.1 p.2 (gal (t : F →+* F) p.1 y)) = cusp θ p.1 (p.2 * ringChar F ^ j) := by
      funext y; exact GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow F θ t j ht p.1 p.2 y
    have h2 : (fun y => J θ L (deg L) (gal (t : F →+* F) (deg L) y)) =
        J θ (L.map fun p => (p.1, p.2 * ringChar F ^ j)) (deg L) := by
      funext y; exact ih (deg L) y
    rw [h1, h2]
    exact congrFun (hc_congr_deg p.1 (deg L) _ _ (J θ (L.map fun p => (p.1, p.2 * ringChar F ^ j))) n
      (deg_map_mul L _).symm) x

end GlobalTheory.Shin
