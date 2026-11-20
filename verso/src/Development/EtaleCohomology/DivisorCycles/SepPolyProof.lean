import Development.EtaleCohomology.DivisorCycles.OpenCoset

open Matrix Polynomial
namespace LateralTheory.DivDb.SepPolyProof

noncomputable def disc (C : Type) [Field C] (n : ℕ) : MvPolynomial (Fin n × Fin n) C :=
  resultant (charpoly.univ C (Fin n)) (derivative (charpoly.univ C (Fin n))) n (n - 1)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem univ_map_ev {C : Type} [Field C] {n : ℕ} (x : Mat C n) :
    (charpoly.univ C (Fin n)).map (MvPolynomial.eval (fun p : Fin n × Fin n => x p.1 p.2)) = x.charpoly := by
  have h := charpoly.univ_map_eval₂Hom (Fin n) (RingHom.id C) (fun p : Fin n × Fin n => x p.1 p.2)
  have hx : (Matrix.of (fun p : Fin n × Fin n => x p.1 p.2).curry) = x := by ext i j; rfl
  rw [hx] at h
  exact h

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem ev_disc {C : Type} [Field C] [CharZero C] {n : ℕ} (x : Mat C n) :
    ev x (disc C n) = resultant x.charpoly (derivative x.charpoly) := by
  unfold ev disc
  rw [← resultant_map_map, ← derivative_map, univ_map_ev]
  have h1 : x.charpoly.natDegree = n := by simpa using charpoly_natDegree_eq_dim x
  rw [natDegree_derivative, h1]

end LateralTheory.DivDb.SepPolyProof

namespace LateralTheory.DivDb
open LateralTheory.DivDb.SepPolyProof in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Both sides reduce to the same expression.
-/
theorem SepPoly_of : SepPoly := by
  intro C _ _ n
  refine ⟨disc C n, fun x => ?_⟩
  rw [ev_disc, Ne, resultant_eq_zero_iff]
  have h0 : x.charpoly ≠ 0 := (charpoly_monic x).ne_zero
  simp only [ne_eq, h0, not_false_eq_true, true_or, true_and, not_not]
  rfl
end LateralTheory.DivDb
