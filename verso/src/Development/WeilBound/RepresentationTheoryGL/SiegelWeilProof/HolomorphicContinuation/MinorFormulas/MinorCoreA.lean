import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorB

noncomputable section

open MvPolynomial Matrix

namespace PositivityTheory.Rg.Sw.SP.Mi

variable {R : Type} [CommRing R]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Both sides reduce to the same expression.
-/
theorem foldr_eq_prod {ρ : ℕ} {M : Type} [AddCommGroup M] [Module R M] (f : Fin ρ → Module.End R M)
    (l : List (Fin ρ)) : l.foldr (fun k g => f k ∘ₗ g) LinearMap.id = (l.map f).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, List.map_cons, List.prod_cons, ih]; rfl

def gens (α : R) (ρ : ℕ) : Set (Module.End R (Pm R ρ)) := Set.range fun pq : Fin ρ × Fin ρ => opE α pq.1 pq.2

/- English proof (translation)
Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem gens_comm (α : R) (ρ : ℕ) : ∀ a ∈ gens α ρ, ∀ b ∈ gens α ρ, a * b = b * a := by
  rintro _ ⟨⟨p, q⟩, rfl⟩ _ ⟨⟨p', q'⟩, rfl⟩
  exact mComm R ρ α p q p' q'

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem coe_list_prod {A : Type} [Ring A] [Algebra R A] (S : Subalgebra R A) (l : List S) :
    ((l.prod : S) : A) = (l.map Subtype.val).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.prod_cons, ih]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem opE_C_mul (α r : R) {ρ : ℕ} (p q : Fin ρ) (f : Pm R ρ) : opE α p q (C r * f) = C r * opE α p q f := by
  have h0 : del p q (C r : Pm R ρ) = 0 := by
    rw [← algebraMap_eq]; exact (del p q).map_algebraMap r
  change C α * X (q, p) * (C r * f) + del p q (C r * f) = C r * (C α * X (q, p) * f + del p q f)
  rw [Derivation.leibniz, h0, smul_zero, add_zero, smul_eq_mul]
  ring

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion repeatedly using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem sum_del (ρ : ℕ) :
    ∑ j : Fin (ρ + 1), (-1 : Pm R (ρ + 1)) ^ (j : ℕ) * del 0 j ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det =
      -((ρ : Pm R (ρ + 1)) * (Xm R (ρ + 1)).det) := by
  have h1 : ∀ j : Fin (ρ + 1), del 0 j ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det =
      ∑ c : Fin ρ, X (j, c.succ) * (updateCol ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ) c
        (fun a => X (j.succAbove a, 0))).det := by
    intro j
    rw [deriv_det]
    refine Finset.sum_congr rfl fun c _ => ?_
    have : (fun a => del 0 j (((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ) a c)) =
        (X (j, c.succ) : Pm R (ρ + 1)) • (fun a => (X (j.succAbove a, 0) : Pm R (ρ + 1))) := by
      funext a
      simp [Xm, del, mkDerivation_X, mul_comm]
    rw [this, det_updateCol_smul]
  have h2 : ∀ c : Fin ρ, ∑ j : Fin (ρ + 1), (-1 : Pm R (ρ + 1)) ^ (j : ℕ) * (X (j, c.succ) *
      (updateCol ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ) c (fun a => X (j.succAbove a, 0))).det) =
      -(Xm R (ρ + 1)).det := by
    intro c
    have hB := det_succ_column_zero ((Xm R (ρ + 1)).submatrix id (Equiv.swap 0 c.succ))
    rw [det_permute', Equiv.Perm.sign_swap (Fin.succ_ne_zero c).symm] at hB
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at hB
    rw [hB]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc]
    congr 2
    ext p q
    by_cases h : q = c
    · subst h; simp [Xm, updateCol_apply, Equiv.swap_apply_right]
    · have h3 : q.succ ≠ 0 := Fin.succ_ne_zero q
      have h4 : q.succ ≠ c.succ := fun e => h (Fin.succ_injective _ e)
      simp [Xm, updateCol_apply, h, Equiv.swap_apply_of_ne_of_ne h3 h4]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [h2]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end PositivityTheory.Rg.Sw.SP.Mi
