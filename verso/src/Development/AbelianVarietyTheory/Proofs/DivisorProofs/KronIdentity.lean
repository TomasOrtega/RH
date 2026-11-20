import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim

namespace GlobalTheory.KroneckerIdentity

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem kron_identity {T : Type} [Fintype T] [DecidableEq T] {J : T → Type}
    [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)] {R : Type} [CommRing R] :
    (GlobalTheory.DefPt.kron fun (t : T) ↦ (1 : Matrix (J t) (J t) R))
      = (1 : Matrix ((t : T) → J t) ((t : T) → J t) R) := by
  ext I I'
  simp only [GlobalTheory.DefPt.kron, Matrix.of_apply, Matrix.one_apply]
  by_cases h : I = I'
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨t, ht⟩ : ∃ t, I t ≠ I' t := not_forall.mp fun hc => h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)

end GlobalTheory.KroneckerIdentity
