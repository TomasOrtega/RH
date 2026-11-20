import Formalism.MahlerMeasure.Statement

namespace Formalism.GM

open MvPolynomial

namespace QuotientRingDecomposition

variable {R : Type} [CommRing R] {r Q : ℕ}

noncomputable def E (e : Fin r → Fin Q) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => ((e i : ℕ)))

def modQ (hQ : 0 < Q) (m : Fin r →₀ ℕ) : Fin r → Fin Q := fun i => ⟨m i % Q, Nat.mod_lt _ hQ⟩

noncomputable def divQ (Q : ℕ) (m : Fin r →₀ ℕ) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m i / Q)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma E_apply (e : Fin r → Fin Q) (i : Fin r) : E e i = (e i : ℕ) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma divQ_apply (m : Fin r →₀ ℕ) (i : Fin r) : divQ Q m i = m i / Q := rfl

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
lemma decomp (hQ : 0 < Q) (m : Fin r →₀ ℕ) : E (modQ hQ m) + Q • divQ Q m = m := by
  ext i
  simp [modQ, Nat.mod_add_div]

end QuotientRingDecomposition

end Formalism.GM
