import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.LowIrr

def zR (P Q R S : ℕ) : Fin R × Fin (P + Q) → Ln P Q R S := fun w => (finSumFinEquiv.symm w.2, .inl w.1)

def yS (P Q R S : ℕ) : Fin S × Fin (P + Q) → Ln P Q R S := fun w => (finSumFinEquiv.symm w.2, .inr w.1)

def kap (P Q k k' : ℕ) : Fin (P + Q) → ℂ := fun i => if (i : ℕ) < P then (k : ℂ) else -(k' : ℂ)

/- English proof (translation)
Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem zR_inj (P Q R S : ℕ) : Function.Injective (zR P Q R S) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ e
  simp only [zR, Prod.mk.injEq, Sum.inl.injEq, EmbeddingLike.apply_eq_iff_eq] at e
  rw [e.1, e.2]

/- English proof (translation)
Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem yS_inj (P Q R S : ℕ) : Function.Injective (yS P Q R S) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ e
  simp only [yS, Prod.mk.injEq, Sum.inr.injEq, EmbeddingLike.apply_eq_iff_eq] at e
  rw [e.1, e.2]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem zR_ne_yS (P Q R S : ℕ) (u w) : zR P Q R S u ≠ yS P Q R S w := by
  simp [zR, yS]

/- English proof (translation)
Extract witnesses or component facts from the available result. Prove the first alternative. Prove the second alternative.
-/
theorem zR_or_yS (P Q R S : ℕ) (s : Ln P Q R S) :
    (∃ u, zR P Q R S u = s) ∨ ∃ w, yS P Q R S w = s := by
  obtain ⟨a, c | d⟩ := s
  · exact Or.inl ⟨(c, finSumFinEquiv a), by simp [zR]⟩
  · exact Or.inr ⟨(d, finSumFinEquiv a), by simp [yS]⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem fockF_rowOp {σ I J : Type} [DecidableEq σ] [Fintype J] (z : I × J → σ) (c d : I)
    (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (GlobalTheory.Capelli.rowOp ℂ z c d f) g = Formalism.REAL.fockF f (GlobalTheory.Capelli.rowOp ℂ z d c g) := by
  rw [GlobalTheory.Capelli.rowOp_apply, GlobalTheory.Capelli.rowOp_apply, Formalism.REAL.fischerInner_sum_left, Formalism.REAL.fischerInner_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Formalism.REAL.fischerInner_X_mul_left, Formalism.REAL.fischerInner_pderiv_left]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem eab_isKC_inl {R S : ℕ} (c d : Fin R) : IsKC (Eab (.inl c) (.inl d) : Mat R S) := by
  intro a b h
  simp only [Eab, Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'; exact absurd trivial h
  · rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem eab_isKC_inr {R S : ℕ} (c d : Fin S) : IsKC (Eab (.inr c) (.inr d) : Mat R S) := by
  intro a b h
  simp only [Eab, Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'; exact absurd trivial h
  · rfl

end GlobalTheory.LowIrr

end
