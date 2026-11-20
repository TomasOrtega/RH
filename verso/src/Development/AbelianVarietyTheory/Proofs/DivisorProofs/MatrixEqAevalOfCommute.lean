import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAevalOfCommuteOfSeparable

namespace GlobalTheory.CentralizerSeparable

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem matrix_eq_aeval_of_commute :
    ∀ {k : Type} [Field k] (n : ℕ) (N X : Matrix (Fin n) (Fin n) k), N.charpoly.Separable →
      Commute X N → ∃ q : Polynomial k, X = Polynomial.aeval N q := by
  intro k _ n N X hs hc
  obtain ⟨u, r, h⟩ := hs
  exact GlobalTheory.SepCentralizer.eq_aeval_of_commute_of_separable k n N X u r h hc.eq

end GlobalTheory.CentralizerSeparable
