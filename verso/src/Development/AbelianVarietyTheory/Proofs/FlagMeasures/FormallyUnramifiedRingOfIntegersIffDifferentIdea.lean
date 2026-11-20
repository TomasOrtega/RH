import Mathlib
open NumberField

namespace GlobalTheory

open NumberField in

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top (F E : Type) [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Algebra.FormallyUnramified (𝓞 F) (𝓞 E) ↔ differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
  rw [← Algebra.unramifiedLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  constructor
  · intro h
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact (dvd_differentIdeal_iff (P := M)).1 (Ideal.dvd_iff_le.2 hle) (h ⟨M, hM.isPrime⟩)
  · intro h P
    show Algebra.IsUnramifiedAt _ P.asIdeal
    rw [← not_dvd_differentIdeal_iff, h, Ideal.dvd_iff_le, top_le_iff]
    exact P.isPrime.ne_top

end GlobalTheory
