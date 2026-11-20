import Mathlib
open NumberField

namespace GlobalTheory

open NumberField in

/- English proof (translation)
Rewrite using `[← Algebra.unramifiedLocus_eq_univ_iff, Set.eq_univ_iff_forall]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`.

Conclude with `(dvd_differentIdeal_iff (P := M)).1 (Ideal.dvd_iff_le.2 hle) (h ⟨M, hM.isPrime⟩)`. Introduce `h P show Algebra.IsUnramifiedAt _ P.asIdeal`. Rewrite using `[← not_dvd_differentIdeal_iff, h, Ideal.dvd_iff_le, top_le_iff]`. Conclude with `P.isPrime.ne_top`.
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
