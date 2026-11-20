import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `hI : Ideal.span {f} ≠ (0 : Ideal B)`. Rewrite using `[Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hf`. Establish `hfin` using `Ideal.finite_factors hI`. Apply `(hfin.image (fun v : IsDedekindDomain.HeightOneSpectrum B => v.asIdeal)).subset` to reduce the goal to its premises.

Introduce and unpack `P ⟨hmax, hfP⟩`. Establish `hne : P ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `hf ((Submodule.mem_bot B).mp hfP)`. Use `⟨⟨P, hmax.isPrime, hne⟩, ?_, rfl⟩` and prove the remaining obligations.

Use `show P ∣ Ideal.span {f}`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hfP`.
-/
theorem finite_maximal_ideals_containing (B : Type) [CommRing B] [IsDedekindDomain B] (f : B)
    (hf : f ≠ 0) : {P : Ideal B | P.IsMaximal ∧ f ∈ P}.Finite := by
  have hI : Ideal.span {f} ≠ (0 : Ideal B) := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact hf
  have hfin := Ideal.finite_factors hI
  apply (hfin.image (fun v : IsDedekindDomain.HeightOneSpectrum B => v.asIdeal)).subset
  rintro P ⟨hmax, hfP⟩
  have hne : P ≠ ⊥ := by
    rintro rfl
    exact hf ((Submodule.mem_bot B).mp hfP)
  refine ⟨⟨P, hmax.isPrime, hne⟩, ?_, rfl⟩
  show P ∣ Ideal.span {f}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hfP

/- English proof (translation)
Introduce `B _ _ f hf` and use `finite_maximal_ideals_containing B f hf`.
-/
theorem finite_maximal_ideals_containing' : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B),
    f ≠ 0 → {P : Ideal B | P.IsMaximal ∧ f ∈ P}.Finite :=
  fun B _ _ f hf => finite_maximal_ideals_containing B f hf

end GlobalTheory
