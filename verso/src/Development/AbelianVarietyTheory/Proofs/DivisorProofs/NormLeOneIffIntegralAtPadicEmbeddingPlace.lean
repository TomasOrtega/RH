import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace GlobalTheory.FrameRead

/- English proof (translation)
Establish `hy : IsIntegral ℤ (f x)` using `hx.map f.toIntAlgHom`. Use `(Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hy.tower_top` as an intermediate fact. Rewrite `this` using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`. Conclude with `this` after adjusting the coercions.
-/
theorem norm_map_le_one_of_isIntegral_int {F C : Type} [CommRing F] [NormedField C] [IsUltrametricDist C] (f : F →+* C) {x : F}
    (hx : IsIntegral ℤ x) : ‖f x‖ ≤ 1 := by
  have hy : IsIntegral ℤ (f x) := hx.map f.toIntAlgHom
  have := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hy.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at this
  exact_mod_cast this

/- English proof (translation)
Introduce `K _ _ l _ w e0 hw x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨n, d, h | h⟩` from `w.exists_primeCompl_mul_eq_or_mul_eq (K := K) x`. Conclude with `⟨d, d.2, n, by rw [mul_comm]; exact h⟩`.

Distinguish the cases in `hn : n ∈ w.asIdeal`. It suffices to derive a contradiction. Use `d.2 ((hw d).2 ?_)` and prove the remaining obligations. Establish `h1 : ‖e0 ((d : 𝓞 K) : K)‖ = ‖e0 x‖ * ‖e0 (n : K)‖`. Establish `: ((d : 𝓞 K) : K) = x * (n : K)` using `h.symm`.

Rewrite using `[this, map_mul, norm_mul]`. Rewrite using `[h1]`. Establish `h2 : ‖e0 (n : K)‖ < 1` using `(hw n).1 hn`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨n, hn, d, by rw [mul_comm]; exact h⟩`.

Introduce and unpack `⟨s, hs, r, hr⟩`. Establish `hs1 : 1 ≤ ‖e0 (s : K)‖`. Assume the negation of the conclusion as `h`. Conclude with `hs ((hw s).2 (lt_of_not_ge h))`. Establish `hr1 : ‖e0 (r : K)‖ ≤ 1` using `norm_map_le_one_of_isIntegral_int e0 r.isIntegral_coe`.

Establish `h1 : ‖e0 (s : K)‖ * ‖e0 x‖ ≤ 1` using `by rw [← norm_mul, ← map_mul, hr]; exact hr1`. Use polynomial arithmetic with `[norm_nonneg (e0 x)]`.
-/
theorem norm_le_one_iff_integral_at : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l), AtPlace w e0 → ∀ x : K, ‖e0 x‖ ≤ 1 ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ r : 𝓞 K, (s : K) * x = r := by
  intro K _ _ l _ w e0 hw x
  constructor
  · intro hx
    obtain ⟨n, d, h | h⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := K) x
    · exact ⟨d, d.2, n, by rw [mul_comm]; exact h⟩
    · by_cases hn : n ∈ w.asIdeal
      · exfalso
        refine d.2 ((hw d).2 ?_)
        have h1 : ‖e0 ((d : 𝓞 K) : K)‖ = ‖e0 x‖ * ‖e0 (n : K)‖ := by
          have : ((d : 𝓞 K) : K) = x * (n : K) := h.symm
          rw [this, map_mul, norm_mul]
        rw [h1]
        have h2 : ‖e0 (n : K)‖ < 1 := (hw n).1 hn
        calc ‖e0 x‖ * ‖e0 (n : K)‖ ≤ 1 * ‖e0 (n : K)‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact h2
      · exact ⟨n, hn, d, by rw [mul_comm]; exact h⟩
  · rintro ⟨s, hs, r, hr⟩
    have hs1 : 1 ≤ ‖e0 (s : K)‖ := by
      by_contra h
      exact hs ((hw s).2 (lt_of_not_ge h))
    have hr1 : ‖e0 (r : K)‖ ≤ 1 := norm_map_le_one_of_isIntegral_int e0 r.isIntegral_coe
    have h1 : ‖e0 (s : K)‖ * ‖e0 x‖ ≤ 1 := by rw [← norm_mul, ← map_mul, hr]; exact hr1
    nlinarith [norm_nonneg (e0 x)]

end GlobalTheory.FrameRead
