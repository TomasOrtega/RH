import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PdPlace

/- English proof (translation)
Establish `hnu : ¬ IsUnit ((p : ℕ) : 𝓞 E)`. Introduce `hu`. Establish `h1` using `hu.map (Algebra.norm ℤ : 𝓞 E →* ℤ)`. Rewrite `h1` using `[show ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) by simp, Algebra.norm_algebraMap]`. Establish `h2` using `Int.isUnit_iff_natAbs_eq.1 h1`.

Establish `h3 : 0 < Module.finrank ℤ (𝓞 E)` using `Module.finrank_pos`. Rewrite `h2` using `[Int.natAbs_pow, Int.natAbs_natCast]`. Break down `Nat.pow_eq_one.1 h2 with h | h` into its components or cases. Conclude with `hp.one_lt.ne' h`. Conclude with `h3.ne' h`.

Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 E)}) (by rwa [Ne, Ideal.span_singleton_eq_top])`. Establish `hmem : ((p : ℕ) : 𝓞 E) ∈ M` using `hle (Ideal.subset_span rfl)`. Use `⟨⟨M, hM.isPrime, fun h => ?_⟩, hmem⟩` and prove the remaining obligations. Rewrite `hmem` using `[h, Ideal.mem_bot]`. Conclude with `hp.ne_zero (by exact_mod_cast hmem)`.
-/
theorem exists_place_over_prime (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (Formalism.BasicNotions.placesOver E p).Nonempty := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 E) := by
    intro hu
    have h1 := hu.map (Algebra.norm ℤ : 𝓞 E →* ℤ)
    rw [show ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) by simp, Algebra.norm_algebraMap] at h1
    have h2 := Int.isUnit_iff_natAbs_eq.1 h1
    have h3 : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h2
    rcases Nat.pow_eq_one.1 h2 with h | h
    · exact hp.one_lt.ne' h
    · exact h3.ne' h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 E)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : ((p : ℕ) : 𝓞 E) ∈ M := hle (Ideal.subset_span rfl)
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hmem⟩
  rw [h, Ideal.mem_bot] at hmem
  exact hp.ne_zero (by exact_mod_cast hmem)

/- English proof (translation)
Introduce `D T i`. Establish `hp : (if T.l i = D.host.pde then D.host.pde' else D.host.pde).Prime` using `by split_ifs exacts [D.host.pde'_prime, D.host.pde_prime]`. Take `⟨v, hv⟩` from `exists_place_over_prime D.host.E _ hp`. Rewrite `hv` using `[← T.pD_eq i]`. Conclude with `⟨v, hv⟩`.
-/
theorem pD_nonempty : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw), (T.pD i).Nonempty := by
  intro D T i
  have hp : (if T.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    exacts [D.host.pde'_prime, D.host.pde_prime]
  obtain ⟨v, hv⟩ := exists_place_over_prime D.host.E _ hp
  rw [← T.pD_eq i] at hv
  exact ⟨v, hv⟩

end GlobalTheory.PdPlace
