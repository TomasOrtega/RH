import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRepsCoprimeOutsideModulus
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueDegreeOneOfLinearMem

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory

/- English proof (translation)
Introduce `F E _ _ _ _ _ θ D hgen m hm hmD y N`. Take `⟨u, v, huv⟩` from `hgen y`. Establish `hmN : m ^ N ≠ ⊥` using `pow_ne_zero N hm`. Take `⟨a, b, ha, hb, -, hcop⟩` from `exists_reps_coprime_outside_modulus (𝓞 F) (m ^ N) u v hmN`. Use `⟨algebraMap (𝓞 F) (𝓞 E) a + algebraMap (𝓞 F) (𝓞 E) b * θ, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[huv]`. Establish `e : algebraMap (𝓞 F) (𝓞 E) a + algebraMap (𝓞 F) (𝓞 E) b * θ - (algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ) = algebraMap (𝓞 F) (𝓞 E) (a - u) + algebraMap (𝓞 F) (𝓞 E) (b - v) * θ`. Simplify using `only [map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `Ideal.add_mem _ (Ideal.mem_map_of_mem _ ha) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb))`. Introduce `P hmP hk`. Establish `hPmax : P.asIdeal.IsMaximal` using `P.isMaximal`. Establish `hpmax : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.asIdeal`. Establish `hmNp : ¬ m ^ N ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))` using `fun h => hmP (hpmax.isPrime.le_of_pow_le h)`.

Establish `hD : algebraMap (𝓞 F) (𝓞 E) D ∉ P.asIdeal`. Introduce `h`. Apply `hmP` to reduce the goal to its premises. Use `hmD.trans ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]`.

Conclude with `h`. Establish `hbP : algebraMap (𝓞 F) (𝓞 E) b ∉ P.asIdeal`. Introduce `h`. Apply `hcop _ hpmax hmNp` to reduce the goal to its premises. Use `⟨?_, Ideal.mem_comap.mpr h⟩` and prove the remaining obligations.

Rewrite using `[Ideal.mem_comap]`. Use `P.asIdeal.sub_mem hk (P.asIdeal.mul_mem_right θ h)` as an intermediate fact. Simplify using `using this`. Conclude with `residue_degree_one_of_linear_mem (𝓞 F) (𝓞 E) P.asIdeal θ D a b hpmax hgen hD hbP hk`.
-/
theorem exists_shift_mod_pow_degOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (θ : 𝓞 E) (D : 𝓞 F), (∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ) → ∀ (m : Ideal (𝓞 F)), m ≠ ⊥ → m ≤ Ideal.span {D} → ∀ (y : 𝓞 E) (N : ℕ), ∃ k : 𝓞 E, k - algebraMap (𝓞 F) (𝓞 E) D * y ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (m ^ N) ∧ ∀ P : HeightOneSpectrum (𝓞 E), ¬ m ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) → k ∈ P.asIdeal → DegOne F P := by
  intro F E _ _ _ _ _ θ D hgen m hm hmD y N
  obtain ⟨u, v, huv⟩ := hgen y
  have hmN : m ^ N ≠ ⊥ := pow_ne_zero N hm
  obtain ⟨a, b, ha, hb, -, hcop⟩ := exists_reps_coprime_outside_modulus (𝓞 F) (m ^ N) u v hmN
  refine ⟨algebraMap (𝓞 F) (𝓞 E) a + algebraMap (𝓞 F) (𝓞 E) b * θ, ?_, ?_⟩
  · rw [huv]
    have e : algebraMap (𝓞 F) (𝓞 E) a + algebraMap (𝓞 F) (𝓞 E) b * θ -
        (algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ) =
        algebraMap (𝓞 F) (𝓞 E) (a - u) + algebraMap (𝓞 F) (𝓞 E) (b - v) * θ := by
      simp only [map_sub]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ ha)
      (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb))
  · intro P hmP hk
    have hPmax : P.asIdeal.IsMaximal := P.isMaximal
    have hpmax : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.asIdeal
    have hmNp : ¬ m ^ N ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := fun h =>
      hmP (hpmax.isPrime.le_of_pow_le h)
    have hD : algebraMap (𝓞 F) (𝓞 E) D ∉ P.asIdeal := by
      intro h
      apply hmP
      refine hmD.trans ?_
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      exact h
    have hbP : algebraMap (𝓞 F) (𝓞 E) b ∉ P.asIdeal := by
      intro h
      apply hcop _ hpmax hmNp
      refine ⟨?_, Ideal.mem_comap.mpr h⟩
      rw [Ideal.mem_comap]
      have := P.asIdeal.sub_mem hk (P.asIdeal.mul_mem_right θ h)
      simpa using this
    exact residue_degree_one_of_linear_mem (𝓞 F) (𝓞 E) P.asIdeal θ D a b hpmax hgen hD hbP hk
end GlobalTheory
