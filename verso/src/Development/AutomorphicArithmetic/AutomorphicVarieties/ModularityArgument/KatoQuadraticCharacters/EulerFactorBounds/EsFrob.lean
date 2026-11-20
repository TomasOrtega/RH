import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.FrobeniusConjugateInertia.FrobConjIne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES
open scoped Matrix MatrixGroups Pointwise

/- English proof (translation)
Introduce `Ω _ _ _ l _ v B σ hq hql hB hF`. Take `⟨hσ, hfr⟩` from `hF`. Establish `hmem : ∀ g : Gal(Ω/ℚ), g ∈ ValuationSubring.decompositionSubgroup ℚ B → ∀ y ∈ B, g y ∈ B` using `fun g hg y hy => (B.subMulAction ℚ).smul_mem' ⟨g, hg⟩ hy`. Use `⟨⟨?_, fun y hy => ⟨hmem σ hσ y hy, hmem σ⁻¹ (inv_mem hσ) y hy, hfr y ((B.valuation_le_one_iff y).mpr hy)⟩⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[ValuationSubring.mem_nonunits_iff]`.

Establish `h` using `(hB ((normV v : ℕ) : 𝓞 ℚ)).mpr ((UpperTheory.V.Z.Kato.Nb.mem_place_iff v _).mpr dvd_rfl)`. Simplify using `using h`. Establish `hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal`. Rewrite using `[UpperTheory.V.Z.Kato.Nb.mem_place_iff]`. Introduce `hd`.

Conclude with `hql ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp hd)`. Conclude with `cycZ_of_isFrob hl hB ⟨hσ, hfr⟩`.
-/
theorem UpperTheory.V.Z.Kato.Nb.sEsFrob : UpperTheory.V.Z.Kato.Nb.SEsFrob := by
  intro Ω _ _ _ l _ v B σ hq hql hB hF
  obtain ⟨hσ, hfr⟩ := hF
  have hmem : ∀ g : Gal(Ω/ℚ), g ∈ ValuationSubring.decompositionSubgroup ℚ B → ∀ y ∈ B, g y ∈ B :=
    fun g hg y hy => (B.subMulAction ℚ).smul_mem' ⟨g, hg⟩ hy
  refine ⟨⟨?_, fun y hy => ⟨hmem σ hσ y hy, hmem σ⁻¹ (inv_mem hσ) y hy,
    hfr y ((B.valuation_le_one_iff y).mpr hy)⟩⟩, ?_⟩
  · rw [ValuationSubring.mem_nonunits_iff]
    have h := (hB ((normV v : ℕ) : 𝓞 ℚ)).mpr ((UpperTheory.V.Z.Kato.Nb.mem_place_iff v _).mpr dvd_rfl)
    simpa using h
  · have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
      rw [UpperTheory.V.Z.Kato.Nb.mem_place_iff]
      intro hd
      exact hql ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp hd)
    exact cycZ_of_isFrob hl hB ⟨hσ, hfr⟩
