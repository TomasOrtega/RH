import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

/- English proof (translation)
Use `h.real` as an intermediate fact. Use `h.cplx` as an intermediate fact. Establish `: Algebra.IsQuadraticExtension F L` using `{ finrank_eq_two' := h.rank }`. Establish `hr : ComplexEmbedding.IsReal (ψ.comp (algebraMap F L))` using `InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)`. Take `⟨σ, hσ⟩` from `NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) ψ (ComplexEmbedding.conjugate ψ) (by`.

Use extensionality with `a`. Conclude with `(RingHom.congr_fun hr a).symm)`. Establish `hcard : Nat.card (L ≃ₐ[F] L) = 2` using `by rw [IsGalois.card_aut_eq_finrank, h.rank]`. Take `⟨y, -, hy⟩` from `(Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard`. Establish `hne : σ.symm ≠ 1`.

Introduce `e`. Establish `hc : ¬ ComplexEmbedding.IsReal ψ` using `InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex _)`. Apply `hc` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff, ← hσ, e]`. Both sides reduce to the same expression.

Establish `e : c = σ.symm` using `(hy c h.ne).trans (hy _ hne).symm`. Rewrite using `[e]`. Conclude with `RingHom.congr_fun hσ x`.
-/
theorem CMData.embedding_conj {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    {c : L ≃ₐ[F] L} {I : Type} {φ : I → L →+* ℂ} (h : GlobalTheory.Mem.Chr.CMData F c φ) (ψ : L →+* ℂ) (x : L) :
    ψ (c x) = (starRingEnd ℂ) (ψ x) := by
  have := h.real
  have := h.cplx
  have : Algebra.IsQuadraticExtension F L := { finrank_eq_two' := h.rank }
  have hr : ComplexEmbedding.IsReal (ψ.comp (algebraMap F L)) :=
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) ψ
    (ComplexEmbedding.conjugate ψ) (by
      ext a
      exact (RingHom.congr_fun hr a).symm)
  have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, h.rank]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
  have hne : σ.symm ≠ 1 := by
    intro e
    have hc : ¬ ComplexEmbedding.IsReal ψ :=
      InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex _)
    apply hc
    rw [ComplexEmbedding.isReal_iff, ← hσ, e]
    rfl
  have e : c = σ.symm := (hy c h.ne).trans (hy _ hne).symm
  rw [e]
  exact RingHom.congr_fun hσ x

open Classical in

/- English proof (translation)
Introduce `F L _ _ _ _ _ c I _ φ h k hk hv`. Take `⟨a, ha⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 L) L (k : L) fun v => (hv v).le`. Establish `hi : IsIntegral ℤ (k : L)` using `ha ▸ a.isIntegral_coe`. Take `⟨n, hn, hp⟩` from `NumberField.Embeddings.pow_eq_one_of_norm_eq_one L ℂ hi (fun ψ => by`. Establish `h1` using `congrArg (fun z => ‖ψ z‖) hk`.

Simplify using `only [map_mul, h.embedding_conj, map_one, norm_mul, norm_one, RCLike.norm_conj] at h1`. Use polynomial arithmetic with `[norm_nonneg (ψ (k : L))])`. Conclude with `⟨n, hn, hp⟩`.
-/
theorem normOne_unit_isRoot : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → ∀ k : Lˣ, (k : L) * c (k : L) = 1 → (∀ v : HeightOneSpectrum (𝓞 L), v.valuation L (k : L) = 1) → ∃ m : ℕ, 0 < m ∧ (k : L) ^ m = 1 := by
  intro F L _ _ _ _ _ c I _ φ h k hk hv
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 L) L (k : L) fun v => (hv v).le
  have hi : IsIntegral ℤ (k : L) := ha ▸ a.isIntegral_coe
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one L ℂ hi (fun ψ => by
    have h1 := congrArg (fun z => ‖ψ z‖) hk
    simp only [map_mul, h.embedding_conj, map_one, norm_mul, norm_one, RCLike.norm_conj] at h1
    nlinarith [norm_nonneg (ψ (k : L))])
  exact ⟨n, hn, hp⟩

/- English proof (translation)
Take `⟨m, hm, hk⟩` from `h`. Establish `hi : IsIntegral ℤ (k : L)` using `IsIntegral.of_pow hm (hk ▸ isIntegral_one)`. Take `⟨X, hX⟩ : ∃ X : 𝓞 L, algebraMap (𝓞 L) L X = k` from `⟨⟨k, hi⟩, rfl⟩`. Establish `h1 : X ^ m = 1` using `RingOfIntegers.coe_injective (by rw [map_pow, hX, hk, map_one])`. Conclude with `⟨Units.ofPowEqOne X m h1 hm.ne', Units.ext hX⟩`.
-/
theorem exists_unit_of_root {L : Type} [Field L] [NumberField L] (k : Lˣ) (h : ∃ m : ℕ, 0 < m ∧ (k : L) ^ m = 1) :
    ∃ ζ : (𝓞 L)ˣ, Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L) ζ = k := by
  obtain ⟨m, hm, hk⟩ := h
  have hi : IsIntegral ℤ (k : L) := IsIntegral.of_pow hm (hk ▸ isIntegral_one)
  obtain ⟨X, hX⟩ : ∃ X : 𝓞 L, algebraMap (𝓞 L) L X = k := ⟨⟨k, hi⟩, rfl⟩
  have h1 : X ^ m = 1 := RingOfIntegers.coe_injective (by rw [map_pow, hX, hk, map_one])
  exact ⟨Units.ofPowEqOne X m h1 hm.ne', Units.ext hX⟩

end GlobalTheory.Mem.Chr
