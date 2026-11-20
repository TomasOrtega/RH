import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import ReciprocityTheory.NeutralLocalFields.HilbertClassField
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HilbertClassFieldA
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField

namespace GlobalTheory

/- English proof (translation)
Take `⟨j, hj⟩` from `hc`. Use extensionality with `x`. Apply `j.injective` to reduce the goal to its premises. Use `show j (c (c x)) = j x`. Rewrite using `[hj, hj, Complex.conj_conj]`.
-/
theorem complexConjugation_mul_self {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (c : Ω ≃ₐ[E] Ω) (hc : IsComplexConjugation c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := hc
  ext x
  apply j.injective
  show j (c (c x)) = j x
  rw [hj, hj, Complex.conj_conj]

/- English proof (translation)
Introduce and unpack `⟨j, hj⟩`. Set `φ : E →+* ℂ` to `j.comp (algebraMap E Ω)`. Establish `hφ : ComplexEmbedding.IsReal φ`. Use extensionality with `x`. Use `show starRingEnd ℂ (j (algebraMap E Ω x)) = j (algebraMap E Ω x)`.

Rewrite using `[← hj, AlgEquiv.commutes]`. Establish `hw : (InfinitePlace.mk φ).IsReal` using `InfinitePlace.isReal_mk_iff.mpr hφ`. Establish `: IsEmpty {w : InfinitePlace E // w.IsReal}` using `by classical`. Rewrite `hE` using `[InfinitePlace.nrRealPlaces]`. Conclude with `Fintype.card_eq_zero_iff.mp (by convert hE)`.

Conclude with `this.false ⟨_, hw⟩`.
-/
theorem not_isComplexConjugation_of_nrRealPlaces_eq_zero {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] (hE : InfinitePlace.nrRealPlaces E = 0)
    (c : Ω ≃ₐ[E] Ω) : ¬ IsComplexConjugation c := by
  rintro ⟨j, hj⟩
  let φ : E →+* ℂ := j.comp (algebraMap E Ω)
  have hφ : ComplexEmbedding.IsReal φ := by
    ext x
    show starRingEnd ℂ (j (algebraMap E Ω x)) = j (algebraMap E Ω x)
    rw [← hj, AlgEquiv.commutes]
  have hw : (InfinitePlace.mk φ).IsReal := InfinitePlace.isReal_mk_iff.mpr hφ
  have : IsEmpty {w : InfinitePlace E // w.IsReal} := by
    classical
    rw [InfinitePlace.nrRealPlaces] at hE
    exact Fintype.card_eq_zero_iff.mp (by convert hE)
  exact this.false ⟨_, hw⟩

/- English proof (translation)
Introduce `E Ω _ _ _ _ l _ O _ _ hl M _ _ z hz c hc`. Break down `hl with hl | hE` into its components or cases. Establish `h1 : z 1 = 0`. Use `hz 1 1` as an intermediate fact. Simplify using `only [mul_one] at this`.

Simplify using `using this`. Establish `h2 : z c + z c = 0`. Rewrite using `[← hz, show (c * c : G E Ω) = 1 from complexConjugation_mul_self c hc, h1]`. Establish `hu : IsUnit (2 : ℤ_[l])`. Use `(PadicInt.norm_natCast_eq_one_iff (p := l) (n := 2)).mpr ((Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hl)` as an intermediate fact.

Rewrite using `[PadicInt.isUnit_iff]`. Conclude with `this` after adjusting the coercions. Establish `hu' : IsUnit (2 : O)`. Use `hu.map (algebraMap ℤ_[l] O)` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis.

Establish `h3 : (2 : O) • z c = 0` using `by rw [two_smul]; exact h2`. Conclude with `(hu'.smul_left_cancel).mp (h3.trans (smul_zero _).symm)`. Conclude with `absurd hc (not_isComplexConjugation_of_nrRealPlaces_eq_zero hE c)`.
-/
theorem addHom_complexConjugation_eq_zero : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (M : Type) [AddCommGroup M] [Module O M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    ∀ (c : Ω ≃ₐ[E] Ω), IsComplexConjugation c → z c = 0 := by
  intro E Ω _ _ _ _ l _ O _ _ hl M _ _ z hz c hc
  rcases hl with hl | hE
  · have h1 : z 1 = 0 := by
      have := hz 1 1
      simp only [mul_one] at this
      simpa using this
    have h2 : z c + z c = 0 := by
      rw [← hz, show (c * c : G E Ω) = 1 from complexConjugation_mul_self c hc, h1]
    have hu : IsUnit (2 : ℤ_[l]) := by
      have := (PadicInt.norm_natCast_eq_one_iff (p := l) (n := 2)).mpr
        ((Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hl)
      rw [PadicInt.isUnit_iff]; exact_mod_cast this
    have hu' : IsUnit (2 : O) := by
      have := hu.map (algebraMap ℤ_[l] O)
      rwa [map_ofNat] at this
    have h3 : (2 : O) • z c = 0 := by rw [two_smul]; exact h2
    exact (hu'.smul_left_cancel).mp (h3.trans (smul_zero _).symm)
  · exact absurd hc (not_isComplexConjugation_of_nrRealPlaces_eq_zero hE c)

end GlobalTheory
