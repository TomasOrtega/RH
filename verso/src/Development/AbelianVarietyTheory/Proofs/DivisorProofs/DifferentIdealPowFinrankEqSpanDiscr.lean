import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.GalDiff

open scoped Pointwise

variable (E : Type) [Field E] [NumberField E]

/- English proof (translation)
Rewrite using `[← Submodule.mem_div_iff_forall_mul_mem, ← coeSubmodule_differentIdeal ℤ ℚ (L := E) (𝓞 E), IsLocalization.mem_coeSubmodule]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨x, h, rfl⟩`. Introduce and unpack `⟨y, hy, h⟩`.

Establish `: y = x` using `FaithfulSMul.algebraMap_injective (𝓞 E) E h`. Conclude with `this ▸ hy`.
-/
theorem mem_differentIdeal_iff_one (x : 𝓞 E) :
    x ∈ differentIdeal ℤ (𝓞 E) ↔
      ∀ y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E), (x : E) * y ∈ (1 : Submodule (𝓞 E) E) := by
  rw [← Submodule.mem_div_iff_forall_mul_mem, ← coeSubmodule_differentIdeal ℤ ℚ (L := E) (𝓞 E),
    IsLocalization.mem_coeSubmodule]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, h⟩
    have : y = x := FaithfulSMul.algebraMap_injective (𝓞 E) E h
    exact this ▸ hy

/- English proof (translation)
Establish `hone : ∀ (τ : E ≃ₐ[ℚ] E) (a : E), a ∈ (1 : Submodule (𝓞 E) E) → τ a ∈ (1 : Submodule (𝓞 E) E)`. Introduce `τ a ha`. Rewrite `ha`, the goal using `[Submodule.mem_one]`. Take `⟨b, rfl⟩` from `ha`. Conclude with `⟨τ • b, rfl⟩`.

Rewrite `hx`, the goal using `[mem_differentIdeal_iff_one]`. Introduce `y hy`. Establish `hy' : σ.symm y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E)`. Rewrite `hy`, the goal using `[Submodule.mem_traceDual]`. Introduce `a ha`.

Use `hy (σ a) (hone σ a ha)` as an intermediate fact. Rewrite `this`, the goal using `[Algebra.traceForm_apply]`. Rewrite using `[← Algebra.trace_eq_of_algEquiv σ, map_mul, AlgEquiv.apply_symm_apply]`. Conclude with `this`. Use `hone σ _ (hx _ hy')` as an intermediate fact.

Rewrite `this` using `[map_mul, AlgEquiv.apply_symm_apply]`. Conclude with `this`.
-/
theorem galois_smul_mem_differentIdeal (σ : E ≃ₐ[ℚ] E) {x : 𝓞 E}
    (hx : x ∈ differentIdeal ℤ (𝓞 E)) : σ • x ∈ differentIdeal ℤ (𝓞 E) := by
  have hone : ∀ (τ : E ≃ₐ[ℚ] E) (a : E), a ∈ (1 : Submodule (𝓞 E) E) →
      τ a ∈ (1 : Submodule (𝓞 E) E) := by
    intro τ a ha
    rw [Submodule.mem_one] at ha ⊢
    obtain ⟨b, rfl⟩ := ha
    exact ⟨τ • b, rfl⟩
  rw [mem_differentIdeal_iff_one] at hx ⊢
  intro y hy
  have hy' : σ.symm y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual] at hy ⊢
    intro a ha
    have := hy (σ a) (hone σ a ha)
    rw [Algebra.traceForm_apply] at this ⊢
    rw [← Algebra.trace_eq_of_algEquiv σ, map_mul, AlgEquiv.apply_symm_apply]
    exact this
  have := hone σ _ (hx _ hy')
  rw [map_mul, AlgEquiv.apply_symm_apply] at this
  exact this

/- English proof (translation)
Introduce `E _ _ _`. Establish `hmap : Ideal.span {((discr E : ℤ) : 𝓞 E)} = (Ideal.span {discr E}).map (algebraMap ℤ (𝓞 E))`. Rewrite using `[Ideal.map_span, Set.image_singleton, eq_intCast]`. Rewrite using `[hmap]`. Use `set D := differentIdeal ℤ (𝓞 E) with hD`.

Establish `hN : Ideal.absNorm D = (discr E).natAbs` using `absNorm_differentIdeal E (𝓞 E)`. Establish `hrel : Ideal.relNorm ℤ D = Ideal.span {discr E}`. Rewrite using `[Ideal.relNorm_int, hN, Ideal.span_singleton_eq_span_singleton]`. Conclude with `(Int.associated_natAbs _).symm`. Establish `hle : (Ideal.span {discr E}).map (algebraMap ℤ (𝓞 E)) ≤ D ^ Module.finrank ℚ E`.

Rewrite using `[← hrel, Ideal.map_le_iff_le_comap, Ideal.relNorm_apply, Ideal.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `h1 : algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) = ∏ σ : E ≃ₐ[ℚ] E, σ • x`. Apply `FaithfulSMul.algebraMap_injective (𝓞 E) E` to reduce the goal to its premises. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ ℚ E, Algebra.algebraMap_intNorm (L := E), Algebra.norm_eq_prod_automorphisms, map_prod]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) ∈ D ^ Module.finrank ℚ E`. Rewrite using `[h1, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.prod_const]`. Conclude with `Ideal.prod_mem_prod fun σ _ => galois_smul_mem_differentIdeal E σ hx`. Take `⟨L, hL⟩` from `Ideal.dvd_iff_le.mpr hle`.

Establish `h2` using `congrArg Ideal.absNorm hL`. Rewrite `h2` using `[Ideal.absNorm_algebraMap, map_mul, map_pow, hN, RingOfIntegers.rank, Ideal.absNorm_span_singleton, Algebra.norm_self]`. Establish `h0 : (discr E).natAbs ^ Module.finrank ℚ E ≠ 0` using `pow_ne_zero _ (Int.natAbs_ne_zero.mpr (discr_ne_zero E))`. Establish `h3 : Ideal.absNorm L = 1`. Apply `mul_left_cancel₀ h0` to reduce the goal to its premises.

Rewrite using `[mul_one]`. Conclude with `h2.symm`. Rewrite using `[hL, Ideal.absNorm_eq_one_iff.mp h3, Ideal.mul_top]`.
-/
theorem differentIdeal_pow_finrank_eq_span_discr :
    ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F],
      differentIdeal ℤ (𝓞 F) ^ Module.finrank ℚ F = Ideal.span {((discr F : ℤ) : 𝓞 F)} := by
  intro E _ _ _
  classical
  have hmap : Ideal.span {((discr E : ℤ) : 𝓞 E)} = (Ideal.span {discr E}).map (algebraMap ℤ (𝓞 E)) := by
    rw [Ideal.map_span, Set.image_singleton, eq_intCast]
  rw [hmap]
  set D := differentIdeal ℤ (𝓞 E) with hD
  have hN : Ideal.absNorm D = (discr E).natAbs := absNorm_differentIdeal E (𝓞 E)
  have hrel : Ideal.relNorm ℤ D = Ideal.span {discr E} := by
    rw [Ideal.relNorm_int, hN, Ideal.span_singleton_eq_span_singleton]
    exact (Int.associated_natAbs _).symm
  have hle : (Ideal.span {discr E}).map (algebraMap ℤ (𝓞 E)) ≤ D ^ Module.finrank ℚ E := by
    rw [← hrel, Ideal.map_le_iff_le_comap, Ideal.relNorm_apply, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) = ∏ σ : E ≃ₐ[ℚ] E, σ • x := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ ℚ E,
        Algebra.algebraMap_intNorm (L := E), Algebra.norm_eq_prod_automorphisms, map_prod]
      rfl
    change algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) ∈ D ^ Module.finrank ℚ E
    rw [h1, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, ← Finset.card_univ,
      ← Finset.prod_const]
    exact Ideal.prod_mem_prod fun σ _ => galois_smul_mem_differentIdeal E σ hx
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.mpr hle
  have h2 := congrArg Ideal.absNorm hL
  rw [Ideal.absNorm_algebraMap, map_mul, map_pow, hN, RingOfIntegers.rank,
    Ideal.absNorm_span_singleton, Algebra.norm_self] at h2
  have h0 : (discr E).natAbs ^ Module.finrank ℚ E ≠ 0 :=
    pow_ne_zero _ (Int.natAbs_ne_zero.mpr (discr_ne_zero E))
  have h3 : Ideal.absNorm L = 1 := by
    apply mul_left_cancel₀ h0
    rw [mul_one]
    exact h2.symm
  rw [hL, Ideal.absNorm_eq_one_iff.mp h3, Ideal.mul_top]

end GlobalTheory.GalDiff
