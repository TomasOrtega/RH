import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm Module
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.CovIdeal

open GlobalTheory.LatFacts

variable (E : Type) [Field E] [NumberField E]

def lat (I : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) (Fin 1 → E) :=
  (I : Submodule (𝓞 E) E).comap (LinearMap.proj 0)

/- English proof (translation)
Simplify using `[lat]`.
-/
theorem mem_lat (I : FractionalIdeal (𝓞 E)⁰ E) (y : Fin 1 → E) : y ∈ lat E I ↔ y 0 ∈ I := by
  simp [lat]

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[mem_lat, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨y 0, h, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `a`. Use `fin_cases a`. Simplify using the standard rewrite rules. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify using `using hx`.
-/
theorem lat_eq_map (I : FractionalIdeal (𝓞 E)⁰ E) :
    lat E I = (I : Submodule (𝓞 E) E).map (LinearMap.single (𝓞 E) (fun _ : Fin 1 => E) 0) := by
  ext y
  rw [mem_lat, Submodule.mem_map]
  constructor
  · intro h
    refine ⟨y 0, h, ?_⟩
    funext a
    fin_cases a
    simp
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

/- English proof (translation)
Rewrite using `[lat_eq_map]`. Conclude with `(FractionalIdeal.fg_of_isNoetherianRing le_rfl I).map _`. Use `span_eq_top := by`. Establish `hbot : (I : Submodule (𝓞 E) E) ≠ ⊥` using `fun h => hI (FractionalIdeal.coeToSubmodule_eq_bot.1 h)`. Take `⟨c, hcI, hc0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hbot`.

Rewrite using `[eq_top_iff]`. Introduce `v _`. Establish `hv : v = (v 0 / c) • (Pi.single 0 c : Fin 1 → E)`. Use function extensionality and compare the values at `a`. Use `fin_cases a`.

Simplify using `[hc0]`. Rewrite using `[hv]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, mem_lat]`. Simplify using `using hcI`.
-/
theorem isLattice_lat (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) : Submodule.IsLattice E (lat E I) where
  fg := by
    rw [lat_eq_map]
    exact (FractionalIdeal.fg_of_isNoetherianRing le_rfl I).map _
  span_eq_top := by
    have hbot : (I : Submodule (𝓞 E) E) ≠ ⊥ := fun h => hI (FractionalIdeal.coeToSubmodule_eq_bot.1 h)
    obtain ⟨c, hcI, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    rw [eq_top_iff]
    intro v _
    have hv : v = (v 0 / c) • (Pi.single 0 c : Fin 1 → E) := by
      funext a
      fin_cases a
      simp [hc0]
    rw [hv]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [SetLike.mem_coe, mem_lat]
    simpa using hcI

/- English proof (translation)
Use `set B := mixedEmbedding.fractionalIdealLatticeBasis E I`. Set `φ : mixedEmbedding.mixedSpace E →ₗ[ℤ] VecInf E 1` to `((mix E 1).toLinearMap.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin 1 => mixedEmbedding.mixedSpace E) 0)).toIntLinearMap`. Establish `hφ : ∀ z, φ z = mix E 1 (Pi.single 0 z)` using `fun _ => rfl`. Establish `key : ∀ (y : Fin 1 → E) (w : InfinitePlace E), (Matrix.of (oneInf E 1 w))⁻¹ *ᵥ (fun a => w.embedding (y a)) = φ (mixedEmbedding E (y 0)) w`. Introduce `y w`.

Rewrite using `[of_oneInf, inv_one, one_mulVec, hφ]`. Use function extensionality and compare the values at `a`. Use `fin_cases a`. Simplify using `[mix_apply]`. Establish `hrange : Set.range ((Pi.basis fun _ : Fin 1 => B).map (mix E 1)) = φ '' Set.range B`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, k⟩, rfl⟩`. Establish `ha : a = 0` using `Subsingleton.elim _ _`. Substitute `ha` using the available equality.

Conclude with `⟨B k, ⟨k, rfl⟩, by simp [hφ, Basis.map_apply, Pi.basis_apply]⟩`. Introduce and unpack `⟨_, ⟨k, rfl⟩, rfl⟩`. Conclude with `⟨⟨0, k⟩, by simp [hφ, Basis.map_apply, Pi.basis_apply]⟩`. Establish `hspan : Submodule.span ℤ (mixedEmbedding E '' (I.1 : Set E)) = Submodule.span ℤ (Set.range B)` using `by conv_rhs => rw [← Submodule.span_eq (Submodule.span ℤ (Set.range B))]`. Use `congr 1`.

Use extensionality with `x`. Rewrite using `[SetLike.mem_coe, mixedEmbedding.mem_span_fractionalIdealLatticeBasis]`. Unfold `latAt`. Rewrite using `[hrange, Submodule.span_image, ← hspan, ← Submodule.span_image, ← Set.image_comp]`. Use `congr 1`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y 0, (mem_lat E _ y).1 hy, funext fun w => (key y w).symm⟩`. Introduce and unpack `⟨t, ht, rfl⟩`.

Conclude with `⟨fun _ => t, (mem_lat E _ _).2 ht, funext fun w => key _ w⟩`.
-/
theorem latAt_lat [IsTotallyComplex E] (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    latAt E 1 (lat E I.1) (oneInf E 1) = Submodule.span ℤ (Set.range
      ((Pi.basis fun _ : Fin 1 => mixedEmbedding.fractionalIdealLatticeBasis E I).map (mix E 1))) := by
  set B := mixedEmbedding.fractionalIdealLatticeBasis E I

  let φ : mixedEmbedding.mixedSpace E →ₗ[ℤ] VecInf E 1 :=
    ((mix E 1).toLinearMap.toAddMonoidHom.comp
      (AddMonoidHom.single (fun _ : Fin 1 => mixedEmbedding.mixedSpace E) 0)).toIntLinearMap
  have hφ : ∀ z, φ z = mix E 1 (Pi.single 0 z) := fun _ => rfl

  have key : ∀ (y : Fin 1 → E) (w : InfinitePlace E),
      (Matrix.of (oneInf E 1 w))⁻¹ *ᵥ (fun a => w.embedding (y a)) = φ (mixedEmbedding E (y 0)) w := by
    intro y w
    rw [of_oneInf, inv_one, one_mulVec, hφ]
    funext a
    fin_cases a
    simp [mix_apply]
  have hrange : Set.range ((Pi.basis fun _ : Fin 1 => B).map (mix E 1)) = φ '' Set.range B := by
    ext x
    constructor
    · rintro ⟨⟨a, k⟩, rfl⟩
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      exact ⟨B k, ⟨k, rfl⟩, by simp [hφ, Basis.map_apply, Pi.basis_apply]⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨⟨0, k⟩, by simp [hφ, Basis.map_apply, Pi.basis_apply]⟩

  have hspan : Submodule.span ℤ (mixedEmbedding E '' (I.1 : Set E)) = Submodule.span ℤ (Set.range B) := by
    conv_rhs => rw [← Submodule.span_eq (Submodule.span ℤ (Set.range B))]
    congr 1
    ext x
    rw [SetLike.mem_coe, mixedEmbedding.mem_span_fractionalIdealLatticeBasis]
  unfold latAt
  rw [hrange, Submodule.span_image, ← hspan, ← Submodule.span_image, ← Set.image_comp]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y 0, (mem_lat E _ y).1 hy, funext fun w => (key y w).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨fun _ => t, (mem_lat E _ _).2 ht, funext fun w => key _ w⟩

/- English proof (translation)
Establish `hO` using `volume_fd_intB E 1`. Rewrite `hO` using `[mul_one, intB, volume_fd_map, pow_one, measureReal_def]`. Rewrite using `[latAt_lat, covAt_span, volume_fd_map, pow_one, measureReal_def, mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)), hO]`.
-/
theorem covAt_lat [IsTotallyComplex E] (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    covAt E 1 (latAt E 1 (lat E I.1) (oneInf E 1)) =
      (FractionalIdeal.absNorm I.1 : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E := by

  have hO := volume_fd_intB E 1
  rw [mul_one, intB, volume_fd_map, pow_one, measureReal_def] at hO

  rw [latAt_lat, covAt_span, volume_fd_map, pow_one, measureReal_def,
    mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)), hO]

/- English proof (translation)
Introduce `E _ _ hE 𝔞 h𝔞`. Establish `hne : (𝔞 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]` and apply the resulting hypothesis. Set `J : (FractionalIdeal (𝓞 E)⁰ E)ˣ` to `Units.mk0 (𝔞 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ (inv_ne_zero hne)`. Use `⟨lat E J.1, fun y => ?_, isLattice_lat E J.1 (inv_ne_zero hne), ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_lat]`. Express the relevant statement in the definitionally equal form `y 0 ∈ (𝔞 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ↔ _`. Rewrite using `[FractionalIdeal.mem_inv_iff hne]`. Prove the components needed by the constructor for the conclusion. Introduce `h t ht`.

Take `⟨r, hr⟩` from `(FractionalIdeal.mem_one_iff _).1 (h (t : E) (FractionalIdeal.mem_coeIdeal_of_mem _ ht))`. Conclude with `⟨r, by rw [hr, mul_comm]⟩`. Introduce `h x hx`. Take `⟨t, ht, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hx`. Take `⟨r, hr⟩` from `h t ht`.

Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨r, by rw [hr, mul_comm]⟩`. Use `hE` as an intermediate fact. Rewrite using `[covAt_lat E J]`. Express the relevant statement in the definitionally equal form `(FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : ℝ) * _ = _`. Rewrite using `[map_inv₀, FractionalIdeal.coeIdeal_absNorm]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem covolume_inv_ideal : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ Λ₀ : Submodule (𝓞 E) (Fin 1 → E), (∀ y, y ∈ Λ₀ ↔ ∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Submodule.IsLattice E Λ₀ ∧ covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) = Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E / (Ideal.absNorm 𝔞 : ℝ) := by
  intro E _ _ hE 𝔞 h𝔞
  have hne : (𝔞 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]

  let J : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mk0 (𝔞 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ (inv_ne_zero hne)
  refine ⟨lat E J.1, fun y => ?_, isLattice_lat E J.1 (inv_ne_zero hne), ?_⟩
  · rw [mem_lat]
    change y 0 ∈ (𝔞 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ↔ _
    rw [FractionalIdeal.mem_inv_iff hne]
    constructor
    · intro h t ht
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1
        (h (t : E) (FractionalIdeal.mem_coeIdeal_of_mem _ ht))
      exact ⟨r, by rw [hr, mul_comm]⟩
    · intro h x hx
      obtain ⟨t, ht, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      obtain ⟨r, hr⟩ := h t ht
      exact (FractionalIdeal.mem_one_iff _).2 ⟨r, by rw [hr, mul_comm]⟩
  · have := hE
    rw [covAt_lat E J]
    change (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : ℝ) * _ = _
    rw [map_inv₀, FractionalIdeal.coeIdeal_absNorm]
    push_cast
    ring

end GlobalTheory.CovIdeal
