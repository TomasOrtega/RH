import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdeleTranslateIntegralAdditiveTotalPropertiesStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
open IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.WpFam.TrIs

/- English proof (translation)
Introduce `K _ _ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hT`. Take `⟨_, _, _, hL0, ⟨𝔞, h𝔞, hL1⟩, _, _, _⟩` from `hT`. Take `⟨hsub, _, hleft, hright⟩` from `GlobalTheory.T.isIdeleTranslateIntegral_additive_total_properties K t`. Establish `hA : ∀ y : Af K, y ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) ↔ ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (y v) ≤ 1` using `fun y => GlobalTheory.Idele.mem_adelicIdeal_one_iff`. Establish `hone : ∀ x : K, x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔ algebraMap K (Af K) x ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K)` using `fun x => (GlobalTheory.Idele.algebraMap_mem_adelicIdeal (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) x).symm`.

Establish `hmem𝔞 : ∀ a' : K, a' ∈ 𝔞 ↔ (t : Af K) * algebraMap K (Af K) a' ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K)`. Introduce `a'`. Rewrite using `[h𝔞, hA]`. Establish `hL0' : ∀ z, z ∈ Λ₀.lattice ↔ z ∈ ι '' ((1 : FractionalIdeal (𝓞 K)⁰ K) : Set K)` using `fun z => Set.ext_iff.1 hL0 z`. Establish `hL1' : ∀ z, z ∈ Λ₁.lattice ↔ z ∈ ι '' ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Set K)` using `fun z => Set.ext_iff.1 hL1 z`.

Establish `h0 : ∀ a : K, ι a ∈ Λ₀.lattice ↔ a ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)`. Introduce `a`. Rewrite using `[hL0']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, e⟩`.

Rewrite using `[← ι.injective e]` and apply the resulting hypothesis. Introduce `h`. Conclude with `⟨a, h, rfl⟩`. Establish `h1 : ∀ a' : K, ι a' ∈ Λ₁.lattice ↔ a' ∈ 𝔞`. Introduce `a'`.

Rewrite using `[hL1']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, e⟩`. Rewrite using `[← ι.injective e]` and apply the resulting hypothesis. Introduce `h`.

Conclude with `⟨a', h, rfl⟩`. Establish `hTr : ∀ x x' : K, Tr t x x' ↔ (t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K)` using `fun x x' => (hA _).symm`. Use `⟨hsub, ?_, ?_, hleft, hright, ?_, ?_⟩` and prove the remaining obligations. Introduce `x x' h`. Establish `hd` using `(hTr x x').1 h`.

Rewrite using `[h0, h1, hone, hmem𝔞]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `add_mem hd hx` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Introduce `hx`. Use `sub_mem hx hd` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Introduce `x x' hx hx'`. Rewrite using `[hTr]`.

Conclude with `sub_mem ((hmem𝔞 x').1 ((h1 x').1 hx')) ((hone x).1 ((h0 x).1 hx))`. Introduce `z hz`. Take `⟨k, -, e⟩` from `(hL0' z).1 hz`. Conclude with `⟨k, e⟩`. Introduce `z hz`.

Take `⟨k, -, e⟩` from `(hL1' z).1 hz`. Conclude with `⟨k, e⟩`.
-/
theorem main : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → IsTr ι Λ₀ Λ₁ (Tr t) := by
  intro K _ _ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hT
  obtain ⟨_, _, _, hL0, ⟨𝔞, h𝔞, hL1⟩, _, _, _⟩ := hT
  obtain ⟨hsub, _, hleft, hright⟩ := GlobalTheory.T.isIdeleTranslateIntegral_additive_total_properties K t
  have hA : ∀ y : Af K, y ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (y v) ≤ 1 := fun y => GlobalTheory.Idele.mem_adelicIdeal_one_iff
  have hone : ∀ x : K, x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      algebraMap K (Af K) x ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := fun x =>
    (GlobalTheory.Idele.algebraMap_mem_adelicIdeal (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) x).symm
  have hmem𝔞 : ∀ a' : K, a' ∈ 𝔞 ↔ (t : Af K) * algebraMap K (Af K) a' ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a'
    rw [h𝔞, hA]
  have hL0' : ∀ z, z ∈ Λ₀.lattice ↔ z ∈ ι '' ((1 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL0 z
  have hL1' : ∀ z, z ∈ Λ₁.lattice ↔ z ∈ ι '' ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL1 z
  have h0 : ∀ a : K, ι a ∈ Λ₀.lattice ↔ a ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a
    rw [hL0']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← ι.injective e]
    · intro h; exact ⟨a, h, rfl⟩
  have h1 : ∀ a' : K, ι a' ∈ Λ₁.lattice ↔ a' ∈ 𝔞 := by
    intro a'
    rw [hL1']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← ι.injective e]
    · intro h; exact ⟨a', h, rfl⟩
  have hTr : ∀ x x' : K, Tr t x x' ↔ (t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := fun x x' => (hA _).symm
  refine ⟨hsub, ?_, ?_, hleft, hright, ?_, ?_⟩
  · intro x x' h
    have hd := (hTr x x').1 h
    rw [h0, h1, hone, hmem𝔞]
    constructor
    · intro hx
      have := add_mem hd hx
      rwa [sub_add_cancel] at this
    · intro hx
      have := sub_mem hx hd
      rwa [sub_sub_cancel] at this
  · intro x x' hx hx'
    rw [hTr]
    exact sub_mem ((hmem𝔞 x').1 ((h1 x').1 hx')) ((hone x).1 ((h0 x).1 hx))
  · intro z hz
    obtain ⟨k, -, e⟩ := (hL0' z).1 hz
    exact ⟨k, e⟩
  · intro z hz
    obtain ⟨k, -, e⟩ := (hL1' z).1 hz
    exact ⟨k, e⟩

end GlobalTheory.WpFam.TrIs
