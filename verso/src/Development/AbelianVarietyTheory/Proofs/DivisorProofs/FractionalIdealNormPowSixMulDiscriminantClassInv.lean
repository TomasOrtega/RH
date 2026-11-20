import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.DiscClass

/- English proof (translation)
Set `e : (Λ.lattice : Set ℂ) ≃ (Λ'.lattice : Set ℂ)` to `(Equiv.mulLeft₀ u hu).subtypeEquiv fun w => by simpa using (h w).symm`. Establish `h2 : ∀ P : PeriodPair, P.G k = ∑' w : (P.lattice : Set ℂ), ((w : ℂ) ^ k)⁻¹` using `fun _ => rfl`. Rewrite using `[h2, h2, ← e.tsum_eq, ← tsum_mul_left]`. Use `tsum_congr fun w => ?_` and prove the remaining obligations. Establish `: ((e w : (Λ'.lattice : Set ℂ)) : ℂ) = u * w` using `rfl`.

Rewrite using `[this, mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu), one_mul]`.
-/
theorem G_eq_of_mul (Λ Λ' : PeriodPair) (u : ℂ) (hu : u ≠ 0) (h : ∀ w, u * w ∈ Λ'.lattice ↔ w ∈ Λ.lattice) (k : ℕ) :
    Λ.G k = u ^ k * Λ'.G k := by
  let e : (Λ.lattice : Set ℂ) ≃ (Λ'.lattice : Set ℂ) :=
    (Equiv.mulLeft₀ u hu).subtypeEquiv fun w => by simpa using (h w).symm
  have h2 : ∀ P : PeriodPair, P.G k = ∑' w : (P.lattice : Set ℂ), ((w : ℂ) ^ k)⁻¹ := fun _ => rfl
  rw [h2, h2, ← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun w => ?_
  have : ((e w : (Λ'.lattice : Set ℂ)) : ℂ) = u * w := rfl
  rw [this, mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu), one_mul]

/- English proof (translation)
Simplify using `only [latDisc, PeriodPair.g₂, PeriodPair.g₃, G_eq_of_mul Λ Λ' u hu h 4, G_eq_of_mul Λ Λ' u hu h 6]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem latDisc_eq_of_mul (Λ Λ' : PeriodPair) (u : ℂ) (hu : u ≠ 0) (h : ∀ w, u * w ∈ Λ'.lattice ↔ w ∈ Λ.lattice) :
    latDisc Λ = u ^ 12 * latDisc Λ' := by
  simp only [latDisc, PeriodPair.g₂, PeriodPair.g₃, G_eq_of_mul Λ Λ' u hu h 4, G_eq_of_mul Λ Λ' u hu h 6]
  ring

/- English proof (translation)
Establish `hcx : (InfinitePlace.mk φK).IsComplex`. Rewrite using `[InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_iff]`. Introduce `e`. Apply `hc` to reduce the goal to its premises. Use extensionality with `y`.

Simplify using `only [RingHom.comp_apply]`. Rewrite using `[← ComplexEmbedding.conjugate_coe_eq, e]`. Establish `hpos : 0 < InfinitePlace.nrComplexPlaces K` using `by classical`. Unfold `InfinitePlace.nrComplexPlaces`. Use `Fintype.card_pos_iff.2 (⟨⟨_, hcx⟩⟩ : Nonempty {w : InfinitePlace K // w.IsComplex})` and compare the differences between its conclusion and the goal.

Establish `hr` using `InfinitePlace.card_add_two_mul_card_eq_rank K`. Establish `hcard : Fintype.card (InfinitePlace K) = 1`. Rewrite using `[InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]`. Use linear arithmetic over natural numbers and integers. Establish `huniq : ∀ w : InfinitePlace K, w = InfinitePlace.mk φK` using `fun w => Fintype.card_le_one_iff.1 hcard.le w _`.

Establish `hp` using `InfinitePlace.prod_eq_abs_norm x`. Establish `e : (∏ w : InfinitePlace K, w x ^ w.mult) = InfinitePlace.mk φK x ^ (InfinitePlace.mk φK).mult`. Rewrite using `[Fintype.prod_eq_single (InfinitePlace.mk φK) fun w hw => absurd (huniq w) hw]`. Rewrite using `[← hp, e, InfinitePlace.apply, InfinitePlace.mult_isComplex ⟨_, hcx⟩]`.
-/
theorem abs_norm_eq_norm_sq {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (h2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (x : K) :
    ((|Algebra.norm ℚ x| : ℚ) : ℝ) = ‖φK x‖ ^ 2 := by
  have hcx : (InfinitePlace.mk φK).IsComplex := by
    rw [InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_iff]
    intro e
    apply hc
    ext y
    simp only [RingHom.comp_apply]
    rw [← ComplexEmbedding.conjugate_coe_eq, e]
  have hpos : 0 < InfinitePlace.nrComplexPlaces K := by
    classical
    unfold InfinitePlace.nrComplexPlaces
    convert Fintype.card_pos_iff.2 (⟨⟨_, hcx⟩⟩ : Nonempty {w : InfinitePlace K // w.IsComplex})
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hcard : Fintype.card (InfinitePlace K) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]; omega
  have huniq : ∀ w : InfinitePlace K, w = InfinitePlace.mk φK := fun w =>
    Fintype.card_le_one_iff.1 hcard.le w _
  have hp := InfinitePlace.prod_eq_abs_norm x
  have e : (∏ w : InfinitePlace K, w x ^ w.mult) = InfinitePlace.mk φK x ^ (InfinitePlace.mk φK).mult := by
    rw [Fintype.prod_eq_single (InfinitePlace.mk φK) fun w hw => absurd (huniq w) hw]
  rw [← hp, e, InfinitePlace.apply, InfinitePlace.mult_isComplex ⟨_, hcx⟩]

/- English proof (translation)
Establish `h1 : ClassGroup.mk K (𝔟 * 𝔞⁻¹) = 1` using `by rw [map_mul, map_inv, ← hcl, mul_inv_cancel]`. Take `⟨c, hcE⟩` from `(FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h1)`. Establish `hb' : (𝔟 : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ c * 𝔞`. Rewrite using `[← hcE, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]`. Establish `hc0 : c ≠ 0`.

Introduce and unpack `rfl`. Apply `𝔟.ne_zero` to reduce the goal to its premises. Rewrite using `[hb', FractionalIdeal.spanSingleton_zero, zero_mul]`. Establish `hu : φK c ≠ 0` using `(map_ne_zero φK).2 hc0`. Establish `hlat : ∀ w, φK c * w ∈ Λb.lattice ↔ w ∈ Λa.lattice`.

Introduce `w`. Establish `eb : φK c * w ∈ Λb.lattice ↔ φK c * w ∈ φK '' ((𝔟 : FractionalIdeal (𝓞 K)⁰ K) : Set K)`. Rewrite using `[← hb]`. Both sides reduce to the same expression. Establish `ea : w ∈ Λa.lattice ↔ w ∈ φK '' ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Set K)`.

Rewrite using `[← ha]`. Both sides reduce to the same expression. Rewrite using `[eb, ea]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, e⟩`.

Establish `hy' : y ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K)` using `hy`. Rewrite `hy'` using `[hb', FractionalIdeal.mem_singleton_mul]`. Take `⟨y', hy', rfl⟩` from `hy'`. Use `⟨y', hy', ?_⟩` and prove the remaining obligations. Rewrite `e` using `[map_mul]`.

Conclude with `mul_left_cancel₀ hu e`. Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨c * y, ?_, map_mul _ _ _⟩` and prove the remaining obligations. Use `show c * y ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K)`. Rewrite using `[hb', FractionalIdeal.mem_singleton_mul]`.

Conclude with `⟨y, hy, rfl⟩`. Establish `hD` using `latDisc_eq_of_mul Λa Λb (φK c) hu hlat`. Establish `hN : nrm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) = ‖φK c‖ ^ 2 * nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K)`. Unfold `nrm`. Rewrite using `[hb', map_mul, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, abs_norm_eq_norm_sq φK h2 hc c]`.

Rewrite using `[hN, hD, norm_mul, norm_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nrm_pow_mul_norm_latDisc_eq {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (h2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λa Λb : PeriodPair)
    (ha : IsLatOf φK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) Λa) (hb : IsLatOf φK (𝔟 : FractionalIdeal (𝓞 K)⁰ K) Λb)
    (hcl : ClassGroup.mk K 𝔞 = ClassGroup.mk K 𝔟) :
    nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λa‖ = nrm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λb‖ := by

  have h1 : ClassGroup.mk K (𝔟 * 𝔞⁻¹) = 1 := by rw [map_mul, map_inv, ← hcl, mul_inv_cancel]
  obtain ⟨c, hcE⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h1)
  have hb' : (𝔟 : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ c * 𝔞 := by
    rw [← hcE, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply 𝔟.ne_zero
    rw [hb', FractionalIdeal.spanSingleton_zero, zero_mul]
  have hu : φK c ≠ 0 := (map_ne_zero φK).2 hc0

  have hlat : ∀ w, φK c * w ∈ Λb.lattice ↔ w ∈ Λa.lattice := by
    intro w
    have eb : φK c * w ∈ Λb.lattice ↔ φK c * w ∈ φK '' ((𝔟 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
      rw [← hb]; rfl
    have ea : w ∈ Λa.lattice ↔ w ∈ φK '' ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
      rw [← ha]; rfl
    rw [eb, ea]
    constructor
    · rintro ⟨y, hy, e⟩
      have hy' : y ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K) := hy
      rw [hb', FractionalIdeal.mem_singleton_mul] at hy'
      obtain ⟨y', hy', rfl⟩ := hy'
      refine ⟨y', hy', ?_⟩
      rw [map_mul] at e
      exact mul_left_cancel₀ hu e
    · rintro ⟨y, hy, rfl⟩
      refine ⟨c * y, ?_, map_mul _ _ _⟩
      show c * y ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K)
      rw [hb', FractionalIdeal.mem_singleton_mul]
      exact ⟨y, hy, rfl⟩
  have hD := latDisc_eq_of_mul Λa Λb (φK c) hu hlat

  have hN : nrm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) = ‖φK c‖ ^ 2 * nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
    unfold nrm
    rw [hb', map_mul, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, abs_norm_eq_norm_sq φK h2 hc c]
  rw [hN, hD, norm_mul, norm_pow]
  ring

end GlobalTheory.DiscClass
