import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import GroundTheory.AutomorphicForms.ReductionIdele
import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

open scoped nonZeroDivisors in

/- English proof (translation)
Take `⟨D, hD0, hD⟩` from `exists_mul_mem_integralFiniteAdeles_of_isCompact hQ`. Use `set z : ℤ := Rat.ringOfIntegersEquiv D with hz`. Establish `hz0 : z ≠ 0`. Introduce `h`. Conclude with `hD0 (Rat.ringOfIntegersEquiv.injective (by rw [map_zero]; exact h))`.

Establish `hdz : algebraMap (𝓞 ℚ) ℚ D = z` using `(Rat.ringOfIntegersEquiv_apply_coe D).symm`. Use `⟨z.natAbs, Int.natAbs_pos.2 hz0, fun q hq => ?_⟩` and prove the remaining obligations. Establish `h1` using `hD _ hq`. Rewrite `h1` using `[← map_mul]`. Establish `h2 : algebraMap (𝓞 ℚ) ℚ D * q ∈ ((1 : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) : FractionalIdeal (𝓞 ℚ)⁰ ℚ)`.

Rewrite using `[← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]`. Conclude with `h1`. Rewrite `h2` using `[Units.val_one]`. Take `⟨r, hr⟩` from `(FractionalIdeal.mem_one_iff _).mp h2`. Establish `hn : ((Rat.ringOfIntegersEquiv r : ℤ) : ℚ) = (z : ℚ) * q`.

Rewrite using `[← hdz, ← hr]`. Conclude with `Rat.ringOfIntegersEquiv_apply_coe r |>.symm ▸ rfl`. Break down `Int.natAbs_eq z with h | h` into its components or cases. Use `⟨Rat.ringOfIntegersEquiv r, ?_⟩` and prove the remaining obligations. Establish `e1 : ((z.natAbs : ℕ) : ℤ) = z` using `by omega`.

Rewrite using `[hn, show ((z.natAbs : ℕ) : ℚ) = (z : ℚ) by rw [← Int.cast_natCast, e1]]`. Use `⟨-Rat.ringOfIntegersEquiv r, ?_⟩` and prove the remaining obligations. Establish `e1 : ((z.natAbs : ℕ) : ℤ) = -z` using `by omega`. Rewrite using `[Int.cast_neg, hn, show ((z.natAbs : ℕ) : ℚ) = -(z : ℚ) by`. Rewrite using `[← Int.cast_natCast, e1, Int.cast_neg], neg_mul]`.
-/
private theorem den_of {Q : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hQ : IsCompact Q) :
    ∃ d : ℕ, 0 < d ∧ ∀ q : ℚ, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ Q →
      ∃ l : ℤ, (d : ℚ) * q = l := by
  obtain ⟨D, hD0, hD⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hQ
  set z : ℤ := Rat.ringOfIntegersEquiv D with hz
  have hz0 : z ≠ 0 := by
    intro h
    exact hD0 (Rat.ringOfIntegersEquiv.injective (by rw [map_zero]; exact h))
  have hdz : algebraMap (𝓞 ℚ) ℚ D = z := (Rat.ringOfIntegersEquiv_apply_coe D).symm
  refine ⟨z.natAbs, Int.natAbs_pos.2 hz0, fun q hq => ?_⟩
  have h1 := hD _ hq
  rw [← map_mul] at h1
  have h2 : algebraMap (𝓞 ℚ) ℚ D * q ∈
      ((1 : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) : FractionalIdeal (𝓞 ℚ)⁰ ℚ) := by
    rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
    exact h1
  rw [Units.val_one] at h2
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
  have hn : ((Rat.ringOfIntegersEquiv r : ℤ) : ℚ) = (z : ℚ) * q := by
    rw [← hdz, ← hr]
    exact Rat.ringOfIntegersEquiv_apply_coe r |>.symm ▸ rfl
  rcases Int.natAbs_eq z with h | h
  · refine ⟨Rat.ringOfIntegersEquiv r, ?_⟩
    have e1 : ((z.natAbs : ℕ) : ℤ) = z := by omega
    rw [hn, show ((z.natAbs : ℕ) : ℚ) = (z : ℚ) by rw [← Int.cast_natCast, e1]]
  · refine ⟨-Rat.ringOfIntegersEquiv r, ?_⟩
    have e1 : ((z.natAbs : ℕ) : ℤ) = -z := by omega
    rw [Int.cast_neg, hn, show ((z.natAbs : ℕ) : ℚ) = -(z : ℚ) by
      rw [← Int.cast_natCast, e1, Int.cast_neg], neg_mul]

/- English proof (translation)
Take `⟨l, hl⟩` from `h`. Use `⟨c * l, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[mul_assoc, hl]`.
-/
private theorem mul_int {a : ℕ} {q : ℚ} (c : ℕ) (h : ∃ l : ℤ, (a : ℚ) * q = l) :
    ∃ l : ℤ, ((c * a : ℕ) : ℚ) * q = l := by
  obtain ⟨l, hl⟩ := h
  refine ⟨c * l, ?_⟩
  push_cast
  rw [mul_assoc, hl]

/- English proof (translation)
Introduce `L hL S hS`. Establish `hf : Continuous fun u : (A ℚ)ˣ => (u : A ℚ).2` using `continuous_snd.comp Units.continuous_val`. Establish `hi : Continuous fun u : (A ℚ)ˣ => ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2` using `continuous_snd.comp Units.continuous_coe_inv`. Establish `hp : ∀ i : Fin 2, Continuous fun v : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ => v i` using `fun i => continuous_apply i`. Use `set Q0 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) := (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (A ℚ)ˣ => p.1 0 * ((p.2⁻¹ : (A ℚ)ˣ) : A ℚ).2) '' (L ×ˢ S) with hQ0`.

Use `set Q2 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) := (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (A ℚ)ˣ => p.1 1 * (p.2 : A ℚ).2) '' (L ×ˢ S) with hQ2`. Use `set Q1 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) := (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (A ℚ)ˣ => (p.1 1 - p.2.1 1) * (p.2.2 : A ℚ).2) '' (L ×ˢ (L ×ˢ S)) with hQ1`. Establish `c0 : IsCompact Q0` using `(hL.prod hS).image (((hp 0).comp continuous_fst).mul (hi.comp continuous_snd))`. Establish `c2 : IsCompact Q2` using `(hL.prod hS).image (((hp 1).comp continuous_fst).mul (hf.comp continuous_snd))`. Establish `c1 : IsCompact Q1` using `(hL.prod (hL.prod hS)).image ((((hp 1).comp continuous_fst).sub ((hp 1).comp (continuous_fst.comp continuous_snd))).mul (hf.comp (continuous_snd.comp continuous_snd)))`.

Take `⟨d0, hd0, H0⟩` from `den_of c0`. Take `⟨d2, hd2, H2⟩` from `den_of c2`. Take `⟨d1, hd1, H1⟩` from `den_of c1`. Use `⟨d1 * d2 * d0, by positivity, fun u hu b ξ ξ' h h' => ?_⟩` and prove the remaining obligations. Establish `hu1 : (u : A ℚ).2 * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 = 1`.

Establish `h0 : (u : A ℚ) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ) = 1` using `Units.mul_inv u`. Conclude with `congrArg Prod.snd h0`. Establish `hu2 : ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 * (u : A ℚ).2 = 1`. Rewrite using `[mul_comm, hu1]`. Use `⟨mul_int _ (H0 _ ⟨(_, u), ⟨h, hu⟩, ?_⟩), fun e => ?_, fun e => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * (u : A ℚ).2 * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 = _`. Rewrite using `[mul_assoc, hu1, mul_one]`. Use `H2 (ξ 1) ⟨(_, u), ⟨h, hu⟩, by` as an intermediate fact. Express the relevant statement in the definitionally equal form `(algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 * (u : A ℚ).2 = _`. Rewrite using `[e, map_zero, zero_mul, zero_add, mul_assoc, hu2, mul_one]⟩`.

Take `⟨l, hl⟩` from `this`. Use `⟨d1 * l * d0, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← hl]`. Expand and normalize the polynomial expressions, which then agree.

Use `H1 (ξ 1 - ξ' 1) ⟨(_, _, u), ⟨h, h', hu⟩, by` as an intermediate fact. Express the relevant statement in the definitionally equal form `((algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 - (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 0) * b + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2) * (u : A ℚ).2 = _`. Rewrite using `[e, ← sub_mul, mul_assoc, hu2, mul_one, map_sub]`. Use the proof step `ring⟩`. Take `⟨l, hl⟩` from `this`.

Use `⟨d2 * l * d0, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← hl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.exists_common_denom_of_isCompact_unipotent_translates :
    ∀ (L : Set (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ)), IsCompact L → ∀ S : Set (A ℚ)ˣ, IsCompact S →
        ∃ d : ℕ, 0 < d ∧ ∀ u ∈ S, ∀ (b : FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ ξ' : Fin 2 → ℚ),
          (![algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * (u : A ℚ).2,
              (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2]) ∈ L →
          (![algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 0) * (u : A ℚ).2,
              (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 0) * b + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2]) ∈ L →
          (∃ l : ℤ, (d : ℚ) * ξ 0 = l) ∧ (ξ 0 = 0 → ∃ l : ℤ, (d : ℚ) * ξ 1 = l) ∧
            (ξ 0 = ξ' 0 → ∃ l : ℤ, (d : ℚ) * (ξ 1 - ξ' 1) = l) := by
  intro L hL S hS
  have hf : Continuous fun u : (A ℚ)ˣ => (u : A ℚ).2 :=
    continuous_snd.comp Units.continuous_val
  have hi : Continuous fun u : (A ℚ)ˣ => ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  have hp : ∀ i : Fin 2, Continuous fun v : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ => v i :=
    fun i => continuous_apply i
  set Q0 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (A ℚ)ˣ =>
      p.1 0 * ((p.2⁻¹ : (A ℚ)ˣ) : A ℚ).2) '' (L ×ˢ S) with hQ0
  set Q2 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (A ℚ)ˣ => p.1 1 * (p.2 : A ℚ).2) '' (L ×ˢ S)
    with hQ2
  set Q1 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (A ℚ)ˣ =>
      (p.1 1 - p.2.1 1) * (p.2.2 : A ℚ).2) '' (L ×ˢ (L ×ˢ S)) with hQ1
  have c0 : IsCompact Q0 := (hL.prod hS).image
    (((hp 0).comp continuous_fst).mul (hi.comp continuous_snd))
  have c2 : IsCompact Q2 := (hL.prod hS).image
    (((hp 1).comp continuous_fst).mul (hf.comp continuous_snd))
  have c1 : IsCompact Q1 := (hL.prod (hL.prod hS)).image
    ((((hp 1).comp continuous_fst).sub ((hp 1).comp (continuous_fst.comp continuous_snd))).mul
      (hf.comp (continuous_snd.comp continuous_snd)))
  obtain ⟨d0, hd0, H0⟩ := den_of c0
  obtain ⟨d2, hd2, H2⟩ := den_of c2
  obtain ⟨d1, hd1, H1⟩ := den_of c1
  refine ⟨d1 * d2 * d0, by positivity, fun u hu b ξ ξ' h h' => ?_⟩
  have hu1 : (u : A ℚ).2 * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 = 1 := by
    have h0 : (u : A ℚ) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := Units.mul_inv u
    exact congrArg Prod.snd h0
  have hu2 : ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 * (u : A ℚ).2 = 1 := by
    rw [mul_comm, hu1]
  refine ⟨mul_int _ (H0 _ ⟨(_, u), ⟨h, hu⟩, ?_⟩), fun e => ?_, fun e => ?_⟩
  · change algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * (u : A ℚ).2 *
      ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 = _
    rw [mul_assoc, hu1, mul_one]
  · have := H2 (ξ 1) ⟨(_, u), ⟨h, hu⟩, by
      change (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b +
        algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 * (u : A ℚ).2 = _
      rw [e, map_zero, zero_mul, zero_add, mul_assoc, hu2, mul_one]⟩
    obtain ⟨l, hl⟩ := this
    refine ⟨d1 * l * d0, ?_⟩
    push_cast
    rw [← hl]
    ring
  · have := H1 (ξ 1 - ξ' 1) ⟨(_, _, u), ⟨h, h', hu⟩, by
      change ((algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b +
        algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 -
        (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 0) * b +
        algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2) * (u : A ℚ).2 = _
      rw [e, ← sub_mul, mul_assoc, hu2, mul_one, map_sub]
      ring⟩
    obtain ⟨l, hl⟩ := this
    refine ⟨d2 * l * d0, ?_⟩
    push_cast
    rw [← hl]
    ring
