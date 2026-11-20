import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDehomIdeal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartZeroSet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartSet chartLift segre_chartLift chartLift_segre_apply)

/- English proof (translation)
Introduce `K _ _ ι _ P m σ i hP`. Use `set Q : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hQ`. Use `set J : Ideal (MvPolynomial (Σ k, ι k) ℂ) := Q ⊔ dehomIdeal i with hJ`. Use `set G : Fin m → MvPolynomial (Σ k, ι k) ℂ := fun a => ∏ k, X ⟨k, σ a k⟩ with hG`. Establish `hseg : ∀ f, segreDehom σ i f = dehom i (aeval G f)`.

Introduce `f`. Rewrite using `[← AlgHom.comp_apply, comp_aeval]`. Both sides reduce to the same expression. Establish `hcomap : ((Q.map (dehom i)).radical).comap (dehom i) = J.radical`. Establish `hd : (dehom i : MvPolynomial (Σ k, ι k) ℂ →+* DehomRing i) = Ideal.Quotient.mk (dehomIdeal i)` using `rfl`.

Rewrite using `[← Ideal.comap_coe (dehom i), ← Ideal.map_coe (dehom i), Ideal.comap_radical, hd, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]`. Establish `hval : ∀ (y : (Σ k, ι k) → ℂ) (f : MvPolynomial (Fin m) ℂ), aeval (R` using `ℂ) y (aeval G f) = aeval (R := ℂ) (fun a => segre y (σ a)) f := by`. Introduce `y f`. Rewrite using `[← AlgHom.comp_apply, comp_aeval]`. Use `congr 2`.

Use function extensionality and compare the values at `a`. Simplify using `[hG, segre]`. Establish `hzero : ∀ y : (Σ k, ι k) → ℂ, y ∈ zeroLocus ℂ J ↔ y ∈ mcPts P ∧ ∀ k, y ⟨k, i k⟩ = 1`. Introduce `y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Establish `h1 : ∀ k, y ⟨k, i k⟩ = 1` using `fun k => by`. Use `hy _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`. Use `⟨⟨fun k => ⟨i k, by simp [h1 k]⟩, fun f hf => ?_⟩, h1⟩` and prove the remaining obligations.

Use `hy _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))` as an intermediate fact. Conclude with `this`. Introduce and unpack `⟨hy, h1⟩`. Establish `hle : J ≤ RingHom.ker (aeval (R` using `ℂ) y : MvPolynomial (Σ k, ι k) ℂ →+* ℂ) := by`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Rewrite using `[hQ, Ideal.map_le_iff_le_comap]`. Introduce `f hf`. Conclude with `hy.2 f hf`. Rewrite using `[dehomIdeal, Ideal.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`.

Simplify using `[RingHom.mem_ker, h1 k]`. Conclude with `fun p hp => hle hp`. Use extensionality with `f`. Rewrite using `[Ideal.mem_comap, hseg, ← Ideal.mem_comap, hcomap, ← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), segreChartIdeal, mem_vanishingIdeal_iff, mem_vanishingIdeal_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `hf y hy`. Rewrite using `[hval]`. Take `⟨hym, h1⟩` from `(hzero y).1 hy`. Use `hf _ ⟨y, hym, ?_, rfl⟩` and prove the remaining obligations. Simplify using `[segre, h1]`.

Introduce and unpack `hf x ⟨z, hz, hzi, rfl⟩`. Establish `hne : ∀ k, z ⟨k, i k⟩ ≠ 0` using `fun k h0 => by`. Establish `h` using `Finset.prod_eq_zero (f := fun k => z ⟨k, i k⟩) (Finset.mem_univ k) h0`. Conclude with `one_ne_zero ((show segre z i = 1 from hzi).symm.trans h)`. Use `set y := chartLift σ i (fun a => segre z (σ a)) with hy`.

Establish `hyz : y = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p`. Use function extensionality and compare the values at `p`. Rewrite using `[hy, chartLift_segre_apply σ i z hzi p.1 p.2, mul_comm]`. Establish `hym : y ∈ mcPts P`. Rewrite using `[hyz]`.

Conclude with `SegreChartZeroSet.scaleAll_mem P hP (fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz`. Establish `h1 : ∀ k, y ⟨k, i k⟩ = 1` using `fun k => by`. Rewrite using `[hyz]`. Conclude with `inv_mul_cancel₀ (hne k)`. Use `hf y ((hzero y).2 ⟨hym, h1⟩)` as an intermediate fact.

Rewrite `this` using `[hval, hy, segre_chartLift σ i z hzi]`. Then use the resulting hypothesis.
-/
theorem ChartDehomIdeal.proof : ChartDehomIdeal.Statement := by
  intro K _ _ ι _ P m σ i hP
  classical
  set Q : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hQ
  set J : Ideal (MvPolynomial (Σ k, ι k) ℂ) := Q ⊔ dehomIdeal i with hJ
  set G : Fin m → MvPolynomial (Σ k, ι k) ℂ := fun a => ∏ k, X ⟨k, σ a k⟩ with hG

  have hseg : ∀ f, segreDehom σ i f = dehom i (aeval G f) := by
    intro f
    rw [← AlgHom.comp_apply, comp_aeval]
    rfl

  have hcomap : ((Q.map (dehom i)).radical).comap (dehom i) = J.radical := by
    have hd : (dehom i : MvPolynomial (Σ k, ι k) ℂ →+* DehomRing i) = Ideal.Quotient.mk (dehomIdeal i) := rfl
    rw [← Ideal.comap_coe (dehom i), ← Ideal.map_coe (dehom i), Ideal.comap_radical, hd,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

  have hval : ∀ (y : (Σ k, ι k) → ℂ) (f : MvPolynomial (Fin m) ℂ),
      aeval (R := ℂ) y (aeval G f) = aeval (R := ℂ) (fun a => segre y (σ a)) f := by
    intro y f
    rw [← AlgHom.comp_apply, comp_aeval]
    congr 2
    funext a
    simp [hG, segre]

  have hzero : ∀ y : (Σ k, ι k) → ℂ, y ∈ zeroLocus ℂ J ↔ y ∈ mcPts P ∧ ∀ k, y ⟨k, i k⟩ = 1 := by
    intro y
    constructor
    · intro hy
      have h1 : ∀ k, y ⟨k, i k⟩ = 1 := fun k => by
        have := hy _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
        simpa [sub_eq_zero] using this
      refine ⟨⟨fun k => ⟨i k, by simp [h1 k]⟩, fun f hf => ?_⟩, h1⟩
      have := hy _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
      exact this
    · rintro ⟨hy, h1⟩
      have hle : J ≤ RingHom.ker (aeval (R := ℂ) y : MvPolynomial (Σ k, ι k) ℂ →+* ℂ) := by
        refine sup_le ?_ ?_
        · rw [hQ, Ideal.map_le_iff_le_comap]
          intro f hf
          exact hy.2 f hf
        · rw [dehomIdeal, Ideal.span_le]
          rintro _ ⟨k, rfl⟩
          simp [RingHom.mem_ker, h1 k]
      exact fun p hp => hle hp
  ext f
  rw [Ideal.mem_comap, hseg, ← Ideal.mem_comap, hcomap, ← vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
    segreChartIdeal, mem_vanishingIdeal_iff, mem_vanishingIdeal_iff]
  constructor
  · intro hf y hy
    rw [hval]
    obtain ⟨hym, h1⟩ := (hzero y).1 hy
    refine hf _ ⟨y, hym, ?_, rfl⟩
    simp [segre, h1]
  · rintro hf x ⟨z, hz, hzi, rfl⟩
    have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
      have h := Finset.prod_eq_zero (f := fun k => z ⟨k, i k⟩) (Finset.mem_univ k) h0
      exact one_ne_zero ((show segre z i = 1 from hzi).symm.trans h)
    set y := chartLift σ i (fun a => segre z (σ a)) with hy
    have hyz : y = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
      funext p
      rw [hy, chartLift_segre_apply σ i z hzi p.1 p.2, mul_comm]
    have hym : y ∈ mcPts P := by
      rw [hyz]
      exact SegreChartZeroSet.scaleAll_mem P hP (fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz
    have h1 : ∀ k, y ⟨k, i k⟩ = 1 := fun k => by
      rw [hyz]
      exact inv_mul_cancel₀ (hne k)
    have := hf y ((hzero y).2 ⟨hym, h1⟩)
    rwa [hval, hy, segre_chartLift σ i z hzi] at this

end GroundTheory.Heights₂.Heights.Targets
