import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StBaseRatioBasis
import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartDetRatio
import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartDualRational
import GroundTheory.HeightsAndTheta.Heights.Intersections.StWWRatioBasis
import GroundTheory.HeightsAndTheta.Heights.Intersections.StDiagRatioBasis
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

/- English proof (translation)
Use `charZero_of_inj_zero fun n hn => ?_` and prove the remaining obligations. Establish `hmem : ((n : ℤ) : ℤ) ∈ (T.baseIdeal x).comap (C : ℤ →+* MRing (fun _ : Unit => ι))`. Rewrite using `[Ideal.mem_comap, T.baseIdeal, RingHom.mem_ker, T.multiConeMap, eval₂Hom_C, eq_intCast, Int.cast_natCast, ← map_natCast (C : Ω →+* MvPolynomial Unit Ω), hn, map_zero]`. Rewrite `hmem` using `[h.2.2.1]`. Conclude with `(Ideal.mem_bot).1 hmem` after adjusting the coercions.
-/
theorem charZero_of_isArithVar_baseIdeal {Ω : Type} [Field Ω] {ι : Type} [Fintype ι] {x : ι → Ω} {D : ℕ}
    (h : IsArithVar (T.baseIdeal x) D) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : ((n : ℤ) : ℤ) ∈ (T.baseIdeal x).comap (C : ℤ →+* MRing (fun _ : Unit => ι)) := by
    rw [Ideal.mem_comap, T.baseIdeal, RingHom.mem_ker, T.multiConeMap, eval₂Hom_C, eq_intCast,
      Int.cast_natCast, ← map_natCast (C : Ω →+* MvPolynomial Unit Ω), hn, map_zero]
  rw [h.2.2.1] at hmem
  exact_mod_cast (Ideal.mem_bot).1 hmem

/- English proof (translation)
Establish `h : (mConeMap c : MRing ι →+* MvPolynomial K Φ) = T.multiConeMap c` using `MvPolynomial.ringHom_ext (fun r => by simp [T.multiConeMap, mConeMap]) (fun p => by simp [T.multiConeMap, mConeMap])`. Rewrite using `[mCoordIdeal, ← h]`. Both sides reduce to the same expression.
-/
theorem mCoordIdeal_eq_ker_multiConeMap {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Φ : Type} [Field Φ] (c : (Σ k, ι k) → Φ) : mCoordIdeal c = RingHom.ker (T.multiConeMap c) := by
  have h : (mConeMap c : MRing ι →+* MvPolynomial K Φ) = T.multiConeMap c :=
    MvPolynomial.ringHom_ext (fun r => by simp [T.multiConeMap, mConeMap])
      (fun p => by simp [T.multiConeMap, mConeMap])
  rw [mCoordIdeal, ← h]
  rfl

/- English proof (translation)
Introduce `Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hSec hGen hDetG D hD a ha`. Use `haveI : CharZero Ω := charZero_of_isArithVar_baseIdeal hD`. Use `haveI : CharZero Φ := charZero_of_injective_algebraMap (algebraMap Ω Φ).injective`. Take `⟨i₀, d, t, hx, rfl, ht, htF, htA⟩` from `hB Ω ι x D hD`. Take `⟨l₀, hδ, hδF⟩` from `hDet Ω ι ν E x B e δ i₀ hx hDetG`.

Take `⟨b, g, hg, hgF, k₀, k₁, hk⟩` from `hDual Ω ι κ E x B φ i₀ hx hSec hGen`. Use `⟨fun j => ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨c, t', hc, ht', htL, hal⟩` from `hY Ω ι ν κ E Φ x e b φ δ g i₀ l₀ k₀ k₁ d t (a j) hx ht htF htA hδ hδF hg hgF hk (ha.transcendental j)`. Establish `h` using `CoordConeArithVar.full T.YBlk (T.yyIdx ι ν κ) Φ _ c (d + 1) t' ⟨.base⟩ hc ht' htL hal`. Rewrite `h` using `[mCoordIdeal_eq_ker_multiConeMap]`.

Conclude with `h`. Take `⟨c, t', hc, ht', htL, hal⟩` from `hW Ω ι ν κ E Φ x e b φ δ g i₀ l₀ k₀ k₁ d t a hx ht htF htA hδ hδF hg hgF hk ha`. Establish `h` using `CoordConeArithVar.full T.WBlk (T.wwIdx ι ν κ) Φ _ c (d + 2) t' ⟨.base⟩ hc ht' htL hal`. Rewrite `h` using `[mCoordIdeal_eq_ker_multiConeMap]`. Conclude with `h`.

Take `⟨c, t', hc, ht', htL, hal⟩` from `hΔ Ω ι ν κ E Φ x e b φ δ g i₀ l₀ k₀ k₁ d t (a 0) hx ht htF htA hδ hδF hg hgF hk (ha.transcendental 0)`. Establish `h` using `CoordConeArithVar.full T.WBlk (T.wwIdx ι ν κ) Φ _ c (d + 1) t' ⟨.base⟩ hc ht' htL hal`. Rewrite `h` using `[mCoordIdeal_eq_ker_multiConeMap]`. Conclude with `h`.
-/
theorem WWArithVar.proof (hB : BaseRatioBasis.Statement) (hDet : ChartDetRatio.Statement)
    (hDual : ChartDualRational.Statement) (hY : YYRatioBasis.Statement) (hW : WWRatioBasis.Statement)
    (hΔ : DiagRatioBasis.Statement) : WWArithVar.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hSec hGen hDetG D hD a ha
  haveI : CharZero Ω := charZero_of_isArithVar_baseIdeal hD
  haveI : CharZero Φ := charZero_of_injective_algebraMap (algebraMap Ω Φ).injective
  obtain ⟨i₀, d, t, hx, rfl, ht, htF, htA⟩ := hB Ω ι x D hD
  obtain ⟨l₀, hδ, hδF⟩ := hDet Ω ι ν E x B e δ i₀ hx hDetG
  obtain ⟨b, g, hg, hgF, k₀, k₁, hk⟩ := hDual Ω ι κ E x B φ i₀ hx hSec hGen
  refine ⟨fun j => ?_, ?_, ?_⟩
  · obtain ⟨c, t', hc, ht', htL, hal⟩ := hY Ω ι ν κ E Φ x e b φ δ g i₀ l₀ k₀ k₁ d t (a j) hx ht htF htA hδ
      hδF hg hgF hk (ha.transcendental j)
    have h := CoordConeArithVar.full T.YBlk (T.yyIdx ι ν κ) Φ _ c (d + 1) t' ⟨.base⟩ hc ht' htL hal
    rw [mCoordIdeal_eq_ker_multiConeMap] at h
    exact h
  · obtain ⟨c, t', hc, ht', htL, hal⟩ := hW Ω ι ν κ E Φ x e b φ δ g i₀ l₀ k₀ k₁ d t a hx ht htF htA hδ
      hδF hg hgF hk ha
    have h := CoordConeArithVar.full T.WBlk (T.wwIdx ι ν κ) Φ _ c (d + 2) t' ⟨.base⟩ hc ht' htL hal
    rw [mCoordIdeal_eq_ker_multiConeMap] at h
    exact h
  · obtain ⟨c, t', hc, ht', htL, hal⟩ := hΔ Ω ι ν κ E Φ x e b φ δ g i₀ l₀ k₀ k₁ d t (a 0) hx ht htF htA hδ
      hδF hg hgF hk (ha.transcendental 0)
    have h := CoordConeArithVar.full T.WBlk (T.wwIdx ι ν κ) Φ _ c (d + 1) t' ⟨.base⟩ hc ht' htL hal
    rw [mCoordIdeal_eq_ker_multiConeMap] at h
    exact h

end

end GroundTheory.Heights₂.Heights.Inter
