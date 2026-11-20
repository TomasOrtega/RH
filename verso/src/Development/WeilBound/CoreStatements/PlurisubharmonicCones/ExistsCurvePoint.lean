import Mathlib
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.AevalZeroOfMem
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFunctionFieldFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartTrdeg
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartHomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartDehomog
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNefAddBlock
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjContract
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo PositivityTheory.HtPt GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar

namespace LevelTowerAlt

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime]

/- English proof (translation)
Rewrite using `[Bridge.GeoNum.ker_red, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hpW`.
-/
theorem ker_red_le {W : Ideal (MRing J)} (hpW : (C (p : ℤ) : MRing J) ∈ W) :
    RingHom.ker (Bridge.GeoNum.red (ι := J) p) ≤ W := by
  classical
  rw [Bridge.GeoNum.ker_red, Ideal.span_le, Set.singleton_subset_iff]
  exact hpW

/- English proof (translation)
Establish `hker` using `ker_red_le p hpW`. Establish `hcm : (W.map (Bridge.GeoNum.red p)).comap (Bridge.GeoNum.red p) = W` using `Bridge.GeoNum.comap_map_eq p hker`. Establish `: W.IsPrime` using `hW.1`. Use `⟨Ideal.map_isPrime_of_surjective (Bridge.GeoNum.red_surjective p) hker, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Bridge.isMultiHomogIdeal_iff]`.

Take `⟨S, hS, hWS⟩` from `hW.2.1`. Use `⟨Bridge.GeoNum.red p '' S, ?_, by rw [hWS, Ideal.map_span]⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨b, hb⟩` from `hS f hf`. Conclude with `⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩`.

Rewrite using `[← Bridge.GeoNum.isRelevant_comap_iff p, hcm]`. Conclude with `hW.2.2`.
-/
theorem map_red_prime [DecidableEq K] {W : Ideal (MRing J)} (hW : IsMultiProjPrime W)
    (hpW : (C (p : ℤ) : MRing J) ∈ W) : NumbersDVR.IsMultiProjPrime (W.map (Bridge.GeoNum.red p)) := by
  have hker := ker_red_le p hpW
  have hcm : (W.map (Bridge.GeoNum.red p)).comap (Bridge.GeoNum.red p) = W :=
    Bridge.GeoNum.comap_map_eq p hker
  have : W.IsPrime := hW.1
  refine ⟨Ideal.map_isPrime_of_surjective (Bridge.GeoNum.red_surjective p) hker, ?_, ?_⟩
  · rw [Bridge.isMultiHomogIdeal_iff]
    obtain ⟨S, hS, hWS⟩ := hW.2.1
    refine ⟨Bridge.GeoNum.red p '' S, ?_, by rw [hWS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨b, hb⟩ := hS f hf
    exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [← Bridge.GeoNum.isRelevant_comap_iff p, hcm]
    exact hW.2.2

/- English proof (translation)
Take `⟨hQ, hQd⟩` from `NefAddBlock.map_red p hW hpW 1 hdim`. Establish `hcm` using `Bridge.GeoNum.comap_map_eq p (ker_red_le p hpW)`. Use `set Q := W.map (Bridge.GeoNum.red p)`. Use `hQ.isPrime` as an intermediate fact. Take `⟨n, hn, hrn⟩` from `FieldNumbers.FunctionFieldFinite.relDim_eq_trdeg FieldNumbers.MChartDehomog.proof (FieldNumbers.MChartTrdeg.proof FieldNumbers.MChartHomog.proof) Q hQ`.

Establish `hn1 : n = 1`. Rewrite `hrn` using `[hQd]`. Conclude with `(WithTop.coe_injective (WithBot.coe_injective hrn)).symm` after adjusting the coercions. Use `choose c hc using hQ.relevant`. Set `π : NumbersDVR.MRing J (ZMod p) →+* FractionRing (NumbersDVR.MRing J (ZMod p) ⧸ Q)` to `(algebraMap (NumbersDVR.MRing J (ZMod p) ⧸ Q) _).comp (Ideal.Quotient.mk Q)`.

Establish `hπ : ∀ g, π g = 0 ↔ g ∈ Q` using `fun g => by`. Express the relevant statement in the definitionally equal form `algebraMap (NumbersDVR.MRing J (ZMod p) ⧸ Q) _ (Ideal.Quotient.mk Q g) = 0 ↔ _`. Rewrite using `[map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]`. Set `y₀ : (Σ k, J k) → FractionRing (NumbersDVR.MRing J (ZMod p) ⧸ Q)` to `fun x => π (X x)`. Establish `hy₀` using `hom_eq_aeval (π.comp (Bridge.GeoNum.red p)) y₀ fun x => by simp only [RingHom.comp_apply, map_X, y₀]`.

Establish `hyc : ∀ k, y₀ ⟨k, c k⟩ ≠ 0` using `fun k h => hc k ((hπ _).1 h)`. Establish `hW₀ : mCoordIdeal y₀ = W`. Use `le_antisymm (fun g hg => ?_) (le_mCoordIdeal hW.2.1 fun g hg => ?_)` and prove the remaining obligations. Rewrite using `[← hcm]`. Conclude with `(hπ _).1 ((hy₀ g).trans (aeval_zero_of_mem hg))`.

Conclude with `(hy₀ g).symm.trans ((hπ _).2 (Ideal.mem_map_of_mem _ hg))`. Establish `hmem : ∀ x, ratioPt y₀ c x ∈ FieldNumbers.homFracDegZero Q` using `fun x => IntermediateField.subset_adjoin _ _ ⟨_, X x, X ⟨x.1, c x.1⟩, isWeightedHomogeneous_X _ _ x, isWeightedHomogeneous_X _ _ (⟨x.1, c x.1⟩ : Σ k, J k), hc x.1, rfl⟩`. Use `⟨FieldNumbers.homFracDegZero Q, inferInstance, inferInstance, fun x => ⟨_, hmem x⟩, c, by rw [hn, hn1, Nat.cast_one], fun k => Subtype.ext (div_self (hyc k)), ?_⟩` and prove the remaining obligations. Rewrite using `[← hW₀, mCoordIdeal_ratioPt y₀ c hyc]`. Conclude with `(mCoordIdeal_comp (FieldNumbers.homFracDegZero Q).val.toRingHom fun x => ⟨_, hmem x⟩).symm`.
-/
theorem exists_curve_point {W : Ideal (MRing J)} (hW : IsMultiProjPrime W) (hpW : (C (p : ℤ) : MRing J) ∈ W)
    (hdim : ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (ZMod p) L) (w : (Σ k, J k) → L) (c : ∀ k, J k),
      Algebra.trdeg (ZMod p) L = 1 ∧ (∀ k, w ⟨k, c k⟩ = 1) ∧ mCoordIdeal w = W := by
  classical
  obtain ⟨hQ, hQd⟩ := NefAddBlock.map_red p hW hpW 1 hdim
  have hcm := Bridge.GeoNum.comap_map_eq p (ker_red_le p hpW)
  set Q := W.map (Bridge.GeoNum.red p)
  have := hQ.isPrime
  obtain ⟨n, hn, hrn⟩ := FieldNumbers.FunctionFieldFinite.relDim_eq_trdeg FieldNumbers.MChartDehomog.proof
    (FieldNumbers.MChartTrdeg.proof FieldNumbers.MChartHomog.proof) Q hQ
  have hn1 : n = 1 := by
    rw [hQd] at hrn
    exact_mod_cast (WithTop.coe_injective (WithBot.coe_injective hrn)).symm
  choose c hc using hQ.relevant
  let π : NumbersDVR.MRing J (ZMod p) →+* FractionRing (NumbersDVR.MRing J (ZMod p) ⧸ Q) :=
    (algebraMap (NumbersDVR.MRing J (ZMod p) ⧸ Q) _).comp (Ideal.Quotient.mk Q)
  have hπ : ∀ g, π g = 0 ↔ g ∈ Q := fun g => by
    change algebraMap (NumbersDVR.MRing J (ZMod p) ⧸ Q) _ (Ideal.Quotient.mk Q g) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  let y₀ : (Σ k, J k) → FractionRing (NumbersDVR.MRing J (ZMod p) ⧸ Q) := fun x => π (X x)
  have hy₀ := hom_eq_aeval (π.comp (Bridge.GeoNum.red p)) y₀ fun x => by simp only [RingHom.comp_apply, map_X, y₀]
  have hyc : ∀ k, y₀ ⟨k, c k⟩ ≠ 0 := fun k h => hc k ((hπ _).1 h)
  have hW₀ : mCoordIdeal y₀ = W := by
    refine le_antisymm (fun g hg => ?_) (le_mCoordIdeal hW.2.1 fun g hg => ?_)
    · rw [← hcm]
      exact (hπ _).1 ((hy₀ g).trans (aeval_zero_of_mem hg))
    · exact (hy₀ g).symm.trans ((hπ _).2 (Ideal.mem_map_of_mem _ hg))
  have hmem : ∀ x, ratioPt y₀ c x ∈ FieldNumbers.homFracDegZero Q := fun x =>
    IntermediateField.subset_adjoin _ _ ⟨_, X x, X ⟨x.1, c x.1⟩, isWeightedHomogeneous_X _ _ x,
      isWeightedHomogeneous_X _ _ (⟨x.1, c x.1⟩ : Σ k, J k), hc x.1, rfl⟩
  refine ⟨FieldNumbers.homFracDegZero Q, inferInstance, inferInstance, fun x => ⟨_, hmem x⟩, c,
    by rw [hn, hn1, Nat.cast_one], fun k => Subtype.ext (div_self (hyc k)), ?_⟩
  rw [← hW₀, mCoordIdeal_ratioPt y₀ c hyc]
  exact (mCoordIdeal_comp (FieldNumbers.homFracDegZero Q).val.toRingHom fun x => ⟨_, hmem x⟩).symm

/- English proof (translation)
Set `Φ : NumbersDVR.MRing J (ZMod p) →ₐ[ZMod p] MvPolynomial K L` to `aeval fun x => C (w x) * X x.1`. Establish `hΦ : ∀ g : MRing J, mConeMap w g = Φ (Bridge.GeoNum.red p g)` using `fun g => by`. Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add f g hf hg => simp only [map_add, hf, hg]`.

Consider the case `mul_X f x hf => simp only [map_mul, hf, map_X]`. Simplify using `[mConeMap, Φ]`. Establish `hcm : mCoordIdeal w = (RingHom.ker Φ).comap (Bridge.GeoNum.red p)`. Use extensionality with `g`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, ← hΦ]`.

Both sides reduce to the same expression. Establish `hm : (mCoordIdeal w).map (Bridge.GeoNum.red p) = RingHom.ker Φ`. Rewrite using `[hcm, Ideal.map_comap_of_surjective _ (Bridge.GeoNum.red_surjective p)]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hcm]`.

Use `Bridge.GeoNum.ker_le_comap p _ ?_` and prove the remaining obligations. Rewrite using `[Bridge.GeoNum.ker_red]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite using `[hm]`. Establish `: (RingHom.ker Φ).IsPrime` using `RingHom.ker_isPrime _`.

Take `⟨m, h1, h2⟩` from `GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := ZMod p) (A := NumbersDVR.MRing J (ZMod p) ⧸ RingHom.ker Φ)`. Use `⟨m, ?_, h1⟩` and prove the remaining obligations. Establish `h3` using `trdeg_le_of_injective (Ideal.kerLiftAlg Φ) (Ideal.kerLiftAlg_injective Φ)`. Rewrite `h3` using `[h2, ← trdeg_add_eq (ZMod p) L, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Cardinal.lift_natCast]`. Establish `h4 : (m : Cardinal) ≤ 1 + (Fintype.card K : Cardinal)` using `h3.trans (by gcongr)`.

Conclude with `h4` after adjusting the coercions.
-/
theorem dim_le {L : Type} [Field L] [Algebra (ZMod p) L] (hL : Algebra.trdeg (ZMod p) L ≤ 1) (w : (Σ k, J k) → L) :
    (C (p : ℤ) : MRing J) ∈ mCoordIdeal w ∧ ∃ m : ℕ, m ≤ 1 + Fintype.card K ∧
      ringKrullDim (NumbersDVR.MRing J (ZMod p) ⧸ (mCoordIdeal w).map (Bridge.GeoNum.red p)) = m := by
  classical
  let Φ : NumbersDVR.MRing J (ZMod p) →ₐ[ZMod p] MvPolynomial K L := aeval fun x => C (w x) * X x.1
  have hΦ : ∀ g : MRing J, mConeMap w g = Φ (Bridge.GeoNum.red p g) := fun g => by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f x hf => simp only [map_mul, hf, map_X]; simp [mConeMap, Φ]
  have hcm : mCoordIdeal w = (RingHom.ker Φ).comap (Bridge.GeoNum.red p) := by
    ext g
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hΦ]
    rfl
  have hm : (mCoordIdeal w).map (Bridge.GeoNum.red p) = RingHom.ker Φ := by
    rw [hcm, Ideal.map_comap_of_surjective _ (Bridge.GeoNum.red_surjective p)]
  refine ⟨?_, ?_⟩
  · rw [hcm]
    refine Bridge.GeoNum.ker_le_comap p _ ?_
    rw [Bridge.GeoNum.ker_red]
    exact Ideal.mem_span_singleton_self _
  · rw [hm]
    have : (RingHom.ker Φ).IsPrime := RingHom.ker_isPrime _
    obtain ⟨m, h1, h2⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := ZMod p)
      (A := NumbersDVR.MRing J (ZMod p) ⧸ RingHom.ker Φ)
    refine ⟨m, ?_, h1⟩
    have h3 := trdeg_le_of_injective (Ideal.kerLiftAlg Φ) (Ideal.kerLiftAlg_injective Φ)
    rw [h2, ← trdeg_add_eq (ZMod p) L, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Cardinal.lift_natCast] at h3
    have h4 : (m : Cardinal) ≤ 1 + (Fintype.card K : Cardinal) := h3.trans (by gcongr)
    exact_mod_cast h4

end LevelTowerAlt
