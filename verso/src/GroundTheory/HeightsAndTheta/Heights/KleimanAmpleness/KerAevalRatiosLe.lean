import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherFurther
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeBaseComap
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TrdegEqOfLeOfIsAlgebraic
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoeNeZeroOfNotMem
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XMemMIdealOverIff
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemMIdealOverIff
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartHomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartLocDim
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim chartMap chartIdeal chartMonomial)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn)

namespace ModelCurvesDim

section Specialise

variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [Algebra F Ω]

def ratios (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
The claim follows from `Algebra.subset_adjoin ⟨p, rfl⟩`.
-/
theorem ratios_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) :
    ratios y c p ∈ chartRingOver F y c :=
  Algebra.subset_adjoin ⟨p, rfl⟩

/- English proof (translation)
Introduce `f hf`. Take `⟨b, h, hh, hall⟩` from `FieldNumbers.MChartHomog.proof.{0} F K ι c f`. Use `set Q : Ideal (NumbersDVR.MRing ι F) := RingHom.ker (aeval y : MvPolynomial (Σ k, ι k) F →ₐ[F] Ω) with hQ`. Establish `: Q.IsPrime` using `RingHom.ker_isPrime _`. Establish `hcQ : ∀ k, (X ⟨k, c k⟩ : NumbersDVR.MRing ι F) ∉ Q` using `fun k hk => hc k (by`.

Simplify `hk)` using `[hQ, RingHom.mem_ker]`. Establish `hg : Function.Injective (Ideal.kerLiftAlg (aeval y : MvPolynomial (Σ k, ι k) F →ₐ[F] Ω))` using `Ideal.kerLiftAlg_injective _`. Use `set Φ : FractionRing (NumbersDVR.MRing ι F ⧸ Q) →+* Ω := IsFractionRing.lift hg with hΦ`. Establish `hΦm : ∀ g, Φ (algebraMap _ _ (Ideal.Quotient.mk Q g)) = aeval y g` using `fun g => by`. Rewrite using `[hΦ, IsFractionRing.lift_algebraMap]`.

Conclude with `Ideal.kerLiftAlg_mk _ g`. Establish `hcomp : Φ.comp (chartMap Q c : NumbersDVR.MRing ι F →+* _) = (aeval (ratios y c) : MvPolynomial (Σ k, ι k) F →ₐ[F] Ω).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Establish `e1 : algebraMap F (FractionRing (NumbersDVR.MRing ι F ⧸ Q)) r = algebraMap (NumbersDVR.MRing ι F ⧸ Q) _ (Ideal.Quotient.mk Q (C r))`.

Rewrite using `[IsScalarTower.algebraMap_apply F (NumbersDVR.MRing ι F ⧸ Q)]`. Both sides reduce to the same expression. Simplify using `only [RingHom.comp_apply, AlgHom.coe_toRingHom, chartMap, aeval_C]`. Rewrite using `[e1, hΦm, aeval_C]`. Conclude with `(aeval_C (ratios y c) r).symm`.

Introduce `v`. Simplify using `only [RingHom.comp_apply, AlgHom.coe_toRingHom, chartMap, aeval_X, map_div₀, hΦm]`. Conclude with `(aeval_X (ratios y c) v).symm`. Establish `key : Φ (chartMap Q c f) = aeval (ratios y c) f` using `RingHom.congr_fun hcomp f`. Establish `h0 : chartMap Q c f = 0`.

Apply `Φ.injective` to reduce the goal to its premises. Rewrite using `[map_zero, key]`. Conclude with `hf`. Rewrite `h0` using `[hall Q hcQ, div_eq_zero_iff]`. Establish `hhQ : h ∈ Q`.

Break down `h0 with h0 | h0` into its components or cases. Rewrite `h0` using `[IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Then use the resulting hypothesis. Conclude with `absurd h0 (FieldNumbers.MChartLocDim.algebraMap_mk_ne_zero Q (FieldNumbers.MChartLocDim.chartMonomial_not_mem Q c hcQ b))`. Establish `hhy : h ∈ mIdealOver F y` using `by classical`. Rewrite using `[mem_mIdealOver_iff]`.

Introduce `b'`. Establish `hmem : h ∈ weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι) b`. Rewrite using `[mem_weightedHomogeneousSubmodule]`. Conclude with `hh`. Rewrite using `[weightedHomogeneousComponent_of_mem hmem]`.

Use `split_ifs`. Simplify `hhQ` using `[hQ, RingHom.mem_ker]`. Conclude with `map_zero _`. Rewrite using `[chartIdeal, RingHom.mem_ker, hall W hcW, (Ideal.Quotient.eq_zero_iff_mem).2 (hW hhy), map_zero, zero_div]`.
-/
theorem ker_aeval_ratios_le (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (W : Ideal (NumbersDVR.MRing ι F)) [W.IsPrime] (hW : mIdealOver F y ≤ W)
    (hcW : ∀ k, (X ⟨k, c k⟩ : NumbersDVR.MRing ι F) ∉ W) :
    RingHom.ker (aeval (ratios y c) : MvPolynomial (Σ k, ι k) F →ₐ[F] Ω) ≤ chartIdeal W c := by
  intro f hf
  obtain ⟨b, h, hh, hall⟩ := FieldNumbers.MChartHomog.proof.{0} F K ι c f
  set Q : Ideal (NumbersDVR.MRing ι F) :=
    RingHom.ker (aeval y : MvPolynomial (Σ k, ι k) F →ₐ[F] Ω) with hQ
  have : Q.IsPrime := RingHom.ker_isPrime _
  have hcQ : ∀ k, (X ⟨k, c k⟩ : NumbersDVR.MRing ι F) ∉ Q := fun k hk => hc k (by
    simpa [hQ, RingHom.mem_ker] using hk)
  have hg : Function.Injective (Ideal.kerLiftAlg (aeval y : MvPolynomial (Σ k, ι k) F →ₐ[F] Ω)) :=
    Ideal.kerLiftAlg_injective _
  set Φ : FractionRing (NumbersDVR.MRing ι F ⧸ Q) →+* Ω := IsFractionRing.lift hg with hΦ
  have hΦm : ∀ g, Φ (algebraMap _ _ (Ideal.Quotient.mk Q g)) = aeval y g := fun g => by
    rw [hΦ, IsFractionRing.lift_algebraMap]
    exact Ideal.kerLiftAlg_mk _ g
  have hcomp : Φ.comp (chartMap Q c : NumbersDVR.MRing ι F →+* _) =
      (aeval (ratios y c) : MvPolynomial (Σ k, ι k) F →ₐ[F] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have e1 : algebraMap F (FractionRing (NumbersDVR.MRing ι F ⧸ Q)) r =
          algebraMap (NumbersDVR.MRing ι F ⧸ Q) _ (Ideal.Quotient.mk Q (C r)) := by
        rw [IsScalarTower.algebraMap_apply F (NumbersDVR.MRing ι F ⧸ Q)]
        rfl
      simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, chartMap, aeval_C]
      rw [e1, hΦm, aeval_C]
      exact (aeval_C (ratios y c) r).symm
    · intro v
      simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, chartMap, aeval_X, map_div₀, hΦm]
      exact (aeval_X (ratios y c) v).symm
  have key : Φ (chartMap Q c f) = aeval (ratios y c) f := RingHom.congr_fun hcomp f
  have h0 : chartMap Q c f = 0 := by
    apply Φ.injective
    rw [map_zero, key]
    exact hf
  rw [hall Q hcQ, div_eq_zero_iff] at h0
  have hhQ : h ∈ Q := by
    rcases h0 with h0 | h0
    · rwa [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h0
    · exact absurd h0 (FieldNumbers.MChartLocDim.algebraMap_mk_ne_zero Q
        (FieldNumbers.MChartLocDim.chartMonomial_not_mem Q c hcQ b))
  have hhy : h ∈ mIdealOver F y := by
    classical
    rw [mem_mIdealOver_iff]
    intro b'
    have hmem : h ∈ weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι) b := by
      rw [mem_weightedHomogeneousSubmodule]; exact hh
    rw [weightedHomogeneousComponent_of_mem hmem]
    split_ifs
    · simpa [hQ, RingHom.mem_ker] using hhQ
    · exact map_zero _
  rw [chartIdeal, RingHom.mem_ker, hall W hcW, (Ideal.Quotient.eq_zero_iff_mem).2 (hW hhy), map_zero, zero_div]

/- English proof (translation)
Use `set φ := (aeval (ratios y c) : MvPolynomial (Σ k, ι k) F →ₐ[F] Ω) with hφ`. Establish `hA : chartRingOver F y c = φ.range` using `Algebra.adjoin_range_eq_range_aeval F (ratios y c)`. Use `⟨(Ideal.Quotient.liftₐ (RingHom.ker φ) (chartMap W c) (fun a ha => ker_aeval_ratios_le y c hc W hW hcW ha)).comp ((Ideal.quotientKerEquivRange φ).symm.toAlgHom.comp (Subalgebra.equivOfEq _ _ hA).toAlgHom), fun p => ?_⟩` and prove the remaining obligations. Establish `h1 : (Ideal.quotientKerEquivRange φ).symm ((Subalgebra.equivOfEq _ _ hA) ⟨ratios y c p, ratios_mem y c p⟩) = Ideal.Quotient.mk _ (X p)`. Rewrite using `[AlgEquiv.symm_apply_eq]`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[Ideal.quotientKerEquivRange, hφ, ratios]`. Express the relevant statement in the definitionally equal form `(Ideal.Quotient.liftₐ (RingHom.ker φ) (chartMap W c) (fun a ha => ker_aeval_ratios_le y c hc W hW hcW ha)) ((Ideal.quotientKerEquivRange φ).symm ((Subalgebra.equivOfEq _ _ hA) ⟨ratios y c p, ratios_mem y c p⟩)) = _`. Rewrite using `[h1]`. Use `show chartMap W c (X p) = _`.

Simplify using `[chartMap, genPtOf]`.
-/
theorem exists_specialise (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (W : Ideal (NumbersDVR.MRing ι F)) [W.IsPrime] (hW : mIdealOver F y ≤ W)
    (hcW : ∀ k, (X ⟨k, c k⟩ : NumbersDVR.MRing ι F) ∉ W) :
    ∃ σ : chartRingOver F y c →ₐ[F] FractionRing (NumbersDVR.MRing ι F ⧸ W),
      ∀ p : Σ k, ι k, σ ⟨ratios y c p, ratios_mem y c p⟩ = genPtOf W p / genPtOf W ⟨p.1, c p.1⟩ := by
  set φ := (aeval (ratios y c) : MvPolynomial (Σ k, ι k) F →ₐ[F] Ω) with hφ
  have hA : chartRingOver F y c = φ.range := Algebra.adjoin_range_eq_range_aeval F (ratios y c)
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker φ) (chartMap W c)
      (fun a ha => ker_aeval_ratios_le y c hc W hW hcW ha)).comp
    ((Ideal.quotientKerEquivRange φ).symm.toAlgHom.comp (Subalgebra.equivOfEq _ _ hA).toAlgHom), fun p => ?_⟩
  have h1 : (Ideal.quotientKerEquivRange φ).symm ((Subalgebra.equivOfEq _ _ hA) ⟨ratios y c p, ratios_mem y c p⟩) =
      Ideal.Quotient.mk _ (X p) := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    simp [Ideal.quotientKerEquivRange, hφ, ratios]
  change (Ideal.Quotient.liftₐ (RingHom.ker φ) (chartMap W c)
      (fun a ha => ker_aeval_ratios_le y c hc W hW hcW ha)) ((Ideal.quotientKerEquivRange φ).symm
    ((Subalgebra.equivOfEq _ _ hA) ⟨ratios y c p, ratios_mem y c p⟩)) = _
  rw [h1]
  show chartMap W c (X p) = _
  simp [chartMap, genPtOf]

end Specialise

section Key

variable {F : Type} [Field F] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] [Algebra F Ω]
  {L : Type} [Field L] [Algebra F L]

omit [Field L] in
/- English proof (translation)
The claim follows from `Algebra.subset_adjoin ⟨p, rfl⟩`.
-/
theorem ratios_mem' (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) :
    y p / y ⟨p.1, c p.1⟩ ∈ chartRingOver F y c :=
  Algebra.subset_adjoin ⟨p, rfl⟩

/- English proof (translation)
Use `set P : Ideal (chartRingOver F y c) := RingHom.ker (σ : (chartRingOver F y c) →+* L) with hP`. Establish `hPp : P.IsPrime` using `RingHom.ker_isPrime _`. Establish `hmod' : IndefiniteRowSideFullHecke.Kleiman2.modelPts F y = IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀))` using `hmod`. Establish `hO : locIn (chartRingOver F y c) P ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀))`. Rewrite using `[← hmod']`.

Conclude with `⟨c, hc, P, hPp, rfl⟩`. Take `⟨c', hc', P', hP', hOeq⟩` from `hO`. Use `hP'` as an intermediate fact. Establish `hBO : ∀ b ∈ (chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c'), b ∈ locIn (chartRingOver F y c) P` using `fun b hb => by rw [hOeq]; exact le_locIn (chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c') P' hb`. Establish `hAO : ∀ a ∈ (chartRingOver F y c), a ∈ locIn (chartRingOver F y c) P` using `fun a ha => le_locIn (chartRingOver F y c) P ha`.

Establish `hg : Function.Injective (RingHom.kerLift (σ : (chartRingOver F y c) →+* L))` using `RingHom.kerLift_injective _`. Use `set τ : locIn (chartRingOver F y c) P →+* L := (IsFractionRing.lift hg).comp (resMap y c P) with hτ`. Establish `hτa : ∀ (a : (chartRingOver F y c)) (h : (a : Ω) ∈ locIn (chartRingOver F y c) P), τ ⟨a, h⟩ = σ a` using `fun a h => by`. Rewrite using `[hτ, RingHom.comp_apply, resMap_of_mem, resq, IsFractionRing.lift_algebraMap, RingHom.kerLift_mk]`. Both sides reduce to the same expression.

Establish `hτr : ∀ q (h : y q / y ⟨q.1, c q.1⟩ ∈ locIn (chartRingOver F y c) P), τ ⟨y q / y ⟨q.1, c q.1⟩, h⟩ = z q / z ⟨q.1, c q.1⟩` using `fun q h => (hτa ⟨_, ratios_mem' y c q⟩ h).trans (hσ q)`. Establish `hy0 : y ⟨k₀, c' ()⟩ ≠ 0` using `hc' ()`. Establish `hB : ∀ b ∈ (chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c'), ∃ h : b ∈ locIn (chartRingOver F y c) P, IsAlgebraic S0 (τ ⟨b, h⟩)`. Introduce `b hb`. Proceed by induction on `hb using Algebra.adjoin_induction with`.

Consider the case `mem w hw`. Take `⟨⟨⟨⟩, j⟩, rfl⟩` from `hw`. Establish `hw1` using `hBO _ (Algebra.subset_adjoin ⟨⟨(), j⟩, rfl⟩)`. Use `⟨hw1, ?_⟩` and prove the remaining obligations. Establish `hrj` using `hAO _ (ratios_mem' (F := F) y c ⟨k₀, j⟩)`.

Establish `hrc` using `hAO _ (ratios_mem' (F := F) y c ⟨k₀, c' ()⟩)`. Establish `hinv` using `hBO _ (Algebra.subset_adjoin (R := F) (s := Set.range fun q : (Σ _ : Unit, ι k₀) => IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) q / IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ …`. Establish `hunit : IsUnit (⟨_, hrc⟩ : locIn (chartRingOver F y c) P)`. Use `IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)` and prove the remaining obligations. Simplify using `only [Subring.coe_mul, Subring.coe_one, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]`.

Clear denominators, using `[hc k₀, hy0]` for the nonvanishing conditions. Establish `hne : τ ⟨_, hrc⟩ ≠ 0` using `(hunit.map τ).ne_zero`. Establish `hmul : τ ⟨_, hrc⟩ * τ ⟨_, hw1⟩ = τ ⟨_, hrj⟩`. Rewrite using `[← map_mul]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subring.coe_mul, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]`. Clear denominators, using `[hc k₀, hy0]` for the nonvanishing conditions. Establish `hc1 : IsAlgebraic S0 (τ ⟨_, hrc⟩)`. Rewrite using `[hτr ⟨k₀, c' ()⟩ hrc]`.

Conclude with `isAlgebraic_algebraMap (⟨_, hS0 (c' ())⟩ : S0)`. Establish `hj1 : IsAlgebraic S0 (τ ⟨_, hrc⟩ * τ ⟨_, hw1⟩)`. Rewrite using `[hmul, hτr ⟨k₀, j⟩ hrj]`. Conclude with `isAlgebraic_algebraMap (⟨_, hS0 j⟩ : S0)`. Conclude with `IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hne) hc1 hj1`.

Consider the case `algebraMap r`. Establish `h1` using `hBO _ ((chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c').algebraMap_mem r)`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `e1 : τ ⟨algebraMap F Ω r, h1⟩ = algebraMap F L r` using `(hτa (algebraMap F (chartRingOver F y c) r) h1).trans (σ.commutes r)`. Rewrite using `[e1]`.

Conclude with `isAlgebraic_algebraMap (⟨_, S0.algebraMap_mem r⟩ : S0)`. Consider the case `add a b _ _ ha hb`. Take `⟨h1, h1'⟩` from `ha`. Take `⟨h2, h2'⟩` from `hb`. Use `⟨add_mem h1 h2, ?_⟩` and prove the remaining obligations.

Establish `e1 : τ ⟨a + b, add_mem h1 h2⟩ = τ ⟨a, h1⟩ + τ ⟨b, h2⟩` using `by rw [← map_add]; rfl`. Rewrite using `[e1]`. Conclude with `h1'.add h2'`. Consider the case `mul a b _ _ ha hb`. Take `⟨h1, h1'⟩` from `ha`.

Take `⟨h2, h2'⟩` from `hb`. Use `⟨mul_mem h1 h2, ?_⟩` and prove the remaining obligations. Establish `e1 : τ ⟨a * b, mul_mem h1 h2⟩ = τ ⟨a, h1⟩ * τ ⟨b, h2⟩` using `by rw [← map_mul]; rfl`. Rewrite using `[e1]`. Conclude with `h1'.mul h2'`.

Establish `hp` using `hAO _ (ratios_mem' (F := F) y c p)`. Establish `hw : y p / y ⟨p.1, c p.1⟩ ∈ locIn (chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c') P'` using `by rw [← hOeq]; exact hp`. Take `⟨a, b, hb, hab⟩` from `(mem_locIn_chart_iff _ c' P').1 hw`. Establish `hb0 : (b : Ω) ≠ 0` using `coe_ne_zero_of_notMem _ c' P' hb`. Take `⟨ha1, ha2⟩` from `hB a a.2`.

Take `⟨hb1, hb2⟩` from `hB b b.2`. Establish `hinv : (1 : Ω) / b ∈ locIn (chartRingOver F y c) P`. Rewrite using `[hOeq]`. Conclude with `(mem_locIn_chart_iff _ c' P').2 ⟨1, b, hb, by simp⟩`. Establish `hunit : IsUnit (⟨b, hb1⟩ : locIn (chartRingOver F y c) P)` using `IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (by simp [hb0]))`.

Establish `hne : τ ⟨b, hb1⟩ ≠ 0` using `(hunit.map τ).ne_zero`. Establish `hmul : τ ⟨b, hb1⟩ * τ ⟨_, hp⟩ = τ ⟨a, ha1⟩`. Rewrite using `[← map_mul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Subring.coe_mul]`. Rewrite using `[hab]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[← hτr p hp]`. Conclude with `IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hne) hb2 (hmul ▸ ha2)`.
-/
theorem isAlgebraic_ratio (y : (Σ k, ι k) → Ω) (k₀ : K)
    (hmod : IndefiniteRowSideFullHecke.Kleiman2.SameModel F y (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)))
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (z : (Σ k, ι k) → L)
    (σ : chartRingOver F y c →ₐ[F] L)
    (hσ : ∀ p, σ ⟨y p / y ⟨p.1, c p.1⟩, ratios_mem' y c p⟩ = z p / z ⟨p.1, c p.1⟩)
    (S0 : Subalgebra F L) (hS0 : ∀ j : ι k₀, z ⟨k₀, j⟩ / z ⟨k₀, c k₀⟩ ∈ S0) (p : Σ k, ι k) :
    IsAlgebraic S0 (z p / z ⟨p.1, c p.1⟩) := by
  classical
  set P : Ideal (chartRingOver F y c) := RingHom.ker (σ : (chartRingOver F y c) →+* L) with hP
  have hPp : P.IsPrime := RingHom.ker_isPrime _
  have hmod' : IndefiniteRowSideFullHecke.Kleiman2.modelPts F y =
      IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) := hmod
  have hO : locIn (chartRingOver F y c) P ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) := by
    rw [← hmod']
    exact ⟨c, hc, P, hPp, rfl⟩
  obtain ⟨c', hc', P', hP', hOeq⟩ := hO
  have := hP'
  have hBO : ∀ b ∈ (chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c'), b ∈ locIn (chartRingOver F y c) P := fun b hb => by rw [hOeq]; exact le_locIn (chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c') P' hb
  have hAO : ∀ a ∈ (chartRingOver F y c), a ∈ locIn (chartRingOver F y c) P := fun a ha => le_locIn (chartRingOver F y c) P ha
  have hg : Function.Injective (RingHom.kerLift (σ : (chartRingOver F y c) →+* L)) := RingHom.kerLift_injective _
  set τ : locIn (chartRingOver F y c) P →+* L := (IsFractionRing.lift hg).comp (resMap y c P) with hτ
  have hτa : ∀ (a : (chartRingOver F y c)) (h : (a : Ω) ∈ locIn (chartRingOver F y c) P), τ ⟨a, h⟩ = σ a := fun a h => by
    rw [hτ, RingHom.comp_apply, resMap_of_mem, resq, IsFractionRing.lift_algebraMap, RingHom.kerLift_mk]
    rfl
  have hτr : ∀ q (h : y q / y ⟨q.1, c q.1⟩ ∈ locIn (chartRingOver F y c) P), τ ⟨y q / y ⟨q.1, c q.1⟩, h⟩ = z q / z ⟨q.1, c q.1⟩ :=
    fun q h => (hτa ⟨_, ratios_mem' y c q⟩ h).trans (hσ q)
  have hy0 : y ⟨k₀, c' ()⟩ ≠ 0 := hc' ()

  have hB : ∀ b ∈ (chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c'), ∃ h : b ∈ locIn (chartRingOver F y c) P, IsAlgebraic S0 (τ ⟨b, h⟩) := by
    intro b hb
    induction hb using Algebra.adjoin_induction with
    | mem w hw =>
      obtain ⟨⟨⟨⟩, j⟩, rfl⟩ := hw
      have hw1 := hBO _ (Algebra.subset_adjoin ⟨⟨(), j⟩, rfl⟩)
      refine ⟨hw1, ?_⟩
      have hrj := hAO _ (ratios_mem' (F := F) y c ⟨k₀, j⟩)
      have hrc := hAO _ (ratios_mem' (F := F) y c ⟨k₀, c' ()⟩)
      have hinv := hBO _ (Algebra.subset_adjoin (R := F)
        (s := Set.range fun q : (Σ _ : Unit, ι k₀) =>
          IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) q /
            IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) ⟨q.1, c' q.1⟩) ⟨⟨(), c k₀⟩, rfl⟩)
      have hunit : IsUnit (⟨_, hrc⟩ : locIn (chartRingOver F y c) P) := by
        refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
        simp only [Subring.coe_mul, Subring.coe_one, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
        field_simp [hc k₀, hy0]
      have hne : τ ⟨_, hrc⟩ ≠ 0 := (hunit.map τ).ne_zero
      have hmul : τ ⟨_, hrc⟩ * τ ⟨_, hw1⟩ = τ ⟨_, hrj⟩ := by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subring.coe_mul, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
        field_simp [hc k₀, hy0]
      have hc1 : IsAlgebraic S0 (τ ⟨_, hrc⟩) := by
        rw [hτr ⟨k₀, c' ()⟩ hrc]
        exact isAlgebraic_algebraMap (⟨_, hS0 (c' ())⟩ : S0)
      have hj1 : IsAlgebraic S0 (τ ⟨_, hrc⟩ * τ ⟨_, hw1⟩) := by
        rw [hmul, hτr ⟨k₀, j⟩ hrj]
        exact isAlgebraic_algebraMap (⟨_, hS0 j⟩ : S0)
      exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hne) hc1 hj1
    | algebraMap r =>
      have h1 := hBO _ ((chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c').algebraMap_mem r)
      refine ⟨h1, ?_⟩
      have e1 : τ ⟨algebraMap F Ω r, h1⟩ = algebraMap F L r := (hτa (algebraMap F (chartRingOver F y c) r) h1).trans (σ.commutes r)
      rw [e1]
      exact isAlgebraic_algebraMap (⟨_, S0.algebraMap_mem r⟩ : S0)
    | add a b _ _ ha hb =>
      obtain ⟨h1, h1'⟩ := ha
      obtain ⟨h2, h2'⟩ := hb
      refine ⟨add_mem h1 h2, ?_⟩
      have e1 : τ ⟨a + b, add_mem h1 h2⟩ = τ ⟨a, h1⟩ + τ ⟨b, h2⟩ := by rw [← map_add]; rfl
      rw [e1]
      exact h1'.add h2'
    | mul a b _ _ ha hb =>
      obtain ⟨h1, h1'⟩ := ha
      obtain ⟨h2, h2'⟩ := hb
      refine ⟨mul_mem h1 h2, ?_⟩
      have e1 : τ ⟨a * b, mul_mem h1 h2⟩ = τ ⟨a, h1⟩ * τ ⟨b, h2⟩ := by rw [← map_mul]; rfl
      rw [e1]
      exact h1'.mul h2'

  have hp := hAO _ (ratios_mem' (F := F) y c p)
  have hw : y p / y ⟨p.1, c p.1⟩ ∈ locIn (chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c') P' := by rw [← hOeq]; exact hp
  obtain ⟨a, b, hb, hab⟩ := (mem_locIn_chart_iff _ c' P').1 hw
  have hb0 : (b : Ω) ≠ 0 := coe_ne_zero_of_notMem _ c' P' hb
  obtain ⟨ha1, ha2⟩ := hB a a.2
  obtain ⟨hb1, hb2⟩ := hB b b.2
  have hinv : (1 : Ω) / b ∈ locIn (chartRingOver F y c) P := by
    rw [hOeq]
    exact (mem_locIn_chart_iff _ c' P').2 ⟨1, b, hb, by simp⟩
  have hunit : IsUnit (⟨b, hb1⟩ : locIn (chartRingOver F y c) P) :=
    IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (by simp [hb0]))
  have hne : τ ⟨b, hb1⟩ ≠ 0 := (hunit.map τ).ne_zero
  have hmul : τ ⟨b, hb1⟩ * τ ⟨_, hp⟩ = τ ⟨a, ha1⟩ := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subring.coe_mul]
    rw [hab]
    field_simp
  rw [← hτr p hp]
  exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hne) hb2 (hmul ▸ ha2)

end Key

/- English proof (translation)
Unfold `relDim`. Rewrite using `[h]`. Establish `e₁ : WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d) ((((t + Fintype.card K : ℕ) : ℕ∞)) : WithBot ℕ∞) = (((((t + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))` using `rfl`. Rewrite using `[e₁, Nat.cast_add, add_sub_cancel_right]`. Both sides reduce to the same expression.
-/
theorem relDim_of_dim {K : Type} [Fintype K] {ι : K → Type} {F : Type} [Field F]
    (I : Ideal (NumbersDVR.MRing ι F)) (t : ℕ)
    (h : ringKrullDim (NumbersDVR.MRing ι F ⧸ I) = (((t + Fintype.card K : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    relDim I = ((t : ℕ) : WithBot (WithTop ℤ)) := by
  unfold relDim
  rw [h]
  have e₁ : WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)
      ((((t + Fintype.card K : ℕ) : ℕ∞)) : WithBot ℕ∞) =
      (((((t + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl
  rw [e₁, Nat.cast_add, add_sub_cancel_right]
  rfl

/- English proof (translation)
Introduce `F _ K _ _ ι _ Ω _ _ y k₀ N e hmod W hW hle`. Use `hW.isPrime` as an intermediate fact. Use `set z := genPtOf (k := F) W with hz`. Establish `hzW : mIdealOver F z = W` using `mIdealOver_genPtOf W hW.multiHomog`. Establish `hz0 : ∀ p, z p = 0 ↔ (X p : NumbersDVR.MRing ι F) ∈ W` using `fun p => by`.

Rewrite using `[← X_mem_mIdealOver_iff (k := F) z p, hzW]`. Use `choose u hu using hW.relevant`. Establish `hzu : ∀ k, z ⟨k, u k⟩ ≠ 0` using `fun k h => hu k ((hz0 _).1 h)`. Establish `hyu : ∀ k, y ⟨k, u k⟩ ≠ 0` using `fun k h => hu k (hle ((X_mem_mIdealOver_iff (k := F) y _).2 h))`. Take `⟨σ, hσ⟩` from `exists_specialise y u hyu W hle hu`.

Use `set x' : (Σ _ : Unit, Fin (N + 1)) → FractionRing (NumbersDVR.MRing ι F ⧸ W) := IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec z k₀ ∘ e.symm) with hx'`. Use `set c0 : Unit → Fin (N + 1) := fun _ => e (u k₀) with hc0`. Establish `hx'0 : ∀ k, x' ⟨k, c0 k⟩ ≠ 0` using `fun _ => by`. Simplify `hzu k₀` using `[hx', hc0, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]`. Establish `hx'W : mIdealOver F x' = baseComap F k₀ e W`.

Apply `le_antisymm (mIdealOver_le_baseComap F z k₀ e rfl hzW.le)` to reduce the goal to its premises. Introduce `f hf`. Rewrite `hf` using `[baseComap, Ideal.mem_comap, ← hzW]`. Establish `hcomp : (mConeMapOver F z).comp (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) = ((rename (R` using `FractionRing (NumbersDVR.MRing ι F ⧸ W)) fun _ : Unit => k₀).restrictScalars F).comp (mConeMapOver F x') := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises.

Introduce `p`. Simplify using `[mConeMapOver, hx', IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]`. Establish `h1` using `AlgHom.congr_fun hcomp f`. Rewrite `h1` using `[AlgHom.comp_apply, AlgHom.comp_apply]`. Establish `hf' : mConeMapOver F z (rename (fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) f) = 0` using `hf`.

Rewrite `h1` using `[hf']`. Establish `hinj : Function.Injective (rename (R` using `FractionRing (NumbersDVR.MRing ι F ⧸ W)) fun _ : Unit => k₀) := rename_injective _ (fun a b _ => Subsingleton.elim a b)`. Express the relevant statement in the definitionally equal form `mConeMapOver F x' f = 0`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Conclude with `h1.symm`. Use `set S0 := chartRingOver F x' c0 with hS0def`. Establish `hS0 : ∀ j : ι k₀, z ⟨k₀, j⟩ / z ⟨k₀, u k₀⟩ ∈ S0` using `fun j => by`. Use `ratios_mem' (F := F) x' c0 ⟨(), e j⟩` as an intermediate fact. Simplify `this` using `[hx', hc0, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]`.

Establish `hle0 : S0 ≤ chartRingOver F z u` using `Algebra.adjoin_le (by`. Introduce and unpack `_ ⟨⟨⟨⟩, a⟩, rfl⟩`. Use `ratios_mem' (F := F) z u ⟨k₀, e.symm a⟩` as an intermediate fact. Simplify `this)` using `[hx', hc0, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]`. Establish `halg : ∀ t ∈ chartRingOver F z u, IsAlgebraic S0 t` using `fun t ht => isAlgebraic_of_mem_adjoin S0 (by`.

Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `isAlgebraic_ratio y k₀ hmod.2 u hyu z σ hσ S0 hS0 p) ht`. Establish `htr : Algebra.trdeg F S0 = Algebra.trdeg F (chartRingOver F z u)` using `trdeg_eq_of_le_of_isAlgebraic hle0 halg`. Establish `h1` using `trdeg_quotient_mIdealOver (F := F) z u hzu`. Establish `h2` using `trdeg_quotient_mIdealOver (F := F) x' c0 hx'0`.

Rewrite `h1` using `[hzW]`. Rewrite `h2` using `[hx'W, htr]`. Establish `hfin` using `trdeg_lt_aleph0_of_finiteType (R := F) (S := MvPolynomial (Σ k, ι k) F ⧸ W)`. Rewrite `hfin` using `[h1]`. Take `⟨t, ht⟩` from `Cardinal.lt_aleph0.1 (lt_of_le_of_lt le_self_add hfin)`.

Establish `: (baseComap F k₀ e W).IsPrime` using `Ideal.comap_isPrime _ _`. Establish `dimW : ringKrullDim (NumbersDVR.MRing ι F ⧸ W) = (((t + Fintype.card K : ℕ) : ℕ∞) : WithBot ℕ∞)`. Rewrite using `[GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, h1, ht]`. Simplify using the standard rewrite rules. Establish `dim0 : ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) F ⧸ baseComap F k₀ e W) = (((t + Fintype.card Unit : ℕ) : ℕ∞) : WithBot ℕ∞)`.

Rewrite using `[GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, h2, ht]`. Simplify using the standard rewrite rules. Rewrite using `[relDim_of_dim _ t dimW, relDim_of_dim _ t dim0]`.
-/
theorem proof : Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod W hW hle
  have := hW.isPrime
  classical
  set z := genPtOf (k := F) W with hz
  have hzW : mIdealOver F z = W := mIdealOver_genPtOf W hW.multiHomog
  have hz0 : ∀ p, z p = 0 ↔ (X p : NumbersDVR.MRing ι F) ∈ W := fun p => by
    rw [← X_mem_mIdealOver_iff (k := F) z p, hzW]
  choose u hu using hW.relevant
  have hzu : ∀ k, z ⟨k, u k⟩ ≠ 0 := fun k h => hu k ((hz0 _).1 h)
  have hyu : ∀ k, y ⟨k, u k⟩ ≠ 0 := fun k h => hu k (hle ((X_mem_mIdealOver_iff (k := F) y _).2 h))
  obtain ⟨σ, hσ⟩ := exists_specialise y u hyu W hle hu

  set x' : (Σ _ : Unit, Fin (N + 1)) → FractionRing (NumbersDVR.MRing ι F ⧸ W) :=
    IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec z k₀ ∘ e.symm) with hx'
  set c0 : Unit → Fin (N + 1) := fun _ => e (u k₀) with hc0
  have hx'0 : ∀ k, x' ⟨k, c0 k⟩ ≠ 0 := fun _ => by
    simpa [hx', hc0, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hzu k₀
  have hx'W : mIdealOver F x' = baseComap F k₀ e W := by
    apply le_antisymm (mIdealOver_le_baseComap F z k₀ e rfl hzW.le)
    intro f hf
    rw [baseComap, Ideal.mem_comap, ← hzW] at hf
    have hcomp : (mConeMapOver F z).comp
        (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) =
        ((rename (R := FractionRing (NumbersDVR.MRing ι F ⧸ W)) fun _ : Unit => k₀).restrictScalars F).comp
          (mConeMapOver F x') := by
      apply MvPolynomial.algHom_ext
      intro p
      simp [mConeMapOver, hx', IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
    have h1 := AlgHom.congr_fun hcomp f
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at h1
    have hf' : mConeMapOver F z (rename (fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) f) = 0 :=
      hf
    rw [hf'] at h1
    have hinj : Function.Injective
        (rename (R := FractionRing (NumbersDVR.MRing ι F ⧸ W)) fun _ : Unit => k₀) :=
      rename_injective _ (fun a b _ => Subsingleton.elim a b)
    change mConeMapOver F x' f = 0
    apply hinj
    rw [map_zero]
    exact h1.symm

  set S0 := chartRingOver F x' c0 with hS0def
  have hS0 : ∀ j : ι k₀, z ⟨k₀, j⟩ / z ⟨k₀, u k₀⟩ ∈ S0 := fun j => by
    have := ratios_mem' (F := F) x' c0 ⟨(), e j⟩
    simpa [hx', hc0, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec] using this
  have hle0 : S0 ≤ chartRingOver F z u := Algebra.adjoin_le (by
    rintro _ ⟨⟨⟨⟩, a⟩, rfl⟩
    have := ratios_mem' (F := F) z u ⟨k₀, e.symm a⟩
    simpa [hx', hc0, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec] using this)
  have halg : ∀ t ∈ chartRingOver F z u, IsAlgebraic S0 t := fun t ht =>
    isAlgebraic_of_mem_adjoin S0 (by
      rintro _ ⟨p, rfl⟩
      exact isAlgebraic_ratio y k₀ hmod.2 u hyu z σ hσ S0 hS0 p) ht
  have htr : Algebra.trdeg F S0 = Algebra.trdeg F (chartRingOver F z u) :=
    trdeg_eq_of_le_of_isAlgebraic hle0 halg
  have h1 := trdeg_quotient_mIdealOver (F := F) z u hzu
  have h2 := trdeg_quotient_mIdealOver (F := F) x' c0 hx'0
  rw [hzW] at h1
  rw [hx'W, htr] at h2
  have hfin := trdeg_lt_aleph0_of_finiteType (R := F) (S := MvPolynomial (Σ k, ι k) F ⧸ W)
  rw [h1] at hfin
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.1 (lt_of_le_of_lt le_self_add hfin)
  have : (baseComap F k₀ e W).IsPrime := Ideal.comap_isPrime _ _
  have dimW : ringKrullDim (NumbersDVR.MRing ι F ⧸ W) =
      (((t + Fintype.card K : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, h1, ht]
    simp
  have dim0 : ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) F ⧸ baseComap F k₀ e W) =
      (((t + Fintype.card Unit : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, h2, ht]
    simp
  rw [relDim_of_dim _ t dimW, relDim_of_dim _ t dim0]

end ModelCurvesDim

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
