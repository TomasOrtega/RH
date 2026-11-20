import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartDehom
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartMax
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartQuot
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCurve
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterDivSuppLemmas
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

abbrev chartOneIdeal (c : (k : ι) → Fin (n k + 1)) : Ideal (MvPolynomial (Coord n) ℤ) :=
  Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1)

/- English proof (translation)
Establish `hP : NumbersDVR.IsMultiHomogIdeal (ι` using `blockIdx n) (R := ℤ) (orbitIdeal x) := fun g hg b ↦ OrbitCurve.weightedHomogeneousComponent_mem_orbitIdeal x hg b`. Establish `hJ` using `NumbersDVR.SupSpanMultiHomog.proof ℤ ι (blockIdx n) (orbitIdeal x) s a hP hs`. Conclude with `NumbersDVR.MinimalPrimeMultiHomog.proof ℤ ι (blockIdx n) _ V hJ hV.1 f hf b`.
-/
theorem weightedHomogeneousComponent_mem_of_mem_divSupp (x : Cone n (AlgebraicClosure ℚ))
    {s : MvPolynomial (Coord n) ℤ} {a : ι → ℕ} (hs : IsWeightedHomogeneous (coordDeg n) s a)
    {V : Ideal (MvPolynomial (Coord n) ℤ)} (hV : V ∈ Geo.divSupp (orbitIdeal x) s)
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ V) (b : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) b f ∈ V := by
  have hP : NumbersDVR.IsMultiHomogIdeal (ι := blockIdx n) (R := ℤ) (orbitIdeal x) :=
    fun g hg b ↦ OrbitCurve.weightedHomogeneousComponent_mem_orbitIdeal x hg b
  have hJ := NumbersDVR.SupSpanMultiHomog.proof ℤ ι (blockIdx n) (orbitIdeal x) s a hP hs
  exact NumbersDVR.MinimalPrimeMultiHomog.proof ℤ ι (blockIdx n) _ V hJ hV.1 f hf b

variable (V : Ideal (MvPolynomial (Coord n) ℤ)) [V.IsPrime]

def classFrac : MvPolynomial (Coord n) ℤ →ₐ[ℤ] FractionRing (MvPolynomial (Coord n) ℤ ⧸ V) :=
  (IsScalarTower.toAlgHom ℤ (MvPolynomial (Coord n) ℤ ⧸ V) _).comp (Ideal.Quotient.mkₐ ℤ V)

def dehomFrac (c : (k : ι) → Fin (n k + 1)) :
    MvPolynomial (Coord n) ℤ →ₐ[ℤ] FractionRing (MvPolynomial (Coord n) ℤ ⧸ V) :=
  aeval fun p ↦ classFrac V (X p) / classFrac V (X ⟨p.1, c p.1⟩)

omit [Fintype ι] [DecidableEq ι] [V.IsPrime] in
/- English proof (translation)
Express the relevant statement in the definitionally equal form `algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V)) (Ideal.Quotient.mk V f) = 0 ↔ _`. Rewrite using `[map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem classFrac_eq_zero_iff (f : MvPolynomial (Coord n) ℤ) : classFrac V f = 0 ↔ f ∈ V := by
  change algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V)) (Ideal.Quotient.mk V f) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

variable {V}

/- English proof (translation)
Establish `e : (aeval fun p ↦ classFrac V (X p)) = classFrac V` using `MvPolynomial.algHom_ext fun p ↦ aeval_X _ _`. Rewrite using `[dehomFrac, aeval_div_chart (fun p ↦ classFrac V (X p)) c G d hG, DFunLike.congr_fun e G]`.
-/
theorem dehomFrac_of_isWeightedHomogeneous (c : (k : ι) → Fin (n k + 1))
    (G : MvPolynomial (Coord n) ℤ) (d : ι → ℕ) (hG : IsWeightedHomogeneous (coordDeg n) G d) :
    dehomFrac V c G = classFrac V G * ∏ k, (classFrac V (X ⟨k, c k⟩) ^ d k)⁻¹ := by
  have e : (aeval fun p ↦ classFrac V (X p)) = classFrac V := MvPolynomial.algHom_ext fun p ↦ aeval_X _ _
  rw [dehomFrac, aeval_div_chart (fun p ↦ classFrac V (X p)) c G d hG, DFunLike.congr_fun e G]

/- English proof (translation)
Establish `hz : ∀ k, classFrac V (X ⟨k, c k⟩) ≠ 0` using `fun k h ↦ hc k ((classFrac_eq_zero_iff V _).mp h)`. Establish `hle : V ⊔ chartOneIdeal c ≤ RingHom.ker (dehomFrac V c)`. Use `sup_le (fun f hf ↦ ?_) (Ideal.span_le.mpr ?_)` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker, ← sum_weightedHomogeneousComponent (w := coordDeg n) f, finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]`. Use `Finset.sum_eq_zero fun b _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[dehomFrac_of_isWeightedHomogeneous c _ b (weightedHomogeneousComponent_isWeightedHomogeneous b f), (classFrac_eq_zero_iff V _).mpr (hVh f hf b), zero_mul]`. Introduce and unpack `_ ⟨k, rfl⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, dehomFrac, aeval_X]`. Conclude with `sub_eq_zero.mpr (div_self (hz k))`. Use `le_antisymm (fun f hf ↦ ?_) hle` and prove the remaining obligations.

Rewrite `hf` using `[RingHom.mem_ker]`. Establish `hχ : ∀ k, Ideal.Quotient.mk (V ⊔ chartOneIdeal c) (X ⟨k, c k⟩) = 1` using `fun k ↦ by`. Rewrite using `[← map_one (Ideal.Quotient.mk (V ⊔ chartOneIdeal c)), Ideal.Quotient.eq]`. Conclude with `Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)`. Take `⟨D, G, hG, hGf⟩` from `exists_isWeightedHomogeneous_eq_of_chart (Ideal.Quotient.mk (V ⊔ chartOneIdeal c)) c hχ f`.

Establish `hd : G - f ∈ V ⊔ chartOneIdeal c` using `Ideal.Quotient.eq.mp hGf`. Establish `h0 : dehomFrac V c G = 0`. Use `hle hd` as an intermediate fact. Rewrite `this` using `[RingHom.mem_ker, map_sub, hf, sub_zero]`. Then use the resulting hypothesis. Rewrite `h0` using `[dehomFrac_of_isWeightedHomogeneous c G D hG, mul_eq_zero]`.

Establish `hGV : G ∈ V`. Use `(classFrac_eq_zero_iff V G).mp (h0.resolve_right ?_)` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ ↦ inv_ne_zero (pow_ne_zero _ (hz k))`. Simplify using `using sub_mem (Ideal.mem_sup_left hGV) hd`.
-/
theorem ker_dehomFrac
    (hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) :
    RingHom.ker (dehomFrac V c) = V ⊔ chartOneIdeal c := by
  have hz : ∀ k, classFrac V (X ⟨k, c k⟩) ≠ 0 := fun k h ↦ hc k ((classFrac_eq_zero_iff V _).mp h)
  have hle : V ⊔ chartOneIdeal c ≤ RingHom.ker (dehomFrac V c) := by
    refine sup_le (fun f hf ↦ ?_) (Ideal.span_le.mpr ?_)
    · rw [RingHom.mem_ker, ← sum_weightedHomogeneousComponent (w := coordDeg n) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
      refine Finset.sum_eq_zero fun b _ ↦ ?_
      rw [dehomFrac_of_isWeightedHomogeneous c _ b
          (weightedHomogeneousComponent_isWeightedHomogeneous b f),
        (classFrac_eq_zero_iff V _).mpr (hVh f hf b), zero_mul]
    · rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, dehomFrac, aeval_X]
      exact sub_eq_zero.mpr (div_self (hz k))
  refine le_antisymm (fun f hf ↦ ?_) hle
  rw [RingHom.mem_ker] at hf
  have hχ : ∀ k, Ideal.Quotient.mk (V ⊔ chartOneIdeal c) (X ⟨k, c k⟩) = 1 := fun k ↦ by
    rw [← map_one (Ideal.Quotient.mk (V ⊔ chartOneIdeal c)), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  obtain ⟨D, G, hG, hGf⟩ := exists_isWeightedHomogeneous_eq_of_chart
    (Ideal.Quotient.mk (V ⊔ chartOneIdeal c)) c hχ f
  have hd : G - f ∈ V ⊔ chartOneIdeal c := Ideal.Quotient.eq.mp hGf
  have h0 : dehomFrac V c G = 0 := by
    have := hle hd
    rwa [RingHom.mem_ker, map_sub, hf, sub_zero] at this
  rw [dehomFrac_of_isWeightedHomogeneous c G D hG, mul_eq_zero] at h0
  have hGV : G ∈ V := by
    refine (classFrac_eq_zero_iff V G).mp (h0.resolve_right ?_)
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ inv_ne_zero (pow_ne_zero _ (hz k))
  simpa using sub_mem (Ideal.mem_sup_left hGV) hd

/- English proof (translation)
Use `le_antisymm (fun a ha ↦ ?_) (Ideal.comap_mono le_sup_left)` and prove the remaining obligations. Rewrite `ha` using `[Ideal.mem_comap, ← ker_dehomFrac hVh hc, RingHom.mem_ker]`. Rewrite using `[Ideal.mem_comap, ← classFrac_eq_zero_iff V]`. Rewrite using `[← ha]`. Conclude with `((classFrac V).commutes a).trans ((dehomFrac V c).commutes a).symm`.
-/
theorem comap_sup_chartOneIdeal
    (hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) :
    (V ⊔ chartOneIdeal c).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) =
      V.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := by
  refine le_antisymm (fun a ha ↦ ?_) (Ideal.comap_mono le_sup_left)
  rw [Ideal.mem_comap, ← ker_dehomFrac hVh hc, RingHom.mem_ker] at ha
  rw [Ideal.mem_comap, ← classFrac_eq_zero_iff V]
  rw [← ha]
  exact ((classFrac V).commutes a).trans ((dehomFrac V c).commutes a).symm

def quotEquivRange
    (hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) :
    (MvPolynomial (Coord n) ℤ ⧸ (V ⊔ chartOneIdeal c)) ≃+* (dehomFrac V c).range :=
  (Ideal.quotEquivOfEq (ker_dehomFrac hVh hc).symm).trans
    (Ideal.quotientKerEquivRange (dehomFrac V c)).toRingEquiv

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Establish `hz : ∀ k, classFrac V (X ⟨k, c k⟩) ≠ 0` using `fun k h ↦ hc k ((classFrac_eq_zero_iff V _).mp h)`. Establish `hz' : ∀ k, classFrac V (X ⟨k, c' k⟩) ≠ 0` using `fun k h ↦ hc' k ((classFrac_eq_zero_iff V _).mp h)`. Rewrite using `[dehomFrac, ← Algebra.adjoin_range_eq_range_aeval]`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩`.

Establish `hmem : ∀ q : Coord n, classFrac V (X q) / classFrac V (X ⟨q.1, c q.1⟩) ∈ (dehomFrac V c).range` using `fun q ↦ (AlgHom.mem_range _).mpr ⟨X q, by rw [dehomFrac, aeval_X]⟩`. Set `u : (dehomFrac V c).range` to `⟨_, hmem ⟨p.1, c' p.1⟩⟩`. Establish `hu : u ≠ 0` using `fun h ↦ div_ne_zero (hz' p.1) (hz p.1) (congrArg Subtype.val h)`. Take `⟨w, hw⟩` from `hF.mul_inv_cancel hu`. Establish `hinv : (u : FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))⁻¹ ∈ (dehomFrac V c).range`.

Rewrite using `[← eq_inv_of_mul_eq_one_right (congrArg Subtype.val hw)]`. Conclude with `w.2`. Establish `e : classFrac V (X p) / classFrac V (X ⟨p.1, c' p.1⟩) = classFrac V (X p) / classFrac V (X ⟨p.1, c p.1⟩) * (u : FractionRing _)⁻¹`. Express the relevant statement in the definitionally equal form `_ = _ * (classFrac V (X ⟨p.1, c' p.1⟩) / classFrac V (X ⟨p.1, c p.1⟩))⁻¹`. Clear denominators, using `[hz p.1, hz' p.1]` for the nonvanishing conditions.

Express the relevant statement in the definitionally equal form `classFrac V (X p) / classFrac V (X ⟨p.1, c' p.1⟩) ∈ (dehomFrac V c).range`. Rewrite using `[e]`. Conclude with `mul_mem (hmem p) hinv`.
-/
theorem range_dehomFrac_le {c c' : (k : ι) → Fin (n k + 1)}
    (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    (hc' : ∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    (hF : IsField (dehomFrac V c).range) : (dehomFrac V c').range ≤ (dehomFrac V c).range := by
  have hz : ∀ k, classFrac V (X ⟨k, c k⟩) ≠ 0 := fun k h ↦ hc k ((classFrac_eq_zero_iff V _).mp h)
  have hz' : ∀ k, classFrac V (X ⟨k, c' k⟩) ≠ 0 :=
    fun k h ↦ hc' k ((classFrac_eq_zero_iff V _).mp h)
  rw [dehomFrac, ← Algebra.adjoin_range_eq_range_aeval]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨p, rfl⟩
  have hmem : ∀ q : Coord n, classFrac V (X q) / classFrac V (X ⟨q.1, c q.1⟩) ∈ (dehomFrac V c).range :=
    fun q ↦ (AlgHom.mem_range _).mpr ⟨X q, by rw [dehomFrac, aeval_X]⟩
  let u : (dehomFrac V c).range := ⟨_, hmem ⟨p.1, c' p.1⟩⟩
  have hu : u ≠ 0 := fun h ↦ div_ne_zero (hz' p.1) (hz p.1) (congrArg Subtype.val h)
  obtain ⟨w, hw⟩ := hF.mul_inv_cancel hu
  have hinv : (u : FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))⁻¹ ∈ (dehomFrac V c).range := by
    rw [← eq_inv_of_mul_eq_one_right (congrArg Subtype.val hw)]
    exact w.2
  have e : classFrac V (X p) / classFrac V (X ⟨p.1, c' p.1⟩) =
      classFrac V (X p) / classFrac V (X ⟨p.1, c p.1⟩) * (u : FractionRing _)⁻¹ := by
    change _ = _ * (classFrac V (X ⟨p.1, c' p.1⟩) / classFrac V (X ⟨p.1, c p.1⟩))⁻¹
    field_simp [hz p.1, hz' p.1]
  change classFrac V (X p) / classFrac V (X ⟨p.1, c' p.1⟩) ∈ (dehomFrac V c).range
  rw [e]
  exact mul_mem (hmem p) hinv

/- English proof (translation)
Introduce `ι _ _ _ n A x s hx hs V hV c c' hc hc'`. Establish `hPV : orbitIdeal x ≤ V` using `le_sup_left.trans hV.1.1.2`. Establish `: V.IsPrime` using `hV.1.1.1`. Take `⟨a, -, hsa, -⟩` from `id hs`. Establish `hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V` using `fun f hf b ↦ weightedHomogeneousComponent_mem_of_mem_divSupp x ((geoMultiHomog_iff s a).mp hsa) hV hf b`.

Use `⟨comap_sup_chartOneIdeal hVh hc, ?_⟩` and prove the remaining obligations. Establish `hfield : ∀ d : (k : ι) → Fin (n k + 1), (∀ k, (X ⟨k, d k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) → IsField (dehomFrac V d).range`. Introduce `d hd`. Establish `hxd : ∀ k, x k (d k) ≠ 0`. Introduce `k h0`.

Apply `hd k` to reduce the goal to its premises. Apply `hPV` to reduce the goal to its premises. Rewrite using `[orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]`. Simplify using `[flatCone, h0]`. Take `⟨eQ⟩` from `hQ ι n x d hxd V hPV`.

Establish `hmax` using `hM ι n A x s hx hs V hV d hd`. Conclude with `MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax) (eQ.trans (quotEquivRange hVh hd)).symm.toMulEquiv`. Establish `hr : (dehomFrac V c).range = (dehomFrac V c').range` using `le_antisymm (range_dehomFrac_le hc' hc (hfield c' hc')) (range_dehomFrac_le hc hc' (hfield c hc))`. Conclude with `⟨(quotEquivRange hVh hc).trans ((Subalgebra.equivOfEq _ _ hr).toRingEquiv.trans (quotEquivRange hVh hc').symm)⟩`.
-/
theorem OrbitChartDehom.proof (hM : OrbitChartMax.Statement) (hQ : OrbitChartQuot.Statement) :
    OrbitChartDehom.Statement := by
  intro ι _ _ _ n A x s hx hs V hV c c' hc hc'
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hV.1.1.2
  have : V.IsPrime := hV.1.1.1
  obtain ⟨a, -, hsa, -⟩ := id hs
  have hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V :=
    fun f hf b ↦ weightedHomogeneousComponent_mem_of_mem_divSupp x ((geoMultiHomog_iff s a).mp hsa)
      hV hf b
  refine ⟨comap_sup_chartOneIdeal hVh hc, ?_⟩
  have hfield : ∀ d : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, d k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) → IsField (dehomFrac V d).range := by
    intro d hd
    have hxd : ∀ k, x k (d k) ≠ 0 := by
      intro k h0
      apply hd k
      apply hPV
      rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
      simp [flatCone, h0]
    obtain ⟨eQ⟩ := hQ ι n x d hxd V hPV
    have hmax := hM ι n A x s hx hs V hV d hd
    exact MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
      (eQ.trans (quotEquivRange hVh hd)).symm.toMulEquiv
  have hr : (dehomFrac V c).range = (dehomFrac V c').range :=
    le_antisymm (range_dehomFrac_le hc' hc (hfield c' hc')) (range_dehomFrac_le hc hc' (hfield c hc))
  exact ⟨(quotEquivRange hVh hc).trans
    ((Subalgebra.equivOfEq _ _ hr).toRingEquiv.trans (quotEquivRange hVh hc').symm)⟩

end

end GroundTheory.Heights₂.Heights
