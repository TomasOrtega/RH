import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsAddHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderUnderStalkIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverPieces
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderBoundAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AdaptedParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDivisorBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsChartNormalization
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.AffineSpaceCoordinateBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace OrderReduction

def ValidPullbackAlongSmooth : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.QuasiCompact q],
      h ≫ T.structMap = q → (T.pullbackAlong Y q h).IsAdmissible

/- English proof (authored)
Expand the named property. It asserts that an admissible marked triple remains admissible after the indicated smooth pullback, with quasi-compact structural map upstairs and the stated compatibility of structural maps. This is exactly the quantified condition.
-/
theorem validPullbackAlongSmooth_iff :
    ValidPullbackAlongSmooth.{u} ↔
      ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
        (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.QuasiCompact q],
        h ≫ T.structMap = q → (T.pullbackAlong Y q h).IsAdmissible :=
  Iff.rfl

end OrderReduction

namespace MaxContactCoverData

/- English proof (authored)
At a point outside the original support, the ideal has unit stalk. Its power then also has unit stalk, so the point lies outside the support of the power. This proves the inclusion for every exponent.
-/
private theorem support_pow_subset {X : Scheme.{u}} (I : X.IdealSheafData) (s : ℕ) :
    ((I ^ s).support : Set ↥X) ⊆ (I.support : Set ↥X) := by
  intro x hx
  simp only [SetLike.mem_coe] at hx ⊢
  rw [mem_support_iff_stalkIdeal_ne_top] at hx ⊢
  intro hI
  apply hx
  rw [stalkIdeal_pow, hI, Ideal.top_pow]

/- English proof (authored)
Split the product at its final index n. All earlier indices are distinct from n and have exponent zero, giving unit factors. The factor at n has exponent s, so the whole product is that power.
-/
private theorem prod_map_range_pow_ite_eq_pow {X : Scheme.{u}} (A : ℕ → X.IdealSheafData) (n s : ℕ) :
    (List.map (fun j => A j ^ (if j = n then s else 0)) (List.range (n + 1))).prod = A n ^ s := by
  have h1 : (List.map (fun j => A j ^ (if j = n then s else 0)) (List.range n)).prod = 1 := by
    apply List.prod_eq_one
    intro y hy
    simp only [List.mem_map, List.mem_range] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    rw [if_neg (Nat.ne_of_lt hj), pow_zero]
  rw [List.range_succ, List.map_append, List.prod_append, h1, one_mul]
  simp

/- English proof (authored)
The positive mark can be written as n + 1. Take the n-th derivative iterate as the auxiliary ideal. It contains the original ideal. In the defining weighted products for the tuned ideal, choose exponent s at index n and zero at all other indices. The weight of index n is one, so the weighted sum is exactly s. This gives an admitted product for tuning, and the product is the s-th power of the auxiliary ideal.
-/
private theorem exists_le_and_pow_le_tunedSheaf (k : Type u) [Field k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] (I : X.IdealSheafData) (m s : ℕ) (hm : 1 ≤ m) :
    ∃ J : X.IdealSheafData, I ≤ J ∧ J ^ s ≤ tunedSheaf k p I m s := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine ⟨derivIdealSheafIterate k p n I, le_derivIdealSheafIterate k p n I, ?_⟩
  have h0 : (∑ j ∈ Finset.range (n + 1), (n + 1 - j) * (if j = n then s else 0))
      = (n + 1 - n) * (if n = n then s else 0) := by
    refine Finset.sum_eq_single n (fun b _ hb => by simp [hb]) (fun h => ?_)
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
  have hsum : (∑ j ∈ Finset.range (n + 1), (n + 1 - j) * (if j = n then s else 0)) = s := by
    rw [h0, if_pos rfl, Nat.add_sub_cancel_left, one_mul]
  have h := prod_pow_derivIdealSheafIterate_le_tunedSheaf k p I (n + 1) s
    (fun j => if j = n then s else 0) hsum.ge
  rw [prod_map_range_pow_ite_eq_pow] at h
  exact h

/- English proof (authored)
The cover's balanced tuned ideal is defined by the balanced tuning construction for the original field, structural map, ideal and mark. Substituting those data gives the asserted equality.
-/
theorem balancedTunedIdeal_eq_balancedTunedSheaf (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] :
    balancedTunedIdeal T hv = FunctorialResolution.EmbeddedResolution.balancedTunedSheaf T.base T.structMap T.ideal T.mult :=
  rfl

/- English proof (authored)
Choose the auxiliary derivative ideal containing the original ideal and whose power at the tuning exponent is contained in the balanced tuned ideal. The support of the balanced tuned ideal is contained in the support of that power. The latter lies in the auxiliary ideal's support, which in turn lies in the original support by ideal inclusion. Since the original ideal vanishes identically on no component, the balanced tuned ideal cannot vanish identically on a component either.
-/
theorem nonzeroOnComponents_balancedTunedIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    NonzeroOnComponents (balancedTunedIdeal T hv) := by
  have := hv.locallyOfFiniteType
  obtain ⟨J, hIJ, hJ⟩ :=
    exists_le_and_pow_le_tunedSheaf T.base T.structMap T.ideal T.mult (tuningExponent T.mult) hv.one_le_mult
  have hle : J ^ tuningExponent T.mult ≤ balancedTunedIdeal T hv := by
    rw [balancedTunedIdeal_eq_balancedTunedSheaf T hv, balancedTunedSheaf_eq]
    exact hJ
  have hnz := hv.nonzeroOnComponents
  rw [nonzeroOnComponents_iff] at hnz ⊢
  intro C hC hsub
  refine hnz C hC ?_
  intro x hx
  have h1 := hsub hx
  have h2 := SetLike.coe_subset_coe.2 (Scheme.IdealSheafData.support_antitone hle) h1
  have h3 := support_pow_subset J (tuningExponent T.mult) h2
  exact SetLike.coe_subset_coe.2 (Scheme.IdealSheafData.support_antitone hIJ) h3

/- English proof (authored)
If the original order locus is empty, its balanced tuned ideal is the unit ideal and has order zero. Otherwise the pointwise original bound and nonempty locus give maximal order equal to the mark. The tuning theorem bounds the order of the tuned ideal by the chosen tuning exponent. The balanced tuned ideal uses that exponent and the tuned mark equals it, giving the bound.
-/
theorem orderAt_balancedTunedIdeal_le_tunedMult (htf : TunedSheafProperties.{u}) (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) (x : ↥T.scheme) :
    orderAt (balancedTunedIdeal T hv) x ≤ ((tunedMult T : ℕ) : ℕ∞) := by
  have := hv.locallyOfFiniteType
  have := hv.charZero
  have := hv.smooth
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · have htop : balancedTunedIdeal T hv = ⊤ := by
      rw [balancedTunedIdeal_eq_balancedTunedSheaf T hv]
      exact balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty T.base T.structMap T.ideal hv.one_le_mult hemp
    rw [htop, orderAt_top]
    simp
  · have hmax : MaxOrderEq T.ideal T.mult :=
      ⟨(orderLE_iff T.ideal T.mult).2 hord, Set.nonempty_iff_ne_empty.2 hemp⟩
    have hLE := htf.coSupport_tunedSheaf_eq_and_orderLE.orderLE T.base T.scheme T.structMap
      T.ideal T.mult hv.one_le_mult hmax (tuningExponent T.mult) (one_le_tuningExponent T.mult)
    rw [orderLE_iff] at hLE
    have h2 : balancedTunedIdeal T hv = tunedSheaf T.base T.structMap T.ideal T.mult (tuningExponent T.mult) := by
      rw [balancedTunedIdeal_eq_balancedTunedSheaf T hv, balancedTunedSheaf_eq]
    rw [h2]
    exact hLE x

/- English proof (authored)
Balanced tuning is nonzero on components, so the tuned triple is admissible by the admissibility result for tuning. The cover triple is its pullback along the smooth cover map. The cover's structural map is quasi-compact by the good-cover condition. The given preservation of admissibility under smooth pullback therefore applies.
-/
theorem isAdmissible_coverTriple_of_validPullbackAlongSmooth (hpb : OrderReduction.ValidPullbackAlongSmooth.{u})
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
      (balancedTunedIdeal T hv) (tunedMult T)) :
    (coverTriple T hv).IsAdmissible := by
  have hvt := MaxContactOpenCover.isAdmissible_tunedTriple T hv (nonzeroOnComponents_balancedTunedIdeal T hv)
  have hqc := MaxContactOpenCover.quasiCompact_coverMap_comp_structureMorphism T hv hgood
  rw [MaxContactOpenCover.coverTriple_eq_tunedTriple_pullbackAlong T hv]
  exact @hpb (MaxContactOpenCover.tunedTriple T hv) hvt (chosenCoverData T hv).disjointUnion
    (coverMap T hv ≫ T.structMap) (coverMap T hv) (MaxContactCoverData.instSmoothCoverMap T hv) hqc rfl

/- English proof (authored)
At each point the good-cover normal-crossings result supplies an étale chart for the singleton ideal. If no coordinate is assigned to its only entry, the restriction is the unit ideal. If a coordinate is assigned, the restriction is the ideal of that coordinate. This local description is the criterion for a smooth divisor.
-/
theorem isSmoothDivisor_coverMaxContactIdeal (_hpb : OrderReduction.ValidPullbackAlongSmooth.{u})
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
      (balancedTunedIdeal T hv) (tunedMult T)) :
    IsSmoothDivisor (coverTriple T hv).structMap (coverMaxContactIdeal T hv) := by
  refine FunctorialResolution.EmbeddedResolution.isSmoothDivisor_of_locally_coordIdeal (coverMaxContactIdeal T hv) ?_
  intro x
  obtain ⟨U, hxU, m, c, a, _hinj, hnone, hsome⟩ :=
    (MaxContactCoverGeometry.inStrictNormalCrossingPositionAt_of_isMaxContactCover T hv hgood x).exists_etaleChart
  refine ⟨U, hxU, m, c, ?_⟩
  rcases ha : a 0 with _ | t
  · exact Or.inl (hnone 0 (by simp) ha)
  · exact Or.inr ⟨t, hsome 0 (by simp) t ha⟩

end MaxContactCoverData

namespace OrderReduction

/- English proof (authored)
Use the one-step strict-transform theorem for maximal contact and the order-locus inclusion under blowup. The assumed dimension inequality gives the bound at every stage. The tuned ideal order bound gives existence of a good cover, and the normal-crossings lemma allows a hypersurface contained in the center to be included with the other divisors. The stage transform and order-bound theorems give stage admissibility and preservation of the mark bound.

For the cover itself, the disjoint union of the chosen opens has dimension at most the original scheme, and smooth pullback of the tuned triple makes the cover admissible. The cover ideal restricts to the local maximal-contact ideals. It therefore has maximal contact and, using the smooth-divisor criterion, satisfies strict normal-crossing position. Together with the assumed tuning properties these verify all the cover properties.
-/
theorem maxContactCoverProperties_of_tunedSheafProperties (htf : TunedSheafProperties.{u}) (hdim : DimensionNonincreasingAlongBlowups.{u})
    (hpb : ValidPullbackAlongSmooth.{u}) : MaxContactCoverProperties.{u} := by
  refine
    { strictTransform_admissible := ?_
      coSupport_le_preimage := ?_
      schemeDim_level_le := ?_
      exists_goodCover := ?_
      hasSNCWith_cons := ?_
      valid_level := ?_
      orderAt_level_le := ?_
      coverTriple_dim_le := ?_
      coverTriple_valid := ?_
      coverContact_admissible := ?_
      coverContact_snc := ?_
      tuning := htf }
  · intro k _ _ P P₁ p _ _ _ π _ Z E hZ hπ A A₁ μ hμ hordA hsupp htr H hH
    exact FunctorialResolution.EmbeddedResolution.isMaxContactHypersurface_strictTransform_of_orderAt_le k p π Z E hZ hπ A A₁ μ hμ hordA
      hsupp htr H hH
  · intro X X₁ π Z hπ A A₁ μ htr hsupp
    exact FunctorialResolution.EmbeddedResolution.OrderLocusBlowup.orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf π Z hπ A A₁ μ htr hsupp
  · intro T hT s i hi
    exact hdim T hT s i hi
  · intro T hv hord
    exact MaxContactOpenCover.exists_isMaxContactCover T hv (MaxContactCoverData.orderAt_balancedTunedIdeal_le_tunedMult htf T hv hord)
  · intro k _ P p _ Z H N _hsmZ hsnc hZN hHZ
    exact FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_cons_of_le p Z H N hsnc hZN hHZ
  · intro T hT s i hi
    exact MarkedIdealWithBoundary.IsAdmissible.transformAt effectiveCartierSupportContainsNoComponent hT s i hi
  · intro T hT hord s i hi x
    exact FunctorialResolution.EmbeddedResolution.orderAt_ideal_le_mult_along_sequence T hT hord s i hi x
  · intro T hv
    exact MaxContactOpenCover.krullDimSucc_coverTriple_scheme_le_dim T hv
  · intro T hv _hord hgood
    exact MaxContactCoverData.isAdmissible_coverTriple_of_validPullbackAlongSmooth hpb T hv hgood
  · intro T hv hgood _
    exact MaxContactCoverGeometry.isMaxContactHypersurface_coverMaxContactIdeal T hv hgood
  · intro T hv hgood
    exact MaxContactCoverGeometry.inStrictNormalCrossingPosition_of_isMaxContactCover T hv hgood
      (MaxContactCoverData.isSmoothDivisor_coverMaxContactIdeal hpb T hv hgood)

end OrderReduction

end FunctorialResolution.EmbeddedResolution

end
