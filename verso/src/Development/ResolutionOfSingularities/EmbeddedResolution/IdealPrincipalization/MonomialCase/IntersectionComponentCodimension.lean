import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDimensionBound
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StalkKrullDimension
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FiniteKrullDim
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCodimension

/- English proof (authored)
The Krull dimension of the stalk is bounded by the topological Krull dimension of the scheme. The latter is at least the given natural number, so it cannot be the dimension of the empty space. By the finiteness assumption it is also below infinity. Write it as a natural number d. The given number is at most d and therefore strictly below d + 1, the dimension successor of the scheme.
-/
theorem lt_krullDimSucc_of_le_ringKrullDim_stalk (X : Scheme.{u}) (x : ↥X) (n : ℕ)
    (hn : (n : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x))
    (hfin : topologicalKrullDim ↥X ≠ ⊤) : n < krullDimSucc X := by
  have hn' : ((n : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := hn
  have hle : ((n : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim ↥X :=
    le_trans hn' (ringKrullDim_stalk_le_topologicalKrullDim X x)
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  by_cases hb : topologicalKrullDim ↥X = ⊥
  · rw [hb] at hle
    exact absurd (le_bot_iff.mp hle) WithBot.coe_ne_bot
  · obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hb
    rw [← he] at hle hfin ⊢
    have he' : e ≠ ⊤ := by
      intro hcon
      apply hfin
      rw [hcon]
      simp
    lift e to ℕ using he' with m
    rw [withBotSuccToNat_coe]
    have hmm : ((m : ℕ∞)).toNat = m := by simp
    rw [hmm]
    have hnm : n ≤ m := by exact_mod_cast hle
    omega

/- English proof (authored)
Choose a point of the given irreducible component. It lies in the support of the sum of the selected boundary ideals and hence in the support of each summand, since a unit summand would make the sum the unit ideal. Take an étale boundary chart at the point and an affine open inside it containing the point. Each selected divisor is defined there by a coordinate vanishing at the point, and distinct divisors have distinct coordinates. Thus the point's prime contains as many distinct chart coordinates as there are selected divisors. The coordinate dimension bound gives at least that many dimensions in the stalk. The stalk dimension bound then puts this cardinality strictly below the dimension successor of the ambient scheme.
-/
theorem card_lt_krullDimSucc_of_mem_intersectionComponents : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      C ∈ intersectionComponents T.boundary J → J.card < krullDimSucc T.scheme := by
  classical
  intro T hT J C hC
  have hC' : IsIrreducible C ∧ C ⊆ (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) ∧
      ∀ C' : Set ↥T.scheme, IsIrreducible C' → C ⊆ C' →
        C' ⊆ (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) → C' = C :=
    (mem_intersectionComponents_iff T.boundary J C).mp hC
  obtain ⟨hirr, hsub, -⟩ := hC'
  obtain ⟨x, hxC⟩ := hirr.nonempty
  have hxsupp : x ∈ (intersectionIdeal T.boundary J).support := hsub hxC
  have hxj : ∀ j ∈ J, x ∈ (T.boundary.get j).support := by
    intro j hj
    rw [mem_support_iff_stalkIdeal_ne_top]
    intro htop
    rw [mem_support_iff_stalkIdeal_ne_top] at hxsupp
    have hle : T.boundary.get j ≤ intersectionIdeal T.boundary J := by
      rw [intersectionIdeal_eq_iSup]
      exact le_iSup₂ (f := fun (i : Fin T.boundary.length) (_ : i ∈ J) => T.boundary.get i) j hj
    have h1 := stalkIdeal_mono hle x
    rw [htop] at h1
    exact hxsupp (top_le_iff.mp h1)
  obtain ⟨-, hsnc⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).mp hT.snc
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := (hsnc x).exists_etaleChart
  obtain ⟨V, hVB, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp T.scheme.isBasis_affineOpens hxU
  have hV : IsAffineOpen V := hVB
  have hex : ∀ j : Fin T.boundary.length, j ∈ J → ∃ t : Fin m, a (j : ℕ) = some t := by
    intro j hj
    have hne : a (j : ℕ) ≠ none := by
      intro hj'
      have htop := hnone (j : ℕ) j.isLt hj'
      have hx' := hxj j hj
      rw [List.get_eq_getElem] at hx'
      exact Scheme.IdealSheafData.notMem_support_of_comap_ι_eq_top _ htop hxU hx'
    exact Option.ne_none_iff_exists'.mp hne
  choose F hFspec using hex
  have hGinj : Function.Injective
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2) := by
    intro p q h
    have h1 : a (q.1 : ℕ) = some (F p.1 p.2) := by
      rw [hFspec q.1 q.2]
      exact congrArg Option.some h.symm
    have h2 := hinj (p.1 : ℕ) p.1.isLt (q.1 : ℕ) q.1.isLt (F p.1 p.2) (hFspec p.1 p.2) h1
    exact Subtype.ext (Fin.val_injective h2)
  have hcard : (J.attach.image
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2)).card = J.card := by
    rw [Finset.card_image_of_injective _ hGinj, Finset.card_attach]
  have hmem : ∀ t ∈ J.attach.image
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2),
      (c.restrict hVU).coord t ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    intro t ht
    obtain ⟨p, -, hpt⟩ := Finset.mem_image.mp ht
    have hat : a (p.1 : ℕ) = some t := by
      rw [hFspec p.1 p.2]
      exact congrArg Option.some hpt
    have hU' := hsome (p.1 : ℕ) p.1.isLt t hat
    have hV' := restrictIdeal_eq_restrict_coordIdeal_of_le hVU c _ {t} hU'
    have hx' := hxj p.1 p.2
    rw [List.get_eq_getElem] at hx'
    exact coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton hV
      (c.restrict hVU) t _ hV' x hxV hx'
  have hle2 := card_le_ringKrullDim_stalk hV (c.restrict hVU) x hxV
    (J.attach.image (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2)) hmem
  have hfin : topologicalKrullDim ↥T.scheme ≠ ⊤ := ne_of_lt hT.topologicalKrullDim_lt_top
  have hlt := lt_krullDimSucc_of_le_ringKrullDim_stalk T.scheme x _ hle2 hfin
  rwa [hcard] at hlt

/- English proof (authored)
Choose one component from the nonempty intersection-component set. The cardinality bound for a selected family admitting such a component applies to it.
-/
theorem card_lt_krullDimSucc_of_nonempty (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (hJ : (intersectionComponents T.boundary J).Nonempty) :
    J.card < krullDimSucc T.scheme := by
  obtain ⟨C, hC⟩ := hJ
  exact card_lt_krullDimSucc_of_mem_intersectionComponents T hT J C hC

end MonomialCodimension

end FunctorialResolution.EmbeddedResolution
