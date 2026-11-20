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

/- English proof (translation)
Establish `hn' : ((n : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x)` using `hn`. Establish `hle : ((n : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim ↥X` using `le_trans hn' (ringKrullDim_stalk_le_topologicalKrullDim X x)`. Rewrite using `[krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]`. Distinguish the cases in `hb : topologicalKrullDim ↥X = ⊥`. Rewrite `hle` using `[hb]`.

Conclude with `absurd (le_bot_iff.mp hle) WithBot.coe_ne_bot`. Take `⟨e, he⟩` from `WithBot.ne_bot_iff_exists.mp hb`. Rewrite `hle`, `hfin`, the goal using `[← he]`. Establish `he' : e ≠ ⊤`. Introduce `hcon`.

Apply `hfin` to reduce the goal to its premises. Rewrite using `[hcon]`. Simplify using the standard rewrite rules. Use `lift e to ℕ using he' with m`. Rewrite using `[withBotSuccToNat_coe]`.

Establish `hmm : ((m : ℕ∞)).toNat = m` using `by simp`. Rewrite using `[hmm]`. Establish `hnm : n ≤ m` using `by exact_mod_cast hle`. Use linear arithmetic over natural numbers and integers.
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

/- English proof (translation)
Introduce `T hT J C hC`. Establish `hC' : IsIrreducible C ∧ C ⊆ (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) ∧ ∀ C' : Set ↥T.scheme, IsIrreducible C' → C ⊆ C' → C' ⊆ (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) → C' = C` using `(mem_intersectionComponents_iff T.boundary J C).mp hC`. Take `⟨hirr, hsub, -⟩` from `hC'`. Take `⟨x, hxC⟩` from `hirr.nonempty`. Establish `hxsupp : x ∈ (intersectionIdeal T.boundary J).support` using `hsub hxC`.

Establish `hxj : ∀ j ∈ J, x ∈ (T.boundary.get j).support`. Introduce `j hj`. Rewrite using `[mem_support_iff_stalkIdeal_ne_top]`. Introduce `htop`. Rewrite `hxsupp` using `[mem_support_iff_stalkIdeal_ne_top]`.

Establish `hle : T.boundary.get j ≤ intersectionIdeal T.boundary J`. Rewrite using `[intersectionIdeal_eq_iSup]`. Conclude with `le_iSup₂ (f := fun (i : Fin T.boundary.length) (_ : i ∈ J) => T.boundary.get i) j hj`. Establish `h1` using `stalkIdeal_mono hle x`. Rewrite `h1` using `[htop]`.

Conclude with `hxsupp (top_le_iff.mp h1)`. Take `⟨-, hsnc⟩` from `(inStrictNormalCrossingPosition_iff T.structMap T.boundary).mp hT.snc`. Take `⟨U, hxU, m, c, a, hinj, hnone, hsome⟩` from `(hsnc x).exists_etaleChart`. Take `⟨V, hVB, hxV, hVU⟩` from `Opens.isBasis_iff_nbhd.mp T.scheme.isBasis_affineOpens hxU`. Establish `hV : IsAffineOpen V` using `hVB`.

Establish `hex : ∀ j : Fin T.boundary.length, j ∈ J → ∃ t : Fin m, a (j : ℕ) = some t`. Introduce `j hj`. Establish `hne : a (j : ℕ) ≠ none`. Introduce `hj'`. Establish `htop` using `hnone (j : ℕ) j.isLt hj'`.

Establish `hx'` using `hxj j hj`. Rewrite `hx'` using `[List.get_eq_getElem]`. Conclude with `Scheme.IdealSheafData.notMem_support_of_comap_ι_eq_top _ htop hxU hx'`. Conclude with `Option.ne_none_iff_exists'.mp hne`. Use `choose F hFspec using hex`.

Establish `hGinj : Function.Injective (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2)`. Introduce `p q h`. Establish `h1 : a (q.1 : ℕ) = some (F p.1 p.2)`. Rewrite using `[hFspec q.1 q.2]`. Conclude with `congrArg Option.some h.symm`.

Establish `h2` using `hinj (p.1 : ℕ) p.1.isLt (q.1 : ℕ) q.1.isLt (F p.1 p.2) (hFspec p.1 p.2) h1`. Conclude with `Subtype.ext (Fin.val_injective h2)`. Establish `hcard : (J.attach.image (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2)).card = J.card`. Rewrite using `[Finset.card_image_of_injective _ hGinj, Finset.card_attach]`. Establish `hmem : ∀ t ∈ J.attach.image (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2), (c.restrict hVU).coord t ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal`.

Introduce `t ht`. Take `⟨p, -, hpt⟩` from `Finset.mem_image.mp ht`. Establish `hat : a (p.1 : ℕ) = some t`. Rewrite using `[hFspec p.1 p.2]`. Conclude with `congrArg Option.some hpt`.

Establish `hU'` using `hsome (p.1 : ℕ) p.1.isLt t hat`. Establish `hV'` using `restrictIdeal_eq_restrict_coordIdeal_of_le hVU c _ {t} hU'`. Establish `hx'` using `hxj p.1 p.2`. Rewrite `hx'` using `[List.get_eq_getElem]`. Conclude with `coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton hV (c.restrict hVU) t _ hV' x hxV hx'`.

Establish `hle2` using `card_le_ringKrullDim_stalk hV (c.restrict hVU) x hxV (J.attach.image (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2)) hmem`. Establish `hfin : topologicalKrullDim ↥T.scheme ≠ ⊤` using `ne_of_lt hT.topologicalKrullDim_lt_top`. Establish `hlt` using `lt_krullDimSucc_of_le_ringKrullDim_stalk T.scheme x _ hle2 hfin`. Rewrite `hlt` using `[hcard]`. Then use the resulting hypothesis.
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

/- English proof (translation)
Take `⟨C, hC⟩` from `hJ`. Conclude with `card_lt_krullDimSucc_of_mem_intersectionComponents T hT J C hC`.
-/
theorem card_lt_krullDimSucc_of_nonempty (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (hJ : (intersectionComponents T.boundary J).Nonempty) :
    J.card < krullDimSucc T.scheme := by
  obtain ⟨C, hC⟩ := hJ
  exact card_lt_krullDimSucc_of_mem_intersectionComponents T hT J C hC

end MonomialCodimension

end FunctorialResolution.EmbeddedResolution
