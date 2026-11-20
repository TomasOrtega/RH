import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDivisorBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
Every point of the upstairs open maps into the complement of the center’s support. The pullback of the center ideal along the composite from that open therefore has empty support and is the unit ideal.
-/
private theorem comap_comp_eq_top_of_le_preimage_compl {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (V : X₁.Opens) (hV : V ≤ π ⁻¹ᵁ Z.support.compl) :
    Z.comap (V.ι ≫ π) = ⊤ := by
  refine Blowup.comap_eq_top_of_notMem_support _ Z fun x => ?_
  show π.base x.1 ∉ Z.support
  exact hV x.2

/- English proof (authored)
The inverse-image square commutes. Restricting the pulled-back ideal along the upstairs inclusion is consequently the same as restricting the original ideal downstairs and pulling it back along the restricted morphism.
-/
private theorem restrictIdeal_comap_preimage {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (D : X.IdealSheafData) (W : X.Opens) :
    restrictIdeal (D.comap π) (π ⁻¹ᵁ W) = (restrictIdeal D W).comap (π ∣_ W) := by
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι]

/- English proof (authored)
Taking the strict transform of each entry preserves the number of entries. Appending the exceptional ideal adds exactly one.
-/
private theorem length_strictTransform_append_exceptionalIdeal {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length = E.length + 1 := by
  simp

/- English proof (authored)
The given index is in the first part of the appended list. Its entry there is the strict transform of the original entry at that index.
-/
private theorem getElem_strictTransform_append_exceptionalIdeal_of_lt {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData)
    (E : List X.IdealSheafData) (i : ℕ) (hi : i < E.length)
    {h : i < (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length} :
    (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z])[i]'h
      = Blowup.strictTransform π Z (E[i]'hi) := by
  rw [List.getElem_append_left (by simpa using hi)]
  simp

/- English proof (authored)
The mapped list has the original length, so the next index is the first position of the appended singleton. This holds the exceptional ideal.
-/
private theorem getElem_length_strictTransform_append_exceptionalIdeal {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData)
    (E : List X.IdealSheafData)
    {h : E.length < (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length} :
    (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z])[E.length]'h
      = Blowup.exceptionalIdeal π Z := by
  rw [List.getElem_append_right (by simp)]
  simp

/- English proof (authored)
Restrict the blowup to the open, where it remains a blowup of the restricted center ideal. The open avoids the center’s support, so this ideal is the unit ideal. The blowup of the unit ideal is an isomorphism by the universal property.
-/
theorem isIso_morphismRestrict_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}} {π : X₁ ⟶ X}
    {Z : X.IdealSheafData} (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (W : X.Opens)
    (hW : ∀ x : X, x ∈ W → x ∉ Z.support) :
    IsIso (π ∣_ W) := by
  have h1 := hπ.restrict W
  have h2 : Z.comap (Scheme.Opens.ι W) = ⊤ := by
    refine Blowup.comap_eq_top_of_notMem_support _ Z fun x => ?_
    show x.1 ∉ Z.support
    exact hW x.1 x.2
  rw [h2] at h1
  exact h1.isIso_of_top

/- English proof (authored)
Restrict the strict transform to the open, which commutes with its formation. The center ideal pulls back to the unit ideal there because the open lies off its support. The strict transform is saturation of the total transform by this unit ideal. Saturation by powers of one leaves every section ideal unchanged.
-/
theorem restrictIdeal_strictTransform_eq_comap_of_le_compl {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)]
    (V : X₁.Opens) (hV : V ≤ π ⁻¹ᵁ Z.support.compl) :
    restrictIdeal (Blowup.strictTransform π Z D) V = restrictIdeal (D.comap π) V := by
  have := quasiCompact_strictTransformι_comp_ι π Z D V
  have hZ : Z.comap (V.ι ≫ π) = ⊤ := comap_comp_eq_top_of_le_preimage_compl π Z V hV
  rw [restrictIdeal_strictTransform π Z D V, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp]
  refine Scheme.IdealSheafData.ext ?_
  funext W
  exact strictTransform_ideal_eq_comap_of_isUnit (V.ι ≫ π) Z D W 1 (by simp [hZ]) isUnit_one

/- English proof (authored)
The pointwise condition says that the open lies in the inverse image of the complement of the center. On such an open the strict and total transforms agree because the exceptional ideal is the unit ideal.
-/
theorem restrictIdeal_strictTransform_eq_comap_of_notMem_support {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)]
    (V : X₁.Opens) (hV : ∀ x : X₁, x ∈ V → π.base x ∉ Z.support) :
    restrictIdeal (Blowup.strictTransform π Z D) V = restrictIdeal (D.comap π) V := by
  refine restrictIdeal_strictTransform_eq_comap_of_le_compl π Z D V ?_
  intro x hx
  exact hV x hx

/- English proof (authored)
The exceptional ideal is the pullback of the center. Its restriction is the pullback along the composite from the given open. This composite avoids the center support, so the ideal is the unit ideal.
-/
theorem restrictIdeal_exceptionalIdeal_eq_top_of_le_compl {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (V : X₁.Opens) (hV : V ≤ π ⁻¹ᵁ Z.support.compl) :
    restrictIdeal (Blowup.exceptionalIdeal π Z) V = ⊤ := by
  rw [restrictIdeal_eq_comap_ι, Blowup.exceptionalIdeal_eq_comap, ← Scheme.IdealSheafData.comap_comp]
  exact comap_comp_eq_top_of_le_preimage_compl π Z V hV

/- English proof (authored)
The pointwise hypothesis puts the open in the inverse image of the complement of the center. The exceptional ideal is the unit ideal there, since it is pulled back from the center.
-/
theorem restrictIdeal_exceptionalIdeal_eq_top_of_notMem_support {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (V : X₁.Opens)
    (hV : ∀ x : X₁, x ∈ V → π.base x ∉ Z.support) :
    restrictIdeal (Blowup.exceptionalIdeal π Z) V = ⊤ := by
  refine restrictIdeal_exceptionalIdeal_eq_top_of_le_compl π Z V ?_
  intro x hx
  exact hV x hx

/- English proof (authored)
Choose a downstairs étale chart with distinct boundary coordinates and a coordinate center, then a blowup chart containing the given point upstairs. Assign the exceptional divisor the distinguished coordinate. An original divisor absent downstairs stays absent. An original divisor defined by the distinguished coordinate has empty strict transform on this chart. Every other present divisor has strict transform given by its corresponding chart coordinate. These remaining indices retain their original distinctness and none is the distinguished index. Together with the exceptional divisor they give the required pointwise chart.
-/
theorem inStrictNormalCrossingPositionAt_strictTransform_of_mem_support {X X₁ : Scheme.{u}} {k : Type u}
    [Field k] [NoetherianSpace X₁] (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (E : List X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (hZE : HasStrictNormalCrossingsWith p Z E) (x₁ : X₁) (hx₁ : π.base x₁ ∈ Z.support) :
    InStrictNormalCrossingPositionAt (π ≫ p) (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]) x₁ := by
  classical
  have instQuasiCompact : ∀ D : X.IdealSheafData, QuasiCompact (strictTransformι π Z D) :=
    fun D => quasiCompact_strictTransformι_of_noetherianSpace π Z D
  unfold HasStrictNormalCrossingsWith at hZE
  obtain ⟨U, hxU, m, c, a, S, ha1, ha2, ha3, hZU⟩ := hZE _ hx₁
  have hxmem : x₁ ∈ π ⁻¹ᵁ U := hxU
  obtain ⟨s, hs, hx₁B⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x₁ hxmem
  set B := blowupChartOfIsBlowup π c S hπ hZU s hs with hBdef
  have hlen : (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length = E.length + 1 :=
    length_strictTransform_append_exceptionalIdeal π Z E
  unfold InStrictNormalCrossingPositionAt
  refine ⟨B.domain, hx₁B, m, B.chart,
    fun i => if i = E.length then some s else if a i = some s then none else a i, ?_, ?_, ?_⟩
  · intro i hi j hj t hti htj
    have hti' : (if i = E.length then some s else if a i = some s then none else a i) = some t :=
      hti
    have htj' : (if j = E.length then some s else if a j = some s then none else a j) = some t :=
      htj
    rw [hlen] at hi hj
    by_cases hiE : i = E.length
    · by_cases hjE : j = E.length
      · rw [hiE, hjE]
      · exfalso
        rw [if_pos hiE] at hti'
        rw [if_neg hjE] at htj'
        have hts : s = t := Option.some.inj hti'
        by_cases haj : a j = some s
        · rw [if_pos haj] at htj'
          simp at htj'
        · rw [if_neg haj] at htj'
          exact haj (by rw [htj', ← hts])
    · by_cases hjE : j = E.length
      · exfalso
        rw [if_pos hjE] at htj'
        rw [if_neg hiE] at hti'
        have hts : s = t := Option.some.inj htj'
        by_cases hai : a i = some s
        · rw [if_pos hai] at hti'
          simp at hti'
        · rw [if_neg hai] at hti'
          exact hai (by rw [hti', ← hts])
      · rw [if_neg hiE] at hti'
        rw [if_neg hjE] at htj'
        by_cases hai : a i = some s
        · rw [if_pos hai] at hti'
          simp at hti'
        · rw [if_neg hai] at hti'
          by_cases haj : a j = some s
          · rw [if_pos haj] at htj'
            simp at htj'
          · rw [if_neg haj] at htj'
            exact ha1 i (by omega) j (by omega) t hti' htj'
  · intro i h hnone
    have hnone' : (if i = E.length then some s else if a i = some s then none else a i) = none :=
      hnone
    have hcount : i < E.length + 1 := by rw [hlen] at h; exact h
    by_cases hiE : i = E.length
    · rw [if_pos hiE] at hnone'
      simp at hnone'
    · have hi : i < E.length := by omega
      rw [getElem_strictTransform_append_exceptionalIdeal_of_lt π Z E i hi]
      rw [if_neg hiE] at hnone'
      by_cases hai : a i = some s
      · have hD := ha3 i hi s hai
        have hres := BlowupChart.restrictIdeal_strictTransform_coordIdeal B Z (E[i]'hi) hs hZU s hD
        simpa using hres
      · rw [if_neg hai] at hnone'
        exact BlowupChart.restrictIdeal_strictTransform_of_eq_top B Z (E[i]'hi) (ha2 i hi hnone')
  · intro i h t hti
    have hti' : (if i = E.length then some s else if a i = some s then none else a i) = some t :=
      hti
    have hcount : i < E.length + 1 := by rw [hlen] at h; exact h
    by_cases hiE : i = E.length
    · subst hiE
      rw [getElem_length_strictTransform_append_exceptionalIdeal π Z E]
      have hts : s = t := by simpa using hti'
      rw [← hts]
      exact BlowupChart.restrictIdeal_exceptionalIdeal B Z hs hZU
    · have hi : i < E.length := by omega
      rw [getElem_strictTransform_append_exceptionalIdeal_of_lt π Z E i hi]
      rw [if_neg hiE] at hti'
      by_cases hai : a i = some s
      · rw [if_pos hai] at hti'
        simp at hti'
      · rw [if_neg hai] at hti'
        have hD := ha3 i hi t hti'
        have hts : t ≠ s := by
          intro hh
          exact hai (by rw [hti', hh])
        rw [BlowupChart.restrictIdeal_strictTransform_coordIdeal B Z (E[i]'hi) hs hZU t hD,
          if_neg hts]

/- English proof (authored)
Take a downstairs boundary chart and shrink it to the complement of the center. The blowup restricts to an isomorphism, so transporting the chart upstairs gives an étale chart with the same boundary coordinate assignment. On this open strict transforms equal total transforms, which preserve the coordinate and unit ideals under the transported chart. The exceptional ideal is the unit ideal, so it is assigned no coordinate. The coordinate indices that remain are distinct.
-/
theorem inStrictNormalCrossingPositionAt_strictTransform_of_notMem_support {X X₁ : Scheme.{u}} {k : Type u}
    [Field k] [NoetherianSpace X₁] (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (E : List X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (hE : InStrictNormalCrossingPosition p E) (x₁ : X₁) (hx₁ : π.base x₁ ∉ Z.support) :
    InStrictNormalCrossingPositionAt (π ≫ p) (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]) x₁ := by
  classical
  have instQuasiCompact : ∀ D : X.IdealSheafData, QuasiCompact (strictTransformι π Z D) :=
    fun D => quasiCompact_strictTransformι_of_noetherianSpace π Z D
  rw [inStrictNormalCrossingPosition_iff] at hE
  obtain ⟨hEdiv, hEpos⟩ := hE
  have hpos := hEpos (π.base x₁)
  unfold InStrictNormalCrossingPositionAt at hpos
  obtain ⟨U, hxU, m, c, a, ha1, ha2, ha3⟩ := hpos
  have hWU : U ⊓ Z.support.compl ≤ U := inf_le_left
  have hiso : IsIso (π ∣_ (U ⊓ Z.support.compl)) :=
    isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hπ (U ⊓ Z.support.compl) (fun x hx => hx.2)
  have hxW : π.base x₁ ∈ U ⊓ Z.support.compl := ⟨hxU, hx₁⟩
  have hVle : (π ⁻¹ᵁ (U ⊓ Z.support.compl)) ≤ π ⁻¹ᵁ Z.support.compl := fun x hx => hx.2
  have hcs : ((π ∣_ (U ⊓ Z.support.compl)) ≫ (c.restrict hWU).map) ≫ affineSpaceFinToSpec k m
      = (π ⁻¹ᵁ (U ⊓ Z.support.compl)).ι ≫ (π ≫ p) := by
    rw [Category.assoc, (c.restrict hWU).comp_struct, ← Category.assoc, morphismRestrict_ι,
      Category.assoc]
  have het : Etale ((π ∣_ (U ⊓ Z.support.compl)) ≫ (c.restrict hWU).map) := by
    have : IsIso (π ∣_ (U ⊓ Z.support.compl)) := hiso
    have : Etale (c.restrict hWU).map := (c.restrict hWU).isEtale
    infer_instance
  have hlen : (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length = E.length + 1 :=
    length_strictTransform_append_exceptionalIdeal π Z E
  unfold InStrictNormalCrossingPositionAt
  refine ⟨π ⁻¹ᵁ (U ⊓ Z.support.compl), hxW, m,
    ⟨(π ∣_ (U ⊓ Z.support.compl)) ≫ (c.restrict hWU).map, hcs, het⟩,
    fun i => if i = E.length then none else a i, ?_, ?_, ?_⟩
  · intro i hi j hj t hti htj
    have hti' : (if i = E.length then none else a i) = some t := hti
    have htj' : (if j = E.length then none else a j) = some t := htj
    rw [hlen] at hi hj
    have hiE : i ≠ E.length := by
      intro hh
      rw [if_pos hh] at hti'
      simp at hti'
    have hjE : j ≠ E.length := by
      intro hh
      rw [if_pos hh] at htj'
      simp at htj'
    rw [if_neg hiE] at hti'
    rw [if_neg hjE] at htj'
    exact ha1 i (by omega) j (by omega) t hti' htj'
  · intro i h hnone
    have hcount : i < E.length + 1 := by rw [hlen] at h; exact h
    by_cases hiE : i = E.length
    · subst hiE
      rw [getElem_length_strictTransform_append_exceptionalIdeal π Z E]
      exact restrictIdeal_exceptionalIdeal_eq_top_of_le_compl π Z _ hVle
    · have hi : i < E.length := by omega
      have hnone' : (if i = E.length then none else a i) = none := hnone
      rw [if_neg hiE] at hnone'
      rw [getElem_strictTransform_append_exceptionalIdeal_of_lt π Z E i hi,
        restrictIdeal_strictTransform_eq_comap_of_le_compl π Z (E[i]'hi) _ hVle,
        restrictIdeal_comap_preimage π (E[i]'hi) (U ⊓ Z.support.compl),
        restrictIdeal_eq_top_of_le (E[i]'hi) hWU (ha2 i hi hnone')]
      exact Scheme.IdealSheafData.comap_top _
  · intro i h t hti
    have hti' : (if i = E.length then none else a i) = some t := hti
    have hcount : i < E.length + 1 := by rw [hlen] at h; exact h
    have hiE : i ≠ E.length := by
      intro hh
      rw [if_pos hh] at hti'
      simp at hti'
    have hi : i < E.length := by omega
    rw [if_neg hiE] at hti'
    rw [getElem_strictTransform_append_exceptionalIdeal_of_lt π Z E i hi,
      restrictIdeal_strictTransform_eq_comap_of_le_compl π Z (E[i]'hi) _ hVle,
      restrictIdeal_comap_preimage π (E[i]'hi) (U ⊓ Z.support.compl),
      restrictIdeal_eq_restrict_coordIdeal_of_le hWU c (E[i]'hi) {t} (ha3 i hi t hti')]
    simp only [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
    exact (Scheme.IdealSheafData.comap_comp ..).symm

/- English proof (authored)
At every point choose the strict-transform boundary chart for points over the center or the transported chart for points off the center. This proves the pointwise normal crossings condition. The same charts show each member is a smooth divisor, since its ideal is everywhere locally a coordinate ideal or the unit ideal. Thus the full list is in strict normal crossings position.
-/
theorem inStrictNormalCrossingPosition_strictTransform_append {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    [NoetherianSpace X₁] (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X) (Z : X.IdealSheafData)
    (E : List X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hE : InStrictNormalCrossingPosition p E)
    (hZE : HasStrictNormalCrossingsWith p Z E) :
    InStrictNormalCrossingPosition (π ≫ p) (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]) := by
  classical
  have hat : ∀ x₁ : X₁,
      InStrictNormalCrossingPositionAt (π ≫ p) (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]) x₁ := by
    intro x₁
    by_cases hx : π.base x₁ ∈ Z.support
    · exact inStrictNormalCrossingPositionAt_strictTransform_of_mem_support p π Z E hπ hZE x₁ hx
    · exact inStrictNormalCrossingPositionAt_strictTransform_of_notMem_support p π Z E hπ hE x₁ hx
  rw [inStrictNormalCrossingPosition_iff]
  refine ⟨?_, hat⟩
  intro D hD
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hD
  refine isSmoothDivisor_of_locally_coordIdeal _ fun x₁ => ?_
  have hx := hat x₁
  unfold InStrictNormalCrossingPositionAt at hx
  obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := hx
  refine ⟨U, hxU, m, c, ?_⟩
  cases hai : a i with
  | none => exact Or.inl (h2 i hi hai)
  | some t => exact Or.inr ⟨t, h3 i hi t hai⟩

/- English proof (authored)
Apply the strict-transform and exceptional-divisor result to the list with the specified first member. Taking strict transforms entry by entry gives the strict transform of that member as the first entry, followed by the transformed tail and the exceptional ideal.
-/
theorem inStrictNormalCrossingPosition_strictTransform_cons_append {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    [NoetherianSpace X₁] (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X) (Z : X.IdealSheafData)
    (H : X.IdealSheafData) (E : List X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (hE : InStrictNormalCrossingPosition p (H :: E)) (hZE : HasStrictNormalCrossingsWith p Z (H :: E)) :
    InStrictNormalCrossingPosition (π ≫ p)
      (Blowup.strictTransform π Z H :: (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z])) :=
  inStrictNormalCrossingPosition_strictTransform_append p π Z (H :: E) hπ hE hZE

end FunctorialResolution.EmbeddedResolution

end
