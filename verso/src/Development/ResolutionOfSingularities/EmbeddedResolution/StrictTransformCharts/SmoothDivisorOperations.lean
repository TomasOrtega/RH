import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothDivisorEtaleChart
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
Restriction is pullback along the open inclusion. Pullback extends the section ideals and preserves their product, giving the restriction formula.
-/
theorem restrictIdeal_mul {X : Scheme.{u}} (I J : X.IdealSheafData) (U : X.Opens) :
    restrictIdeal (I * J) U = restrictIdeal I U * restrictIdeal J U :=
  Scheme.IdealSheafData.comap_mul I J U.ι

/- English proof (authored)
The original chart commutes with the structural map to the field. Composing its field equation with the restricted morphism gives the composite through the downstairs open inclusion. The restriction square identifies that composite with the upstairs inclusion followed by the original morphism, giving the required equation.
-/
private theorem etaleChart_comap_map_comp_affineSpaceFinToSpec {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (π : X' ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (V : X'.Opens) (hV : V ≤ π ⁻¹ᵁ U) :
    (π.resLE U V hV ≫ c.map) ≫ affineSpaceFinToSpec k m = V.ι ≫ (π ≫ p) := by
  have h1 : π.resLE U V hV ≫ U.ι = V.ι ≫ π := by simp
  rw [Category.assoc, c.comp_struct, ← Category.assoc, h1, Category.assoc]

/- English proof (authored)
The restricted morphism and the original chart map are both étale by hypothesis. Étale morphisms are closed under composition.
-/
private theorem etale_etaleChart_comap_map {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (π : X' ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (V : X'.Opens) (hV : V ≤ π ⁻¹ᵁ U)
    (he : AlgebraicGeometry.Etale (π.resLE U V hV)) :
    AlgebraicGeometry.Etale (π.resLE U V hV ≫ c.map) := by
  have := he
  have := c.isEtale
  infer_instance

def EtaleChart.comap {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (π : X' ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (V : X'.Opens) (hV : V ≤ π ⁻¹ᵁ U)
    (he : AlgebraicGeometry.Etale (π.resLE U V hV)) : EtaleChart (π ≫ p) V m where
  map := π.resLE U V hV ≫ c.map
  comp_struct := etaleChart_comap_map_comp_affineSpaceFinToSpec p π c V hV
  isEtale := etale_etaleChart_comap_map p π c V hV he

/- English proof (authored)
The pulled-back chart is defined with map given by the restricted morphism followed by the original chart map. Its map is therefore that composite.
-/
theorem EtaleChart.comap_map {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (π : X' ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (V : X'.Opens) (hV : V ≤ π ⁻¹ᵁ U)
    (he : AlgebraicGeometry.Etale (π.resLE U V hV)) :
    (EtaleChart.comap p π c V hV he).map = π.resLE U V hV ≫ c.map := rfl

/- English proof (authored)
The coordinate ideal on a chart is the pullback of the corresponding coordinate ideal on affine space. For the pulled-back chart its map is a composite. Functoriality makes this pullback the pullback to the original chart followed by pullback along the restricted morphism.
-/
theorem EtaleChart.comap_coordIdeal {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (π : X' ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (V : X'.Opens) (hV : V ≤ π ⁻¹ᵁ U)
    (he : AlgebraicGeometry.Etale (π.resLE U V hV)) (S : Finset (Fin m)) :
    (EtaleChart.comap p π c V hV he).coordIdeal S =
      (c.coordIdeal S).comap (π.resLE U V hV) := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.comap_map,
    Scheme.IdealSheafData.comap_comp]

/- English proof (authored)
At a point of either divisor, choose an étale chart making that divisor a coordinate divisor. Shrink to avoid the support of the other divisor, which is possible by disjointness. The ideal of the other divisor is the unit ideal there, so the product is the same coordinate ideal. At a point outside both supports choose a chart in their common complement, where both ideals are unit ideals. These local descriptions give the smooth divisor property.
-/
theorem isSmoothDivisor_mul_of_disjoint_support {X : Scheme.{u}} {k : Type u} [Field k]
    [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (A B : X.IdealSheafData) (hA : IsSmoothDivisor p A) (hB : IsSmoothDivisor p B)
    (hAB : Disjoint (A.support : Set X) (B.support : Set X)) :
    IsSmoothDivisor p (A * B) := by
  refine isSmoothDivisor_of_locally_coordIdeal (p := p) (A * B) ?_
  intro x
  by_cases hxA : x ∈ A.support
  · have hxB : x ∉ B.support := fun h => Set.disjoint_left.mp hAB hxA h
    obtain ⟨U, m, c, j, hxU, hAU⟩ :=
      exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton p A hA x hxA
    refine ⟨U ⊓ B.support.compl, ⟨hxU, hxB⟩, m, c.restrict inf_le_left, Or.inr ⟨j, ?_⟩⟩
    have hBtop : restrictIdeal B (U ⊓ B.support.compl) = ⊤ := by
      refine (restrictIdeal_eq_top_iff_forall_notMem_support ..).mpr ?_
      intro y hy
      exact hy.2
    have hc := restrictIdeal_eq_restrict_coordIdeal_of_le (U := U) (V := U ⊓ B.support.compl)
      inf_le_left c A {j} hAU
    rw [restrictIdeal_mul, hBtop, Scheme.IdealSheafData.mul_top, hc]
  · by_cases hxB : x ∈ B.support
    · obtain ⟨U, m, c, j, hxU, hBU⟩ :=
        exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton p B hB x hxB
      refine ⟨U ⊓ A.support.compl, ⟨hxU, hxA⟩, m, c.restrict inf_le_left, Or.inr ⟨j, ?_⟩⟩
      have hAtop : restrictIdeal A (U ⊓ A.support.compl) = ⊤ := by
        refine (restrictIdeal_eq_top_iff_forall_notMem_support ..).mpr ?_
        intro y hy
        exact hy.2
      have hc := restrictIdeal_eq_restrict_coordIdeal_of_le (U := U) (V := U ⊓ A.support.compl)
        inf_le_left c B {j} hBU
      rw [restrictIdeal_mul, hAtop, Scheme.IdealSheafData.top_mul, hc]
    · obtain ⟨U, m, hxU, hUW, -, ⟨c⟩⟩ :=
        exists_etaleChart_le p x (A.support.compl ⊓ B.support.compl) ⟨hxA, hxB⟩
      refine ⟨U, hxU, m, c, Or.inl ?_⟩
      have hAtopW : restrictIdeal A (A.support.compl ⊓ B.support.compl) = ⊤ := by
        refine (restrictIdeal_eq_top_iff_forall_notMem_support ..).mpr ?_
        intro y hy
        exact hy.1
      have hBtopW : restrictIdeal B (A.support.compl ⊓ B.support.compl) = ⊤ := by
        refine (restrictIdeal_eq_top_iff_forall_notMem_support ..).mpr ?_
        intro y hy
        exact hy.2
      have hAtop : restrictIdeal A U = ⊤ := restrictIdeal_eq_top_of_le A hUW hAtopW
      have hBtop : restrictIdeal B U = ⊤ := restrictIdeal_eq_top_of_le B hUW hBtopW
      rw [restrictIdeal_mul, hAtop, hBtop, Scheme.IdealSheafData.mul_top]

/- English proof (authored)
Pulling back along the indicated morphism and restricting to the open is the same as pulling back along the composite from the open subscheme. The composite avoids the support by hypothesis. Thus the pulled-back ideal is the unit ideal on that open.
-/
private theorem restrictIdeal_comap_eq_top_of_notMem_support {X X' : Scheme.{u}} (π : X' ⟶ X)
    (B : X.IdealSheafData) (V : X'.Opens) (hV : ∀ y : X', y ∈ V → π.base y ∉ B.support) :
    restrictIdeal (B.comap π) V = ⊤ := by
  have hcc : B.comap (V.ι ≫ π) = (B.comap π).comap V.ι := by
    rw [Scheme.IdealSheafData.comap_comp]
  have htop : B.comap (V.ι ≫ π) = ⊤ := by
    refine Blowup.comap_eq_top_of_notMem_support (V.ι ≫ π) B ?_
    intro y
    have hy : V.ι.base y ∈ Set.range V.ι.base := Set.mem_range_self y
    rw [Scheme.Opens.range_ι] at hy
    have h2 : π.base (V.ι.base y) ∉ B.support := hV _ hy
    simpa using h2
  rw [restrictIdeal_eq_comap_ι, ← hcc]
  exact htop

/- English proof (authored)
At a point whose image belongs to the divisor support, take a downstairs coordinate chart for the divisor and shrink it into the complement of the center. The blowup is an isomorphism there, and composing with this isomorphism gives an étale chart upstairs. Its coordinate ideal is the pullback of the original divisor ideal. At any other point choose an upstairs étale chart in the inverse image of the complement of the divisor support, where the pullback is the unit ideal. Thus the pulled-back ideal satisfies the local coordinate criterion for a smooth divisor.
-/
theorem isSmoothDivisor_comap_of_isBlowupAlongIdealSheaf {X X' : Scheme.{u}} {k : Type u} [Field k]
    [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X' ⟶ X) [AlgebraicGeometry.Smooth (π ≫ p)] (Z B : X.IdealSheafData)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hB : IsSmoothDivisor p B)
    (hdisj : Disjoint (Z.support : Set X) (B.support : Set X)) :
    IsSmoothDivisor (π ≫ p) (B.comap π) := by
  refine isSmoothDivisor_of_locally_coordIdeal (B.comap π) ?_
  intro x'
  by_cases hx : π.base x' ∈ B.support
  · obtain ⟨U, m, c, j, hxU, hBU⟩ :=
      exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton p B hB (π.base x') hx
    have hxZ : π.base x' ∉ Z.support := fun hZ => (Set.disjoint_left.mp hdisj hZ) hx
    have hWle : (U ⊓ Z.support.compl : X.Opens) ≤ U := inf_le_left
    have hWsup : ∀ y : X, y ∈ (U ⊓ Z.support.compl : X.Opens) → y ∉ Z.support :=
      fun y hy => hy.2
    have hiso : IsIso (π ∣_ (U ⊓ Z.support.compl : X.Opens)) :=
      isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hπ (U ⊓ Z.support.compl : X.Opens) hWsup
    have hiso2 : IsIso (π.resLE (U ⊓ Z.support.compl : X.Opens)
        (π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens)) le_rfl) := by
      rw [Scheme.Hom.resLE_eq_morphismRestrict]
      exact hiso
    have he : AlgebraicGeometry.Etale (π.resLE (U ⊓ Z.support.compl : X.Opens)
        (π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens)) le_rfl) := inferInstance
    have hxV : x' ∈ (π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens)) := ⟨hxU, hxZ⟩
    refine ⟨π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens), hxV, m,
      EtaleChart.comap p π (c.restrict hWle)
        (π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens)) le_rfl he, Or.inr ⟨j, ?_⟩⟩
    rw [EtaleChart.comap_coordIdeal,
      restrictIdeal_comap_eq_comap_resLE_restrictIdeal π B (U ⊓ Z.support.compl : X.Opens)
        (π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens)) le_rfl,
      restrictIdeal_eq_restrict_coordIdeal_of_le hWle c B {j} hBU]
  · obtain ⟨U, m, hxU, hUW, -, ⟨c⟩⟩ :=
      exists_etaleChart_le (π ≫ p) x' (π ⁻¹ᵁ B.support.compl) hx
    refine ⟨U, hxU, m, c, Or.inl ?_⟩
    refine restrictIdeal_comap_eq_top_of_notMem_support π B U ?_
    intro y hy
    have hy' : y ∈ π ⁻¹ᵁ B.support.compl := hUW hy
    exact hy'

/- English proof (authored)
At a point over the center, the image is outside the second support. On the inverse image of that complement the pullback of the second ideal is the unit ideal, so the total transform of the product equals that of the first ideal. The strict transforms therefore agree there, since both saturate the same total transform by the same exceptional ideal. Away from the center strict transforms agree with the total transforms, and ideal pullback preserves products. These two kinds of opens cover the scheme, giving the equality.
-/
theorem strictTransform_mul_of_disjoint_support {X X' : Scheme.{u}} [IsLocallyNoetherian X']
    (π : X' ⟶ X) (Z A B : X.IdealSheafData)
    (hBZ : Disjoint (B.support : Set X) (Z.support : Set X)) :
    Blowup.strictTransform π Z (A * B) = Blowup.strictTransform π Z A * B.comap π := by
  have hqAB : QuasiCompact (strictTransformι π Z (A * B)) :=
    FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π Z (A * B)
  have hqA : QuasiCompact (strictTransformι π Z A) :=
    FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π Z A
  refine eq_of_locally_restrictIdeal_eq _ _ ?_
  intro x
  by_cases hx : π.base x ∈ Z.support
  · have hxB : π.base x ∉ B.support := fun hB => (Set.disjoint_left.mp hBZ hB) hx
    refine ⟨π ⁻¹ᵁ B.support.compl, ?_, ?_⟩
    · exact hxB
    · have hVmem : ∀ y : X', y ∈ π ⁻¹ᵁ B.support.compl → π.base y ∉ B.support := by
        intro y hy
        exact hy
      have hBtop : restrictIdeal (B.comap π) (π ⁻¹ᵁ B.support.compl) = ⊤ :=
        restrictIdeal_comap_eq_top_of_notMem_support π B _ hVmem
      have hcomapB : B.comap ((π ⁻¹ᵁ B.support.compl).ι ≫ π) = ⊤ := by
        rw [Scheme.IdealSheafData.comap_comp]
        exact hBtop
      have hD : (A * B).comap ((π ⁻¹ᵁ B.support.compl).ι ≫ π)
          = A.comap ((π ⁻¹ᵁ B.support.compl).ι ≫ π) := by
        rw [Scheme.IdealSheafData.comap_mul, hcomapB, Scheme.IdealSheafData.mul_top]
      rw [restrictIdeal_mul, hBtop, Scheme.IdealSheafData.mul_top,
        restrictIdeal_strictTransform π Z (A * B) (π ⁻¹ᵁ B.support.compl),
        restrictIdeal_strictTransform π Z A (π ⁻¹ᵁ B.support.compl)]
      exact strictTransform_eq_of_comap_eq _ _ Z (A * B) Z A rfl hD
  · refine ⟨π ⁻¹ᵁ Z.support.compl, ?_, ?_⟩
    · exact hx
    · have hVmem : ∀ y : X', y ∈ π ⁻¹ᵁ Z.support.compl → π.base y ∉ Z.support := by
        intro y hy
        exact hy
      rw [restrictIdeal_strictTransform_eq_comap_of_notMem_support π Z (A * B) _ hVmem,
        Scheme.IdealSheafData.comap_mul, restrictIdeal_mul, restrictIdeal_mul,
        restrictIdeal_strictTransform_eq_comap_of_notMem_support π Z A _ hVmem]

end FunctorialResolution.EmbeddedResolution

end
