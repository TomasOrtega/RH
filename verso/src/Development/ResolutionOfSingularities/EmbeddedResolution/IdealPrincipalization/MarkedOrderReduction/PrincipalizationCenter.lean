import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.InvarianceUnderIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedSchemeWithCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MarkedSchemeWithCenter

variable {k : Type u} [Field k]

def boundarySupport (D : MarkedSchemeWithCenter.{u} k) : Set ↥D.ambient :=
  {x : ↥D.ambient | ∃ J ∈ D.boundary, x ∈ (↑J.support : Set ↥D.ambient)}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_boundarySupport_iff (D : MarkedSchemeWithCenter.{u} k) (x : ↥D.ambient) :
    x ∈ D.boundarySupport ↔ ∃ J ∈ D.boundary, x ∈ (↑J.support : Set ↥D.ambient) :=
  Iff.rfl

end MarkedSchemeWithCenter

/- English proof (translation)
Simplify using `only [Scheme.IdealSheafData.support_comap]`. Conclude with `Iff.rfl`.
-/
theorem mem_comap_support_iff_base_mem_support {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) (x : ↥X) :
    x ∈ (J.comap f).support ↔ f.base x ∈ J.support := by
  simp only [Scheme.IdealSheafData.support_comap]
  exact Iff.rfl

namespace MarkedSchemeWithCenter

variable {k : Type u} [Field k]

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨J, hJ, hx⟩`. Take `⟨K, hK, rfl⟩` from `List.mem_map.1 hJ`. Conclude with `⟨K, hK, (mem_comap_support_iff_base_mem_support e.hom K x).1 hx⟩`.

Introduce and unpack `⟨K, hK, hx⟩`. Conclude with `⟨K.comap e.hom, List.mem_map.2 ⟨K, hK, rfl⟩, (mem_comap_support_iff_base_mem_support e.hom K x).2 hx⟩`.
-/
theorem boundarySupport_transport (D : MarkedSchemeWithCenter.{u} k) {A : Scheme.{u}} (e : A ≅ D.ambient) :
    (D.transport e).boundarySupport = e.hom.base ⁻¹' D.boundarySupport := by
  ext x
  constructor
  · rintro ⟨J, hJ, hx⟩
    obtain ⟨K, hK, rfl⟩ := List.mem_map.1 hJ
    exact ⟨K, hK, (mem_comap_support_iff_base_mem_support e.hom K x).1 hx⟩
  · rintro ⟨K, hK, hx⟩
    exact ⟨K.comap e.hom, List.mem_map.2 ⟨K, hK, rfl⟩,
      (mem_comap_support_iff_base_mem_support e.hom K x).2 hx⟩

end MarkedSchemeWithCenter

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

/- English proof (translation)
Use extensionality with `x`. Use `Iff.trans (MarkedSchemeWithCenter.mem_boundarySupport_iff (s.dataAt i) x) ?_` and prove the remaining obligations. Conclude with `(MarkedSequenceOfBlowups.mem_boundaryLocus_iff s.toMarkedSequenceOfBlowups i x).symm`.
-/
theorem boundarySupport_dataAt (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    (s.dataAt i).boundarySupport = s.toMarkedSequenceOfBlowups.boundaryLocus i := by
  ext x
  refine Iff.trans (MarkedSchemeWithCenter.mem_boundarySupport_iff (s.dataAt i) x) ?_
  exact (MarkedSequenceOfBlowups.mem_boundaryLocus_iff s.toMarkedSequenceOfBlowups i x).symm

end MarkedBlowupSequenceData

structure HasPrincipalizationCenter {k : Type u} [Field k] (μ : ℕ) (D : MarkedSchemeWithCenter.{u} k) : Prop where
  center_nonempty : (↑D.center.support : Set ↥D.ambient).Nonempty
  cert : PrincipalizationCertificate D.ambient D.structMap D.ideal μ D.boundarySupport D.center

/- English proof (translation)
Introduce `D A e hD`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hD.center_nonempty`. Use `⟨e.inv.base x, ?_⟩` and prove the remaining obligations. Establish `key : e.hom.base (e.inv.base x) = x`.

Simplify using the standard rewrite rules. Establish `hmem : e.hom.base (e.inv.base x) ∈ D.center.support`. Rewrite using `[key]`. Conclude with `hx`. Conclude with `(mem_comap_support_iff_base_mem_support e.hom D.center (e.inv.base x)).2 hmem`.

Establish `hcert` using `PrincipalizationCertificate.comap_iso hT e hD.cert`. Rewrite using `[MarkedSchemeWithCenter.boundarySupport_transport]`. Conclude with `hcert`.
-/
theorem isInvariantUnderIso_hasPrincipalizationCenter {k : Type u} [Field k] (hT : OrderCertificateIsoInvariantOfMaxContact.{u}) (μ : ℕ) :
    IsInvariantUnderIso (fun D : MarkedSchemeWithCenter.{u} k => HasPrincipalizationCenter μ D) := by
  intro D A e hD
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hD.center_nonempty
    refine ⟨e.inv.base x, ?_⟩
    have key : e.hom.base (e.inv.base x) = x := by
      simp
    have hmem : e.hom.base (e.inv.base x) ∈ D.center.support := by
      rw [key]; exact hx
    exact (mem_comap_support_iff_base_mem_support e.hom D.center (e.inv.base x)).2 hmem
  · have hcert := PrincipalizationCertificate.comap_iso hT e hD.cert
    rw [MarkedSchemeWithCenter.boundarySupport_transport]
    exact hcert

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `i hi`. Establish `hi' : i < s.toBlowupSequenceData.length`. Rewrite using `[← s.toMarkedSequence_length]`. Conclude with `hi`.

Conclude with `(hs i hi').center_nonempty`. Introduce `i hi`. Establish `hi' : i < s.toBlowupSequenceData.length`. Rewrite using `[← s.toMarkedSequence_length]`. Conclude with `hi`.

Establish `h` using `(hs i hi').cert`. Rewrite `h` using `[s.boundarySupport_dataAt i]`. Rewrite using `[toMarkedSequence_projectionToSpec]`. Conclude with `h`.
-/
theorem nonempty_center_and_certificate_of_hasPrincipalizationCenter (s : MarkedBlowupSequenceData p I m E) (μ : ℕ)
    (hs : ∀ i < s.toBlowupSequenceData.length, HasPrincipalizationCenter μ (s.dataAt i)) :
    (∀ i < s.toMarkedSequenceOfBlowups.length,
        (↑(s.toMarkedSequenceOfBlowups.center i).support : Set ↥(s.toMarkedSequenceOfBlowups.schemeAt i)).Nonempty) ∧
      (∀ i < s.toMarkedSequenceOfBlowups.length,
        PrincipalizationCertificate (s.toMarkedSequenceOfBlowups.schemeAt i) (s.toMarkedSequenceOfBlowups.projectionToSpec i) (s.toMarkedSequenceOfBlowups.ideal i) μ
          (s.toMarkedSequenceOfBlowups.boundaryLocus i) (s.toMarkedSequenceOfBlowups.center i)) := by
  constructor
  · intro i hi
    have hi' : i < s.toBlowupSequenceData.length := by
      rw [← s.toMarkedSequence_length]; exact hi
    exact (hs i hi').center_nonempty
  · intro i hi
    have hi' : i < s.toBlowupSequenceData.length := by
      rw [← s.toMarkedSequence_length]; exact hi
    have h := (hs i hi').cert
    rw [s.boundarySupport_dataAt i] at h
    rw [toMarkedSequence_projectionToSpec]
    exact h

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution

end
