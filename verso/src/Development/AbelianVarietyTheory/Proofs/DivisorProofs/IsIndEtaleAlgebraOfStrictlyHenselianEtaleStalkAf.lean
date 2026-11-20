import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

/- English proof (translation)
Take `⟨J, _, _, D, s, t, hs, hj⟩` from `hg`. Use `⟨J, inferInstance, inferInstance, D, (Functor.const J).map (CommRingCat.ofHom φ) ≫ s, t, hs, fun j => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `show RingHom.Etale ((s.app j).hom.comp φ)`. Conclude with `RingHom.Etale.stableUnderComposition _ _ hφ (hj j).1`. Establish `h2` using `(hj j).2 show CommRingCat.ofHom φ ≫ s.app j ≫ t.app j = CommRingCat.ofHom (g.comp φ)`.

Rewrite using `[h2]`. Both sides reduce to the same expression.
-/
theorem isIndEtale_comp_etale {A B O : Type} [CommRing A] [CommRing B] [CommRing O] (φ : A →+* B)
    (hφ : φ.Etale) (g : B →+* O) (hg : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale g) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp φ) := by
  obtain ⟨J, _, _, D, s, t, hs, hj⟩ := hg
  refine ⟨J, inferInstance, inferInstance, D, (Functor.const J).map (CommRingCat.ofHom φ) ≫ s, t, hs,
    fun j => ⟨?_, ?_⟩⟩
  · show RingHom.Etale ((s.app j).hom.comp φ)
    exact RingHom.Etale.stableUnderComposition _ _ hφ (hj j).1
  · have h2 := (hj j).2
    show CommRingCat.ofHom φ ≫ s.app j ≫ t.app j = CommRingCat.ofHom (g.comp φ)
    rw [h2]
    rfl

/- English proof (translation)
Introduce `A _ O _ s hs`. Take `⟨hSH, A', _, _, j, hj, hind, rfl⟩` from `hs`. Use `set φ := Spec.preimage j with hφdef`. Establish `hjφ : Spec.map φ = j` using `Spec.map_preimage j`. Establish `hφ : φ.hom.Etale`.

Rewrite `hj` using `[← hjφ]`. Conclude with `(HasRingHomProperty.Spec_iff (P := @Etale)).mp hj`. Use `letI : Algebra A O := ((algebraMap A' O).comp φ.hom).toAlgebra`. Use `⟨this, hSH, ?_, ?_⟩` and prove the remaining obligations. Conclude with `isIndEtale_comp_etale φ.hom hφ (algebraMap A' O) hind`.

Rewrite using `[← hjφ, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem isStalk_affine : ∀ (A : Type) [CommRing A] (O : Type) [CommRing O]
    (s : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of A)), IsStalk O s →
    ∃ _ : Algebra A O, SH O ∧ IndEt A O ∧ s = Spec.map (CommRingCat.ofHom (algebraMap A O)) := by
  intro A _ O _ s hs
  obtain ⟨hSH, A', _, _, j, hj, hind, rfl⟩ := hs
  set φ := Spec.preimage j with hφdef
  have hjφ : Spec.map φ = j := Spec.map_preimage j
  have hφ : φ.hom.Etale := by
    rw [← hjφ] at hj
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp hj
  letI : Algebra A O := ((algebraMap A' O).comp φ.hom).toAlgebra
  refine ⟨this, hSH, ?_, ?_⟩
  · exact isIndEtale_comp_etale φ.hom hφ (algebraMap A' O) hind
  · rw [← hjφ, ← Spec.map_comp]
    rfl

end GlobalTheory.EtC
