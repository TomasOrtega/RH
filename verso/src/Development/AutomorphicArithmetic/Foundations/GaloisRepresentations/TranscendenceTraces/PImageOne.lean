import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `Z P S k b _ _ _`. Establish `hk : IsFinite k` using `IsFinite.of_comp k b`. Establish `ht : IsFinite k.toImage`. Establish `: IsFinite (k.toImage ≫ k.imageι)` using `by rw [k.toImage_imageι]; exact hk`. Conclude with `IsFinite.of_comp k.toImage k.imageι`.

Establish `hs : Surjective k.toImage` using `surjective_of_isDominant_of_isClosed_range k.toImage k.toImage.isClosedMap.isClosed_range`. Establish `e : k.toImage ≫ (k.imageι ≫ b) = k ≫ b` using `k.toImage_imageι_assoc b`. Establish `huc : UniversallyClosed (k.imageι ≫ b)`. Establish `: UniversallyClosed (k.toImage ≫ (k.imageι ≫ b))` using `by rw [e]; infer_instance`. Conclude with `UniversallyClosed.of_comp_surjective k.toImage _`.

Establish `hqf : LocallyQuasiFinite (k.imageι ≫ b)`. Use `.of_finite_preimage_singleton _ fun s => ?_` and prove the remaining obligations. Use `(((k ≫ b).finite_preimage_singleton s).image k.toImage).subset ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨x, rfl⟩` from `k.toImage.surjective y`.

Use `⟨x, ?_, rfl⟩` and prove the remaining obligations. Establish `: (k ≫ b) x = (k.imageι ≫ b) (k.toImage x)`. Rewrite using `[← e, Scheme.Hom.comp_apply]`. Conclude with `this.trans hy`. Establish `: IsProper (k.imageι ≫ b)` using `⟨⟩`.

Conclude with `⟨IsFinite.of_isProper_of_locallyQuasiFinite _, ht⟩`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.imageOne_of :
    ImageOne := by
  intro Z P S k b _ _ _
  have hk : IsFinite k := IsFinite.of_comp k b
  have ht : IsFinite k.toImage := by
    have : IsFinite (k.toImage ≫ k.imageι) := by rw [k.toImage_imageι]; exact hk
    exact IsFinite.of_comp k.toImage k.imageι
  have hs : Surjective k.toImage :=
     surjective_of_isDominant_of_isClosed_range k.toImage k.toImage.isClosedMap.isClosed_range
  have e : k.toImage ≫ (k.imageι ≫ b) = k ≫ b := k.toImage_imageι_assoc b
  have huc : UniversallyClosed (k.imageι ≫ b) := by
    have : UniversallyClosed (k.toImage ≫ (k.imageι ≫ b)) := by rw [e]; infer_instance
    exact UniversallyClosed.of_comp_surjective k.toImage _
  have hqf : LocallyQuasiFinite (k.imageι ≫ b) := by
    refine .of_finite_preimage_singleton _ fun s => ?_
    refine (((k ≫ b).finite_preimage_singleton s).image k.toImage).subset ?_
    intro y hy
    obtain ⟨x, rfl⟩ := k.toImage.surjective y
    refine ⟨x, ?_, rfl⟩
    have : (k ≫ b) x = (k.imageι ≫ b) (k.toImage x) := by
      rw [← e, Scheme.Hom.comp_apply]
    exact this.trans hy
  have : IsProper (k.imageι ≫ b) := ⟨⟩
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, ht⟩
