import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `Z S p _ A _ u`. Use `haveI : IsAffine (pullback p u) := isAffine_of_isAffineHom (pullback.snd p u)`. Set `V` to `pullback p u`. Set `e : Spec Γ(V, ⊤) ≅ V` to `V.isoSpec.symm`. Set `φ : CommRingCat.of A ⟶ Γ(V, ⊤)` to `Spec.preimage (e.hom ≫ pullback.snd p u)`.

Establish `hφ : Spec.map φ = e.hom ≫ pullback.snd p u` using `Spec.map_preimage _`. Use `letI alg : Algebra A Γ(V, ⊤) := φ.hom.toAlgebra`. Establish `hφ' : Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤))) = e.hom ≫ pullback.snd p u` using `hφ`. Use `⟨Γ(V, ⊤), inferInstance, alg, e.hom ≫ pullback.fst p u, ?_, ?_⟩` and prove the remaining obligations. Establish `hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤))))`.

Rewrite using `[hφ']`. Use `infer_instance`. Establish `h2` using `(IsFinite.SpecMap_iff _).1 hfin`. Conclude with `RingHom.finite_algebraMap.1 h2`. Rewrite using `[hφ']`.

Conclude with `IsPullback.of_iso (IsPullback.of_hasPullback p u) e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.chart_of :
    Chart := by
  intro Z S p _ A _ u
  haveI : IsAffine (pullback p u) := isAffine_of_isAffineHom (pullback.snd p u)
  let V := pullback p u
  let e : Spec Γ(V, ⊤) ≅ V := V.isoSpec.symm
  let φ : CommRingCat.of A ⟶ Γ(V, ⊤) := Spec.preimage (e.hom ≫ pullback.snd p u)
  have hφ : Spec.map φ = e.hom ≫ pullback.snd p u := Spec.map_preimage _
  letI alg : Algebra A Γ(V, ⊤) := φ.hom.toAlgebra
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤))) = e.hom ≫ pullback.snd p u := hφ
  refine ⟨Γ(V, ⊤), inferInstance, alg, e.hom ≫ pullback.fst p u, ?_, ?_⟩
  · have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤)))) := by
      rw [hφ']; infer_instance
    have h2 := (IsFinite.SpecMap_iff _).1 hfin
    exact RingHom.finite_algebraMap.1 h2
  · rw [hφ']
    exact IsPullback.of_iso (IsPullback.of_hasPullback p u) e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
