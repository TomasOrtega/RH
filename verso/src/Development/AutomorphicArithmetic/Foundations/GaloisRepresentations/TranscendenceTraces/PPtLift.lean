import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Establish `h : (pt (Spec.map s) : Spec B) = PrimeSpectrum.comap s.hom (IsLocalRing.closedPoint Ω)` using `rfl`. Express the relevant statement in the definitionally equal form `(pt (Spec.map s) : Spec B).asIdeal = _`. Rewrite using `[h, RingHom.ker_eq_comap_bot]`. Express the relevant statement in the definitionally equal form `Ideal.comap s.hom (IsLocalRing.maximalIdeal Ω) = _`. Rewrite using `[IsLocalRing.maximalIdeal_eq_bot]`.
-/
private theorem pt_map_ideal {Ω : Type} [Field Ω] {B : CommRingCat.{0}} (s : B ⟶ CommRingCat.of Ω) :
    (show PrimeSpectrum B from pt (Spec.map s)).asIdeal = RingHom.ker s.hom := by
  have h : (pt (Spec.map s) : Spec B) = PrimeSpectrum.comap s.hom (IsLocalRing.closedPoint Ω) := rfl
  change (pt (Spec.map s) : Spec B).asIdeal = _
  rw [h, RingHom.ker_eq_comap_bot]
  change Ideal.comap s.hom (IsLocalRing.maximalIdeal Ω) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]

/- English proof (translation)
Use `letI : Algebra Ω B := φ.hom.toAlgebra`. Use `haveI : Algebra.IsIntegral Ω B := ⟨hφ⟩`. Establish `hb : Function.Bijective (algebraMap Ω (B ⧸ q))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Set `e : Ω ≃+* B ⧸ q` to `RingEquiv.ofBijective (algebraMap Ω (B ⧸ q)) hb`. Use `⟨CommRingCat.ofHom (e.symm.toRingHom.comp (Ideal.Quotient.mk q)), ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `a`. Express the relevant statement in the definitionally equal form `e.symm (Ideal.Quotient.mk q (φ.hom a)) = a`. Conclude with `e.symm_apply_apply a`. Use extensionality with `b`. Express the relevant statement in the definitionally equal form `e.symm (Ideal.Quotient.mk q b) = 0 ↔ b ∈ q`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Simplify using the standard rewrite rules.
-/
private theorem exists_retract {Ω : Type} [Field Ω] [IsAlgClosed Ω] {B : CommRingCat.{0}} (φ : CommRingCat.of Ω ⟶ B)
    (hφ : φ.hom.IsIntegral) (q : Ideal B) [q.IsPrime] :
    ∃ s : B ⟶ CommRingCat.of Ω, φ ≫ s = 𝟙 _ ∧ RingHom.ker s.hom = q := by
  letI : Algebra Ω B := φ.hom.toAlgebra
  haveI : Algebra.IsIntegral Ω B := ⟨hφ⟩
  have hb : Function.Bijective (algebraMap Ω (B ⧸ q)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : Ω ≃+* B ⧸ q := RingEquiv.ofBijective (algebraMap Ω (B ⧸ q)) hb
  refine ⟨CommRingCat.ofHom (e.symm.toRingHom.comp (Ideal.Quotient.mk q)), ?_, ?_⟩
  · ext a
    change e.symm (Ideal.Quotient.mk q (φ.hom a)) = a
    exact e.symm_apply_apply a
  · ext b
    change e.symm (Ideal.Quotient.mk q b) = 0 ↔ b ∈ q
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp

/- English proof (translation)
Introduce `V U r _ Ω _ _ x v hv`. Take `⟨t, ht1, ht2⟩` from `Scheme.Pullback.exists_preimage_pullback (f := r) (g := x) v (IsLocalRing.closedPoint Ω) hv`. Set `P` to `pullback r x`. Use `haveI : IsIntegralHom (pullback.snd r x) := inferInstance`. Use `haveI : IsAffine P := isAffine_of_isAffineHom (pullback.snd r x)`.

Set `φ : CommRingCat.of Ω ⟶ Γ(P, ⊤)` to `Spec.preimage (P.isoSpec.inv ≫ pullback.snd r x)`. Establish `hφ' : Spec.map φ = P.isoSpec.inv ≫ pullback.snd r x` using `Spec.map_preimage _`. Establish `hφ : φ.hom.IsIntegral`. Rewrite using `[← IsIntegralHom.SpecMap_iff, hφ']`. Use `infer_instance`.

Set `y : Spec Γ(P, ⊤)` to `P.isoSpec.hom t`. Use `haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y`. Take `⟨s, hs, hk⟩` from `exists_retract φ hφ y.asIdeal`. Use `⟨Spec.map s ≫ P.isoSpec.inv ≫ pullback.fst r x, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Spec.map s ≫ Spec.map φ = 𝟙 _`.

Rewrite using `[← Spec.map_comp, hs, Spec.map_id]`. Rewrite using `[Category.assoc, Category.assoc, pullback.condition, ← Category.assoc P.isoSpec.inv, ← hφ', ← Category.assoc, h1, Category.id_comp]`. Establish `hy : (pt (Spec.map s) : Spec Γ(P, ⊤)) = y` using `PrimeSpectrum.ext ((pt_map_ideal s).trans hk)`. Rewrite using `[← Category.assoc, pt_comp, pt_comp, hy]`. Express the relevant statement in the definitionally equal form `(pullback.fst r x) (P.isoSpec.inv (P.isoSpec.hom t)) = v`.

Establish `h2 : P.isoSpec.inv (P.isoSpec.hom t) = t`. Rewrite using `[← Scheme.Hom.comp_apply, Iso.hom_inv_id]`. Both sides reduce to the same expression. Rewrite using `[h2, ht1]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.ptLift_of :
    PtLift := by
  intro V U r _ Ω _ _ x v hv
  obtain ⟨t, ht1, ht2⟩ := Scheme.Pullback.exists_preimage_pullback (f := r) (g := x) v
    (IsLocalRing.closedPoint Ω) hv
  let P := pullback r x
  haveI : IsIntegralHom (pullback.snd r x) := inferInstance
  haveI : IsAffine P := isAffine_of_isAffineHom (pullback.snd r x)
  let φ : CommRingCat.of Ω ⟶ Γ(P, ⊤) := Spec.preimage (P.isoSpec.inv ≫ pullback.snd r x)
  have hφ' : Spec.map φ = P.isoSpec.inv ≫ pullback.snd r x := Spec.map_preimage _
  have hφ : φ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hφ']
    infer_instance
  let y : Spec Γ(P, ⊤) := P.isoSpec.hom t
  haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  obtain ⟨s, hs, hk⟩ := exists_retract φ hφ y.asIdeal
  refine ⟨Spec.map s ≫ P.isoSpec.inv ≫ pullback.fst r x, ?_, ?_⟩
  · have h1 : Spec.map s ≫ Spec.map φ = 𝟙 _ := by
      rw [← Spec.map_comp, hs, Spec.map_id]
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc P.isoSpec.inv,
      ← hφ', ← Category.assoc, h1, Category.id_comp]
  · have hy : (pt (Spec.map s) : Spec Γ(P, ⊤)) = y :=
      PrimeSpectrum.ext ((pt_map_ideal s).trans hk)
    rw [← Category.assoc, pt_comp, pt_comp, hy]
    change (pullback.fst r x) (P.isoSpec.inv (P.isoSpec.hom t)) = v
    have h2 : P.isoSpec.inv (P.isoSpec.hom t) = t := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    rw [h2, ht1]
