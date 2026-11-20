import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalUnramifiedOfIsIndEtale

open CategoryTheory Limits IsLocalRing

namespace GlobalTheory.IndEtaleLocal

/- English proof (translation)
Take `⟨J, _, _, D, t, s, hs, hst⟩` from `h`. Take `⟨i, g', h1, h2⟩` from `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit (CommRingCat.of A) D t (S := CommRingCat.of Z) (CommRingCat.ofHom (algebraMap A Z)) (Cocone.mk _ s) hs (RingHom.finitePresentation_algebraMap.mpr inferInstance) (CommRingCat.ofHom g.toRingHom) (fun i => by`. Rewrite using `[(hst i).2]`. Use extensionality with `a`. Use the proof step `simp)`.

Set `: Algebra A (D.obj i)` to `(t.app i).hom.toAlgebra`. Establish `het : Algebra.Etale A (D.obj i)` using `(hst i).1`. Use `⟨D.obj i, inferInstance, inferInstance, het, { toRingHom := g'.hom, commutes' := fun a => congr($(h1).hom a) }, { toRingHom := (s.app i).hom, commutes' := fun a => congr($((hst i).2).hom a) }, ?_⟩` and prove the remaining obligations. Use extensionality with `z`. Conclude with `(congr($(h2).hom z)).symm`.
-/
theorem exists_etale_factor {A S Z : Type} [CommRing A] [CommRing S] [Algebra A S]
    [CommRing Z] [Algebra A Z] [Algebra.FinitePresentation A Z]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) (g : Z →ₐ[A] S) :
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra A W) (_ : Algebra.Etale A W)
      (u : Z →ₐ[A] W) (v : W →ₐ[A] S), v.comp u = g := by
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := h
  obtain ⟨i, g', h1, h2⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    (CommRingCat.of A) D t (S := CommRingCat.of Z) (CommRingCat.ofHom (algebraMap A Z))
    (Cocone.mk _ s) hs
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)
    (CommRingCat.ofHom g.toRingHom) (fun i => by
      rw [(hst i).2]
      ext a
      simp)
  let : Algebra A (D.obj i) := (t.app i).hom.toAlgebra
  have het : Algebra.Etale A (D.obj i) := (hst i).1
  refine ⟨D.obj i, inferInstance, inferInstance, het,
    { toRingHom := g'.hom, commutes' := fun a => congr($(h1).hom a) },
    { toRingHom := (s.app i).hom, commutes' := fun a => congr($((hst i).2).hom a) }, ?_⟩
  ext z
  exact (congr($(h2).hom z)).symm

/- English proof (translation)
Use `Module.Flat.of_forall_isTrivialRelation fun {l f x} hfx => ?_` and prove the remaining obligations. Set `p : MvPolynomial (Fin l) A` to `∑ i, f i • MvPolynomial.X i`. Set `I : Ideal (MvPolynomial (Fin l) A)` to `Ideal.span {p}`. Establish `: Algebra.FinitePresentation A (MvPolynomial (Fin l) A ⧸ I)` using `Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton p)`. Set `g : (MvPolynomial (Fin l) A ⧸ I) →ₐ[A] S` to `Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) (by`.

Introduce `a ha`. Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`. Establish `: MvPolynomial.aeval x p = 0`. Simplify using `only [p, map_sum, map_smul, MvPolynomial.aeval_X, hfx]`. Rewrite using `[map_mul, this, mul_zero])`.

Take `⟨W, _, _, _, u, v, huv⟩` from `exists_etale_factor h g`. Set `w : Fin l → W` to `fun i => u (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))`. Establish `hw : ∀ i, v (w i) = x i` using `fun i => by`. Use `DFunLike.congr_fun huv (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))` as an intermediate fact. Conclude with `this.trans (MvPolynomial.aeval_X x i)`.

Establish `hrel : ∑ i, f i • w i = 0`. Establish `h0 : Ideal.Quotient.mkₐ A I p = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self p)`. Establish `: u (Ideal.Quotient.mkₐ A I p) = 0` using `by rw [h0, map_zero]`. Simplify `this` using `only [p, map_sum, map_smul]`. Take `⟨k, a, y, hy, ha⟩` from `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := W) hrel`.

Use `⟨k, a, fun j => v (y j), fun i => ?_, ha⟩` and prove the remaining obligations. Rewrite using `[← hw, hy, map_sum]`. Simplify using `only [map_smul]`.
-/
theorem flat_of_isIndEtale {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) : Module.Flat A S := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l f x} hfx => ?_
  let p : MvPolynomial (Fin l) A := ∑ i, f i • MvPolynomial.X i
  let I : Ideal (MvPolynomial (Fin l) A) := Ideal.span {p}
  have : Algebra.FinitePresentation A (MvPolynomial (Fin l) A ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton p)
  let g : (MvPolynomial (Fin l) A ⧸ I) →ₐ[A] S :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      have : MvPolynomial.aeval x p = 0 := by
        simp only [p, map_sum, map_smul, MvPolynomial.aeval_X, hfx]
      rw [map_mul, this, mul_zero])
  obtain ⟨W, _, _, _, u, v, huv⟩ := exists_etale_factor h g
  let w : Fin l → W := fun i => u (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
  have hw : ∀ i, v (w i) = x i := fun i => by
    have := DFunLike.congr_fun huv (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
    exact this.trans (MvPolynomial.aeval_X x i)
  have hrel : ∑ i, f i • w i = 0 := by
    have h0 : Ideal.Quotient.mkₐ A I p = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self p)
    have : u (Ideal.Quotient.mkₐ A I p) = 0 := by rw [h0, map_zero]
    simpa only [p, map_sum, map_smul] using this
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := W) hrel
  refine ⟨k, a, fun j => v (y j), fun i => ?_, ha⟩
  rw [← hw, hy, map_sum]
  simp only [map_smul]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale`. Consider the case `exact _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale`. Consider the case `(apply _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale ..)`.
-/
theorem exists_local_unramified {A S : Type} [CommRing A] [IsLocalRing A] [CommRing S]
    [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) (s : S) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : Algebra A L)
      (_ : IsLocalHom (algebraMap A L)) (_ : Algebra.FormallyUnramified A L)
      (_ : Algebra.EssFiniteType A L) (φ : L →ₐ[A] S) (_ : IsLocalHom φ) (x : L), φ x = s := by
  first
  | exact @_root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale
  | exact _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale
  | (apply _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale ..)

/- English proof (translation)
Use `⟨flat_of_isIndEtale h, le_antisymm ?_ fun s hs => ?_, ⟨fun r => ?_⟩⟩` and prove the remaining obligations. Conclude with `((local_hom_TFAE (algebraMap A S)).out 0 2 rfl rfl).mp inferInstance`. Take `⟨L, _, _, _, _, _, _, φ, hφ, x, rfl⟩` from `exists_local_unramified h s`. Establish `hx : x ∈ maximalIdeal L` using `fun hx => hs (hx.map φ)`. Rewrite `hx` using `[← Algebra.FormallyUnramified.map_maximalIdeal (R := A)]`.

Use `Ideal.mem_map_of_mem (φ : L →+* S) hx` as an intermediate fact. Rewrite `this` using `[Ideal.map_map, AlgHom.comp_algebraMap]`. Then use the resulting hypothesis. Take `⟨s, rfl⟩` from `residue_surjective r`. Take `⟨L, _, _, _, _, _, _, φ, hφ, x, rfl⟩` from `exists_local_unramified h s`. Establish `: IsLocalHom (φ : L →+* S)` using `⟨hφ.1⟩`.

Set `ψ : ResidueField L →ₐ[ResidueField A] ResidueField S` to `{ toRingHom := ResidueField.map (φ : L →+* S) commutes' := fun a => by`. Take `⟨a, rfl⟩` from `residue_surjective a`. Simplify using `[ResidueField.algebraMap_residue] }`. Use `(Algebra.IsSeparable.isSeparable (ResidueField A) (residue L x)).map ψ ψ.injective` as an intermediate fact. Conclude with `this`.
-/
theorem flat_map_maximalIdeal_isSeparable (A S : Type) [CommRing A] [IsLocalRing A] [CommRing S]
    [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) :
    Module.Flat A S ∧ (maximalIdeal A).map (algebraMap A S) = maximalIdeal S ∧
      Algebra.IsSeparable (ResidueField A) (ResidueField S) := by
  refine ⟨flat_of_isIndEtale h, le_antisymm ?_ fun s hs => ?_, ⟨fun r => ?_⟩⟩
  · exact ((local_hom_TFAE (algebraMap A S)).out 0 2 rfl rfl).mp inferInstance
  · obtain ⟨L, _, _, _, _, _, _, φ, hφ, x, rfl⟩ := exists_local_unramified h s
    have hx : x ∈ maximalIdeal L := fun hx => hs (hx.map φ)
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A)] at hx
    have := Ideal.mem_map_of_mem (φ : L →+* S) hx
    rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this
  · obtain ⟨s, rfl⟩ := residue_surjective r
    obtain ⟨L, _, _, _, _, _, _, φ, hφ, x, rfl⟩ := exists_local_unramified h s
    have : IsLocalHom (φ : L →+* S) := ⟨hφ.1⟩
    let ψ : ResidueField L →ₐ[ResidueField A] ResidueField S :=
      { toRingHom := ResidueField.map (φ : L →+* S)
        commutes' := fun a => by
          obtain ⟨a, rfl⟩ := residue_surjective a
          simp [ResidueField.algebraMap_residue] }
    have := (Algebra.IsSeparable.isSeparable (ResidueField A) (residue L x)).map ψ ψ.injective
    exact this

end GlobalTheory.IndEtaleLocal
