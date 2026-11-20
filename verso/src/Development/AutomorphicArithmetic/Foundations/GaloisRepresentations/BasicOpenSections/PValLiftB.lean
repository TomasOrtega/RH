import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed

open CategoryTheory Limits AlgebraicGeometry
open UpperTheory.Gal.TranscendenceTraces (gp pt)
open UpperTheory.Gal.crystallineComparison (resPt)
open UpperTheory.Gal UpperTheory.Gal.Mod

/- English proof (translation)
Use `haveI : Nontrivial (TensorProduct k A B) := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k A B (algebraMap k B).injective`. Take `⟨M, hM⟩` from `Ideal.exists_maximal (TensorProduct k A B)`. Use `letI := Ideal.Quotient.field M`. Set `q : TensorProduct k A B →+* TensorProduct k A B ⧸ M` to `Ideal.Quotient.mk M`. Set `iA : A →ₐ[k] TensorProduct k A B` to `Algebra.TensorProduct.includeLeft`.

Set `iB : B →ₐ[k] TensorProduct k A B` to `Algebra.TensorProduct.includeRight`. Use `⟨AlgebraicClosure (TensorProduct k A B ⧸ M), inferInstance, inferInstance, (algebraMap _ _).comp (q.comp iA.toRingHom), (algebraMap _ _).comp (q.comp iB.toRingHom), ?_⟩` and prove the remaining obligations. Use extensionality with `c`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes, iA, iB]`.
-/
private theorem exists_common_algClosed_embedding {k A B : Type} [Field k] [Field A] [Field B] [Algebra k A]
    [Algebra k B] :
    ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (f : A →+* C) (g : B →+* C),
      f.comp (algebraMap k A) = g.comp (algebraMap k B) := by
  haveI : Nontrivial (TensorProduct k A B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k A B
      (algebraMap k B).injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct k A B)
  letI := Ideal.Quotient.field M
  let q : TensorProduct k A B →+* TensorProduct k A B ⧸ M := Ideal.Quotient.mk M
  let iA : A →ₐ[k] TensorProduct k A B := Algebra.TensorProduct.includeLeft
  let iB : B →ₐ[k] TensorProduct k A B := Algebra.TensorProduct.includeRight
  refine ⟨AlgebraicClosure (TensorProduct k A B ⧸ M), inferInstance, inferInstance,
    (algebraMap _ _).comp (q.comp iA.toRingHom), (algebraMap _ _).comp (q.comp iB.toRingHom), ?_⟩
  ext c
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgHom.commutes, iA, iB]

/- English proof (translation)
Introduce `p Y Ω _ x η hsp hp`. Set `O` to `Y.presheaf.stalk (pt x)`. Set `sx : O ⟶ CommRingCat.of Ω` to `Scheme.stalkClosedPointTo x`. Use `haveI : IsLocalHom sx.hom := Scheme.isLocalHom_stalkClosedPointTo' x`. Establish `hx : Spec.map sx ≫ Y.fromSpecStalk (pt x) = x` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk x`.

Set `K` to `AlgebraicClosure (Y.residueField η)`. Set `f : O →+* K` to `(algebraMap (Y.residueField η) K).comp ((Y.residue η).hom.comp (Y.presheaf.stalkSpecializes hsp).hom)`. Take `⟨A, hA, hloc⟩` from `IsLocalRing.exists_factor_valuationRing f`. Set `g : O →+* A` to `f.codRestrict A.toSubring hA`. Use `haveI : IsLocalHom g := hloc`.

Use `haveI : IsAlgClosed (FractionRing A) := IsAlgClosed.of_ringEquiv K _ (FractionRing.algEquiv A K).symm.toRingEquiv`. Set `φ : IsLocalRing.ResidueField O →+* Ω` to `IsLocalRing.ResidueField.lift sx.hom`. Set `ψ : IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField A` to `IsLocalRing.ResidueField.map g`. Use `letI : Algebra (IsLocalRing.ResidueField O) Ω := φ.toAlgebra`. Use `letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField A) := ψ.toAlgebra`.

Take `⟨C, _, _, fa, fb, hab⟩` from `exists_common_algClosed_embedding (k := IsLocalRing.ResidueField O) (A := Ω) (B := IsLocalRing.ResidueField A)`. Use `⟨A, inferInstance, inferInstance, inferInstance, inferInstance, Spec.map (CommRingCat.ofHom g) ≫ Y.fromSpecStalk (pt x), C, inferInstance, inferInstance, fa, fb, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `hu` using `((Y.mem_basicOpen (p : Γ(Y, ⊤)) η trivial).mp hp).map (Y.residue η).hom`. Simplify using `only [map_natCast] at hu`.

Establish `h1` using `congrArg A.subtype h0`. Simplify using `only [map_natCast, map_zero] at h1`. Establish `h2 : (p : Y.residueField η) = 0` using `(algebraMap (Y.residueField η) K).injective (by rw [map_natCast, map_zero]; exact h1)`. Conclude with `hu.ne_zero h2`. Use `conv_lhs => rw [← hx]`.

Simplify using `only [sp, resPt, ← Spec.map_comp_assoc]`. Use `congr 2`. Use extensionality with `z`. Establish `hz` using `congrArg (fun h => h (IsLocalRing.residue O z)) hab`. Simplify `hz` using `[φ, ψ, RingHom.algebraMap_toAlgebra, IsLocalRing.ResidueField.map_residue]`.
-/
theorem UpperTheory.Gal.Mod.valLiftB :
    ValLift := by
  intro p Y Ω _ x η hsp hp
  let O := Y.presheaf.stalk (pt x)
  let sx : O ⟶ CommRingCat.of Ω := Scheme.stalkClosedPointTo x
  haveI : IsLocalHom sx.hom := Scheme.isLocalHom_stalkClosedPointTo' x
  have hx : Spec.map sx ≫ Y.fromSpecStalk (pt x) = x :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
  let K := AlgebraicClosure (Y.residueField η)
  let f : O →+* K := (algebraMap (Y.residueField η) K).comp
    ((Y.residue η).hom.comp (Y.presheaf.stalkSpecializes hsp).hom)
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  let g : O →+* A := f.codRestrict A.toSubring hA
  haveI : IsLocalHom g := hloc
  haveI : IsAlgClosed (FractionRing A) :=
    IsAlgClosed.of_ringEquiv K _ (FractionRing.algEquiv A K).symm.toRingEquiv
  let φ : IsLocalRing.ResidueField O →+* Ω := IsLocalRing.ResidueField.lift sx.hom
  let ψ : IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField A :=
    IsLocalRing.ResidueField.map g
  letI : Algebra (IsLocalRing.ResidueField O) Ω := φ.toAlgebra
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField A) := ψ.toAlgebra
  obtain ⟨C, _, _, fa, fb, hab⟩ := exists_common_algClosed_embedding (k := IsLocalRing.ResidueField O) (A := Ω)
    (B := IsLocalRing.ResidueField A)
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom g) ≫ Y.fromSpecStalk (pt x), C, inferInstance, inferInstance,
    fa, fb, ?_, ?_⟩
  · intro h0
    have hu := ((Y.mem_basicOpen (p : Γ(Y, ⊤)) η trivial).mp hp).map (Y.residue η).hom
    simp only [map_natCast] at hu
    have h1 := congrArg A.subtype h0
    simp only [map_natCast, map_zero] at h1
    have h2 : (p : Y.residueField η) = 0 :=
      (algebraMap (Y.residueField η) K).injective (by rw [map_natCast, map_zero]; exact h1)
    exact hu.ne_zero h2
  · conv_lhs => rw [← hx]
    simp only [sp, resPt, ← Spec.map_comp_assoc]
    congr 2
    ext z
    have hz := congrArg (fun h => h (IsLocalRing.residue O z)) hab
    simpa [φ, ψ, RingHom.algebraMap_toAlgebra, IsLocalRing.ResidueField.map_residue] using hz
