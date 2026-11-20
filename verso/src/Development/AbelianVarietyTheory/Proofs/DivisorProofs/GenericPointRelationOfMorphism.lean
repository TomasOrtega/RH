import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Side
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry GlobalTheory.ShFam.GalCarry.Corr

set_option autoImplicit false

namespace GlobalTheory.ShFam.GalCarry.Corr.AllPoints

/- English proof (translation)
Use `letI := f.toAlgebra`. Use `letI := g.toAlgebra`. Take `⟨m, hm⟩` from `Ideal.exists_maximal (TensorProduct k A B)`. Use `letI : Field (TensorProduct k A B ⧸ m) := Ideal.Quotient.field m`. Set `π : TensorProduct k A B →+* AlgebraicClosure (TensorProduct k A B ⧸ m)` to `(algebraMap _ _).comp (Ideal.Quotient.mk m)`.

Use `⟨AlgebraicClosure (TensorProduct k A B ⧸ m), inferInstance, inferInstance, π.comp (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A B).toRingHom, π.comp (Algebra.TensorProduct.includeRight : B →ₐ[k] TensorProduct k A B).toRingHom, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Conclude with `congrArg π (((Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A B).commutes x).trans ((Algebra.TensorProduct.includeRight : B →ₐ[k] TensorProduct k A B).commutes x).symm)`.
-/
theorem exists_common_field {k A B : Type} [Field k] [Field A] [Field B] (f : k →+* A) (g : k →+* B) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (a : A →+* Ω) (b : B →+* Ω), a.comp f = b.comp g := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct k A B)
  letI : Field (TensorProduct k A B ⧸ m) := Ideal.Quotient.field m
  let π : TensorProduct k A B →+* AlgebraicClosure (TensorProduct k A B ⧸ m) :=
    (algebraMap _ _).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure (TensorProduct k A B ⧸ m), inferInstance, inferInstance,
    π.comp (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A B).toRingHom,
    π.comp (Algebra.TensorProduct.includeRight : B →ₐ[k] TensorProduct k A B).toRingHom, ?_⟩
  ext x
  exact congrArg π (((Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A B).commutes x).trans
    ((Algebra.TensorProduct.includeRight : B →ₐ[k] TensorProduct k A B).commutes x).symm)

/- English proof (translation)
Take `⟨Ω, _, _, a, b, h⟩` from `exists_common_field (IsLocalRing.ResidueField.map ψ) (IsLocalRing.ResidueField.lift χ)`. Use `⟨Ω, inferInstance, inferInstance, a.comp (IsLocalRing.residue W), b, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot a).1 a.injective, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]`. Use extensionality with `x`. Use `congrArg (fun f => f (IsLocalRing.residue A x)) h` as an intermediate fact.

Simplify using `using this`.
-/
theorem exists_common_local {A W K : Type} [CommRing A] [IsLocalRing A] [CommRing W] [IsLocalRing W] [Field K]
    (ψ : A →+* W) [IsLocalHom ψ] (χ : A →+* K) [IsLocalHom χ] :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (r : W →+* Ω) (β : K →+* Ω),
      RingHom.ker r = IsLocalRing.maximalIdeal W ∧ r.comp ψ = β.comp χ := by
  obtain ⟨Ω, _, _, a, b, h⟩ := exists_common_field (IsLocalRing.ResidueField.map ψ) (IsLocalRing.ResidueField.lift χ)
  refine ⟨Ω, inferInstance, inferInstance, a.comp (IsLocalRing.residue W), b, ?_, ?_⟩
  · rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot a).1 a.injective, ← RingHom.ker_eq_comap_bot,
      IsLocalRing.ker_residue]
  · ext x
    have := congrArg (fun f => f (IsLocalRing.residue A x)) h
    simpa using this

/- English proof (translation)
Take `⟨⟨y, s⟩, rfl⟩` from `(Scheme.SpecToEquivOfField K X).symm.surjective a`. Take `⟨⟨z, t⟩, rfl⟩` from `(Scheme.SpecToEquivOfField K X).symm.surjective b`. Establish `key : ∀ (y : X) (s : X.residueField y ⟶ CommRingCat.of K), spMap β ≫ (Scheme.SpecToEquivOfField K X).symm ⟨y, s⟩ = (Scheme.SpecToEquivOfField L X).symm ⟨y, s ≫ CommRingCat.ofHom β⟩` using `fun y s => by`. Simplify using `only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]`. Rewrite `h` using `[key, key]`.

Establish `h2` using `(Scheme.SpecToEquivOfField L X).symm.injective h`. Take `rfl : y = z` from `congrArg Sigma.fst h2`. Simplify using `only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h2`. Use `congr 2`. Use extensionality with `x`.

Conclude with `β.injective (congrArg (fun f => f.hom x) h2)`.
-/
theorem cancel_field {K L : Type} [Field K] [Field L] (β : K →+* L) {X : Scheme.{0}} {a b : Sp K ⟶ X}
    (h : spMap β ≫ a = spMap β ≫ b) : a = b := by
  obtain ⟨⟨y, s⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective a
  obtain ⟨⟨z, t⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective b
  have key : ∀ (y : X) (s : X.residueField y ⟶ CommRingCat.of K),
      spMap β ≫ (Scheme.SpecToEquivOfField K X).symm ⟨y, s⟩ =
        (Scheme.SpecToEquivOfField L X).symm ⟨y, s ≫ CommRingCat.ofHom β⟩ := fun y s => by
    simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
  rw [key, key] at h
  have h2 := (Scheme.SpecToEquivOfField L X).symm.injective h
  obtain rfl : y = z := congrArg Sigma.fst h2
  simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h2
  congr 2
  ext x
  exact β.injective (congrArg (fun f => f.hom x) h2)

/- English proof (translation)
Take `⟨W, hW⟩` from `GlobalTheory.exists_dominatesStalk (p (IsLocalRing.closedPoint K))`. Take `⟨ψ, _, hψ⟩` from `GlobalTheory.dominatesStalk_iff_exists_isLocalHom.mp hW`. Take `⟨Ω, _, _, r, β, hr, h⟩` from `exists_common_local ψ (Scheme.stalkClosedPointTo (R := .of K) p).hom`. Use `⟨W, spMap ψ ≫ X.fromSpecStalk _, Ω, inferInstance, inferInstance, r, β, hr, ?_, ?_⟩` and prove the remaining obligations. Establish `e : (algebraMap W X.functionField).comp ψ = algebraMap _ X.functionField` using `RingHom.ext hψ`.

Rewrite using `[← Category.assoc, ← spMap_comp, e]`. Conclude with `GlobalTheory.specAlgebraMap_fromSpecStalk _`. Rewrite using `[← Category.assoc, ← spMap_comp, h, spMap_comp, Category.assoc]`. Conclude with `congrArg (spMap β ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of K) p)`.
-/
theorem exists_specialisation {X : Scheme.{0}} [IsIntegral X] {K : Type} [Field K] (p : Sp K ⟶ X) :
    ∃ (W : ValuationSubring X.functionField) (q : Sp W ⟶ X) (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (r : W →+* Ω) (β : K →+* Ω), RingHom.ker r = IsLocalRing.maximalIdeal W ∧
      spMap (algebraMap W X.functionField) ≫ q = X.fromSpecStalk (genericPoint X) ∧
      spMap r ≫ q = spMap β ≫ p := by
  obtain ⟨W, hW⟩ := GlobalTheory.exists_dominatesStalk (p (IsLocalRing.closedPoint K))
  obtain ⟨ψ, _, hψ⟩ := GlobalTheory.dominatesStalk_iff_exists_isLocalHom.mp hW
  obtain ⟨Ω, _, _, r, β, hr, h⟩ := exists_common_local ψ (Scheme.stalkClosedPointTo (R := .of K) p).hom
  refine ⟨W, spMap ψ ≫ X.fromSpecStalk _, Ω, inferInstance, inferInstance, r, β, hr, ?_, ?_⟩
  · have e : (algebraMap W X.functionField).comp ψ = algebraMap _ X.functionField := RingHom.ext hψ
    rw [← Category.assoc, ← spMap_comp, e]
    exact GlobalTheory.specAlgebraMap_fromSpecStalk _
  · rw [← Category.assoc, ← spMap_comp, h, spMap_comp, Category.assoc]
    exact congrArg (spMap β ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of K) p)

/- English proof (translation)
Introduce `F _ _ I I' Y Y' Rel hS i i' φ _ hgen K _ _ p`. Take `⟨-, h2, h3, h4⟩` from `hS`. Take `⟨W, q, Ω, _, _, r, β, hr, hq, hp⟩` from `exists_specialisation p`. Take `⟨⟨i'', p''⟩, hp'', -⟩` from `h3 K i p`. Set `ι : (Y i).Fn →+* AlgebraicClosure (Y i).Fn` to `algebraMap _ _`.

Set `ν : W →+* AlgebraicClosure (Y i).Fn` to `ι.comp (algebraMap W (Y i).X.functionField)`. Establish `hν : spMap ν ≫ q = spMap ι ≫ genericPt (Y i)` using `(congrArg (· ≫ q) (spMap_comp _ ι)).trans ((Category.assoc _ _ _).trans (congrArg (spMap ι ≫ ·) hq))`. Establish `hinj : Function.Injective ν` using `ι.injective.comp Subtype.val_injective`. Establish `a1` using `h4 W _ ν Ω r i i' q (q ≫ φ) hinj hr (by`. Rewrite using `[← Category.assoc, hν, Category.assoc]`.

Conclude with `hgen)`. Rewrite `a1` using `[← Category.assoc, hp]`. Establish `a2` using `h2 K Ω β i i'' p p'' hp''`. Establish `e` using `(h3 Ω i (spMap β ≫ p)).unique (y₁ := ⟨i'', spMap β ≫ p''⟩) (y₂ := ⟨i', (spMap β ≫ p) ≫ φ⟩) a2 a1`. Take `rfl : i'' = i'` from `congrArg Sigma.fst e`.

Simplify using `only [Sigma.mk.inj_iff, heq_eq_eq, true_and, Category.assoc] at e`. Rewrite using `[← cancel_field β e]`. Conclude with `hp''`.
-/
theorem rel_of_generic : ∀ (F : Type) [Field F] [CharZero F] (I I' : Type) (Y : I → Var F) (Y' : I' → Var F)
    (Rel : ∀ (K : Type) [Field K] (i : I) (i' : I'), (Sp K ⟶ (Y i).X) → (Sp K ⟶ (Y' i').X) → Prop), Side Y Y' Rel → ∀ (i : I) (i' : I') (φ : (Y i).X ⟶ (Y' i').X), φ ≫ (Y' i').str = (Y i).str →
      Rel (AlgebraicClosure (Y i).Fn) i i' (spMap (algebraMap (Y i).Fn (AlgebraicClosure (Y i).Fn)) ≫ genericPt (Y i))
        (spMap (algebraMap (Y i).Fn (AlgebraicClosure (Y i).Fn)) ≫ genericPt (Y i) ≫ φ) →
      ∀ (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ (Y i).X), Rel K i i' p (p ≫ φ) := by
  intro F _ _ I I' Y Y' Rel hS i i' φ _ hgen K _ _ p
  obtain ⟨-, h2, h3, h4⟩ := hS
  obtain ⟨W, q, Ω, _, _, r, β, hr, hq, hp⟩ := exists_specialisation p
  obtain ⟨⟨i'', p''⟩, hp'', -⟩ := h3 K i p
  let ι : (Y i).Fn →+* AlgebraicClosure (Y i).Fn := algebraMap _ _
  let ν : W →+* AlgebraicClosure (Y i).Fn := ι.comp (algebraMap W (Y i).X.functionField)
  have hν : spMap ν ≫ q = spMap ι ≫ genericPt (Y i) :=
    (congrArg (· ≫ q) (spMap_comp _ ι)).trans ((Category.assoc _ _ _).trans (congrArg (spMap ι ≫ ·) hq))
  have hinj : Function.Injective ν := ι.injective.comp Subtype.val_injective
  have a1 := h4 W _ ν Ω r i i' q (q ≫ φ) hinj hr (by
    rw [← Category.assoc, hν, Category.assoc]; exact hgen)
  rw [← Category.assoc, hp] at a1
  have a2 := h2 K Ω β i i'' p p'' hp''
  have e := (h3 Ω i (spMap β ≫ p)).unique (y₁ := ⟨i'', spMap β ≫ p''⟩) (y₂ := ⟨i', (spMap β ≫ p) ≫ φ⟩) a2 a1
  obtain rfl : i'' = i' := congrArg Sigma.fst e
  simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and, Category.assoc] at e
  rw [← cancel_field β e]
  exact hp''

end GlobalTheory.ShFam.GalCarry.Corr.AllPoints
