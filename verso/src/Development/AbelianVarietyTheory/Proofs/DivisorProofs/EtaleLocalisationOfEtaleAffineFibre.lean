import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.AffFib

/- English proof (translation)
Establish `e : (show (Spec R).Opens from PrimeSpectrum.basicOpen f).ι ≫ Spec.map θ = (basicOpenIsoSpecAway f).hom ≫ Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f)))`. Rewrite using `[Spec.map_comp, ← Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]`. Rewrite using `[e]`. Establish `key : Etale (Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f)))) ↔ ((algebraMap R (Localization.Away f)).comp θ.hom).Etale` using `HasRingHomProperty.Spec_iff (P := @Etale)`. Rewrite using `[← key]`.

Prove the components needed by the constructor for the conclusion. Introduce `H`. Establish `e2 : Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f))) = (basicOpenIsoSpecAway f).inv ≫ ((basicOpenIsoSpecAway f).hom ≫ Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f))))` using `(Iso.inv_hom_id_assoc _ _).symm`. Rewrite using `[e2]`. Use `infer_instance`.

Introduce `H`. Use `infer_instance`.
-/
theorem etale_basicOpen_iff (S R : CommRingCat.{0}) (θ : S ⟶ R) (f : R) :
    Etale ((show (Spec R).Opens from PrimeSpectrum.basicOpen f).ι ≫ Spec.map θ) ↔
      ((algebraMap R (Localization.Away f)).comp θ.hom).Etale := by
  have e : (show (Spec R).Opens from PrimeSpectrum.basicOpen f).ι ≫ Spec.map θ =
      (basicOpenIsoSpecAway f).hom ≫ Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f))) := by
    rw [Spec.map_comp, ← Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  rw [e]
  have key : Etale (Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f)))) ↔
      ((algebraMap R (Localization.Away f)).comp θ.hom).Etale := HasRingHomProperty.Spec_iff (P := @Etale)
  rw [← key]
  constructor
  · intro H
    have e2 : Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f))) =
        (basicOpenIsoSpecAway f).inv ≫ ((basicOpenIsoSpecAway f).hom ≫
          Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f)))) :=
      (Iso.inv_hom_id_assoc _ _).symm
    rw [e2]; infer_instance
  · intro H; infer_instance

end GlobalTheory.Mum.AffFib

/- English proof (translation)
Introduce `A C B φ ψ Ω _ ω W w hw hE`. Use `letI := φ.hom.toAlgebra`. Use `letI := ψ.hom.toAlgebra`. Use `letI := (φ ≫ ψ).hom.toAlgebra`. Use `letI := ω.hom.toAlgebra`.

Use `letI : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `set F := pullback.map (Spec.map (φ ≫ ψ)) (Spec.map ω) (Spec.map φ) (Spec.map ω) (Spec.map ψ) (𝟙 _) (𝟙 _) (by simp [Spec.map_comp]) (by simp) with hFdef`. Use `haveI := hE`. Set `θ` to `Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)`. Set `θc : CommRingCat.of (TensorProduct A Ω C) ⟶ CommRingCat.of (TensorProduct A Ω B)` to `CommRingCat.ofHom θ.toRingHom`.

Establish `pB : IsPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B).toRingHom)) (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Ω →+* TensorProduct A Ω B))) (Spec.map (φ ≫ ψ)) (Spec.map ω)` using `(isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A Ω B)).flip`. Establish `pC : IsPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] TensorProduct A Ω C).toRingHom)) (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Ω →+* TensorProduct A Ω C))) (Spec.map φ) (Spec.map ω)` using `(isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A Ω C)).flip`. Set `eB` to `pB.isoPullback`. Set `eC` to `pC.isoPullback`. Establish `hF : eB.hom ≫ F = Spec.map θc ≫ eC.hom`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, hFdef, pullback.lift_fst, ← Category.assoc, IsPullback.isoPullback_hom_fst, ← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Rewrite using `[Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd, hFdef, pullback.lift_snd, ← Category.assoc, IsPullback.isoPullback_hom_snd, ← Spec.map_comp, Category.comp_id]`. Use `congr 1`.

Use extensionality with `c`. Simplify using `[θc, θ]`. Establish `hθ : Spec.map θc = eB.hom ≫ F ≫ eC.inv`. Rewrite using `[← Category.assoc, hF, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Set `U : (Spec (CommRingCat.of (TensorProduct A Ω B))).Opens` to `eB.hom ⁻¹ᵁ W`.

Set `y` to `eB.inv w`. Establish `hy : y ∈ U` using `by show eB.hom (eB.inv w) ∈ W`. Simplify using `using hw`. Take `⟨_, ⟨f, rfl⟩, hyf, hfU⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy U.2`. Establish `hD : (show (Spec (CommRingCat.of (TensorProduct A Ω B))).Opens from PrimeSpectrum.basicOpen f) ≤ U` using `hfU`.

Use `⟨y.asIdeal, y.isPrime, f, ?_, (PrimeSpectrum.mem_basicOpen f y).1 hyf, ?_⟩` and prove the remaining obligations. Establish `: pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B).toRingHom) y`. Rewrite using `[← pB.isoPullback_hom_fst]`. Use `show _ = (eB.hom ≫ pullback.fst _ _) (eB.inv w)`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Both sides reduce to the same expression. Use `(GlobalTheory.Mum.AffFib.etale_basicOpen_iff _ _ θc f).1 ?_` and prove the remaining obligations. Rewrite using `[hθ, ← Scheme.homOfLE_ι _ hD]`. Establish `e1 : (Spec (CommRingCat.of (TensorProduct A Ω B))).homOfLE hD ≫ U.ι ≫ eB.hom ≫ F ≫ eC.inv = (Spec (CommRingCat.of (TensorProduct A Ω B))).homOfLE hD ≫ (eB.hom ∣_ W) ≫ (W.ι ≫ F) ≫ eC.inv`.

Rewrite using `[← Category.assoc (U.ι), ← morphismRestrict_ι]`. Simplify using `only [Category.assoc]`. Rewrite using `[Category.assoc, e1]`. Use `infer_instance`.
-/
theorem GlobalTheory.Mum.etale_localisation_of_etale_affine_fibre : ∀ (A C B : CommRingCat.{0}) (φ : A ⟶ C) (ψ : C ⟶ B) (Ω : Type) [Field Ω] (ω : A ⟶ CommRingCat.of Ω) (W : (pullback (Spec.map (φ ≫ ψ)) (Spec.map ω)).Opens) (w : ↥(pullback (Spec.map (φ ≫ ψ)) (Spec.map ω))), w ∈ W → Etale (W.ι ≫ pullback.map (Spec.map (φ ≫ ψ)) (Spec.map ω) (Spec.map φ) (Spec.map ω) (Spec.map ψ) (𝟙 _) (𝟙 _) (by simp [Spec.map_comp]) (by simp)) → letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra; letI := (φ ≫ ψ).hom.toAlgebra; letI := ω.hom.toAlgebra; letI : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq (fun _ => rfl); ∃ (Q' : Ideal (TensorProduct A Ω B)) (_ : Q'.IsPrime) (f : TensorProduct A Ω B), Q'.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B) = (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w).asIdeal ∧ f ∉ Q' ∧ ((algebraMap (TensorProduct A Ω B) (Localization.Away f)).comp (Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)).toRingHom).Etale := by
  intro A C B φ ψ Ω _ ω W w hw hE
  letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra; letI := (φ ≫ ψ).hom.toAlgebra; letI := ω.hom.toAlgebra
  letI : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  set F := pullback.map (Spec.map (φ ≫ ψ)) (Spec.map ω) (Spec.map φ) (Spec.map ω) (Spec.map ψ) (𝟙 _) (𝟙 _)
    (by simp [Spec.map_comp]) (by simp) with hFdef
  haveI := hE
  let θ := Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)
  let θc : CommRingCat.of (TensorProduct A Ω C) ⟶ CommRingCat.of (TensorProduct A Ω B) :=
    CommRingCat.ofHom θ.toRingHom
  have pB : IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Ω →+* TensorProduct A Ω B)))
      (Spec.map (φ ≫ ψ)) (Spec.map ω) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A Ω B)).flip
  have pC : IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] TensorProduct A Ω C).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Ω →+* TensorProduct A Ω C)))
      (Spec.map φ) (Spec.map ω) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A Ω C)).flip
  let eB := pB.isoPullback
  let eC := pC.isoPullback
  have hF : eB.hom ≫ F = Spec.map θc ≫ eC.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, hFdef, pullback.lift_fst,
        ← Category.assoc, IsPullback.isoPullback_hom_fst, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
    · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd, hFdef, pullback.lift_snd,
        ← Category.assoc, IsPullback.isoPullback_hom_snd, ← Spec.map_comp, Category.comp_id]
      congr 1
      ext c
      simp [θc, θ]
  have hθ : Spec.map θc = eB.hom ≫ F ≫ eC.inv := by
    rw [← Category.assoc, hF, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let U : (Spec (CommRingCat.of (TensorProduct A Ω B))).Opens := eB.hom ⁻¹ᵁ W
  let y := eB.inv w
  have hy : y ∈ U := by
    show eB.hom (eB.inv w) ∈ W
    simpa using hw
  obtain ⟨_, ⟨f, rfl⟩, hyf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy U.2
  have hD : (show (Spec (CommRingCat.of (TensorProduct A Ω B))).Opens from PrimeSpectrum.basicOpen f) ≤ U := hfU
  refine ⟨y.asIdeal, y.isPrime, f, ?_, (PrimeSpectrum.mem_basicOpen f y).1 hyf, ?_⟩
  · have : pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B).toRingHom) y := by
      rw [← pB.isoPullback_hom_fst]
      show _ = (eB.hom ≫ pullback.fst _ _) (eB.inv w)
      simp
    rw [this]
    rfl
  · refine (GlobalTheory.Mum.AffFib.etale_basicOpen_iff _ _ θc f).1 ?_
    rw [hθ, ← Scheme.homOfLE_ι _ hD]
    have e1 : (Spec (CommRingCat.of (TensorProduct A Ω B))).homOfLE hD ≫ U.ι ≫ eB.hom ≫ F ≫ eC.inv =
        (Spec (CommRingCat.of (TensorProduct A Ω B))).homOfLE hD ≫ (eB.hom ∣_ W) ≫ (W.ι ≫ F) ≫ eC.inv := by
      rw [← Category.assoc (U.ι), ← morphismRestrict_ι]
      simp only [Category.assoc]
    rw [Category.assoc, e1]
    infer_instance
