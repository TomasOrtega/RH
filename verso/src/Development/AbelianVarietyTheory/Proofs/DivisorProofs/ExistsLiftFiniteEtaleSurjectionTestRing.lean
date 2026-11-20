import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.EvNatPf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory

/- English proof (translation)
Introduce `Y Z π hfin het hsurj K _ p x`. Set `P` to `pullback π x`. Set `f : P ⟶ Sp p.R` to `pullback.snd π x`. Establish `: IsFinite f` using `inferInstance`. Establish `: Etale f` using `inferInstance`.

Establish `: Surjective f` using `inferInstance`. Establish `: IsAffine P` using `isAffine_of_isAffineHom f`. Set `g : Spec Γ(P, ⊤) ⟶ Spec (CommRingCat.of p.R)` to `P.isoSpec.inv ≫ f`. Set `φ : CommRingCat.of p.R ⟶ Γ(P, ⊤)` to `Spec.preimage g`. Establish `hφ : Spec.map φ = g` using `Spec.map_preimage g`.

Establish `hg_et : Etale (Spec.map φ)` using `by rw [hφ]; infer_instance`. Establish `hg_surj : Surjective (Spec.map φ)` using `by rw [hφ]; infer_instance`. Establish `hφet : φ.hom.Etale` using `(HasRingHomProperty.Spec_iff (P := @Etale)).1 hg_et`. Establish `hφff : φ.hom.FaithfullyFlat` using `(flat_and_surjective_SpecMap_iff φ).1 ⟨inferInstance, hg_surj⟩`. Use `letI : Algebra p.R Γ(P, ⊤) := φ.hom.toAlgebra`.

Establish `hBet : Algebra.Etale p.R Γ(P, ⊤)` using `hφet`. Establish `hBff : Module.FaithfullyFlat p.R Γ(P, ⊤)` using `hφff`. Establish `hpred : _root_.IsReduced p.R` using `(Ideal.isRadical_iff_quotient_reduced _).1 p.rad`. Establish `hBred : _root_.IsReduced Γ(P, ⊤)` using `GlobalTheory.isReduced_algebra_of_smooth_of_isReduced p.R Γ(P, ⊤)`. Use `letI : Algebra K Γ(P, ⊤) := (φ.hom.comp (algebraMap K p.R)).toAlgebra`.

Use `haveI : IsScalarTower K p.R Γ(P, ⊤) := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : Algebra.FiniteType K Γ(P, ⊤) := Algebra.FiniteType.trans (S := p.R) inferInstance inferInstance`. Take `⟨n, s, hs⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType K Γ(P, ⊤))`. Establish `hrad : (RingHom.ker s).IsRadical` using `(Ideal.isRadical_iff_quotient_reduced _).2 (isReduced_of_injective (Ideal.kerLiftAlg s) (Ideal.kerLiftAlg_injective s))`. Set `q : TRing K` to `⟨n, RingHom.ker s, hrad⟩`.

Set `e : q.R ≃ₐ[K] Γ(P, ⊤)` to `Ideal.quotientKerAlgEquivOfSurjective hs`. Set `φK : p.R →ₐ[K] Γ(P, ⊤)` to `{ φ.hom with commutes' := fun _ => rfl }`. Set `ι : p.R →ₐ[K] q.R` to `e.symm.toAlgHom.comp φK`. Use `⟨q, ι, ?_, ?_⟩` and prove the remaining obligations. Use `letI := ι.toRingHom.toAlgebra`.

Set `e' : Γ(P, ⊤) ≃ₐ[p.R] q.R` to `AlgEquiv.ofRingEquiv (f := e.symm.toRingEquiv) (fun _ => rfl)`. Conclude with `⟨Module.FaithfullyFlat.of_linearEquiv _ _ e'.symm.toLinearEquiv, Algebra.Etale.of_equiv e'⟩`. Use `⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ P.isoSpec.inv ≫ pullback.fst π x, ?_⟩` and prove the remaining obligations. Establish `hι : CommRingCat.ofHom ι.toRingHom = φ ≫ CommRingCat.ofHom e.symm.toRingHom` using `rfl`. Rewrite using `[Category.assoc, Category.assoc, pullback.condition]`.

Express the relevant statement in the definitionally equal form `_ ≫ g ≫ x = _`. Rewrite using `[← hφ, ← Category.assoc, ← Spec.map_comp, ← hι]`.
-/
theorem exists_lift_finiteEtale_testRing : ∀ (Y Z : Scheme.{0}) (π : Z ⟶ Y), IsFinite π → Etale π → Surjective π →
    ∀ (K : Type) [Field K] (p : TRing K) (x : Sp p.R ⟶ Y), ∃ (q : TRing K) (ι : p.R →ₐ[K] q.R),
      (letI := ι.toRingHom.toAlgebra; Module.FaithfullyFlat p.R q.R ∧ Algebra.Etale p.R q.R) ∧
      ∃ z : Sp q.R ⟶ Z, z ≫ π = spMap ι.toRingHom ≫ x := by
  intro Y Z π hfin het hsurj K _ p x
  let P := pullback π x
  let f : P ⟶ Sp p.R := pullback.snd π x
  have : IsFinite f := inferInstance
  have : Etale f := inferInstance
  have : Surjective f := inferInstance
  have : IsAffine P := isAffine_of_isAffineHom f
  let g : Spec Γ(P, ⊤) ⟶ Spec (CommRingCat.of p.R) := P.isoSpec.inv ≫ f
  let φ : CommRingCat.of p.R ⟶ Γ(P, ⊤) := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hg_et : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hg_surj : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
  have hφet : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hg_et
  have hφff : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 ⟨inferInstance, hg_surj⟩
  letI : Algebra p.R Γ(P, ⊤) := φ.hom.toAlgebra
  have hBet : Algebra.Etale p.R Γ(P, ⊤) := hφet
  have hBff : Module.FaithfullyFlat p.R Γ(P, ⊤) := hφff
  have hpred : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  have hBred : _root_.IsReduced Γ(P, ⊤) := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced p.R Γ(P, ⊤)
  letI : Algebra K Γ(P, ⊤) := (φ.hom.comp (algebraMap K p.R)).toAlgebra
  haveI : IsScalarTower K p.R Γ(P, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType K Γ(P, ⊤) := Algebra.FiniteType.trans (S := p.R) inferInstance inferInstance
  obtain ⟨n, s, hs⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType K Γ(P, ⊤))
  have hrad : (RingHom.ker s).IsRadical := (Ideal.isRadical_iff_quotient_reduced _).2
    (isReduced_of_injective (Ideal.kerLiftAlg s) (Ideal.kerLiftAlg_injective s))
  let q : TRing K := ⟨n, RingHom.ker s, hrad⟩
  let e : q.R ≃ₐ[K] Γ(P, ⊤) := Ideal.quotientKerAlgEquivOfSurjective hs
  let φK : p.R →ₐ[K] Γ(P, ⊤) := { φ.hom with commutes' := fun _ => rfl }
  let ι : p.R →ₐ[K] q.R := e.symm.toAlgHom.comp φK
  refine ⟨q, ι, ?_, ?_⟩
  · letI := ι.toRingHom.toAlgebra
    let e' : Γ(P, ⊤) ≃ₐ[p.R] q.R := AlgEquiv.ofRingEquiv (f := e.symm.toRingEquiv) (fun _ => rfl)
    exact ⟨Module.FaithfullyFlat.of_linearEquiv _ _ e'.symm.toLinearEquiv, Algebra.Etale.of_equiv e'⟩
  · refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ P.isoSpec.inv ≫ pullback.fst π x, ?_⟩
    have hι : CommRingCat.ofHom ι.toRingHom = φ ≫ CommRingCat.ofHom e.symm.toRingHom := rfl
    rw [Category.assoc, Category.assoc, pullback.condition]
    change _ ≫ g ≫ x = _
    rw [← hφ, ← Category.assoc, ← Spec.map_comp, ← hι]

end GlobalTheory
