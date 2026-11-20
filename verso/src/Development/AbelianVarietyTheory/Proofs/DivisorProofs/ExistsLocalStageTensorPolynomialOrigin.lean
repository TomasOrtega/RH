import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
open IsLocalRing Polynomial

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocalStage

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hf`. Establish `hle : GlobalTheory.KeyOriginCut.originIdeal T ≤ (maximalIdeal T).comap (Polynomial.constantCoeff : Polynomial T →+* T)`. Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `x hx`. Simplify using `using hx`. Rewrite using `[Ideal.span_le]`. Introduce `x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`.

Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Simplify using `using hle hf`. Introduce `hf`. Rewrite using `[← Polynomial.X_mul_divX_add f]`.

Use `Ideal.add_mem _ ?_ ?_` and prove the remaining obligations. Conclude with `Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))`. Conclude with `Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)`.
-/
theorem mem_originIdeal_iff {T : Type} [CommRing T] [IsLocalRing T] (f : Polynomial T) :
    f ∈ GlobalTheory.KeyOriginCut.originIdeal T ↔ f.coeff 0 ∈ maximalIdeal T := by
  constructor
  · intro hf
    have hle : GlobalTheory.KeyOriginCut.originIdeal T ≤
        (maximalIdeal T).comap (Polynomial.constantCoeff : Polynomial T →+* T) := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simpa using hx
      · rw [Ideal.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp
    simpa using hle hf
  · intro hf
    rw [← Polynomial.X_mul_divX_add f]
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    · exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)

/- English proof (translation)
Use extensionality with `f`. Rewrite using `[Ideal.mem_comap, mem_originIdeal_iff, mem_originIdeal_iff]`. Simplify using `only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]`. Rewrite using `[IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]`.
-/
theorem comap_originIdeal {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] :
    (GlobalTheory.KeyOriginCut.originIdeal S).comap (Polynomial.mapRingHom φ) =
      GlobalTheory.KeyOriginCut.originIdeal R := by
  ext f
  rw [Ideal.mem_comap, mem_originIdeal_iff, mem_originIdeal_iff]
  simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_map_iff]

/- English proof (translation)
Introduce `T O _ _ _ _ _ _ _ hO A _ _ i hi EA _ _ _ QA _ hQA jA hjA A' _ _ ι α hαι hα`. Use `letI : Algebra (Polynomial A) (Polynomial A') := (Polynomial.mapRingHom ι).toAlgebra`. Use `letI : Algebra (Polynomial A) O := ((algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i)).toAlgebra`. Use `haveI : Algebra.Etale (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA) := Algebra.Etale.baseChange (Polynomial A) EA (Polynomial A')`. Set `f : Polynomial A' →ₐ[Polynomial A] O` to `{ toRingHom := (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom α) commutes' := by`.

Introduce `p`. Express the relevant statement in the definitionally equal form `(algebraMap (Polynomial T) O) (Polynomial.map α (Polynomial.map ι p)) = (algebraMap (Polynomial T) O) (Polynomial.map i p)`. Rewrite using `[Polynomial.map_map, hαι] }`. Set `g : EA →ₐ[Polynomial A] O` to `{ toRingHom := jA.comp (algebraMap EA (Localization.AtPrime QA)) commutes' := by`. Introduce `p`.

Express the relevant statement in the definitionally equal form `jA (algebraMap EA (Localization.AtPrime QA) (algebraMap (Polynomial A) EA p)) = (algebraMap (Polynomial T) O) (Polynomial.map i p)`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Conclude with `congrArg (fun h => h p) hjA }`. Set `F : (Polynomial A' ⊗[Polynomial A] EA) →+* O` to `(Algebra.TensorProduct.productMap f g).toRingHom`. Establish `hF : ∀ a b, F (a ⊗ₜ b) = f a * g b` using `fun a b => by`.

Simplify using `[F, Algebra.TensorProduct.productMap_apply_tmul]`. Set `Q' : Ideal (Polynomial A' ⊗[Polynomial A] EA)` to `(maximalIdeal O).comap F`. Use `⟨Polynomial A' ⊗[Polynomial A] EA, inferInstance, inferInstance, inferInstance, Q', Ideal.comap_isPrime _ _, ?_, ?_⟩` and prove the remaining obligations. Establish `hcomp : F.comp (algebraMap (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)) = (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom α)`. Use `RingHom.ext fun p => ?_` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, hF, map_one, mul_one]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `((maximalIdeal O).comap F).comap _ = _`. Rewrite using `[Ideal.comap_comap, hcomp, ← Ideal.comap_comap, hO, comap_originIdeal]`. Set `h : EA →+* (Polynomial A' ⊗[Polynomial A] EA)` to `(Algebra.TensorProduct.includeRight : EA →ₐ[Polynomial A] _).toRingHom`.

Establish `hh : ∀ x, F (h x) = jA (algebraMap EA (Localization.AtPrime QA) x)` using `fun x => by`. Express the relevant statement in the definitionally equal form `F (1 ⊗ₜ x) = _`. Rewrite using `[hF, map_one, one_mul]`. Both sides reduce to the same expression. Establish `hy : QA.primeCompl ≤ Q'.primeCompl.comap h`.

Introduce `x hx`. Establish `hu : IsUnit (jA (algebraMap EA (Localization.AtPrime QA) x))` using `(IsLocalization.map_units (Localization.AtPrime QA) (⟨x, hx⟩ : QA.primeCompl)).map jA`. Express the relevant statement in the definitionally equal form `h x ∉ Q'`. Introduce `hmem`. Establish `hmem' : F (h x) ∈ maximalIdeal O` using `hmem`.

Rewrite `hmem'` using `[hh]`. Conclude with `((mem_maximalIdeal _).mp hmem') hu`. Establish `hγ : ∀ y : Q'.primeCompl, IsUnit (F y)`. Introduce `y`. Assume the negation of the conclusion as `hc`.

Conclude with `y.2 ((mem_maximalIdeal _).mpr hc)`. Set `β : Localization.AtPrime QA →+* Localization.AtPrime Q'` to `IsLocalization.map (M := QA.primeCompl) (S := Localization.AtPrime QA) (Localization.AtPrime Q') (g := h) (T := Q'.primeCompl) hy`. Set `γ : Localization.AtPrime Q' →+* O` to `IsLocalization.lift (M := Q'.primeCompl) (S := Localization.AtPrime Q') (g := F) hγ`. Use `⟨β, γ, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `RingHom.ext fun a => ?_` and prove the remaining obligations.

Simplify using `only [RingHom.comp_apply]`. Rewrite using `[IsScalarTower.algebraMap_apply (Polynomial A) EA (Localization.AtPrime QA), IsScalarTower.algebraMap_apply (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA) (Localization.AtPrime Q')]`. Express the relevant statement in the definitionally equal form `_ = β (algebraMap EA (Localization.AtPrime QA) _)`. Rewrite using `[IsLocalization.map_eq]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `algebraMap (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA) (Polynomial.C (ι a)) = (1 : Polynomial A') ⊗ₜ algebraMap (Polynomial A) EA (Polynomial.C a)`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `_ = Polynomial.map ι (Polynomial.C a)`. Rewrite using `[Polynomial.map_C]`.

Both sides reduce to the same expression. Use `IsLocalization.ringHom_ext QA.primeCompl (RingHom.ext fun x => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`. Express the relevant statement in the definitionally equal form `γ (β (algebraMap EA (Localization.AtPrime QA) x)) = _`. Rewrite using `[IsLocalization.map_eq, IsLocalization.lift_eq, hh]`.

Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[IsScalarTower.algebraMap_apply (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA) (Localization.AtPrime Q'), IsLocalization.lift_eq, Algebra.TensorProduct.algebraMap_apply, hF, map_one, mul_one]`. Express the relevant statement in the definitionally equal form `algebraMap (Polynomial T) O (Polynomial.map α (Polynomial.C a)) = _`. Rewrite using `[Polynomial.map_C, IsScalarTower.algebraMap_apply T (Polynomial T) O]`.

Both sides reduce to the same expression.
-/
theorem localStage : ∀ (T O : Type) [CommRing T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T), IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (A' : Type) [CommRing A'] [IsLocalRing A'] (ι : A →+* A') (α : A' →+* T), α.comp ι = i → IsLocalHom α →
    ∃ (E' : Type) (_ : CommRing E') (_ : Algebra (Polynomial A') E') (_ : Algebra.Etale (Polynomial A') E')
      (Q' : Ideal E') (_ : Q'.IsPrime),
      Q'.comap (algebraMap (Polynomial A') E') = GlobalTheory.KeyOriginCut.originIdeal A' ∧
      ∃ (β : Localization.AtPrime QA →+* Localization.AtPrime Q') (γ : Localization.AtPrime Q' →+* O),
        ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).comp ι =
          β.comp ((algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C) ∧
        γ.comp β = jA ∧
        γ.comp ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C) =
          (algebraMap T O).comp α := by
  intro T O _ _ _ _ _ _ _ hO A _ _ i hi EA _ _ _ QA _ hQA jA hjA A' _ _ ι α hαι hα
  letI : Algebra (Polynomial A) (Polynomial A') := (Polynomial.mapRingHom ι).toAlgebra
  letI : Algebra (Polynomial A) O := ((algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i)).toAlgebra
  haveI : Algebra.Etale (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA) :=
    Algebra.Etale.baseChange (Polynomial A) EA (Polynomial A')
  let f : Polynomial A' →ₐ[Polynomial A] O :=
    { toRingHom := (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom α)
      commutes' := by
        intro p
        change (algebraMap (Polynomial T) O) (Polynomial.map α (Polynomial.map ι p)) =
          (algebraMap (Polynomial T) O) (Polynomial.map i p)
        rw [Polynomial.map_map, hαι] }
  let g : EA →ₐ[Polynomial A] O :=
    { toRingHom := jA.comp (algebraMap EA (Localization.AtPrime QA))
      commutes' := by
        intro p
        change jA (algebraMap EA (Localization.AtPrime QA) (algebraMap (Polynomial A) EA p)) =
          (algebraMap (Polynomial T) O) (Polynomial.map i p)
        rw [← IsScalarTower.algebraMap_apply]
        exact congrArg (fun h => h p) hjA }
  let F : (Polynomial A' ⊗[Polynomial A] EA) →+* O :=
    (Algebra.TensorProduct.productMap f g).toRingHom
  have hF : ∀ a b, F (a ⊗ₜ b) = f a * g b := fun a b => by
    simp [F, Algebra.TensorProduct.productMap_apply_tmul]
  let Q' : Ideal (Polynomial A' ⊗[Polynomial A] EA) := (maximalIdeal O).comap F
  refine ⟨Polynomial A' ⊗[Polynomial A] EA, inferInstance, inferInstance, inferInstance, Q',
    Ideal.comap_isPrime _ _, ?_, ?_⟩
  · have hcomp : F.comp (algebraMap (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom α) := by
      refine RingHom.ext fun p => ?_
      rw [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, hF, map_one, mul_one]
      rfl
    change ((maximalIdeal O).comap F).comap _ = _
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, hO, comap_originIdeal]
  let h : EA →+* (Polynomial A' ⊗[Polynomial A] EA) :=
    (Algebra.TensorProduct.includeRight : EA →ₐ[Polynomial A] _).toRingHom
  have hh : ∀ x, F (h x) = jA (algebraMap EA (Localization.AtPrime QA) x) := fun x => by
    change F (1 ⊗ₜ x) = _
    rw [hF, map_one, one_mul]
    rfl
  have hy : QA.primeCompl ≤ Q'.primeCompl.comap h := by
    intro x hx
    have hu : IsUnit (jA (algebraMap EA (Localization.AtPrime QA) x)) :=
      (IsLocalization.map_units (Localization.AtPrime QA) (⟨x, hx⟩ : QA.primeCompl)).map jA
    change h x ∉ Q'
    intro hmem
    have hmem' : F (h x) ∈ maximalIdeal O := hmem
    rw [hh] at hmem'
    exact ((mem_maximalIdeal _).mp hmem') hu
  have hγ : ∀ y : Q'.primeCompl, IsUnit (F y) := by
    intro y
    by_contra hc
    exact y.2 ((mem_maximalIdeal _).mpr hc)
  let β : Localization.AtPrime QA →+* Localization.AtPrime Q' :=
    IsLocalization.map (M := QA.primeCompl) (S := Localization.AtPrime QA) (Localization.AtPrime Q')
      (g := h) (T := Q'.primeCompl) hy
  let γ : Localization.AtPrime Q' →+* O :=
    IsLocalization.lift (M := Q'.primeCompl) (S := Localization.AtPrime Q') (g := F) hγ
  refine ⟨β, γ, ?_, ?_, ?_⟩
  · refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply (Polynomial A) EA (Localization.AtPrime QA),
      IsScalarTower.algebraMap_apply (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)
        (Localization.AtPrime Q')]
    change _ = β (algebraMap EA (Localization.AtPrime QA) _)
    rw [IsLocalization.map_eq]
    congr 1
    change algebraMap (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA) (Polynomial.C (ι a)) =
      (1 : Polynomial A') ⊗ₜ algebraMap (Polynomial A) EA (Polynomial.C a)
    rw [Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply',
      Algebra.TensorProduct.algebraMap_apply]
    congr 1
    change _ = Polynomial.map ι (Polynomial.C a)
    rw [Polynomial.map_C]
    rfl
  · refine IsLocalization.ringHom_ext QA.primeCompl (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply]
    change γ (β (algebraMap EA (Localization.AtPrime QA) x)) = _
    rw [IsLocalization.map_eq, IsLocalization.lift_eq, hh]
  · refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)
        (Localization.AtPrime Q'), IsLocalization.lift_eq, Algebra.TensorProduct.algebraMap_apply,
      hF, map_one, mul_one]
    change algebraMap (Polynomial T) O (Polynomial.map α (Polynomial.C a)) = _
    rw [Polynomial.map_C, IsScalarTower.algebraMap_apply T (Polynomial T) O]
    rfl

end GlobalTheory.LocalStage
