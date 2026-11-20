import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleHeightOneOfRegularLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralPi
open IsLocalRing

namespace GlobalTheory.PurityProd

/- English proof (translation)
Set `e : A ≃ₐ[A] Localization.AtPrime (maximalIdeal A)` to `IsLocalization.atUnits A (maximalIdeal A).primeCompl (fun x hx => by`. Simplify `IsLocalRing.notMem_maximalIdeal.mp hx)` using `[IsUnit.mem_submonoid_iff]`. Use `haveI : Algebra.Etale A (Localization.AtPrime (maximalIdeal A)) := Algebra.Etale.of_equiv e`. Use `haveI : Algebra.Etale A (TensorProduct A (Localization.AtPrime (maximalIdeal A)) B) := Algebra.Etale.comp A (Localization.AtPrime (maximalIdeal A)) _`. Set `f : TensorProduct A (Localization.AtPrime (maximalIdeal A)) B ≃ₐ[A] B` to `(Algebra.TensorProduct.congr e.symm AlgEquiv.refl).trans (Algebra.TensorProduct.lid A B)`.

Conclude with `Algebra.Etale.of_equiv f`.
-/
theorem etale_of_etale_atMaximal {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    (h : Algebra.Etale (Localization.AtPrime (maximalIdeal A))
      (TensorProduct A (Localization.AtPrime (maximalIdeal A)) B)) :
    Algebra.Etale A B := by
  let e : A ≃ₐ[A] Localization.AtPrime (maximalIdeal A) :=
    IsLocalization.atUnits A (maximalIdeal A).primeCompl (fun x hx => by
      simpa [IsUnit.mem_submonoid_iff] using IsLocalRing.notMem_maximalIdeal.mp hx)
  haveI : Algebra.Etale A (Localization.AtPrime (maximalIdeal A)) := Algebra.Etale.of_equiv e
  haveI : Algebra.Etale A (TensorProduct A (Localization.AtPrime (maximalIdeal A)) B) :=
    Algebra.Etale.comp A (Localization.AtPrime (maximalIdeal A)) _
  let f : TensorProduct A (Localization.AtPrime (maximalIdeal A)) B ≃ₐ[A] B :=
    (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).trans (Algebra.TensorProduct.lid A B)
  exact Algebra.Etale.of_equiv f

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IntegralPi.main`. Consider the case `exact _root_.GlobalTheory.IntegralPi.main`. Consider the case `(apply _root_.GlobalTheory.IntegralPi.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IntegralPi.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IntegralPi.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IntegralPi.main ..)`.
-/
theorem isIntegral_of_forall_apply {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x := by
  first
  | exact @_root_.GlobalTheory.IntegralPi.main
  | exact _root_.GlobalTheory.IntegralPi.main
  | (apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPi.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPi.main ..)

/- English proof (translation)
Assemble the required witnesses or components as `⟨(Algebra.FormallyEtale.pi_iff C).mp inferInstance i, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩`.
-/
theorem etale_of_etale_pi {R : Type} [CommRing R] [IsNoetherianRing R] {ι : Type} [Finite ι]
    (C : ι → Type) [∀ i, CommRing (C i)] [∀ i, Algebra R (C i)] [∀ i, Module.Finite R (C i)]
    (h : Algebra.Etale R (∀ i, C i)) (i : ι) : Algebra.Etale R (C i) :=
  ⟨(Algebra.FormallyEtale.pi_iff C).mp inferInstance i,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

end GlobalTheory.PurityProd

namespace GlobalTheory.PurityProd

/- English proof (translation)
Introduce `A E _ _ _ _ hred hart hnz hfin hq`. Distinguish the cases in `hm : (maximalIdeal A).height ≤ 1`. Conclude with `etale_of_etale_atMaximal (hq (maximalIdeal A) hm)`. Take `⟨hdom, hint⟩` from `GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing A`. Use `haveI := hdom`.

Use `haveI : Fintype (MaximalSpectrum E) := Fintype.ofFinite _`. Use `letI (I : MaximalSpectrum E) : Field (E ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal`. Set `F : MaximalSpectrum E → Type` to `fun I => E ⧸ I.asIdeal`. Set `ψ : E ≃ₐ[A] (∀ I, F I)` to `(IsArtinianRing.equivPi E).restrictScalars A`. Set `C : MaximalSpectrum E → Type` to `fun I => integralClosure A (F I)`.

Set `Ψ : integralClosure A E →ₐ[A] ∀ I, C I` to `AlgHom.pi fun I => ((Pi.evalAlgHom A F I).comp (ψ.toAlgHom.comp (integralClosure A E).val)).codRestrict (integralClosure A (F I)) fun x => x.2.map ((Pi.evalAlgHom A F I).comp ψ.toAlgHom)`. Establish `hΨ : Function.Bijective Ψ`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `ψ.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `I`. Conclude with `congrArg Subtype.val (congrFun hxy I)`. Introduce `l`. Use `⟨⟨ψ.symm fun I => (l I).1, ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `(isIntegral_of_forall_apply (fun I => ((l I : F I))) fun I => (l I).2).map ψ.symm.toAlgHom`. Use function extensionality and compare the values at `I`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `ψ (ψ.symm fun I => (l I).1) I = (l I).1`. Rewrite using `[AlgEquiv.apply_symm_apply]`.

Set `Φ : integralClosure A E ≃ₐ[A] ∀ I, C I` to `AlgEquiv.ofBijective Ψ hΨ`. Establish `hinjF : ∀ I, Function.Injective (algebraMap A (F I))`. Introduce `I`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`.

Establish `hne : ψ.symm (Pi.single I 1) ≠ 0`. Introduce `h0`. Use `congrArg ψ h0` as an intermediate fact. Rewrite `this` using `[AlgEquiv.apply_symm_apply, map_zero]`. Conclude with `one_ne_zero (by simpa using congrFun this I : (1 : F I) = 0)`.

Establish `h0 : a • ψ.symm (Pi.single I 1) = 0`. Apply `ψ.injective` to reduce the goal to its premises. Rewrite using `[map_smul, AlgEquiv.apply_symm_apply, map_zero]`. Use function extensionality and compare the values at `J`. Distinguish the cases in `hJ : J = I`.

Substitute `hJ` using the available equality. Simplify using `[Algebra.smul_def, ha]`. Simplify using `[hJ]`. Break down `smul_eq_zero.mp h0 with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd h hne`. Use `haveI hfaith : ∀ I, FaithfulSMul A (C I) := fun I => by`. Rewrite using `[faithfulSMul_iff_algebraMap_injective]`. Introduce `a b hab`. Apply `hinjF I` to reduce the goal to its premises.

Conclude with `congrArg Subtype.val hab`. Use `haveI hfC : ∀ I, FaithfulSMul (C I) (F I) := fun I => (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective`. Use `haveI hintC : ∀ I, IsIntegrallyClosed (C I) := fun I => IsIntegrallyClosed.of_isIntegrallyClosedIn (C I) (F I)`. Use `haveI hfinC : ∀ I, Module.Finite A (C I) := fun I => Module.Finite.of_surjective ((Pi.evalAlgHom A C I).toLinearMap.comp Φ.toLinearMap) (by`. Introduce `c`.

Take `⟨x, hx⟩` from `Φ.surjective (Pi.single I c)`. Conclude with `⟨x, by simp [hx]⟩)`. Use `haveI : ∀ I, Algebra.Etale A (C I) := by`. Introduce `I`. Establish `key` using `GlobalTheory.T.etale_of_etale_height_one_of_regularLocalRing A (C I)`.

Use `key ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `IsRegularLocalRing.spanFinrank_maximalIdeal`. Rewrite using `[← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]`. Conclude with `(le_of_lt (not_le.mp hm))` after adjusting the coercions. Introduce `hf`.

Apply `hm` to reduce the goal to its premises. Rewrite using `[(IsLocalRing.isField_iff_maximalIdeal_eq).mp hf, Ideal.height_bot]`. Conclude with `zero_le_one`. Introduce `p _ hp`. Establish `h1` using `hq p (le_of_eq hp)`.

Set `G : TensorProduct A (Localization.AtPrime p) (integralClosure A E) ≃ₐ[Localization.AtPrime p] ∀ J, TensorProduct A (Localization.AtPrime p) (C J)` to `(Algebra.TensorProduct.congr AlgEquiv.refl Φ).trans (Algebra.TensorProduct.piRight A (Localization.AtPrime p) (Localization.AtPrime p) C)`. Use `haveI : Algebra.Etale (Localization.AtPrime p) (∀ J, TensorProduct A (Localization.AtPrime p) (C J)) := Algebra.Etale.of_equiv G`. Conclude with `etale_of_etale_pi (fun J => TensorProduct A (Localization.AtPrime p) (C J)) this I`. Conclude with `Algebra.Etale.of_equiv Φ.symm`.
-/
theorem etale_integralClosure_of_isArtinianRing : ∀ (A E : Type) [CommRing A] [IsRegularLocalRing A]
    [CommRing E] [Algebra A E], IsReduced E → IsArtinianRing E → NoZeroSMulDivisors A E →
    Module.Finite A (integralClosure A E) →
    (∀ (q : Ideal A) [q.IsPrime], q.height ≤ 1 → Algebra.Etale (Localization.AtPrime q)
      (TensorProduct A (Localization.AtPrime q) (integralClosure A E))) →
    Algebra.Etale A (integralClosure A E) := by
  intro A E _ _ _ _ hred hart hnz hfin hq
  classical
  by_cases hm : (maximalIdeal A).height ≤ 1
  · exact etale_of_etale_atMaximal (hq (maximalIdeal A) hm)
  obtain ⟨hdom, hint⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing A
  haveI := hdom
  haveI : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  letI (I : MaximalSpectrum E) : Field (E ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  let F : MaximalSpectrum E → Type := fun I => E ⧸ I.asIdeal
  let ψ : E ≃ₐ[A] (∀ I, F I) := (IsArtinianRing.equivPi E).restrictScalars A
  let C : MaximalSpectrum E → Type := fun I => integralClosure A (F I)
  let Ψ : integralClosure A E →ₐ[A] ∀ I, C I := AlgHom.pi fun I =>
    ((Pi.evalAlgHom A F I).comp (ψ.toAlgHom.comp (integralClosure A E).val)).codRestrict
      (integralClosure A (F I)) fun x => x.2.map ((Pi.evalAlgHom A F I).comp ψ.toAlgHom)
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply ψ.injective
      funext I
      exact congrArg Subtype.val (congrFun hxy I)
    · intro l
      refine ⟨⟨ψ.symm fun I => (l I).1, ?_⟩, ?_⟩
      · exact (isIntegral_of_forall_apply (fun I => ((l I : F I))) fun I => (l I).2).map
          ψ.symm.toAlgHom
      · funext I
        apply Subtype.ext
        change ψ (ψ.symm fun I => (l I).1) I = (l I).1
        rw [AlgEquiv.apply_symm_apply]
  let Φ : integralClosure A E ≃ₐ[A] ∀ I, C I := AlgEquiv.ofBijective Ψ hΨ
  have hinjF : ∀ I, Function.Injective (algebraMap A (F I)) := by
    intro I
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hne : ψ.symm (Pi.single I 1) ≠ 0 := by
      intro h0
      have := congrArg ψ h0
      rw [AlgEquiv.apply_symm_apply, map_zero] at this
      exact one_ne_zero (by simpa using congrFun this I : (1 : F I) = 0)
    have h0 : a • ψ.symm (Pi.single I 1) = 0 := by
      apply ψ.injective
      rw [map_smul, AlgEquiv.apply_symm_apply, map_zero]
      funext J
      by_cases hJ : J = I
      · subst hJ; simp [Algebra.smul_def, ha]
      · simp [hJ]
    rcases smul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hne
  haveI hfaith : ∀ I, FaithfulSMul A (C I) := fun I => by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    apply hinjF I
    exact congrArg Subtype.val hab
  haveI hfC : ∀ I, FaithfulSMul (C I) (F I) := fun I =>
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  haveI hintC : ∀ I, IsIntegrallyClosed (C I) := fun I =>
    IsIntegrallyClosed.of_isIntegrallyClosedIn (C I) (F I)
  haveI hfinC : ∀ I, Module.Finite A (C I) := fun I =>
    Module.Finite.of_surjective ((Pi.evalAlgHom A C I).toLinearMap.comp Φ.toLinearMap) (by
      intro c
      obtain ⟨x, hx⟩ := Φ.surjective (Pi.single I c)
      exact ⟨x, by simp [hx]⟩)
  haveI : ∀ I, Algebra.Etale A (C I) := by
    intro I
    have key := GlobalTheory.T.etale_of_etale_height_one_of_regularLocalRing A (C I)
    refine key ?_ ?_ ?_ ?_
    · exact IsRegularLocalRing.spanFinrank_maximalIdeal
    · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
      exact_mod_cast (le_of_lt (not_le.mp hm))
    · intro hf
      apply hm
      rw [(IsLocalRing.isField_iff_maximalIdeal_eq).mp hf, Ideal.height_bot]
      exact zero_le_one
    · intro p _ hp
      have h1 := hq p (le_of_eq hp)
      let G : TensorProduct A (Localization.AtPrime p) (integralClosure A E) ≃ₐ[Localization.AtPrime p]
          ∀ J, TensorProduct A (Localization.AtPrime p) (C J) :=
        (Algebra.TensorProduct.congr AlgEquiv.refl Φ).trans
          (Algebra.TensorProduct.piRight A (Localization.AtPrime p) (Localization.AtPrime p) C)
      haveI : Algebra.Etale (Localization.AtPrime p)
          (∀ J, TensorProduct A (Localization.AtPrime p) (C J)) := Algebra.Etale.of_equiv G
      exact etale_of_etale_pi (fun J => TensorProduct A (Localization.AtPrime p) (C J)) this I
  exact Algebra.Etale.of_equiv Φ.symm

end GlobalTheory.PurityProd
