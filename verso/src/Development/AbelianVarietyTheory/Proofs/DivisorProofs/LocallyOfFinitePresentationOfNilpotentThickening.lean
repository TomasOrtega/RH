import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

open scoped TensorProduct

namespace GlobalTheory

open Algebra in
/- English proof (translation)
Use `set J := I.map (algebraMap P A)`. Take `⟨s, hs⟩` from `h.out`. Set `t : Finset A` to `s.image (fun x => Quotient.out x)`. Establish `hmk : (Ideal.Quotient.mkₐ P J) '' (t : Set A) = (s : Set (A ⧸ J))`. Use extensionality with `x`.

Simplify using `[t]`. Set `C` to `Algebra.adjoin P (t : Set A)`. Establish `key : ∀ b : A, ∃ c ∈ C, b - c ∈ J`. Introduce `b`. Establish `hb : Ideal.Quotient.mkₐ P J b ∈ (C.map (Ideal.Quotient.mkₐ P J))`.

Rewrite using `[AlgHom.map_adjoin, hmk, hs]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨c, hc, hcb⟩` from `hb`. Conclude with `⟨c, hc, Ideal.Quotient.eq.mp (by simpa using hcb.symm)⟩`. Establish `base : (⊤ : Submodule P A) ≤ Subalgebra.toSubmodule C ⊔ I • ⊤`.

Introduce `b _`. Take `⟨c, hc, hbc⟩` from `key b`. Establish `: b - c ∈ I • (⊤ : Submodule P A)`. Rewrite using `[Ideal.smul_top_eq_map]`. Conclude with `hbc`.

Use `Submodule.add_mem_sup (show c ∈ Subalgebra.toSubmodule C from hc) this` as an intermediate fact. Simplify using `using this`. Establish `step : ∀ n : ℕ, (⊤ : Submodule P A) ≤ Subalgebra.toSubmodule C ⊔ (I ^ n) • ⊤`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `b _`. Conclude with `Submodule.mem_sup_right (by rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; trivial)`. Consider the case `succ n ih`. Use `ih.trans (sup_le le_sup_left ?_)` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_succ, Submodule.mul_smul]`. Conclude with `sup_le_sup_right Submodule.smul_le_right _`. Take `⟨N, hN⟩` from `hI`. Establish `hC : Subalgebra.toSubmodule C = ⊤`.

Use `step N` as an intermediate fact. Rewrite `this` using `[hN, Submodule.zero_eq_bot, Submodule.bot_smul, sup_bot_eq]`. Conclude with `top_le_iff.mp this`. Conclude with `⟨⟨t, Algebra.toSubmodule_eq_top.mp hC⟩⟩`.
-/
theorem finiteType_of_finiteType_quotient_map_nilpotent {P A : Type} [CommRing P] [CommRing A]
    [Algebra P A] (I : Ideal P) (hI : IsNilpotent I)
    [h : Algebra.FiniteType P (A ⧸ I.map (algebraMap P A))] : Algebra.FiniteType P A := by
  set J := I.map (algebraMap P A)
  obtain ⟨s, hs⟩ := h.out
  classical
  let t : Finset A := s.image (fun x => Quotient.out x)
  have hmk : (Ideal.Quotient.mkₐ P J) '' (t : Set A) = (s : Set (A ⧸ J)) := by
    ext x; simp [t]
  let C := Algebra.adjoin P (t : Set A)
  have key : ∀ b : A, ∃ c ∈ C, b - c ∈ J := by
    intro b
    have hb : Ideal.Quotient.mkₐ P J b ∈ (C.map (Ideal.Quotient.mkₐ P J)) := by
      rw [AlgHom.map_adjoin, hmk, hs]; trivial
    obtain ⟨c, hc, hcb⟩ := hb
    exact ⟨c, hc, Ideal.Quotient.eq.mp (by simpa using hcb.symm)⟩
  have base : (⊤ : Submodule P A) ≤ Subalgebra.toSubmodule C ⊔ I • ⊤ := by
    intro b _
    obtain ⟨c, hc, hbc⟩ := key b
    have : b - c ∈ I • (⊤ : Submodule P A) := by
      rw [Ideal.smul_top_eq_map]; exact hbc
    have := Submodule.add_mem_sup (show c ∈ Subalgebra.toSubmodule C from hc) this
    simpa using this
  have step : ∀ n : ℕ, (⊤ : Submodule P A) ≤ Subalgebra.toSubmodule C ⊔ (I ^ n) • ⊤ := by
    intro n
    induction n with
    | zero =>
      intro b _
      exact Submodule.mem_sup_right (by rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; trivial)
    | succ n ih =>
      refine ih.trans (sup_le le_sup_left ?_)
      calc (I ^ n) • (⊤ : Submodule P A) ≤ (I ^ n) • (Subalgebra.toSubmodule C ⊔ I • ⊤) :=
            Submodule.smul_mono le_rfl base
        _ = (I ^ n) • Subalgebra.toSubmodule C ⊔ (I ^ n) • (I • ⊤) := Submodule.smul_sup _ _ _
        _ ≤ Subalgebra.toSubmodule C ⊔ (I ^ (n + 1)) • ⊤ := by
            rw [pow_succ, Submodule.mul_smul]
            exact sup_le_sup_right Submodule.smul_le_right _
  obtain ⟨N, hN⟩ := hI
  have hC : Subalgebra.toSubmodule C = ⊤ := by
    have := step N
    rw [hN, Submodule.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
    exact top_le_iff.mp this
  exact ⟨⟨t, Algebra.toSubmodule_eq_top.mp hC⟩⟩

/- English proof (translation)
Establish `h1 : Algebra.FiniteType P (A ⊗[P] R)`. Rewrite using `[← RingHom.finiteType_algebraMap, ← (Algebra.TensorProduct.includeRight : R →ₐ[P] A ⊗[P] R).comp_algebraMap]`. Conclude with `h.comp (RingHom.FiniteType.of_surjective _ hs)`. Set `f : P →ₐ[P] R` to `Algebra.ofId P R`. Establish `hf : Function.Surjective f` using `hs`.

Set `I : Ideal P` to `RingHom.ker f`. Set `e1 : (A ⧸ I.map (algebraMap P A)) ≃ₐ[P] A ⊗[P] (P ⧸ I)` to `(Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).restrictScalars P`. Set `e2 : A ⊗[P] (P ⧸ I) ≃ₐ[P] A ⊗[P] R` to `Algebra.TensorProduct.congr AlgEquiv.refl (Ideal.quotientKerAlgEquivOfSurjective hf)`. Establish `h2 : Algebra.FiniteType P (A ⧸ I.map (algebraMap P A))` using `h1.equiv (e1.trans e2).symm`. Conclude with `finiteType_of_finiteType_quotient_map_nilpotent I hn`.
-/
theorem finiteType_of_finiteType_tensor_nilpotent {P A R : Type} [CommRing P] [CommRing A]
    [CommRing R] [Algebra P A] [Algebra P R] (hs : Function.Surjective (algebraMap P R))
    (hn : IsNilpotent (RingHom.ker (algebraMap P R)))
    (h : (Algebra.TensorProduct.includeRight : R →ₐ[P] A ⊗[P] R).toRingHom.FiniteType) :
    Algebra.FiniteType P A := by
  have h1 : Algebra.FiniteType P (A ⊗[P] R) := by
    rw [← RingHom.finiteType_algebraMap,
      ← (Algebra.TensorProduct.includeRight : R →ₐ[P] A ⊗[P] R).comp_algebraMap]
    exact h.comp (RingHom.FiniteType.of_surjective _ hs)
  let f : P →ₐ[P] R := Algebra.ofId P R
  have hf : Function.Surjective f := hs
  let I : Ideal P := RingHom.ker f
  let e1 : (A ⧸ I.map (algebraMap P A)) ≃ₐ[P] A ⊗[P] (P ⧸ I) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).restrictScalars P
  let e2 : A ⊗[P] (P ⧸ I) ≃ₐ[P] A ⊗[P] R :=
    Algebra.TensorProduct.congr AlgEquiv.refl (Ideal.quotientKerAlgEquivOfSurjective hf)
  have h2 : Algebra.FiniteType P (A ⧸ I.map (algebraMap P A)) := h1.equiv (e1.trans e2).symm
  exact finiteType_of_finiteType_quotient_map_nilpotent I hn

/- English proof (translation)
Establish `h1 : LocallyOfFinitePresentation (pullback.snd (Spec.map φ) (Spec.map f₁))`. Establish `e : pullback.snd (Spec.map φ) (Spec.map f₁) = hsq.isoPullback.inv ≫ snd`. Rewrite using `[Iso.eq_inv_comp, hsq.isoPullback_hom_snd]`. Rewrite using `[e]`. Conclude with `MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) hsnd`.

Use `letI := φ.hom.toAlgebra`. Use `letI := f₁.hom.toAlgebra`. Establish `hT : LocallyOfFinitePresentation ((pullbackSpecIso P A R₁).inv ≫ pullback.snd _ _)` using `MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) h1`. Rewrite `hT` using `[pullbackSpecIso_inv_snd, LocallyOfFinitePresentation.SpecMap_iff]`. Rewrite using `[LocallyOfFinitePresentation.SpecMap_iff, ← RingHom.FinitePresentation.of_finiteType]`.

Conclude with `finiteType_of_finiteType_tensor_nilpotent (A := A) hs hn (RingHom.FiniteType.of_finitePresentation hT)`.
-/
theorem locallyOfFinitePresentation_specMap_of_isPullback_nilpotent {P R₁ A : CommRingCat.{0}}
    (f₁ : P ⟶ R₁) (hs : Function.Surjective f₁) (hn : IsNilpotent (RingHom.ker f₁.hom))
    [IsNoetherianRing P] (φ : P ⟶ A) {W : Scheme.{0}} (fst : W ⟶ Spec A) (snd : W ⟶ Spec R₁)
    (hsq : IsPullback fst snd (Spec.map φ) (Spec.map f₁)) (hsnd : LocallyOfFinitePresentation snd) :
    LocallyOfFinitePresentation (Spec.map φ) := by
  have h1 : LocallyOfFinitePresentation (pullback.snd (Spec.map φ) (Spec.map f₁)) := by
    have e : pullback.snd (Spec.map φ) (Spec.map f₁) = hsq.isoPullback.inv ≫ snd := by
      rw [Iso.eq_inv_comp, hsq.isoPullback_hom_snd]
    rw [e]
    exact MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) hsnd
  letI := φ.hom.toAlgebra
  letI := f₁.hom.toAlgebra
  have hT : LocallyOfFinitePresentation ((pullbackSpecIso P A R₁).inv ≫ pullback.snd _ _) :=
    MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) h1
  rw [pullbackSpecIso_inv_snd, LocallyOfFinitePresentation.SpecMap_iff] at hT
  rw [LocallyOfFinitePresentation.SpecMap_iff, ← RingHom.FinitePresentation.of_finiteType]
  exact finiteType_of_finiteType_tensor_nilpotent (A := A) hs hn (RingHom.FiniteType.of_finitePresentation hT)

/- English proof (translation)
Introduce `P R₁ f₁ hs hn hP Y Y₁ j₁ hpb hY₁`. Use `haveI : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{0} := HasRingHomProperty.instIsZariskiLocalAtSource`. Rewrite using `[IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation.{0}) Y.left.affineOpenCover.openCover]`. Introduce `i`. Use `haveI : IsOpenImmersion (Y.left.affineOpenCover.f i) := inferInstanceAs (IsOpenImmersion (Y.left.affineOpenCover.openCover.f i))`.

Take `⟨φ, hφ⟩` from `Spec.map_surjective (Y.left.affineOpenCover.f i ≫ Y.hom)`. Establish `hsq : IsPullback (pullback.fst (Y.left.affineOpenCover.f i) j₁) (pullback.snd (Y.left.affineOpenCover.f i) j₁ ≫ Y₁.hom) (Spec.map φ) (Spec.map f₁)`. Rewrite using `[hφ]`. Conclude with `(IsPullback.of_hasPullback (Y.left.affineOpenCover.f i) j₁).paste_vert hpb`. Establish `hfin` using `GlobalTheory.locallyOfFinitePresentation_specMap_of_isPullback_nilpotent f₁ hs hn φ _ _ hsq (MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) hY₁)`.

Rewrite `hfin` using `[hφ]`. Conclude with `hfin`.
-/
theorem locallyOfFinitePresentation_of_nilpotent_thickening :
    ∀ (P R₁ : CommRingCat.{0}) (f₁ : P ⟶ R₁), Function.Surjective f₁ → IsNilpotent (RingHom.ker f₁.hom) → IsNoetherianRing P → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (j₁ : Y₁.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → LocallyOfFinitePresentation Y₁.hom → LocallyOfFinitePresentation Y.hom := by
  intro P R₁ f₁ hs hn hP Y Y₁ j₁ hpb hY₁
  haveI : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation.{0})
    Y.left.affineOpenCover.openCover]
  intro i
  haveI : IsOpenImmersion (Y.left.affineOpenCover.f i) :=
    inferInstanceAs (IsOpenImmersion (Y.left.affineOpenCover.openCover.f i))
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Y.left.affineOpenCover.f i ≫ Y.hom)
  have hsq : IsPullback (pullback.fst (Y.left.affineOpenCover.f i) j₁)
      (pullback.snd (Y.left.affineOpenCover.f i) j₁ ≫ Y₁.hom) (Spec.map φ) (Spec.map f₁) := by
    rw [hφ]; exact (IsPullback.of_hasPullback (Y.left.affineOpenCover.f i) j₁).paste_vert hpb
  have hfin := GlobalTheory.locallyOfFinitePresentation_specMap_of_isPullback_nilpotent f₁ hs hn φ _ _ hsq
    (MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) hY₁)
  rw [hφ] at hfin
  exact hfin

end GlobalTheory
