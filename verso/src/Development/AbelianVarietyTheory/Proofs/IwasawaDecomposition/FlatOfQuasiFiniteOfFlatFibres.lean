import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatOfIsFiniteOfFinitePresentationOfFlatGeometri

open TensorProduct

namespace GlobalTheory

namespace QuasiFiniteFibreFlat

/- English proof (translation)
Set `l` to `IsScalarTower.toAlgHom S T D`. Establish `hl : (l : T →+* D).Flat` using `RingHom.flat_algebraMap_iff.mpr inferInstance`. Establish `h1` using `(RingHom.flat_algebraMap_iff.mpr h).comp (RingHom.Flat.lTensor (S := S) C hl)`. Rewrite using `[← RingHom.flat_algebraMap_iff]`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `c`. Simplify using the standard rewrite rules.
-/
theorem flat_baseChange_trans (S C T D : Type) [CommRing S] [CommRing C] [CommRing T] [CommRing D]
    [Algebra S C] [Algebra S T] [Algebra S D] [Algebra T D] [IsScalarTower S T D]
    [Module.Flat T D] [h : Module.Flat C (C ⊗[S] T)] : Module.Flat C (C ⊗[S] D) := by
  let l := IsScalarTower.toAlgHom S T D
  have hl : (l : T →+* D).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have h1 := (RingHom.flat_algebraMap_iff.mpr h).comp (RingHom.Flat.lTensor (S := S) C hl)
  rw [← RingHom.flat_algebraMap_iff]
  convert h1 using 1
  ext c
  simp

/- English proof (translation)
Set `D` to `Localization.Away e`. Use `letI : Algebra R A' := ((algebraMap A A').comp (algebraMap R A)).toAlgebra`. Use `haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : Module.Flat (A' ⊗[A] B) D := IsLocalization.flat _ (Submonoid.powers e)`. Use `haveI : Algebra.FinitePresentation (A' ⊗[A] B) D := IsLocalization.Away.finitePresentation e`.

Use `haveI : Algebra.FinitePresentation A' D := .trans A' (A' ⊗[A] B) D`. Use `haveI : Module.FinitePresentation A' D := Module.FinitePresentation.of_finite_of_finitePresentation A' D`. Use `haveI : Module.Flat R D := by`. Establish `h1 : (algebraMap B (B ⊗[A] A')).Flat` using `RingHom.flat_algebraMap_iff.mpr inferInstance`. Establish `h2` using `h1.comp (g := (Algebra.TensorProduct.comm A B A' : B ⊗[A] A' →+* A' ⊗[A] B)) (.of_bijective (Algebra.TensorProduct.comm A B A').bijective)`.

Establish `h3` using `((RingHom.flat_algebraMap_iff.mpr hRB).comp h2).comp (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (A' ⊗[A] B) D))`. Rewrite using `[← RingHom.flat_algebraMap_iff]`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `r`. Rewrite using `[IsScalarTower.algebraMap_apply R A' D]`.

Express the relevant statement in the definitionally equal form `algebraMap A' D (algebraMap A A' (algebraMap R A r)) = algebraMap (A' ⊗[A] B) D (1 ⊗ₜ algebraMap R B r)`. Rewrite using `[IsScalarTower.algebraMap_apply A' (A' ⊗[A] B) D, IsScalarTower.algebraMap_apply R A B, Algebra.TensorProduct.algebraMap_apply]`. Use `congr 1`. Conclude with `Algebra.TensorProduct.tmul_one_eq_one_tmul _`. Use `FinitePresFibreFlat.flat_of_flat_fibres (R := R) (A := A') (B := D) fun k C _ _ _ t h w => ?_` and prove the remaining obligations.

Use `letI : Algebra A C := ((algebraMap A' C).comp (algebraMap A A')).toAlgebra`. Use `haveI : IsScalarTower A A' C := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI := H k C t h w`. Use `haveI : Module.Flat C (C ⊗[A'] (A' ⊗[A] B)) := Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange A A' C C B)`. Conclude with `flat_baseChange_trans A' C (A' ⊗[A] B) D`.
-/
theorem flat_away {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra.FinitePresentation A B]
    [hRB : Module.Flat R B]
    (H : ∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C),
      (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B))
    (A' : Type) [CommRing A'] [Algebra A A'] [Module.Flat A A'] (e : A' ⊗[A] B)
    [Module.Finite A' (Localization.Away e)] : Module.Flat A' (Localization.Away e) := by
  let D := Localization.Away e
  letI : Algebra R A' := ((algebraMap A A').comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Flat (A' ⊗[A] B) D := IsLocalization.flat _ (Submonoid.powers e)
  haveI : Algebra.FinitePresentation (A' ⊗[A] B) D := IsLocalization.Away.finitePresentation e
  haveI : Algebra.FinitePresentation A' D := .trans A' (A' ⊗[A] B) D
  haveI : Module.FinitePresentation A' D :=
    Module.FinitePresentation.of_finite_of_finitePresentation A' D
  haveI : Module.Flat R D := by
    have h1 : (algebraMap B (B ⊗[A] A')).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
    have h2 := h1.comp (g := (Algebra.TensorProduct.comm A B A' : B ⊗[A] A' →+* A' ⊗[A] B))
          (.of_bijective (Algebra.TensorProduct.comm A B A').bijective)
    have h3 := ((RingHom.flat_algebraMap_iff.mpr hRB).comp h2).comp
      (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (A' ⊗[A] B) D))
    rw [← RingHom.flat_algebraMap_iff]
    convert h3 using 1
    ext r
    rw [IsScalarTower.algebraMap_apply R A' D]
    change algebraMap A' D (algebraMap A A' (algebraMap R A r)) =
      algebraMap (A' ⊗[A] B) D (1 ⊗ₜ algebraMap R B r)
    rw [IsScalarTower.algebraMap_apply A' (A' ⊗[A] B) D, IsScalarTower.algebraMap_apply R A B,
      Algebra.TensorProduct.algebraMap_apply]
    congr 1
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul _
  refine FinitePresFibreFlat.flat_of_flat_fibres (R := R) (A := A') (B := D)
    fun k C _ _ _ t h w => ?_
  letI : Algebra A C := ((algebraMap A' C).comp (algebraMap A A')).toAlgebra
  haveI : IsScalarTower A A' C := IsScalarTower.of_algebraMap_eq' rfl
  haveI := H k C t h w
  haveI : Module.Flat C (C ⊗[A'] (A' ⊗[A] B)) :=
    Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange A A' C C B)
  exact flat_baseChange_trans A' C (A' ⊗[A] B) D

end QuasiFiniteFibreFlat

/- English proof (translation)
Introduce `R A B _ _ _ _ _ _ _ _ _ _ H`. Use `Module.flat_of_isLocalized_maximal B B (fun P ↦ Localization.AtPrime P) (fun P ↦ Algebra.linearMap B _) fun Q _ => ?_` and prove the remaining obligations. Take `⟨A', _, _, _, P, _, _, e, -, Q', _, _, hQ, he, -, hfin, -⟩` from `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (Q.under A) Q`. Set `T` to `A' ⊗[A] B`. Set `D` to `Localization.Away e`.

Establish `hD : Module.Flat A' D` using `QuasiFiniteFibreFlat.flat_away H A' e`. Set `i : B →+* T` to `Algebra.TensorProduct.includeRight.toRingHom`. Establish `hi : i.Flat`. Establish `h1 : (algebraMap B (B ⊗[A] A')).Flat` using `RingHom.flat_algebraMap_iff.mpr inferInstance`. Conclude with `h1.comp (g := (Algebra.TensorProduct.comm A B A' : B ⊗[A] A' →+* A' ⊗[A] B)) (.of_bijective (Algebra.TensorProduct.comm A B A').bijective)`.

Set `β` to `Localization.localRingHom Q Q' i hQ.symm`. Establish `hβ : β.Flat` using `RingHom.Flat.localRingHom hi Q' Q hQ.symm`. Establish `hle : Submonoid.powers e ≤ Q'.primeCompl`. Rewrite using `[Submonoid.powers_le]`. Conclude with `he`.

Use `letI : Algebra D (Localization.AtPrime Q') := IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle`. Use `haveI : IsScalarTower T D (Localization.AtPrime Q') := IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle`. Use `haveI := IsLocalization.isLocalization_of_submonoid_le D (Localization.AtPrime Q') _ _ hle`. Establish `hDQ : Module.Flat D (Localization.AtPrime Q')` using `IsLocalization.flat _ (Q'.primeCompl.map (algebraMap T D))`. Rewrite using `[← RingHom.flat_algebraMap_iff]`.

Use `ringHom_flat_of_square_of_isLocalHom (α := algebraMap A A') (β := β) (φ' := (algebraMap D (Localization.AtPrime Q')).comp (algebraMap A' D)) ?_ (RingHom.flat_algebraMap_iff.mpr inferInstance) hβ ((RingHom.flat_algebraMap_iff.mpr hD).comp (RingHom.flat_algebraMap_iff.mpr hDQ))` and prove the remaining obligations. Use extensionality with `a`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q), Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply A' T D, ← IsScalarTower.algebraMap_apply T D]`. Use `congr 1`.

Conclude with `Algebra.TensorProduct.tmul_one_eq_one_tmul a`.
-/
theorem flat_of_quasiFinite_of_flat_fibres :
    ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra.FinitePresentation A B] [Algebra.QuasiFinite A B] [Module.Flat R B], (∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C), (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) → Module.Flat A B := by
  intro R A B _ _ _ _ _ _ _ _ _ _ H
  refine Module.flat_of_isLocalized_maximal B B (fun P ↦ Localization.AtPrime P)
    (fun P ↦ Algebra.linearMap B _) fun Q _ => ?_
  obtain ⟨A', _, _, _, P, _, _, e, -, Q', _, _, hQ, he, -, hfin, -⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (Q.under A) Q
  let T := A' ⊗[A] B
  let D := Localization.Away e
  have hD : Module.Flat A' D := QuasiFiniteFibreFlat.flat_away H A' e
  let i : B →+* T := Algebra.TensorProduct.includeRight.toRingHom
  have hi : i.Flat := by
    have h1 : (algebraMap B (B ⊗[A] A')).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
    exact h1.comp (g := (Algebra.TensorProduct.comm A B A' : B ⊗[A] A' →+* A' ⊗[A] B))
          (.of_bijective (Algebra.TensorProduct.comm A B A').bijective)
  let β := Localization.localRingHom Q Q' i hQ.symm
  have hβ : β.Flat := RingHom.Flat.localRingHom hi Q' Q hQ.symm
  have hle : Submonoid.powers e ≤ Q'.primeCompl := by
    rw [Submonoid.powers_le]; exact he
  letI : Algebra D (Localization.AtPrime Q') :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle
  haveI : IsScalarTower T D (Localization.AtPrime Q') :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  haveI := IsLocalization.isLocalization_of_submonoid_le D (Localization.AtPrime Q') _ _ hle
  have hDQ : Module.Flat D (Localization.AtPrime Q') :=
    IsLocalization.flat _ (Q'.primeCompl.map (algebraMap T D))
  rw [← RingHom.flat_algebraMap_iff]
  refine ringHom_flat_of_square_of_isLocalHom (α := algebraMap A A') (β := β)
    (φ' := (algebraMap D (Localization.AtPrime Q')).comp (algebraMap A' D)) ?_
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hβ
    ((RingHom.flat_algebraMap_iff.mpr hD).comp (RingHom.flat_algebraMap_iff.mpr hDQ))
  ext a
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q), Localization.localRingHom_to_map,
    IsScalarTower.algebraMap_apply A' T D, ← IsScalarTower.algebraMap_apply T D]
  congr 1
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul a

end GlobalTheory
