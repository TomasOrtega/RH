import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportQuotientIff
open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory.SupportBC

/- English proof (translation)
Use `letI : Algebra p.ResidueField q.ResidueField := (Ideal.ResidueField.map p q (algebraMap R S) hpq).toAlgebra`. Use `haveI : IsScalarTower R p.ResidueField q.ResidueField := .of_algebraMap_eq fun r => (IsScalarTower.algebraMap_apply R S q.ResidueField r).trans (Ideal.ResidueField.map_algebraMap _ _ _ hpq r).symm`. Establish `e₁ : q.ResidueField ⊗[S] N ≃ₗ[S] q.ResidueField ⊗[S] (S ⊗[R] M)` using `LinearEquiv.lTensor q.ResidueField hl.equiv.symm`. Establish `e₂ : q.ResidueField ⊗[S] (S ⊗[R] M) ≃ₗ[q.ResidueField] q.ResidueField ⊗[R] M` using `AlgebraTensorModule.cancelBaseChange R S q.ResidueField q.ResidueField M`. Establish `e₃ : q.ResidueField ⊗[p.ResidueField] (p.ResidueField ⊗[R] M) ≃ₗ[q.ResidueField] q.ResidueField ⊗[R] M` using `AlgebraTensorModule.cancelBaseChange R p.ResidueField q.ResidueField q.ResidueField M`.

Rewrite using `[e₁.toEquiv.nontrivial_congr, e₂.toEquiv.nontrivial_congr, ← e₃.toEquiv.nontrivial_congr]`. Conclude with `Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right p.ResidueField q.ResidueField`.
-/
theorem nontrivial_fibre_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S)) :
    Nontrivial (q.ResidueField ⊗[S] N) ↔ Nontrivial (p.ResidueField ⊗[R] M) := by
  letI : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap R S) hpq).toAlgebra
  haveI : IsScalarTower R p.ResidueField q.ResidueField :=
    .of_algebraMap_eq fun r =>
      (IsScalarTower.algebraMap_apply R S q.ResidueField r).trans
        (Ideal.ResidueField.map_algebraMap _ _ _ hpq r).symm
  have e₁ : q.ResidueField ⊗[S] N ≃ₗ[S] q.ResidueField ⊗[S] (S ⊗[R] M) :=
    LinearEquiv.lTensor q.ResidueField hl.equiv.symm
  have e₂ : q.ResidueField ⊗[S] (S ⊗[R] M) ≃ₗ[q.ResidueField] q.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R S q.ResidueField q.ResidueField M
  have e₃ : q.ResidueField ⊗[p.ResidueField] (p.ResidueField ⊗[R] M) ≃ₗ[q.ResidueField]
      q.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R p.ResidueField q.ResidueField q.ResidueField M
  rw [e₁.toEquiv.nontrivial_congr, e₂.toEquiv.nontrivial_congr, ← e₃.toEquiv.nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right p.ResidueField q.ResidueField

/- English proof (translation)
Use `haveI : Module.Finite S N := Module.Finite.equiv hl.equiv`. Rewrite using `[Module.mem_support_iff_nontrivial_residueField_tensorProduct, Module.mem_support_iff_nontrivial_residueField_tensorProduct]`. Conclude with `nontrivial_fibre_iff hl _ _ rfl`.
-/
theorem mem_support_iff_of_isBaseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (q : PrimeSpectrum S) :
    q ∈ Module.support S N ↔ PrimeSpectrum.comap (algebraMap R S) q ∈ Module.support R M := by
  haveI : Module.Finite S N := Module.Finite.equiv hl.equiv
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  exact nontrivial_fibre_iff hl _ _ rfl

/- English proof (translation)
Use `set P := Submodule.span R (Set.range s)`. Use `set P' := Submodule.span R' (Set.range fun i => algebraMap S S' (s i))`. Set `h₂ : S →ₗ[R] S'` to `(IsScalarTower.toAlgHom R S S').toLinearMap`. Establish `isb₂ : IsBaseChange R' h₂` using `Algebra.IsPushout.out`. Set `h₁ : (ι →₀ R) →ₗ[R] (ι →₀ R')` to `Finsupp.mapRange.linearMap (Algebra.linearMap R R')`.

Establish `isb₁ : IsBaseChange R' h₁` using `IsBaseChange.finsuppPow ι (IsBaseChange.linearMap R R')`. Establish `hle : P ≤ LinearMap.ker ((P'.mkQ.restrictScalars R).comp h₂)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Set `h₃` to `P.liftQ ((P'.mkQ.restrictScalars R).comp h₂) hle`. Use `⟨h₃, IsBaseChange.of_right_exact R' h₁ h₂ h₃ (f := Finsupp.linearCombination R s) (g := P.mkQ) (f' := Finsupp.linearCombination R' fun i => algebraMap S S' (s i)) (g' := P'.mkQ) ?_ ?_ isb₁ isb₂ ?_ (Submodule.mkQ_surjective P) ?_ (Submodule.mkQ_surjective P')⟩` and prove the remaining obligations. Use `Finsupp.lhom_ext fun i r => ?_` and prove the remaining obligations. Simplify using `only [h₁, h₂, LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.linearCombination_single, LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', Algebra.linearMap_apply, Algebra.smul_def, map_mul]`.

Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Conclude with `P.liftQ_mkQ _ hle`. Rewrite using `[LinearMap.exact_iff, Submodule.ker_mkQ, Finsupp.range_linearCombination]`. Rewrite using `[LinearMap.exact_iff, Submodule.ker_mkQ, Finsupp.range_linearCombination]`.
-/
theorem isBaseChange_quotient_span {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R R' S S']
    {ι : Type*} (s : ι → S) :
    ∃ l : (S ⧸ Submodule.span R (Set.range s)) →ₗ[R]
        (S' ⧸ Submodule.span R' (Set.range fun i => algebraMap S S' (s i))), IsBaseChange R' l := by
  classical
  set P := Submodule.span R (Set.range s)
  set P' := Submodule.span R' (Set.range fun i => algebraMap S S' (s i))
  let h₂ : S →ₗ[R] S' := (IsScalarTower.toAlgHom R S S').toLinearMap
  have isb₂ : IsBaseChange R' h₂ := Algebra.IsPushout.out
  let h₁ : (ι →₀ R) →ₗ[R] (ι →₀ R') := Finsupp.mapRange.linearMap (Algebra.linearMap R R')
  have isb₁ : IsBaseChange R' h₁ := IsBaseChange.finsuppPow ι (IsBaseChange.linearMap R R')
  have hle : P ≤ LinearMap.ker ((P'.mkQ.restrictScalars R).comp h₂) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨i, rfl⟩
  let h₃ := P.liftQ ((P'.mkQ.restrictScalars R).comp h₂) hle
  refine ⟨h₃, IsBaseChange.of_right_exact R' h₁ h₂ h₃
    (f := Finsupp.linearCombination R s) (g := P.mkQ)
    (f' := Finsupp.linearCombination R' fun i => algebraMap S S' (s i)) (g' := P'.mkQ)
    ?_ ?_ isb₁ isb₂ ?_ (Submodule.mkQ_surjective P) ?_ (Submodule.mkQ_surjective P')⟩
  · refine Finsupp.lhom_ext fun i r => ?_
    simp only [h₁, h₂, LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, Finsupp.linearCombination_single, LinearMap.restrictScalars_apply,
      AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', Algebra.linearMap_apply,
      Algebra.smul_def, map_mul]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  · exact P.liftQ_mkQ _ hle
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ, Finsupp.range_linearCombination]
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ, Finsupp.range_linearCombination]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff`. Consider the case `exact _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff`. Consider the case `(apply _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff ..)`.
-/
theorem mem_support_quotient_span_iff_of_isPushout :
    ∀ (R S R' S' : CommRingCat.{0}) (qa : R ⟶ S) (ba : R ⟶ R') (ga : S ⟶ S') (qa' : R' ⟶ S'),
      IsPushout qa ba ga qa' → qa.hom.Finite → ∀ {ι : Type} (s : ι → S) (p : PrimeSpectrum R'),
      ((letI := qa'.hom.toAlgebra;
        p ∈ Module.support R' (S' ⧸ Submodule.span R' (Set.range (fun i => ga.hom (s i))))) ↔
      (letI := qa.hom.toAlgebra;
        PrimeSpectrum.comap ba.hom p ∈ Module.support R (S ⧸ Submodule.span R (Set.range s)))) := by
  first
  | exact @_root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff
  | exact _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff
  | (apply _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff ..)

end GlobalTheory.SupportBC
