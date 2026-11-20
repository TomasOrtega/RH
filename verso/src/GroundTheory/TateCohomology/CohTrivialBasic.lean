import Mathlib
import GroundTheory.TateCohomology.DimensionShift
import GroundTheory.TateCohomology.InducedNorm
import GroundTheory.TateCohomology.CoindOne
import GroundTheory.TateCohomology.UniquelyDivisible
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep
open scoped MonoidAlgebra

universe u

section Def

variable {k G : Type u} [CommRing k] [Group G]

def CohTrivial (A : Rep.{u} k G) : Prop :=
  ∀ (S : Subgroup G) [Fintype S], TateAcyclic (res S.subtype A)

/- English proof (translation)
Introduce `S _` and use `(hN S).of_retract ((resFunctor S.subtype).map i) ((resFunctor S.subtype).map r) (by rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id])`.
-/
theorem CohTrivial.of_retract {M N : Rep.{u} k G} (i : M ⟶ N) (r : N ⟶ M) (h : i ≫ r = 𝟙 M)
    (hN : CohTrivial N) : CohTrivial M := fun S _ =>
  (hN S).of_retract ((resFunctor S.subtype).map i) ((resFunctor S.subtype).map r)
    (by rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id])

/- English proof (translation)
The claim follows from `hN.of_retract e.hom e.inv e.hom_inv_id`.
-/
theorem CohTrivial.of_iso {M N : Rep.{u} k G} (e : M ≅ N) (hN : CohTrivial N) : CohTrivial M :=
  hN.of_retract e.hom e.inv e.hom_inv_id

end Def

section Norm

variable {k G : Type u} [CommRing k] [Group G]

/- English proof (translation)
Set `e : (G ⧸ S) × S ≃ G` to `{ toFun := fun x => x.1.out * x.2 invFun := fun g => ((g : G ⧸ S), cosetPart S g) left_inv := fun x => by`. Take `⟨c, s⟩` from `x`. Use `ext`. Conclude with `mk_out_mul S c s`. Simplify using `only [cosetPart_out_mul]`.

Use `right_inv := fun g => out_mul_cosetPart S g }`. Rewrite using `[← Fintype.sum_prod_type']`. Conclude with `(Fintype.sum_equiv e _ _ fun _ => rfl).symm`.
-/
theorem sum_eq_sum_quotient_sum [Fintype G] (S : Subgroup G) [Fintype S] [Fintype (G ⧸ S)]
    {β : Type*} [AddCommMonoid β] (f : G → β) :
    ∑ g : G, f g = ∑ c : G ⧸ S, ∑ s : S, f (c.out * s) := by
  let e : (G ⧸ S) × S ≃ G :=
    { toFun := fun x => x.1.out * x.2
      invFun := fun g => ((g : G ⧸ S), cosetPart S g)
      left_inv := fun x => by
        obtain ⟨c, s⟩ := x
        ext
        · exact mk_out_mul S c s
        · simp only [cosetPart_out_mul]
      right_inv := fun g => out_mul_cosetPart S g }
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm

variable {V : Type*} [AddCommGroup V] [Module k V]

/- English proof (translation)
Use `⟨∑ c : G ⧸ S, ρ c.out⁻¹ ∘ₗ φ ∘ₗ ρ c.out, fun v => ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← hφ v]`. Rewrite using `[← Fintype.sum_equiv (Equiv.inv G) (fun h => ρ h⁻¹ (φ (ρ h v))) _ (fun h => by simp), sum_eq_sum_quotient_sum S, Finset.sum_comm]`. Use `Fintype.sum_equiv (Equiv.inv S) _ _ fun s => ?_` and prove the remaining obligations. Simplify using `[map_sum, LinearMap.sum_apply, map_mul, mul_inv_rev, Module.End.mul_apply]`.
-/
theorem exists_sum_eq_subgroup [Fintype G] (ρ : Representation k G V) (φ : V →ₗ[k] V)
    (hφ : ∀ v, ∑ g : G, ρ g (φ (ρ g⁻¹ v)) = v) (S : Subgroup G) [Fintype S] :
    ∃ ψ : V →ₗ[k] V, ∀ v, ∑ s : S, ρ s (ψ (ρ (s⁻¹ : S) v)) = v := by
  classical
  refine ⟨∑ c : G ⧸ S, ρ c.out⁻¹ ∘ₗ φ ∘ₗ ρ c.out, fun v => ?_⟩
  conv_rhs => rw [← hφ v]
  rw [← Fintype.sum_equiv (Equiv.inv G) (fun h => ρ h⁻¹ (φ (ρ h v))) _ (fun h => by simp),
    sum_eq_sum_quotient_sum S, Finset.sum_comm]
  refine Fintype.sum_equiv (Equiv.inv S) _ _ fun s => ?_
  simp [map_sum, LinearMap.sum_apply, map_mul, mul_inv_rev, Module.End.mul_apply]

/- English proof (translation)
Introduce `S _` and use `by obtain ⟨ψ, hψ⟩ := exists_sum_eq_subgroup M.ρ φ hφ S exact tateAcyclic_of_sum_eq (res S.subtype M) ψ hψ`.
-/
theorem cohTrivial_of_sum_eq [Fintype G] (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) : CohTrivial M := fun S _ => by
  obtain ⟨ψ, hψ⟩ := exists_sum_eq_subgroup M.ρ φ hφ S
  exact tateAcyclic_of_sum_eq (res S.subtype M) ψ hψ

variable [Fintype G]

/- English proof (translation)
The claim follows from `cohTrivial_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)`.
-/
theorem cohTrivial_coind_bot (B : Rep.{u} k (⊥ : Subgroup G)) :
    CohTrivial (coind (⊥ : Subgroup G).subtype B) :=
  cohTrivial_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)

/- English proof (translation)
Conclude with `(cohTrivial_coind_bot B).of_iso (indCoindIso B)`.
-/
theorem cohTrivial_ind_bot (B : Rep.{u} k (⊥ : Subgroup G)) :
    CohTrivial (ind (⊥ : Subgroup G).subtype B) := by
  classical
  exact (cohTrivial_coind_bot B).of_iso (indCoindIso B)

/- English proof (translation)
Set `φ : M.V →ₗ[k] M.V` to `M.ρ.asModuleEquiv.toLinearMap ∘ₗ (b.repr.symm.toLinearMap.restrictScalars k) ∘ₗ Finsupp.mapRange.linearMap coeffOneProj ∘ₗ (b.repr.toLinearMap.restrictScalars k) ∘ₗ M.ρ.asModuleEquiv.symm.toLinearMap`. Use `⟨φ, fun m => ?_⟩` and prove the remaining obligations. Apply `M.ρ.asModuleEquiv.symm.injective` to reduce the goal to its premises. Apply `b.repr.injective` to reduce the goal to its premises. Simplify using `only [map_sum, φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars, Representation.asModuleEquiv_symm_map_rho, map_smul, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]`.

Generalize the expression as in `b.repr (M.ρ.asModuleEquiv.symm m) = c`. Use extensionality with `i : 1`. Simplify using `only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, coeffOneProj_apply, smul_eq_mul, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.single_mul_single, mul_one, one_mul, inv_inv]`. Use `conv_rhs => rw [← MonoidAlgebra.sum_coeff_single (c i)]`. Conclude with `(Finsupp.sum_fintype _ _ (by simp)).symm`.
-/
theorem exists_sum_eq_of_basis (M : Rep.{u} k G) {ι : Type*}
    (b : Module.Basis ι k[G] M.ρ.asModule) :
    ∃ φ : M.V →ₗ[k] M.V, ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m := by
  let φ : M.V →ₗ[k] M.V := M.ρ.asModuleEquiv.toLinearMap ∘ₗ
    (b.repr.symm.toLinearMap.restrictScalars k) ∘ₗ Finsupp.mapRange.linearMap coeffOneProj ∘ₗ
    (b.repr.toLinearMap.restrictScalars k) ∘ₗ M.ρ.asModuleEquiv.symm.toLinearMap
  refine ⟨φ, fun m => ?_⟩
  apply M.ρ.asModuleEquiv.symm.injective
  apply b.repr.injective
  simp only [map_sum, φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars,
    Representation.asModuleEquiv_symm_map_rho, map_smul, LinearEquiv.symm_apply_apply,
    LinearEquiv.apply_symm_apply]
  generalize b.repr (M.ρ.asModuleEquiv.symm m) = c
  ext i : 1
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, coeffOneProj_apply, smul_eq_mul,
    MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.single_mul_single,
    mul_one, one_mul, inv_inv]
  conv_rhs => rw [← MonoidAlgebra.sum_coeff_single (c i)]
  exact (Finsupp.sum_fintype _ _ (by simp)).symm

/- English proof (translation)
Take `⟨φ, hφ⟩` from `exists_sum_eq_of_basis M (Module.Free.chooseBasis k[G] M.ρ.asModule)`. Conclude with `cohTrivial_of_sum_eq M φ hφ`.
-/
theorem cohTrivial_of_free (M : Rep.{u} k G) [Module.Free k[G] M.ρ.asModule] : CohTrivial M := by
  obtain ⟨φ, hφ⟩ := exists_sum_eq_of_basis M (Module.Free.chooseBasis k[G] M.ρ.asModule)
  exact cohTrivial_of_sum_eq M φ hφ

/- English proof (translation)
Use `Representation.free_asModule_free k G α` as an intermediate fact. Conclude with `cohTrivial_of_free _`.
-/
theorem cohTrivial_free (α : Type u) : CohTrivial (free k G α) := by
  have := Representation.free_asModule_free k G α
  exact cohTrivial_of_free _

end Norm

section ShortExact

variable {k G : Type u} [CommRing k] [Group G]

/- English proof (translation)
Introduce `n` and use `by have e := @asIso _ _ _ _ (TateCohomology.δ hS (n - 1)) (isIso_δ_of_tateAcyclic hS h₂ (n - 1)) have h := (h₃ (n - 1)).of_iso e.symm rwa [sub_add_cancel] at h`.
-/
theorem TateAcyclic.of_shortExact_X₃ [Fintype G] {S : ShortComplex (Rep.{u} k G)}
    (hS : S.ShortExact) (h₂ : TateAcyclic S.X₂) (h₃ : TateAcyclic S.X₃) : TateAcyclic S.X₁ :=
  fun n => by
    have e := @asIso _ _ _ _ (TateCohomology.δ hS (n - 1)) (isIso_δ_of_tateAcyclic hS h₂ (n - 1))
    have h := (h₃ (n - 1)).of_iso e.symm
    rwa [sub_add_cancel] at h

/- English proof (translation)
Introduce `n` and use `(h₁ (n + 1)).of_iso (@asIso _ _ _ _ (TateCohomology.δ hS n) (isIso_δ_of_tateAcyclic hS h₂ n))`.
-/
theorem TateAcyclic.of_shortExact_X₁ [Fintype G] {S : ShortComplex (Rep.{u} k G)}
    (hS : S.ShortExact) (h₂ : TateAcyclic S.X₂) (h₁ : TateAcyclic S.X₁) : TateAcyclic S.X₃ :=
  fun n => (h₁ (n + 1)).of_iso
    (@asIso _ _ _ _ (TateCohomology.δ hS n) (isIso_δ_of_tateAcyclic hS h₂ n))

/- English proof (translation)
Introduce `H _`. Establish `hS' : (S.map (resFunctor H.subtype)).ShortExact` using `(shortExact_res H.subtype).2 hS`. Establish `a : TateAcyclic (S.map (resFunctor H.subtype)).X₂`. Rewrite using `[ShortComplex.map_X₂]`. Conclude with `h₂ H`.

Establish `b : TateAcyclic (S.map (resFunctor H.subtype)).X₃`. Rewrite using `[ShortComplex.map_X₃]`. Conclude with `h₃ H`. Establish `c` using `TateAcyclic.of_shortExact_X₃ hS' a b`. Rewrite `c` using `[ShortComplex.map_X₁]`.

Conclude with `c`.
-/
theorem CohTrivial.of_shortExact_X₃ {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (h₂ : CohTrivial S.X₂) (h₃ : CohTrivial S.X₃) : CohTrivial S.X₁ := by
  intro H _
  have hS' : (S.map (resFunctor H.subtype)).ShortExact := (shortExact_res H.subtype).2 hS
  have a : TateAcyclic (S.map (resFunctor H.subtype)).X₂ := by
    rw [ShortComplex.map_X₂]; exact h₂ H
  have b : TateAcyclic (S.map (resFunctor H.subtype)).X₃ := by
    rw [ShortComplex.map_X₃]; exact h₃ H
  have c := TateAcyclic.of_shortExact_X₃ hS' a b
  rw [ShortComplex.map_X₁] at c
  exact c

/- English proof (translation)
Introduce `H _`. Establish `hS' : (S.map (resFunctor H.subtype)).ShortExact` using `(shortExact_res H.subtype).2 hS`. Establish `a : TateAcyclic (S.map (resFunctor H.subtype)).X₂`. Rewrite using `[ShortComplex.map_X₂]`. Conclude with `h₂ H`.

Establish `b : TateAcyclic (S.map (resFunctor H.subtype)).X₁`. Rewrite using `[ShortComplex.map_X₁]`. Conclude with `h₁ H`. Establish `c` using `TateAcyclic.of_shortExact_X₁ hS' a b`. Rewrite `c` using `[ShortComplex.map_X₃]`.

Conclude with `c`.
-/
theorem CohTrivial.of_shortExact_X₁ {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (h₂ : CohTrivial S.X₂) (h₁ : CohTrivial S.X₁) : CohTrivial S.X₃ := by
  intro H _
  have hS' : (S.map (resFunctor H.subtype)).ShortExact := (shortExact_res H.subtype).2 hS
  have a : TateAcyclic (S.map (resFunctor H.subtype)).X₂ := by
    rw [ShortComplex.map_X₂]; exact h₂ H
  have b : TateAcyclic (S.map (resFunctor H.subtype)).X₁ := by
    rw [ShortComplex.map_X₁]; exact h₁ H
  have c := TateAcyclic.of_shortExact_X₁ hS' a b
  rw [ShortComplex.map_X₃] at c
  exact c

end ShortExact

section Rat

variable {G : Type} [Group G]

end Rat

end GroundTheory.GroupCoh
