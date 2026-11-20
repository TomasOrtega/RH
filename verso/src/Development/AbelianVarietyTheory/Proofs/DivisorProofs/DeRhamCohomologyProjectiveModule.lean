import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTensorModuleCompat
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HdRDescent

universe u v

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `open TensorProduct in`. Introduce `R R' O _ _ _ _ M _ _ _ _ N _ _ _ _ e he`. Use `letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module`. Use `letI : Module (R' ⊗[ℤ] O) N := TensorProduct.Algebra.module`. Set `f : R ⊗[ℤ] O →ₐ[ℤ] R' ⊗[ℤ] O` to `Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℤ R R') (AlgHom.id ℤ O)`.

Use `letI : Algebra (R ⊗[ℤ] O) (R' ⊗[ℤ] O) := f.toRingHom.toAlgebra`. Use `letI : Module (R ⊗[ℤ] O) N := Module.compHom N f.toRingHom`. Use `haveI : IsScalarTower (R ⊗[ℤ] O) (R' ⊗[ℤ] O) N := ⟨fun a x n => mul_smul (f a) x n⟩`. Establish `hf : ∀ (r : R) (o : O), f (r ⊗ₜ o) = algebraMap R R' r ⊗ₜ o` using `fun r o => rfl`. Use `haveI : Module.FaithfullyFlat R R' := inferInstance`.

Use `haveI : IsScalarTower R (R ⊗[ℤ] O) (R' ⊗[ℤ] O) := IsScalarTower.of_algebraMap_eq (fun r => rfl)`. Set `l : R' →ₗ[R] R' ⊗[ℤ] O` to `{ toFun := fun r' => r' ⊗ₜ 1 map_add' := fun x y => add_tmul x y 1 map_smul' := fun r r' => rfl }`. Set `u : (R ⊗[ℤ] O) ⊗[R] R' →ₗ[R ⊗[ℤ] O] R' ⊗[ℤ] O` to `LinearMap.liftBaseChange _ l`. Establish `hu : ∀ (r : R) (o : O) (r' : R'), u ((r ⊗ₜ o) ⊗ₜ r') = (algebraMap R R' r * r') ⊗ₜ o`. Introduce `r o r'`.

Express the relevant statement in the definitionally equal form `f (r ⊗ₜ o) * (r' ⊗ₜ 1) = _`. Rewrite using `[hf, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]`. Set `w : R' →ₗ[ℤ] O →ₗ[ℤ] (R ⊗[ℤ] O) ⊗[R] R'` to `LinearMap.mk₂ ℤ (fun r' o => ((1 : R) ⊗ₜ[ℤ] o) ⊗ₜ[R] r') (fun x y o => by simp [tmul_add]) (fun n x o => map_zsmul (TensorProduct.mk R (R ⊗[ℤ] O) R' ((1 : R) ⊗ₜ[ℤ] o)) n x) (fun x o o' => by simp [tmul_add, add_tmul]) (fun n x o => by`. Express the relevant statement in the definitionally equal form `(TensorProduct.mk R (R ⊗[ℤ] O) R').flip x (TensorProduct.mk ℤ R O 1 (n • o)) = n • (TensorProduct.mk R (R ⊗[ℤ] O) R').flip x (TensorProduct.mk ℤ R O 1 o)`. Rewrite using `[map_zsmul, map_zsmul])`.

Set `v : R' ⊗[ℤ] O →ₗ[ℤ] (R ⊗[ℤ] O) ⊗[R] R'` to `TensorProduct.lift w`. Establish `hv : ∀ (r' : R') (o : O), v (r' ⊗ₜ o) = ((1 : R) ⊗ₜ[ℤ] o) ⊗ₜ[R] r'` using `fun r' o => rfl`. Establish `huv : ∀ y, u (v y) = y`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul r' o`. Rewrite using `[hv, hu, map_one, _root_.one_mul]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Establish `hvu : ∀ x, v (u x) = x`.

Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a r'`. Proceed by induction on `a using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul r o`. Rewrite using `[hu, ← Algebra.smul_def, hv, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Consider the case `add a b ha hb => rw [add_tmul, map_add, map_add, ha, hb]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.

Establish `hubij : Function.Bijective u` using `⟨fun a b hab => by rw [← hvu a, ← hvu b, hab], fun y => ⟨v y, huv y⟩⟩`. Establish `hFF : Module.FaithfullyFlat (R ⊗[ℤ] O) (R' ⊗[ℤ] O)` using `Module.FaithfullyFlat.of_linearEquiv (R ⊗[ℤ] O) ((R ⊗[ℤ] O) ⊗[R] R') (LinearEquiv.ofBijective u hubij).symm`. Establish `hj : ∀ (a : R ⊗[ℤ] O) (m : M), e (1 ⊗ₜ (a • m)) = f a • e (1 ⊗ₜ m)`. Introduce `a m`. Proceed by induction on `a using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul r o`. Rewrite using `[hf, TensorProduct.Algebra.smul_def, TensorProduct.Algebra.smul_def, ← he, TensorProduct.tmul_smul, ← algebraMap_smul R', map_smul]`. Consider the case `add a b ha hb => rw [add_smul, tmul_add, map_add, ha, hb, map_add, add_smul]`. Set `j : M →ₗ[R ⊗[ℤ] O] N` to `{ toFun := fun m => e (1 ⊗ₜ m) map_add' := fun x y => by simp [tmul_add] map_smul' := fun a m => hj a m }`.

Set `Φ : (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M →ₗ[R' ⊗[ℤ] O] N` to `LinearMap.liftBaseChange _ j`. Set `g : R' →+ M →+ (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M` to `AddMonoidHom.mk' (fun r' => (TensorProduct.mk (R ⊗[ℤ] O) (R' ⊗[ℤ] O) M (r' ⊗ₜ[ℤ] (1 : O))).toAddMonoidHom) (by intro a b; ext m; simp [add_tmul])`. Set `ψ : R' ⊗[R] M →+ (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M` to `TensorProduct.liftAddHom g (by`. Introduce `r r' m`. Establish `hr : r • m = ((r ⊗ₜ[ℤ] (1 : O)) : R ⊗[ℤ] O) • m`.

Rewrite using `[TensorProduct.Algebra.smul_def, one_smul]`. Simplify using `only [g, AddMonoidHom.mk'_apply, LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]`. Rewrite using `[hr, ← TensorProduct.smul_tmul, Algebra.smul_def]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `_ = f (r ⊗ₜ 1) * _`.

Simplify using `only [hf, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, Algebra.smul_def])`. Establish `h1 : ∀ y, Φ (ψ y) = e y`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul r' m`. Simplify using `only [ψ, TensorProduct.liftAddHom_tmul, g, AddMonoidHom.mk'_apply, LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply, Φ, LinearMap.liftBaseChange_tmul]`. Express the relevant statement in the definitionally equal form `(r' ⊗ₜ[ℤ] (1 : O)) • e (1 ⊗ₜ m) = _`. Rewrite using `[TensorProduct.Algebra.smul_def, one_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add]`.

Establish `h2 : ∀ z, ψ (e.symm (Φ z)) = z`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x m`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r' o`. Establish `hΦ : Φ ((r' ⊗ₜ[ℤ] o) ⊗ₜ m) = e (r' ⊗ₜ (o • m))`. Simplify using `only [Φ, LinearMap.liftBaseChange_tmul]`.

Express the relevant statement in the definitionally equal form `(r' ⊗ₜ[ℤ] o) • e (1 ⊗ₜ m) = _`. Rewrite using `[TensorProduct.Algebra.smul_def, ← he, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Rewrite using `[hΦ, LinearEquiv.symm_apply_apply]`. Simplify using `only [ψ, TensorProduct.liftAddHom_tmul, g, AddMonoidHom.mk'_apply, LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]`. Establish `ho : o • m = (((1 : R) ⊗ₜ[ℤ] o) : R ⊗[ℤ] O) • m`.

Rewrite using `[TensorProduct.Algebra.smul_def, one_smul]`. Rewrite using `[ho, ← TensorProduct.smul_tmul, Algebra.smul_def]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `f (1 ⊗ₜ o) * _ = _`. Rewrite using `[hf, map_one, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]`.

Consider the case `add x y hx hy => rw [add_tmul, map_add, map_add, map_add, hx, hy]`. Consider the case `add x y hx hy => rw [map_add, map_add, map_add, hx, hy]`. Establish `hinj : Function.Injective Φ` using `fun a b hab => by rw [← h2 a, ← h2 b, hab]`. Establish `hsurj : Function.Surjective Φ` using `fun n => ⟨ψ (e.symm n), by rw [h1, LinearEquiv.apply_symm_apply]⟩`. Conclude with `⟨f.toRingHom.toAlgebra, hFF, ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩⟩⟩`.
-/
theorem baseChange_equiv :
    ∀ (K L O : Type) [Field K] [Field L] [Algebra K L] [CommRing O] (M : Type u) [AddCommGroup M]
    [Module K M] [Module O M] [SMulCommClass K O M] (N : Type v) [AddCommGroup N] [Module L N] [Module O N]
    [SMulCommClass L O N] (e : L ⊗[K] M ≃ₗ[L] N), (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    letI : Module (K ⊗[ℤ] O) M := TensorProduct.Algebra.module
    letI : Module (L ⊗[ℤ] O) N := TensorProduct.Algebra.module
    ∃ _ : Algebra (K ⊗[ℤ] O) (L ⊗[ℤ] O), Module.FaithfullyFlat (K ⊗[ℤ] O) (L ⊗[ℤ] O) ∧
      Nonempty ((L ⊗[ℤ] O) ⊗[K ⊗[ℤ] O] M ≃ₗ[L ⊗[ℤ] O] N) := by
  open TensorProduct in
  intro R R' O _ _ _ _ M _ _ _ _ N _ _ _ _ e he
  letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
  letI : Module (R' ⊗[ℤ] O) N := TensorProduct.Algebra.module
  let f : R ⊗[ℤ] O →ₐ[ℤ] R' ⊗[ℤ] O :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℤ R R') (AlgHom.id ℤ O)
  letI : Algebra (R ⊗[ℤ] O) (R' ⊗[ℤ] O) := f.toRingHom.toAlgebra
  letI : Module (R ⊗[ℤ] O) N := Module.compHom N f.toRingHom
  haveI : IsScalarTower (R ⊗[ℤ] O) (R' ⊗[ℤ] O) N := ⟨fun a x n => mul_smul (f a) x n⟩
  have hf : ∀ (r : R) (o : O), f (r ⊗ₜ o) = algebraMap R R' r ⊗ₜ o := fun r o => rfl

  haveI : Module.FaithfullyFlat R R' := inferInstance
  haveI : IsScalarTower R (R ⊗[ℤ] O) (R' ⊗[ℤ] O) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  let l : R' →ₗ[R] R' ⊗[ℤ] O :=
    { toFun := fun r' => r' ⊗ₜ 1
      map_add' := fun x y => add_tmul x y 1
      map_smul' := fun r r' => rfl }
  let u : (R ⊗[ℤ] O) ⊗[R] R' →ₗ[R ⊗[ℤ] O] R' ⊗[ℤ] O := LinearMap.liftBaseChange _ l
  have hu : ∀ (r : R) (o : O) (r' : R'), u ((r ⊗ₜ o) ⊗ₜ r') = (algebraMap R R' r * r') ⊗ₜ o := by
    intro r o r'
    change f (r ⊗ₜ o) * (r' ⊗ₜ 1) = _
    rw [hf, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  let w : R' →ₗ[ℤ] O →ₗ[ℤ] (R ⊗[ℤ] O) ⊗[R] R' :=
    LinearMap.mk₂ ℤ (fun r' o => ((1 : R) ⊗ₜ[ℤ] o) ⊗ₜ[R] r')
      (fun x y o => by simp [tmul_add])
      (fun n x o => map_zsmul (TensorProduct.mk R (R ⊗[ℤ] O) R' ((1 : R) ⊗ₜ[ℤ] o)) n x)
      (fun x o o' => by simp [tmul_add, add_tmul])
      (fun n x o => by
        change (TensorProduct.mk R (R ⊗[ℤ] O) R').flip x (TensorProduct.mk ℤ R O 1 (n • o)) =
          n • (TensorProduct.mk R (R ⊗[ℤ] O) R').flip x (TensorProduct.mk ℤ R O 1 o)
        rw [map_zsmul, map_zsmul])
  let v : R' ⊗[ℤ] O →ₗ[ℤ] (R ⊗[ℤ] O) ⊗[R] R' := TensorProduct.lift w
  have hv : ∀ (r' : R') (o : O), v (r' ⊗ₜ o) = ((1 : R) ⊗ₜ[ℤ] o) ⊗ₜ[R] r' := fun r' o => rfl
  have huv : ∀ y, u (v y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r' o =>
      rw [hv, hu, map_one, _root_.one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hvu : ∀ x, v (u x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r' =>
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul r o =>
        rw [hu, ← Algebra.smul_def, hv, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul,
          _root_.mul_one]
      | add a b ha hb => rw [add_tmul, map_add, map_add, ha, hb]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hubij : Function.Bijective u :=
    ⟨fun a b hab => by rw [← hvu a, ← hvu b, hab], fun y => ⟨v y, huv y⟩⟩
  have hFF : Module.FaithfullyFlat (R ⊗[ℤ] O) (R' ⊗[ℤ] O) :=
    Module.FaithfullyFlat.of_linearEquiv (R ⊗[ℤ] O) ((R ⊗[ℤ] O) ⊗[R] R')
      (LinearEquiv.ofBijective u hubij).symm

  have hj : ∀ (a : R ⊗[ℤ] O) (m : M), e (1 ⊗ₜ (a • m)) = f a • e (1 ⊗ₜ m) := by
    intro a m
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r o =>
      rw [hf, TensorProduct.Algebra.smul_def, TensorProduct.Algebra.smul_def, ← he,
        TensorProduct.tmul_smul, ← algebraMap_smul R', map_smul]
    | add a b ha hb => rw [add_smul, tmul_add, map_add, ha, hb, map_add, add_smul]
  let j : M →ₗ[R ⊗[ℤ] O] N :=
    { toFun := fun m => e (1 ⊗ₜ m)
      map_add' := fun x y => by simp [tmul_add]
      map_smul' := fun a m => hj a m }
  let Φ : (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M →ₗ[R' ⊗[ℤ] O] N := LinearMap.liftBaseChange _ j
  let g : R' →+ M →+ (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M :=
    AddMonoidHom.mk' (fun r' => (TensorProduct.mk (R ⊗[ℤ] O) (R' ⊗[ℤ] O) M
      (r' ⊗ₜ[ℤ] (1 : O))).toAddMonoidHom) (by intro a b; ext m; simp [add_tmul])
  let ψ : R' ⊗[R] M →+ (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M := TensorProduct.liftAddHom g (by
    intro r r' m
    have hr : r • m = ((r ⊗ₜ[ℤ] (1 : O)) : R ⊗[ℤ] O) • m := by
      rw [TensorProduct.Algebra.smul_def, one_smul]
    simp only [g, AddMonoidHom.mk'_apply, LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
    rw [hr, ← TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    change _ = f (r ⊗ₜ 1) * _
    simp only [hf, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, Algebra.smul_def])
  have h1 : ∀ y, Φ (ψ y) = e y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r' m =>
      simp only [ψ, TensorProduct.liftAddHom_tmul, g, AddMonoidHom.mk'_apply,
        LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply, Φ, LinearMap.liftBaseChange_tmul]
      change (r' ⊗ₜ[ℤ] (1 : O)) • e (1 ⊗ₜ m) = _
      rw [TensorProduct.Algebra.smul_def, one_smul, ← map_smul, TensorProduct.smul_tmul',
        smul_eq_mul, _root_.mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have h2 : ∀ z, ψ (e.symm (Φ z)) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x m =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r' o =>
        have hΦ : Φ ((r' ⊗ₜ[ℤ] o) ⊗ₜ m) = e (r' ⊗ₜ (o • m)) := by
          simp only [Φ, LinearMap.liftBaseChange_tmul]
          change (r' ⊗ₜ[ℤ] o) • e (1 ⊗ₜ m) = _
          rw [TensorProduct.Algebra.smul_def, ← he, ← map_smul, TensorProduct.smul_tmul',
            smul_eq_mul, _root_.mul_one]
        rw [hΦ, LinearEquiv.symm_apply_apply]
        simp only [ψ, TensorProduct.liftAddHom_tmul, g, AddMonoidHom.mk'_apply,
          LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
        have ho : o • m = (((1 : R) ⊗ₜ[ℤ] o) : R ⊗[ℤ] O) • m := by
          rw [TensorProduct.Algebra.smul_def, one_smul]
        rw [ho, ← TensorProduct.smul_tmul, Algebra.smul_def]
        congr 1
        change f (1 ⊗ₜ o) * _ = _
        rw [hf, map_one, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]
      | add x y hx hy => rw [add_tmul, map_add, map_add, map_add, hx, hy]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hinj : Function.Injective Φ := fun a b hab => by rw [← h2 a, ← h2 b, hab]
  have hsurj : Function.Surjective Φ := fun n =>
    ⟨ψ (e.symm n), by rw [h1, LinearEquiv.apply_symm_apply]⟩
  exact ⟨f.toRingHom.toAlgebra, hFF, ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩⟩⟩

section Module

variable {R O : Type} [CommRing R] [CommRing O] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A]

@[reducible] def oModule (a : OAct O A) : Module O (HdR A) :=
  Module.compHom _ (act (dp0 R) (𝟙 _) a)

/- English proof (translation)
The claim follows from `letI := oModule a ⟨fun r o h ↦ (map_smul (act (dp0 R) (𝟙 _) a o) r h).symm⟩`.
-/
theorem smulComm (a : OAct O A) : letI := oModule a; SMulCommClass R O (HdR A) :=
  letI := oModule a
  ⟨fun r o h ↦ (map_smul (act (dp0 R) (𝟙 _) a o) r h).symm⟩

/- English proof (translation)
Use `letI := oModule a`. Use `haveI := smulComm a`. Use `letI : Module (R ⊗[ℤ] O) (HdR A) := TensorProduct.Algebra.module`. Use `Module.ext' _ _ fun x h ↦ ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero`. Express the relevant statement in the definitionally equal form `actAlg (dp0 R) (𝟙 _) a 0 h = (0 : R ⊗[ℤ] O) • h`. Rewrite using `[zero_smul, map_zero, LinearMap.zero_apply]`. Consider the case `tmul r o`. Express the relevant statement in the definitionally equal form `actAlg (dp0 R) (𝟙 _) a (r ⊗ₜ o) h = (r ⊗ₜ o) • h`.

Rewrite using `[actAlg_tmul, TensorProduct.Algebra.smul_def]`. Both sides reduce to the same expression. Consider the case `add x y hx hy`. Express the relevant statement in the definitionally equal form `actAlg (dp0 R) (𝟙 _) a (x + y) h = (x + y) • h`. Rewrite using `[add_smul, map_add, LinearMap.add_apply]`.

Conclude with `congrArg₂ (· + ·) hx hy`.
-/
theorem tensorModule_eq (a : OAct O A) :
    tensorModule (dp0 R) (𝟙 _) a =
      (letI := oModule a; haveI := smulComm a; TensorProduct.Algebra.module) := by
  letI := oModule a
  haveI := smulComm a
  letI : Module (R ⊗[ℤ] O) (HdR A) := TensorProduct.Algebra.module
  refine Module.ext' _ _ fun x h ↦ ?_
  induction x using TensorProduct.induction_on with
  | zero =>
    change actAlg (dp0 R) (𝟙 _) a 0 h = (0 : R ⊗[ℤ] O) • h
    rw [zero_smul, map_zero, LinearMap.zero_apply]
  | tmul r o =>
    change actAlg (dp0 R) (𝟙 _) a (r ⊗ₜ o) h = (r ⊗ₜ o) • h
    rw [actAlg_tmul, TensorProduct.Algebra.smul_def]
    rfl
  | add x y hx hy =>
    change actAlg (dp0 R) (𝟙 _) a (x + y) h = (x + y) • h
    rw [add_smul, map_add, LinearMap.add_apply]
    exact congrArg₂ (· + ·) hx hy

end Module

section BC

variable {R R' : Type} [Field R] [Field R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'}
  {S S' : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A]
  {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'} {A' : Over S'} [GrpObj A']
  {b : S' ⟶ S} {φ : A'.left ⟶ A.left} {m : GrpMor κ t A κ' t' A' (algebraMap R R') b φ}

/- English proof (translation)
Set `e` to `Module.Free.chooseBasis R (prim κ t A)`. Set `E` to `LinearEquiv.ofBijective (liftSemi m.pull) hm`. Set `v` to `(Algebra.TensorProduct.basis R' e).map E`. Establish `hv : ∀ c, v.repr (m.pull c) = Finsupp.mapRange (algebraMap R R') (map_zero _) (e.repr c)`. Introduce `c`.

Establish `h1 : m.pull c = E (1 ⊗ₜ c)` using `(one_smul R' (m.pull c)).symm`. Rewrite using `[h1]`. Simplify using `only [v, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, Algebra.TensorProduct.basis_repr_tmul, one_smul]`. Set `F` to `Algebra.TensorProduct.basis R' e.dualBasis`. Establish `key : ∀ i, liftSemi hm.bcMap (F i) = v.dualBasis i`.

Introduce `i`. Rewrite using `[Algebra.TensorProduct.basis_apply, liftSemi_tmul, one_smul]`. Use `hm.corr_iff.1 fun c ↦ ?_` and prove the remaining obligations. Rewrite using `[Module.Basis.dualBasis_apply, Module.Basis.dualBasis_apply, hv, Finsupp.mapRange_apply]`. Establish `h2 : liftSemi hm.bcMap = (F.equiv v.dualBasis (Equiv.refl _)).toLinearMap` using `F.ext fun i ↦ by rw [key, LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]`.

Rewrite using `[h2]`. Conclude with `LinearEquiv.bijective _`.
-/
theorem bijective_liftSemi_bcMap (hm : m.IsBC) [Module.Finite R (prim κ t A)] :
    Function.Bijective (liftSemi hm.bcMap) := by
  classical
  let e := Module.Free.chooseBasis R (prim κ t A)
  let E := LinearEquiv.ofBijective (liftSemi m.pull) hm
  let v := (Algebra.TensorProduct.basis R' e).map E
  have hv : ∀ c, v.repr (m.pull c) = Finsupp.mapRange (algebraMap R R') (map_zero _) (e.repr c) := by
    intro c
    have h1 : m.pull c = E (1 ⊗ₜ c) := (one_smul R' (m.pull c)).symm
    rw [h1]
    simp only [v, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      Algebra.TensorProduct.basis_repr_tmul, one_smul]
  let F := Algebra.TensorProduct.basis R' e.dualBasis
  have key : ∀ i, liftSemi hm.bcMap (F i) = v.dualBasis i := by
    intro i
    rw [Algebra.TensorProduct.basis_apply, liftSemi_tmul, one_smul]
    refine hm.corr_iff.1 fun c ↦ ?_
    rw [Module.Basis.dualBasis_apply, Module.Basis.dualBasis_apply, hv, Finsupp.mapRange_apply]
  have h2 : liftSemi hm.bcMap = (F.equiv v.dualBasis (Equiv.refl _)).toLinearMap :=
    F.ext fun i ↦ by rw [key, LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
  rw [h2]
  exact LinearEquiv.bijective _

end BC

section Main

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g, SmoothOfRelativeDimension g A₀.hom := by`. Use `hA.smooth` as an intermediate fact. Use `hA.geomConnected` as an intermediate fact. Establish `: ConnectedSpace A₀.left` using `GeometricallyConnected.connectedSpace A₀.hom A₀.hom.isOpenMap`. Conclude with `exists_dim_of_preconnected A₀.hom (Classical.arbitrary _)`.

Take `⟨hFree, -, hBC, -, -⟩` from `GlobalTheory.T.abelianScheme_firstDeRham_structure`. Establish `hh` using `isGrpPullback_pullback A₀ (spMap (algebraMap k K))`. Establish `hbc` using `(hBC k A₀ g hA hg K _ _ hh).1`. Use `haveI : Module.Finite k (primDR A₀) := (hFree.prim hA hg).1`. Establish `hφ` using `bijective_liftSemi_bcMap hbc`.

Establish `hact : ∀ (x : O) (h : HdR A₀), hbc.bcMap (act (dp0 k) (𝟙 _) a x h) = act (dp0 K) (𝟙 _) (OAct.pullback (spMap (algebraMap k K)) A₀ a) x (hbc.bcMap h)`. Introduce `x h`. Use `haveI := a.hom x`. Use `haveI := (OAct.pullback (spMap (algebraMap k K)) A₀ a).hom x`. Use `hbc.corr_iff.1 ?_` and prove the remaining obligations.

Conclude with `GrpMor.Corr.push (m := Published.AbelianDeRham.bcMor hh) (Published.AbelianDeRham.bcMor hh) (a.act x) ((OAct.pullback (spMap (algebraMap k K)) A₀ a).act x) (pullback.lift_fst _ _ _).symm (hbc.corr_iff.2 rfl)`. Use `set B := (Over.pullback (spMap (algebraMap k K))).obj A₀`. Use `set b := OAct.pullback (spMap (algebraMap k K)) A₀ a`. Use `haveI : Module.Finite k (HdR A₀) := inferInstance`. Use `letI := oModule a`.

Use `letI := oModule b`. Use `haveI := smulComm a`. Use `haveI := smulComm b`. Set `e : K ⊗[k] HdR A₀ ≃ₗ[K] HdR B` to `LinearEquiv.ofBijective _ hφ`. Use `haveI : Module.Finite K (HdR B) := Module.Finite.equiv e`.

Establish `he : ∀ (x : O) (h : HdR A₀), e (1 ⊗ₜ (x • h)) = x • e (1 ⊗ₜ h)`. Introduce `x h`. Express the relevant statement in the definitionally equal form `liftSemi hbc.bcMap (1 ⊗ₜ act (dp0 k) (𝟙 _) a x h) = act (dp0 K) (𝟙 _) b x (liftSemi hbc.bcMap (1 ⊗ₜ h))`. Rewrite using `[liftSemi_tmul, liftSemi_tmul, one_smul, one_smul, hact]`. Take `⟨alg, hFF, ⟨e'⟩⟩` from `baseChange_equiv k K O (HdR A₀) (HdR B) e he`.

Establish `hfinB : letI` using `tensorModule (dp0 K) (𝟙 _) b; Module.Finite (K ⊗[ℤ] O) (HdR B) := by`. Use `letI := tensorModule (dp0 K) (𝟙 _) b`. Use `haveI := isScalarTower_tensorModule (dp0 K) (𝟙 _) b`. Conclude with `Module.Finite.of_restrictScalars_finite K (K ⊗[ℤ] O) (HdR B)`. Rewrite `hB`, `hfinB` using `[tensorModule_eq b]`.

Rewrite using `[tensorModule_eq a]`. Use `letI := alg`. Use `haveI := hFF`. Use `letI : Module (k ⊗[ℤ] O) (HdR A₀) := TensorProduct.Algebra.module`. Use `letI : Module (K ⊗[ℤ] O) (HdR B) := TensorProduct.Algebra.module`.

Use `haveI : Module.Projective (K ⊗[ℤ] O) ((K ⊗[ℤ] O) ⊗[k ⊗[ℤ] O] HdR A₀) := Module.Projective.of_equiv e'.symm`. Use `haveI : Module.Finite (K ⊗[ℤ] O) ((K ⊗[ℤ] O) ⊗[k ⊗[ℤ] O] HdR A₀) := Module.Finite.equiv e'.symm`. Conclude with `GlobalTheory.Descent.projective (K ⊗[ℤ] O)`.
-/
theorem projective_of_baseChange (k K : Type) [Field k] [Field K] [Algebra k K] {O : Type} [CommRing O]
    (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀] (hA : IsAbelianScheme A₀) (a : OAct O A₀)
    (hB : letI := tensorModule (dp0 K) (𝟙 _) (OAct.pullback (spMap (algebraMap k K)) A₀ a)
      Module.Projective (K ⊗[ℤ] O) (HdR ((Over.pullback (spMap (algebraMap k K))).obj A₀))) :
    letI := tensorModule (dp0 k) (𝟙 _) a
    Module.Projective (k ⊗[ℤ] O) (HdR A₀) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g, SmoothOfRelativeDimension g A₀.hom := by
    have := hA.smooth
    have := hA.geomConnected
    have : ConnectedSpace A₀.left := GeometricallyConnected.connectedSpace A₀.hom A₀.hom.isOpenMap
    exact exists_dim_of_preconnected A₀.hom (Classical.arbitrary _)
  obtain ⟨hFree, -, hBC, -, -⟩ := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have hh := isGrpPullback_pullback A₀ (spMap (algebraMap k K))
  have hbc := (hBC k A₀ g hA hg K _ _ hh).1
  haveI : Module.Finite k (primDR A₀) := (hFree.prim hA hg).1
  have hφ := bijective_liftSemi_bcMap hbc
  have hact : ∀ (x : O) (h : HdR A₀), hbc.bcMap (act (dp0 k) (𝟙 _) a x h) =
      act (dp0 K) (𝟙 _) (OAct.pullback (spMap (algebraMap k K)) A₀ a) x (hbc.bcMap h) := by
    intro x h
    haveI := a.hom x
    haveI := (OAct.pullback (spMap (algebraMap k K)) A₀ a).hom x
    refine hbc.corr_iff.1 ?_
    exact GrpMor.Corr.push (m := Published.AbelianDeRham.bcMor hh) (Published.AbelianDeRham.bcMor hh)
      (a.act x) ((OAct.pullback (spMap (algebraMap k K)) A₀ a).act x)
      (pullback.lift_fst _ _ _).symm (hbc.corr_iff.2 rfl)
  set B := (Over.pullback (spMap (algebraMap k K))).obj A₀
  set b := OAct.pullback (spMap (algebraMap k K)) A₀ a

  haveI : Module.Finite k (HdR A₀) := inferInstance
  letI := oModule a
  letI := oModule b
  haveI := smulComm a
  haveI := smulComm b
  let e : K ⊗[k] HdR A₀ ≃ₗ[K] HdR B := LinearEquiv.ofBijective _ hφ
  haveI : Module.Finite K (HdR B) := Module.Finite.equiv e
  have he : ∀ (x : O) (h : HdR A₀), e (1 ⊗ₜ (x • h)) = x • e (1 ⊗ₜ h) := by
    intro x h
    change liftSemi hbc.bcMap (1 ⊗ₜ act (dp0 k) (𝟙 _) a x h) =
      act (dp0 K) (𝟙 _) b x (liftSemi hbc.bcMap (1 ⊗ₜ h))
    rw [liftSemi_tmul, liftSemi_tmul, one_smul, one_smul, hact]
  obtain ⟨alg, hFF, ⟨e'⟩⟩ := baseChange_equiv k K O (HdR A₀) (HdR B) e he
  have hfinB : letI := tensorModule (dp0 K) (𝟙 _) b; Module.Finite (K ⊗[ℤ] O) (HdR B) := by
    letI := tensorModule (dp0 K) (𝟙 _) b
    haveI := isScalarTower_tensorModule (dp0 K) (𝟙 _) b
    exact Module.Finite.of_restrictScalars_finite K (K ⊗[ℤ] O) (HdR B)
  rw [tensorModule_eq b] at hB hfinB
  rw [tensorModule_eq a]
  letI := alg
  haveI := hFF
  letI : Module (k ⊗[ℤ] O) (HdR A₀) := TensorProduct.Algebra.module
  letI : Module (K ⊗[ℤ] O) (HdR B) := TensorProduct.Algebra.module
  haveI : Module.Projective (K ⊗[ℤ] O) ((K ⊗[ℤ] O) ⊗[k ⊗[ℤ] O] HdR A₀) :=
    Module.Projective.of_equiv e'.symm
  haveI : Module.Finite (K ⊗[ℤ] O) ((K ⊗[ℤ] O) ⊗[k ⊗[ℤ] O] HdR A₀) := Module.Finite.equiv e'.symm
  exact GlobalTheory.Descent.projective (K ⊗[ℤ] O)

end Main

/- English proof (translation)
Introduce `F _ _ k _ H A₀ _ _ hA a`. Conclude with `projective_of_baseChange k (AlgebraicClosure k) A₀ hA a (H _ (GlobalTheory.isAbelianScheme_pullback_obj _ A₀ hA) _)`.
-/
theorem projective_of_algebraicClosure :
    ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k],
      (∀ (B₀ : Over (Sp (AlgebraicClosure k))) [GrpObj B₀] [IsCommMonObj B₀], IsAbelianScheme B₀ →
        ∀ b : OAct (𝓞 F) B₀, letI := tensorModule (dp0 (AlgebraicClosure k)) (𝟙 _) b;
          Module.Projective (AlgebraicClosure k ⊗[ℤ] 𝓞 F) (HdR B₀)) →
      ∀ (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ →
        ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (dp0 k) (𝟙 _) a;
          Module.Projective (k ⊗[ℤ] 𝓞 F) (HdR A₀) := by
  intro F _ _ k _ H A₀ _ _ hA a
  exact projective_of_baseChange k (AlgebraicClosure k) A₀ hA a
    (H _ (GlobalTheory.isAbelianScheme_pullback_obj _ A₀ hA) _)

end GlobalTheory.HdRDescent
