import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleTensorLiftApplyEqTwoPointValueStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

open Algebra.TensorProduct in

/- English proof (translation)
Use `set H := G.A n`. Establish `V : ∀ (D : Type) [CommRing D] [Algebra R D] (φ ψ : H →ₐ[R] D), lift φ ψ (fun _ _ ↦ Commute.all _ _) (d.coc n) = d.g D (spOver φ ≫ t.y n) (spOver ψ ≫ t.y n) - ((fv d.f H D (toConv φ * toConv ψ).ofConv (t.y n) + (toConv φ * toConv ψ).ofConv (d.h n)) - (fv d.f H D φ (t.y n) + φ (d.h …` using `fun D _ _ φ ψ ↦ GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue R A p G t c d n D φ ψ`. Establish `M : ∀ (D : Type) [CommRing D] [Algebra R D] (φ ψ : H →ₐ[R] D), spOver (toConv φ * toConv ψ).ofConv ≫ t.y n = (spOver φ ≫ t.y n) * (spOver ψ ≫ t.y n)` using `fun D _ _ φ ψ ↦ t.mul n D (toConv φ) (toConv ψ)`. Rewrite using `[mem_symCocycles]`. Prove the components needed by the constructor for the conclusion.

Set `T` to `H ⊗[R] (H ⊗[R] H)`. Set `i1 : H →ₐ[R] H ⊗[R] (H ⊗[R] H)` to `includeLeft`. Set `i2 : H →ₐ[R] H ⊗[R] (H ⊗[R] H)` to `(includeRight : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H)).comp includeLeft`. Set `i3 : H →ₐ[R] H ⊗[R] (H ⊗[R] H)` to `(includeRight : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H)).comp includeRight`. Set `i12` to `(toConv i1 * toConv i2).ofConv`.

Set `i23` to `(toConv i2 * toConv i3).ofConv`. Establish `e1 : ∀ x : H ⊗[R] H, (1 : H) ⊗ₜ[R] x = lift i2 i3 (fun _ _ ↦ Commute.all _ _) x`. Introduce `x`. Proceed by induction on `x with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => rw [tmul_add, map_add, hx, hy]`. Consider the case `tmul a b => simp [i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]`. Establish `e2 : ∀ x : H ⊗[R] H, TensorProduct.assoc R H H H ((Coalgebra.comul (R` using `R) (A := H)).rTensor H x) = lift i12 i3 (fun _ _ ↦ Commute.all _ _) x := by`. Introduce `x`. Proceed by induction on `x with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add]`. Consider the case `tmul a b`. Rewrite using `[LinearMap.rTensor_tmul, lift_tmul]`. Simplify using `only [i12, AlgHom.convMul_apply, ofConv_toConv]`.

Proceed by induction on `(Coalgebra.comul (R := R) a : H ⊗[R] H) with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [add_tmul, map_add, hx, hy, add_mul]`. Consider the case `tmul a1 a2 => simp [i1, i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]`. Establish `e3 : ∀ x : H ⊗[R] H, (Coalgebra.comul (R` using `R) (A := H)).lTensor H x = lift i1 i23 (fun _ _ ↦ Commute.all _ _) x := by`.

Introduce `x`. Proceed by induction on `x with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Consider the case `tmul a b`.

Rewrite using `[LinearMap.lTensor_tmul, lift_tmul]`. Simplify using `only [i23, AlgHom.convMul_apply, ofConv_toConv]`. Proceed by induction on `(Coalgebra.comul (R := R) b : H ⊗[R] H) with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [tmul_add, map_add, hx, hy, mul_add]`.

Consider the case `tmul b1 b2 => simp [i1, i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]`. Establish `e4 : ∀ x : H ⊗[R] H, ((TensorProduct.mk R H H).flip 1).lTensor H x = lift i1 i2 (fun _ _ ↦ Commute.all _ _) x`. Introduce `x`. Proceed by induction on `x with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Consider the case `tmul a b => simp [i1, i2, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]`. Rewrite using `[cobTwo_apply, e1, e2, e3, e4, V, V, V, V]`. Simplify using `only [i12, i23, toConv_ofConv, M, mul_assoc]`. Establish `hc` using `(hg (H ⊗[R] (H ⊗[R] H))).2 (spOver i1 ≫ t.y n) (spOver i2 ≫ t.y n) (spOver i3 ≫ t.y n)`.

Rewrite using `[mul_assoc (toConv i1)]`. Take the linear combination `hc`. Establish `e : ∀ x : H ⊗[R] H, TensorProduct.comm R H H x = lift (includeRight : H →ₐ[R] H ⊗[R] H) (includeLeft : H →ₐ[R] H ⊗[R] H) (fun _ _ ↦ Commute.all _ _) x`. Introduce `x`. Proceed by induction on `x with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Consider the case `tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]`. Establish `e' : d.coc n = lift (includeLeft : H →ₐ[R] H ⊗[R] H) includeRight (fun _ _ ↦ Commute.all _ _) (d.coc n)`. Conclude with `(DFunLike.congr_fun (lift_includeLeft_includeRight (R := R) (S := R) (A := H) (B := H)) (d.coc n)).symm`.

Rewrite using `[e, V]`. Use `conv_rhs => rw [e', V]`. Rewrite using `[mul_comm (toConv (includeRight : H →ₐ[R] H ⊗[R] H)), (hg _).1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coc_mem_symCocycles (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (hg : IsSymCoc d.g) (n : ℕ) :
    d.coc n ∈ symCocycles R (G.A n) := by
  set H := G.A n

  have V : ∀ (D : Type) [CommRing D] [Algebra R D] (φ ψ : H →ₐ[R] D),
      lift φ ψ (fun _ _ ↦ Commute.all _ _) (d.coc n) = d.g D (spOver φ ≫ t.y n) (spOver ψ ≫ t.y n) -
        ((fv d.f H D (toConv φ * toConv ψ).ofConv (t.y n) + (toConv φ * toConv ψ).ofConv (d.h n)) -
          (fv d.f H D φ (t.y n) + φ (d.h n)) - (fv d.f H D ψ (t.y n) + ψ (d.h n))) :=
    fun D _ _ φ ψ ↦ GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue R A p G t c d n D φ ψ
  have M : ∀ (D : Type) [CommRing D] [Algebra R D] (φ ψ : H →ₐ[R] D),
      spOver (toConv φ * toConv ψ).ofConv ≫ t.y n = (spOver φ ≫ t.y n) * (spOver ψ ≫ t.y n) :=
    fun D _ _ φ ψ ↦ t.mul n D (toConv φ) (toConv ψ)
  rw [mem_symCocycles]
  constructor
  · let T := H ⊗[R] (H ⊗[R] H)
    let i1 : H →ₐ[R] H ⊗[R] (H ⊗[R] H) := includeLeft
    let i2 : H →ₐ[R] H ⊗[R] (H ⊗[R] H) := (includeRight : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H)).comp includeLeft
    let i3 : H →ₐ[R] H ⊗[R] (H ⊗[R] H) := (includeRight : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H)).comp includeRight
    let i12 := (toConv i1 * toConv i2).ofConv
    let i23 := (toConv i2 * toConv i3).ofConv
    have e1 : ∀ x : H ⊗[R] H, (1 : H) ⊗ₜ[R] x = lift i2 i3 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | zero => simp
      | add x y hx hy => rw [tmul_add, map_add, hx, hy]
      | tmul a b => simp [i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e2 : ∀ x : H ⊗[R] H, TensorProduct.assoc R H H H ((Coalgebra.comul (R := R) (A := H)).rTensor H x) =
        lift i12 i3 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
      | tmul a b =>
        rw [LinearMap.rTensor_tmul, lift_tmul]
        simp only [i12, AlgHom.convMul_apply, ofConv_toConv]
        induction (Coalgebra.comul (R := R) a : H ⊗[R] H) with
        | zero => simp
        | add x y hx hy => simp only [add_tmul, map_add, hx, hy, add_mul]
        | tmul a1 a2 => simp [i1, i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e3 : ∀ x : H ⊗[R] H, (Coalgebra.comul (R := R) (A := H)).lTensor H x = lift i1 i23 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul a b =>
        rw [LinearMap.lTensor_tmul, lift_tmul]
        simp only [i23, AlgHom.convMul_apply, ofConv_toConv]
        induction (Coalgebra.comul (R := R) b : H ⊗[R] H) with
        | zero => simp
        | add x y hx hy => simp only [tmul_add, map_add, hx, hy, mul_add]
        | tmul b1 b2 => simp [i1, i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e4 : ∀ x : H ⊗[R] H, ((TensorProduct.mk R H H).flip 1).lTensor H x =
        lift i1 i2 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul a b => simp [i1, i2, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    rw [cobTwo_apply, e1, e2, e3, e4, V, V, V, V]
    simp only [i12, i23, toConv_ofConv, M, mul_assoc]
    have hc := (hg (H ⊗[R] (H ⊗[R] H))).2 (spOver i1 ≫ t.y n) (spOver i2 ≫ t.y n) (spOver i3 ≫ t.y n)
    rw [mul_assoc (toConv i1)]
    linear_combination hc
  · have e : ∀ x : H ⊗[R] H, TensorProduct.comm R H H x =
        lift (includeRight : H →ₐ[R] H ⊗[R] H) (includeLeft : H →ₐ[R] H ⊗[R] H) (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e' : d.coc n = lift (includeLeft : H →ₐ[R] H ⊗[R] H) includeRight (fun _ _ ↦ Commute.all _ _) (d.coc n) := by
      exact (DFunLike.congr_fun (lift_includeLeft_includeRight (R := R) (S := R) (A := H) (B := H)) (d.coc n)).symm
    rw [e, V]
    conv_rhs => rw [e', V]
    rw [mul_comm (toConv (includeRight : H →ₐ[R] H ⊗[R] H)), (hg _).1]
    ring

end GlobalTheory.PtExt
