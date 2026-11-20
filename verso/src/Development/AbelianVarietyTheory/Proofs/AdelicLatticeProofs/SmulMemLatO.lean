import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatticeStable

noncomputable def liftFin (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  LinearMap.rTensor D.host.E
    (show Af D.host.F →ₗ[D.host.F] AF D.host.F from LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftFin_tmul (D : D7) (α : Af D.host.F) (m : D.host.E) :
    liftFin D (α ⊗ₜ[D.host.F] m) = pairA D.host.F 0 α ⊗ₜ[D.host.F] m := rfl

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => rw [zero_mul, RingHom.map_zero, zero_mul, LinearMap.map_zero]`. Consider the case `tmul x e`. Express the relevant statement in the definitionally equal form `_ = liftFin D ((sndA D.host.F x ⊗ₜ[D.host.F] e) * _)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, liftFin_tmul]`.

Use `congr 1`. Conclude with `Prod.ext (mul_zero _) rfl`. Consider the case `add x y hx hy => rw [add_mul, hx, hy, RingHom.map_add, add_mul, LinearMap.map_add]`.
-/
theorem mul_pair_tmul (D : D7) (w : AE D) (α : Af D.host.F) (m : D.host.E) :
    w * (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) = liftFin D (finPart D w * (α ⊗ₜ[D.host.F] m)) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [zero_mul, RingHom.map_zero, zero_mul, LinearMap.map_zero]
  | tmul x e =>
    change _ = liftFin D ((sndA D.host.F x ⊗ₜ[D.host.F] e) * _)
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, liftFin_tmul]
    congr 1
    exact Prod.ext (mul_zero _) rfl
  | add x y hx hy => rw [add_mul, hx, hy, RingHom.map_add, add_mul, LinearMap.map_add]

noncomputable def liftMul (D : D7) (c : Af D.host.F ⊗[D.host.F] D.host.E) : Af D.host.F ⊗[D.host.F] D.host.E →+ AE D :=
  (liftFin D).toAddMonoidHom.comp (AddMonoidHom.mulRight c)

/- English proof (translation)
Set `Ψ : WO S T →+ WO S T` to `AddMonoidHom.mk' (fun u => w • u) fun x y => Matrix.ext fun i j => mul_add w (x i j) (y i j)`. Establish `main : latO S T LS LT P ≤ (latO S T LS LT P).comap Ψ`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩`. Set `Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ WO S T` to `AddMonoidHom.mk' (fun y => Matrix.of fun i j => liftMul D (α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * HSpace.gram S k j)) y) fun y y' => Matrix.ext fun i j => (liftMul D _).map_add y y'`.

Establish `hle : intAE D ≤ (latO S T LS LT P).comap Φ`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨β, hβ, o, rfl⟩`. Use `AddSubgroup.subset_closure ⟨β * α, fun v => ?_, fun v hv => ?_, o • a, Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) o ha, s, hs, t, ht, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `mul_mem (hβ v) (hα v)`. Rewrite using `[map_mul, hP v hv, mul_zero]`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `liftFin D ((β ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] _)) = _ ⊗ₜ[D.host.F] _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, liftFin_tmul, Algebra.smul_def, show algebraMap _ _ o = (o : D.host.E) from rfl]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e : Ψ (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * HSpace.gram S k j) : WO S T) = Φ (finPart D w)` using `Matrix.ext fun i j => mul_pair_tmul D w α _`. Rewrite using `[SetLike.mem_coe, AddSubgroup.mem_comap, e]`. Conclude with `hle hw`.

Conclude with `fun u hu => main hu`.
-/
theorem smul_mem_latO (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (w : AE D) (hw : finPart D w ∈ intAE D) :
    ∀ u ∈ latO S T LS LT P, w • u ∈ latO S T LS LT P := by
  let Ψ : WO S T →+ WO S T := AddMonoidHom.mk' (fun u => w • u)
    fun x y => Matrix.ext fun i j => mul_add w (x i j) (y i j)
  have main : latO S T LS LT P ≤ (latO S T LS LT P).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ WO S T := AddMonoidHom.mk'
      (fun y => Matrix.of fun i j => liftMul D
        (α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * HSpace.gram S k j)) y)
      fun y y' => Matrix.ext fun i j => (liftMul D _).map_add y y'
    have hle : intAE D ≤ (latO S T LS LT P).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨β, hβ, o, rfl⟩
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, fun v hv => ?_, o • a,
        Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) o ha, s, hs, t, ht, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · rw [map_mul, hP v hv, mul_zero]
      · ext i j
        change liftFin D ((β ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] _)) = _ ⊗ₜ[D.host.F] _
        rw [Algebra.TensorProduct.tmul_mul_tmul, liftFin_tmul, Algebra.smul_def,
          show algebraMap _ _ o = (o : D.host.E) from rfl]
        congr 1
        ring
    have e : Ψ (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
        (a * t i * ∑ k, star (s k) * HSpace.gram S k j) : WO S T) = Φ (finPart D w) :=
      Matrix.ext fun i j => mul_pair_tmul D w α _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact fun u hu => main hu

end GlobalTheory.LatticeStable
