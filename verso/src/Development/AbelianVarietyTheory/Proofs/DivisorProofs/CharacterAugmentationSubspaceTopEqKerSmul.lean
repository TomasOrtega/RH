import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
open scoped TensorProduct
universe u

namespace GlobalTheory.HTRho

/- English proof (translation)
Introduce `k _ C _ H _ _ σ χ x`. Use `letI : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom`. Use `set L := Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _) with hLdef`. Use `set φ : k ⊗[ℤ] C →ₐ[k] k := Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) with hφdef`. Establish `hsmul : ∀ (a : k ⊗[ℤ] C) (y : H), a • y = L a y` using `fun _ _ => rfl`.

Establish `hLt : ∀ (l : k) (c : C) (y : H), L (l ⊗ₜ c) y = l • σ c y`. Introduce `l c y`. Establish `h1` using `LinearMap.congr_fun (Algebra.TensorProduct.lift_tmul (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _) l c) y`. Rewrite using `[hLdef]`. Use `h1.trans ?_` and prove the remaining obligations.

Rewrite using `[Module.End.mul_apply, Algebra.ofId_apply, Module.algebraMap_end_apply]`. Both sides reduce to the same expression. Establish `hφt : ∀ (l : k) (c : C), φ (l ⊗ₜ c) = l * χ c`. Introduce `l c`. Simplify using `[hφdef, Algebra.TensorProduct.lift_tmul]`.

Establish `key : ∀ (a : k ⊗[ℤ] C) (y : H), L a y - φ a • y ∈ mSub σ χ ⊤`. Introduce `a y`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul l c`.

Rewrite using `[hLt, hφt, mul_smul, ← smul_sub]`. Use `Submodule.smul_mem _ l (Submodule.subset_span ⟨c, y, trivial, ?_⟩)` and prove the remaining obligations. Simplify using the standard rewrite rules. Consider the case `add a b ha hb`. Use `add_mem ha hb using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[map_add, map_add, LinearMap.add_apply, add_smul]`. Normalize the expressions using the abelian group laws. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨c, y, -, rfl⟩` from `hz`. Establish `hmem : ((1 : k) ⊗ₜ c - (χ c) ⊗ₜ (1 : C)) ∈ RingHom.ker φ`. Rewrite using `[RingHom.mem_ker]`. Simplify using `[hφt]`.

Use `Submodule.smul_mem_smul hmem (Submodule.mem_top (x := y))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hsmul, map_sub, LinearMap.sub_apply, hLt, hLt]`. Simplify using the standard rewrite rules. Consider the case `zero => exact Submodule.zero_mem _`.

Consider the case `add a b _ _ ha hb => exact add_mem ha hb`. Consider the case `smul l z _ hz`. Establish `: l • z = ((l ⊗ₜ (1 : C) : k ⊗[ℤ] C)) • z`. Rewrite using `[hsmul, hLt]`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hz`. Introduce `hx`. Use `Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun a b ha hb => add_mem ha hb)` and prove the remaining obligations. Rewrite using `[hsmul]`.

Use `key a y` as an intermediate fact. Rewrite `this` using `[(RingHom.mem_ker).1 ha, zero_smul, sub_zero]`. Then use the resulting hypothesis.
-/
theorem mSub_top_eq_ker_smul : ∀ (k : Type) [Field k] (C : Type) [CommRing C] (H : Type u) [AddCommGroup H]
    [Module k H] (σ : C →+* Module.End k H) (χ : C →+* k),
    letI : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H))
      σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom;
    ∀ x : H, x ∈ GlobalTheory.HTRho.mSub σ χ ⊤ ↔ x ∈ (RingHom.ker (Algebra.TensorProduct.lift (Algebra.ofId k k)
      χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) • ⊤ : Submodule (k ⊗[ℤ] C) H) := by
  intro k _ C _ H _ _ σ χ x
  letI : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H))
      σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom
  set L := Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
    (fun _ _ => Algebra.commutes _ _) with hLdef
  set φ : k ⊗[ℤ] C →ₐ[k] k := Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom
    (fun _ _ => Commute.all _ _) with hφdef
  have hsmul : ∀ (a : k ⊗[ℤ] C) (y : H), a • y = L a y := fun _ _ => rfl
  have hLt : ∀ (l : k) (c : C) (y : H), L (l ⊗ₜ c) y = l • σ c y := by
    intro l c y
    have h1 := LinearMap.congr_fun (Algebra.TensorProduct.lift_tmul (Algebra.ofId k (Module.End k H))
      σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _) l c) y
    rw [hLdef]
    refine h1.trans ?_
    rw [Module.End.mul_apply, Algebra.ofId_apply, Module.algebraMap_end_apply]
    rfl
  have hφt : ∀ (l : k) (c : C), φ (l ⊗ₜ c) = l * χ c := by
    intro l c
    simp [hφdef, Algebra.TensorProduct.lift_tmul]
  have key : ∀ (a : k ⊗[ℤ] C) (y : H), L a y - φ a • y ∈ mSub σ χ ⊤ := by
    intro a y
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul l c =>
      rw [hLt, hφt, mul_smul, ← smul_sub]
      refine Submodule.smul_mem _ l (Submodule.subset_span ⟨c, y, trivial, ?_⟩)
      simp
    | add a b ha hb =>
      convert add_mem ha hb using 1
      rw [map_add, map_add, LinearMap.add_apply, add_smul]
      abel
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, y, -, rfl⟩ := hz
      have hmem : ((1 : k) ⊗ₜ c - (χ c) ⊗ₜ (1 : C)) ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker]
        simp [hφt]
      have := Submodule.smul_mem_smul hmem (Submodule.mem_top (x := y))
      convert this using 1
      rw [hsmul, map_sub, LinearMap.sub_apply, hLt, hLt]
      simp
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul l z _ hz =>
      have : l • z = ((l ⊗ₜ (1 : C) : k ⊗[ℤ] C)) • z := by
        rw [hsmul, hLt]; simp
      rw [this]
      exact Submodule.smul_mem _ _ hz
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun a b ha hb => add_mem ha hb)
    rw [hsmul]
    have := key a y
    rwa [(RingHom.mem_ker).1 ha, zero_smul, sub_zero] at this

end GlobalTheory.HTRho
