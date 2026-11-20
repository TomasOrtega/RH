import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
open scoped TensorProduct
universe u

namespace GlobalTheory.HTRho

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Treat this case separately. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
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
