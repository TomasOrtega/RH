import Development.AbelianVarietyTheory.Definitions.Divisors.Tpr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.WigCap

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def keep (π : CuspSub E a) : Subalgebra ℂ (Module.End ℂ (Sm E a)) where
  carrier := {z | ∀ φ ∈ π.V, z φ ∈ π.V}
  mul_mem' := fun hx hy φ h => hx _ (hy φ h)
  add_mem' := fun hx hy φ h => π.V.add_mem (hx φ h) (hy φ h)
  algebraMap_mem' := fun c φ h => π.V.smul_mem c h

def res (π : CuspSub E a) : keep π →ₐ[ℂ] Module.End ℂ π.V where
  toFun z := z.1.restrict z.2
  map_one' := LinearMap.ext fun φ => Subtype.ext rfl
  map_mul' _ _ := LinearMap.ext fun φ => Subtype.ext rfl
  map_zero' := LinearMap.ext fun φ => Subtype.ext rfl
  map_add' _ _ := LinearMap.ext fun φ => Subtype.ext rfl
  commutes' _ := LinearMap.ext fun φ => Subtype.ext rfl

/- English proof (translation)
Establish `h : ∀ X, lie E a X ∈ keep π` using `fun X φ hφ => π.stable (.lie X) φ hφ`. Conclude with `(keep π).smul_mem ((keep π).sub_mem (h _) ((keep π).smul_mem (h _) _)) _`.
-/
theorem Eop_mem (π : CuspSub E a) (τ : E →+* ℂ) (i j : Fin a) : Eop τ i j ∈ keep π := by
  have h : ∀ X, lie E a X ∈ keep π := fun X φ hφ => π.stable (.lie X) φ hφ
  exact (keep π).smul_mem ((keep π).sub_mem (h _) ((keep π).smul_mem (h _) _)) _

/- English proof (translation)
Use `LinearMap.ext fun φ => Subtype.ext ?_` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem res_Eop (π : CuspSub E a) (τ : E →+* ℂ) (i j : Fin a) :
    res π ⟨Eop τ i j, Eop_mem π τ i j⟩ = cx τ (lieOp π) i j := by
  refine LinearMap.ext fun φ => Subtype.ext ?_
  rfl

end GlobalTheory.WigCap

open GlobalTheory.WigCap in

/- English proof (translation)
Introduce `E _ _ _ a π τ χ hχ`. Set `X : Fin a → Fin a → keep π` to `fun i j => ⟨Eop τ i j, Eop_mem π τ i j⟩`. Establish `hX : (fun i j => res π (X i j)) = cx τ (lieOp π)` using `funext fun i => funext fun j => res_Eop π τ i j`. Establish `hval : (fun i j => (keep π).val (X i j)) = Eop τ` using `rfl`. Prove the components needed by the constructor for the conclusion.

Introduce `i j k l`. Establish `h` using `glRel_Eop (a := a) τ i j k l`. Rewrite using `[← hX]`. Simplify using `only`. Establish `h2 : X i j * X k l - X k l * X i j = (if j = k then X i l else 0) - (if l = i then X k j else 0)`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subalgebra.coe_sub, Subalgebra.coe_mul]`. Rewrite using `[h]`. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[← map_mul, ← map_mul, ← map_sub, h2, map_sub]`.

Apply the tactic sequence `split_ifs <;> simp`. Introduce `u`. Rewrite using `[← hX, ← map_qdet]`. Use `LinearMap.ext fun φ => Subtype.ext ?_` and prove the remaining obligations. Establish `e1 : ((keep π).val (qdet X (u + ((a : ℂ) - 1) / 2))) = cap τ u`.

Rewrite using `[map_qdet, hval]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `((keep π).val (qdet X (u + ((a : ℂ) - 1) / 2))) φ.1 = _`. Rewrite using `[e1, hχ.2 u φ.1 φ.2, Multiset.map_map, Finset.prod_eq_multiset_prod]`. Simplify using `[Algebra.algebraMap_eq_smul_one]`.
-/
theorem GlobalTheory.capelli_cuspSub : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (χ : Fin a → ℂ), π.HasInfChar τ (Multiset.map χ Finset.univ.val) → GlRel (cx τ (lieOp π)) ∧ ∀ u : ℂ, qdet (cx τ (lieOp π)) (u + ((a : ℂ) - 1) / 2) = algebraMap ℂ _ (∏ s, (u + χ s)) := by
  intro E _ _ _ a π τ χ hχ
  let X : Fin a → Fin a → keep π := fun i j => ⟨Eop τ i j, Eop_mem π τ i j⟩
  have hX : (fun i j => res π (X i j)) = cx τ (lieOp π) := funext fun i => funext fun j => res_Eop π τ i j
  have hval : (fun i j => (keep π).val (X i j)) = Eop τ := rfl
  constructor
  · intro i j k l
    have h := glRel_Eop (a := a) τ i j k l
    rw [← hX]
    simp only
    have h2 : X i j * X k l - X k l * X i j = (if j = k then X i l else 0) - (if l = i then X k j else 0) := by
      apply Subtype.ext
      simp only [Subalgebra.coe_sub, Subalgebra.coe_mul]
      rw [h]
      split_ifs <;> rfl
    rw [← map_mul, ← map_mul, ← map_sub, h2, map_sub]
    split_ifs <;> simp
  · intro u
    rw [← hX, ← map_qdet]
    refine LinearMap.ext fun φ => Subtype.ext ?_
    have e1 : ((keep π).val (qdet X (u + ((a : ℂ) - 1) / 2))) = cap τ u := by
      rw [map_qdet, hval]; rfl
    change ((keep π).val (qdet X (u + ((a : ℂ) - 1) / 2))) φ.1 = _
    rw [e1, hχ.2 u φ.1 φ.2, Multiset.map_map, Finset.prod_eq_multiset_prod]
    simp [Algebra.algebraMap_eq_smul_one]
