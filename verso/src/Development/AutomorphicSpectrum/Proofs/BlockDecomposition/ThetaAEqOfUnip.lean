import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirabolic

variable {k : Type} [Field k]

/- English proof (translation)
Establish `key : (unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) x) = w`. Rewrite using `[MulEquiv.symm_apply_eq]`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hx`. Use `show Circle.toUnits (ψ (a ⬝ᵥ ((unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) x)).toAdd)) = _`.

Rewrite using `[key]`.
-/
theorem thetaA_eq_of_unip (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (x : MirUin k n)
    (w : Multiplicative (Fin n → k))
    (hx : ((x : Mir k n) : GL (Fin (n + 1)) k) = unip k n w) :
    thetaA k ψ a x = Circle.toUnits (ψ (a ⬝ᵥ w.toAdd)) := by
  have key : (unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) x) = w := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    exact hx
  show Circle.toUnits (ψ (a ⬝ᵥ ((unipEquiv k n).symm
    ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) x)).toAdd)) = _
  rw [key]

/- English proof (translation)
Introduce `ψ n a m u`. Take `⟨v, hv⟩` from `(u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)`. Establish `hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v` using `hv.symm`. Establish `e : glEmb k n m * ((u : Mir k n) : GL (Fin (n + 1)) k) * (glEmb k n m)⁻¹ = unip k n (Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k).mulVec v.toAdd))`. Rewrite using `[hv', glEmb_mul_unip', mul_inv_cancel_right]`.

Establish `h : levi k n m * (u : Mir k n) * (levi k n m)⁻¹ ∈ MirUin k n` using `by show glEmb k n m * ((u : Mir k n) : GL (Fin (n + 1)) k) * (glEmb k n m)⁻¹ ∈ MirU k n`. Rewrite using `[e]`. Conclude with `⟨_, rfl⟩`. Use `⟨h, ?_⟩` and prove the remaining obligations. Rewrite using `[thetaA_eq_of_unip ψ _ u v hv', thetaA_eq_of_unip ψ a ⟨_, h⟩ _ e]`.

Simplify using `only [toAdd_ofAdd]`. Rewrite using `[dotProduct_mulVec]`.
-/
theorem thetaConj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : ThetaConj k := by
  intro ψ n a m u
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  have e : glEmb k n m * ((u : Mir k n) : GL (Fin (n + 1)) k) * (glEmb k n m)⁻¹ =
      unip k n (Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k).mulVec v.toAdd)) := by
    rw [hv', glEmb_mul_unip', mul_inv_cancel_right]
  have h : levi k n m * (u : Mir k n) * (levi k n m)⁻¹ ∈ MirUin k n := by
    show glEmb k n m * ((u : Mir k n) : GL (Fin (n + 1)) k) * (glEmb k n m)⁻¹ ∈ MirU k n
    rw [e]
    exact ⟨_, rfl⟩
  refine ⟨h, ?_⟩
  rw [thetaA_eq_of_unip ψ _ u v hv', thetaA_eq_of_unip ψ a ⟨_, h⟩ _ e]
  simp only [toAdd_ofAdd]
  rw [dotProduct_mulVec]

end GlobalTheory.CompanionTheory.BZMirabolic

end
