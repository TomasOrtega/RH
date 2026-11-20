import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaAEqOfUnip

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirabolic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Unfold `GlobalTheory.PRep.twKer`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Establish `key : ∀ (u : GlobalTheory.BZMir.MirUin k n) (w : V), τ (GlobalTheory.BZMir.levi k n m) (τ u w) = τ (GlobalTheory.BZMir.levi k n m * u * (GlobalTheory.BZMir.levi k n m)⁻¹) (τ (GlobalTheory.BZMir.levi k n m) w)`. Introduce `u w`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]`. Use `first`. Consider the case `(obtain ⟨u, w, rfl⟩ := hx`. Take `⟨hm, hc⟩` from `GlobalTheory.CompanionTheory.BZMirabolic.thetaConj k ψ n a m u`. Simplify using `only [SetLike.mem_coe, Submodule.mem_comap, map_sub, Units.smul_def, map_smul]`.

Rewrite using `[key, hc]`. Conclude with `Submodule.subset_span ⟨⟨_, hm⟩, _, rfl⟩)`. Consider the case `(obtain ⟨⟨u, w⟩, rfl⟩ := hx`. Take `⟨hm, hc⟩` from `GlobalTheory.CompanionTheory.BZMirabolic.thetaConj k ψ n a m u`. Simplify using `only [SetLike.mem_coe, Submodule.mem_comap, map_sub, Units.smul_def, map_smul]`.

Rewrite using `[key, hc]`. Conclude with `Submodule.subset_span ⟨(⟨_, hm⟩, _), rfl⟩)`.
-/
theorem twKer_le_comap_levi (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k n) V) (a : Fin n → k) (m : GL (Fin n) k) :
    twKer τ (MirUin k n) (thetaA k ψ (vecMul a (m : Matrix (Fin n) (Fin n) k))) ≤
      (twKer τ (MirUin k n) (thetaA k ψ a)).comap (τ (levi k n m)) := by
  unfold GlobalTheory.PRep.twKer
  rw [Submodule.span_le]
  intro x hx
  have key : ∀ (u : GlobalTheory.BZMir.MirUin k n) (w : V),
      τ (GlobalTheory.BZMir.levi k n m) (τ u w) =
        τ (GlobalTheory.BZMir.levi k n m * u * (GlobalTheory.BZMir.levi k n m)⁻¹) (τ (GlobalTheory.BZMir.levi k n m) w) := by
    intro u w
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  first
    | (obtain ⟨u, w, rfl⟩ := hx
       obtain ⟨hm, hc⟩ := GlobalTheory.CompanionTheory.BZMirabolic.thetaConj k ψ n a m u
       simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, Units.smul_def, map_smul]
       rw [key, hc]
       exact Submodule.subset_span ⟨⟨_, hm⟩, _, rfl⟩)
    | (obtain ⟨⟨u, w⟩, rfl⟩ := hx
       obtain ⟨hm, hc⟩ := GlobalTheory.CompanionTheory.BZMirabolic.thetaConj k ψ n a m u
       simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, Units.smul_def, map_smul]
       rw [key, hc]
       exact Submodule.subset_span ⟨(⟨_, hm⟩, _), rfl⟩)

/- English proof (translation)
Unfold `GlobalTheory.BZMir.Fun.TwKerConj`. Introduce `ψ n V _ _ τ a m v`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Conclude with `GlobalTheory.CompanionTheory.BZMirabolic.twKer_le_comap_levi ψ τ a m hv`.

Introduce `hv`. Establish `ha : vecMul (vecMul a (m : Matrix (Fin n) (Fin n) k)) ((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = a`. Rewrite using `[vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]`. Rewrite `hv` using `[← ha]`. Establish `h` using `GlobalTheory.CompanionTheory.BZMirabolic.twKer_le_comap_levi ψ τ _ m⁻¹ hv`.

Rewrite `h` using `[Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]`. Conclude with `h`.
-/
theorem twKerConj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : TwKerConj k := by
  unfold GlobalTheory.BZMir.Fun.TwKerConj
  intro ψ n V _ _ τ a m v
  constructor
  · intro hv
    exact GlobalTheory.CompanionTheory.BZMirabolic.twKer_le_comap_levi ψ τ a m hv
  · intro hv
    have ha : vecMul (vecMul a (m : Matrix (Fin n) (Fin n) k))
        ((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = a := by
      rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
    rw [← ha] at hv
    have h := GlobalTheory.CompanionTheory.BZMirabolic.twKer_le_comap_levi ψ τ _ m⁻¹ hv
    rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel,
      map_one, map_one, Module.End.one_apply] at h
    exact h

end GlobalTheory.CompanionTheory.BZMirabolic

end
