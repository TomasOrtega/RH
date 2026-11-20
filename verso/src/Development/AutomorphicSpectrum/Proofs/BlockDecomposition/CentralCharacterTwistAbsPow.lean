import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.Dblock

/- English proof (translation)
Rewrite using `[← Representation.Equiv.conj_apply_self g φ, LinearEquiv.conj_apply]`. Simplify using `[h]`. Use `congr 1`. Conclude with `φ.right_inv w`.
-/
theorem smul_of_equiv_nu {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) (g : G) (c : ℂ)
    (h : ∀ v, π g v = c • v) (w : W) : σ g w = c • w := by
  rw [← Representation.Equiv.conj_apply_self g φ, LinearEquiv.conj_apply]
  simp [h]
  congr 1
  exact φ.right_inv w

/- English proof (translation)
Introduce `k _ _ _ _ x s t c hx v`. Establish `hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) = t ^ x.1`. Use `ext`. Simplify using `[Matrix.GeneralLinearGroup.scalar]`. Use `smul_of_equiv_nu (x.twEquiv (absPow k s) (isSmoothChar_absPow s)) (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) _ (fun u => ?_) v` and prove the remaining obligations.

Rewrite using `[GlobalTheory.SmGL.twist_apply, GlobalTheory.SmGL.detChar_apply, hx u, smul_smul, hdet, mul_comm]`.
-/
theorem scalarBy_nu : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL k) (s : ℂ) (t : kˣ) (c : ℂ), Zl.ScalarBy x t c →
      Zl.ScalarBy (x.nu s) t (c * ((absPow k s (t ^ x.1) : ℂˣ) : ℂ)) := by
  intro k _ _ _ _ x s t c hx v
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) = t ^ x.1 := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
  refine smul_of_equiv_nu (x.twEquiv (absPow k s) (isSmoothChar_absPow s))
    (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) _ (fun u => ?_) v
  rw [GlobalTheory.SmGL.twist_apply, GlobalTheory.SmGL.detChar_apply, hx u, smul_smul, hdet, mul_comm]

end GlobalTheory.CompanionTheory.Dblock
