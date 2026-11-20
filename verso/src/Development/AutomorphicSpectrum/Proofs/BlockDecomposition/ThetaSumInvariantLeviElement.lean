import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThetaInvLevi

/- English proof (translation)
Introduce `D n V ψ χ θ μ ω hS g a hg Φ`. Take `⟨-, -, -, hχ, -, -, -, hW⟩` from `hS`. Take `⟨-, hχ⟩` from `hχ`. Set `a' : GL (Fin n) (Formalism.L2.Theta.AE D)` to `Matrix.GeneralLinearGroup.map (incA D) a`. Establish `hg' : GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 (a' : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D)) 0 0 (GlobalTheory.MixModel.adj ((a'⁻¹ : GL (Fin n) (Formalism.L2.Theta.AE D)) : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D)))` using `hg`.

Establish `hdet : Matrix.GeneralLinearGroup.det a' = Units.map (incA D : D.host.E →* Formalism.L2.Theta.AE D) (Matrix.GeneralLinearGroup.det a)` using `Units.ext (by exact (RingHom.map_det (incA D) a.1).symm)`. Establish `hχ1 : χ (Matrix.GeneralLinearGroup.det a') = 1`. Rewrite using `[hdet]`. Conclude with `hχ _`. Establish `habs : GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a') = 1`.

Rewrite using `[hdet]`. Conclude with `GlobalTheory.Doubling.absE_inclR _`. Establish `hc : ∀ x, ((ω g Φ : GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank n) : Formalism.IndefR.Datum.Mx D V.rank n → ℂ) x = (Φ : Formalism.IndefR.Datum.Mx D V.rank n → ℂ) (x * (a' : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D)))`. Introduce `x`. Rewrite using `[hW.levi g a' hg' Φ x, hχ1, habs]`.

Simplify using `[GlobalTheory.Doubling.npow]`. Establish `hterm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) = Φ.1 ((ξ * (a : Matrix (Fin n) (Fin n) D.host.E)).map (incA D))`. Introduce `ξ`. Rewrite using `[hc, Matrix.map_mul]`. Both sides reduce to the same expression.

Set `e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E` to `{ toFun := fun ξ => ξ * (a : Matrix (Fin n) (Fin n) D.host.E) invFun := fun ξ => ξ * ((a⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) left_inv := fun ξ => by simp [Matrix.mul_assoc] right_inv := fun ξ => by simp [Matrix.mul_assoc] }`. Rewrite using `[tsum_congr hterm]`. Conclude with `e.tsum_eq (fun ξ => Φ.1 (ξ.map (incA D)))`.
-/
theorem theta_levi_invariant : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
    ∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) →
    ∀ Φ : schwartzA θ V.rank n,
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g a hg Φ
  obtain ⟨-, -, -, hχ, -, -, -, hW⟩ := hS
  obtain ⟨-, hχ⟩ := hχ
  let a' : GL (Fin n) (Formalism.L2.Theta.AE D) := Matrix.GeneralLinearGroup.map (incA D) a
  have hg' : GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 (a' : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D)) 0 0
      (GlobalTheory.MixModel.adj ((a'⁻¹ : GL (Fin n) (Formalism.L2.Theta.AE D)) : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D))) :=
    hg
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D : D.host.E →* Formalism.L2.Theta.AE D) (Matrix.GeneralLinearGroup.det a) :=
    Units.ext (by exact (RingHom.map_det (incA D) a.1).symm)
  have hχ1 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]
    exact hχ _
  have habs : GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]
    exact GlobalTheory.Doubling.absE_inclR _
  have hc : ∀ x, ((ω g Φ : GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank n) : Formalism.IndefR.Datum.Mx D V.rank n → ℂ) x =
      (Φ : Formalism.IndefR.Datum.Mx D V.rank n → ℂ) (x * (a' : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D))) := by
    intro x
    rw [hW.levi g a' hg' Φ x, hχ1, habs]
    simp [GlobalTheory.Doubling.npow]
  have hterm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      (ω g Φ).1 (ξ.map (incA D)) = Φ.1 ((ξ * (a : Matrix (Fin n) (Fin n) D.host.E)).map (incA D)) := by
    intro ξ
    rw [hc, Matrix.map_mul]
    rfl
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun ξ => ξ * (a : Matrix (Fin n) (Fin n) D.host.E)
      invFun := fun ξ => ξ * ((a⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)
      left_inv := fun ξ => by simp [Matrix.mul_assoc]
      right_inv := fun ξ => by simp [Matrix.mul_assoc] }
  rw [tsum_congr hterm]
  exact e.tsum_eq (fun ξ => Φ.1 (ξ.map (incA D)))

end GlobalTheory.CompanionTheory.ThetaInvLevi
