import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilTheta

/- English proof (translation)
Introduce `D θ hθ m n Φ hΦ`. Establish `hy : Continuous fun x : Mx D m n => (fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)` using `continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j => (GlobalTheory.RealWeil.continuous_compAt hθ τ m n).matrix_elem i j`. Establish `hz : Continuous fun x : Mx D m n => (fun i j => finPart D (x i j) : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)` using `continuous_pi fun i => continuous_pi fun j => (GlobalTheory.Member.continuous_finPart D).comp (continuous_id.matrix_elem i j)`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`.

Take `⟨f, g, hg, rfl⟩` from `h`. Use `⟨(f.continuous.comp hy).mul (hg.1.continuous.comp hz), 1, fun _ => f, fun _ => g, fun _ => hg, fun x => ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Consider the case `zero`. Conclude with `⟨continuous_const, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun x => by simp⟩`.

Consider the case `add Φ₁ Φ₂ _ _ h₁ h₂`. Take `⟨c₁, k₁, f₁, g₁, hg₁, hb₁⟩` from `h₁`. Take `⟨c₂, k₂, f₂, g₂, hg₂, hb₂⟩` from `h₂`. Use `⟨c₁.add c₂, k₁ + k₂, Fin.append f₁ f₂, Fin.append g₁ g₂, fun i => ?_, fun x => ?_⟩` and prove the remaining obligations. Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations.

Rewrite using `[Fin.append_left]`. Conclude with `hg₁ i`. Rewrite using `[Fin.append_right]`. Conclude with `hg₂ i`. Rewrite using `[Fin.sum_univ_add]`.

Simplify using `only [Fin.append_left, Fin.append_right]`. Conclude with `(enorm_add_le _ _).trans (add_le_add (hb₁ x) (hb₂ x))`. Consider the case `smul c Φ _ h`. Take `⟨hc, k, f, g, hg, hb⟩` from `h`. Use `⟨hc.const_smul c, k, fun i => c • f i, g, hg, fun x => ?_⟩` and prove the remaining obligations.

Establish `e : ∀ i, ‖(c • f i) (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ = ‖c‖ₑ * ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ` using `fun i => by`. Rewrite using `[smul_apply, smul_eq_mul, mul_assoc, enorm_mul]`. Simplify using `only [e, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← Finset.mul_sum, enorm_mul]`. Use `gcongr`.

Conclude with `hb x`.
-/
theorem schwartzA_continuous_and_dominated : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (Φ : Mx D m n → ℂ),
    Φ ∈ schwartzA θ m n → Continuous Φ ∧ ∃ (k : ℕ) (f : Fin k → SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
      (g : Fin k → (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) ∧
      ∀ x, ‖Φ x‖ₑ ≤ ∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ := by
  intro D θ hθ m n Φ hΦ
  have hy : Continuous fun x : Mx D m n => (fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ) :=
    continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.RealWeil.continuous_compAt hθ τ m n).matrix_elem i j
  have hz : Continuous fun x : Mx D m n =>
      (fun i j => finPart D (x i j) : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.Member.continuous_finPart D).comp (continuous_id.matrix_elem i j)
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨(f.continuous.comp hy).mul (hg.1.continuous.comp hz), 1, fun _ => f, fun _ => g, fun _ => hg, fun x => ?_⟩
    simp
  | zero =>
    exact ⟨continuous_const, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun x => by simp⟩
  | add Φ₁ Φ₂ _ _ h₁ h₂ =>
    obtain ⟨c₁, k₁, f₁, g₁, hg₁, hb₁⟩ := h₁
    obtain ⟨c₂, k₂, f₂, g₂, hg₂, hb₂⟩ := h₂
    refine ⟨c₁.add c₂, k₁ + k₂, Fin.append f₁ f₂, Fin.append g₁ g₂, fun i => ?_, fun x => ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]; exact hg₁ i
      · rw [Fin.append_right]; exact hg₂ i
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      exact (enorm_add_le _ _).trans (add_le_add (hb₁ x) (hb₂ x))
  | smul c Φ _ h =>
    obtain ⟨hc, k, f, g, hg, hb⟩ := h
    refine ⟨hc.const_smul c, k, fun i => c • f i, g, hg, fun x => ?_⟩
    have e : ∀ i, ‖(c • f i) (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ =
        ‖c‖ₑ * ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ := fun i => by
      rw [smul_apply, smul_eq_mul, mul_assoc, enorm_mul]
    simp only [e, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, enorm_mul]
    gcongr
    exact hb x

end GlobalTheory.CompanionTheory.WeilTheta

end
