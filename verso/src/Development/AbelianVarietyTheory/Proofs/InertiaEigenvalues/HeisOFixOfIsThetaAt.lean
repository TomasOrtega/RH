import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.VacFix

variable {D : D7}

/- English proof (translation)
Establish `h0 : hO S T x y = 0`. Unfold `hO`. Use `Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Use `h c b d a` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.

Unfold `symplO`. Rewrite using `[h0, mul_zero, map_zero]`.
-/
theorem symplO_eq_zero (S T : HSp D) (x y : WO S T)
    (h : ∀ c b d a, cA D (y c b) * x d a = 0) : symplO S T x y = 0 := by
  have h0 : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    have := h c b d a
    calc _ = incA D ((HSpace.gram S)⁻¹ a b) * incA D (HSpace.gram T c d) *
        (cA D (y c b) * x d a) := by ring
      _ = 0 := by rw [this, mul_zero]
  unfold symplO
  rw [h0, mul_zero, map_zero]

/- English proof (translation)
Introduce `D ψ S T e Λ c f₀ Φ f u hf h1 h2 h0`. Take `⟨⟨M, hM⟩, hall⟩` from `hf`. Establish `hM' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ ((GlobalTheory.SplitScalar.heisL ψ S T u) ∘ₗ M)`. Use `⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]`.

Rewrite using `[hM.trans Ψ hΨ x hx, GlobalTheory.SplitScalar.heisO_comm, symplO_eq_zero, AddChar.map_zero_eq_one, one_smul]`. Introduce `c b d a`. Rewrite using `[← hx c b, map_mul]`. Take the linear combination `cA D (x c b) * h2 d a`. Simplify using `only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]`.

Rewrite using `[hM.modul Ψ hΨ y hy, GlobalTheory.SplitScalar.heisO_comm ψ S T y u, symplO_eq_zero, AddChar.map_zero_eq_one, one_smul]`. Introduce `c b d a`. Establish `h3 : cA D e * cA D (u c b) = 0` using `by rw [← map_mul, h1, map_zero]`. Rewrite using `[← hy d a]`. Take the linear combination `y d a * h3`.

Simplify using `only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]`. Rewrite using `[hM.vac, h0]`. Establish `e1` using `hall M hM`. Establish `e2` using `hall _ hM'`. Simplify using `only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply] at e2`.

Rewrite `e2` using `[← e1]`. Conclude with `e2.symm`.
-/
theorem heisO_fix_of_isThetaAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (c : ℂ) (f₀ Φ f : WO S T → ℂ) (u : WO S T), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → (∀ i j, e * u i j = 0) → (∀ i j, cA D e * u i j = 0) → heisO ψ S T u f₀ = f₀ → heisO ψ S T u f = f := by
  intro D ψ S T e Λ c f₀ Φ f u hf h1 h2 h0
  obtain ⟨⟨M, hM⟩, hall⟩ := hf
  have hM' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀
      ((GlobalTheory.SplitScalar.heisL ψ S T u) ∘ₗ M) := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
      rw [hM.trans Ψ hΨ x hx, GlobalTheory.SplitScalar.heisO_comm, symplO_eq_zero, AddChar.map_zero_eq_one,
        one_smul]
      intro c b d a
      rw [← hx c b, map_mul]
      linear_combination cA D (x c b) * h2 d a
    · simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
      rw [hM.modul Ψ hΨ y hy, GlobalTheory.SplitScalar.heisO_comm ψ S T y u, symplO_eq_zero,
        AddChar.map_zero_eq_one, one_smul]
      intro c b d a
      have h3 : cA D e * cA D (u c b) = 0 := by rw [← map_mul, h1, map_zero]
      rw [← hy d a]
      linear_combination y d a * h3
    · simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
      rw [hM.vac, h0]
  have e1 := hall M hM
  have e2 := hall _ hM'
  simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply] at e2
  rw [← e1] at e2
  exact e2.symm

end GlobalTheory.VacFix
