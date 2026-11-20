import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecTheta

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

/- English proof (translation)
Set `U : Submodule ℂ (WO S T → ℂ)` to `{ carrier := {g | IsThetaFunO ψ S T g} add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb zero_mem' := GlobalTheory.OrientedHeis.theta_zero smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }`. Use `show f ∈ U`. Rewrite using `[← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]`. Introduce `l hl`. Set `A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)` to `LinearMap.pi fun w => l ∘ₗ GlobalTheory.SplitScalar.heisL ψ S T w`.

Establish `hA0 : ∀ g w, A g w = l (heisO ψ S T w g)` using `fun _ _ => rfl`. Establish `hA : ∀ u g, A (heisO ψ S T u g) = heisO ψ S T u (A g)` using `fun u g => by`. Use function extensionality and compare the values at `w`. Rewrite using `[hA0, GlobalTheory.OrientedHeis.heisO_heisO, map_smul]`. Both sides reduce to the same expression.

Establish `hf0 : A f₀ = 0`. Use function extensionality and compare the values at `w`. Conclude with `(Submodule.mem_dualAnnihilator l).1 hl _ ((GlobalTheory.ThetaClosed.thetaClosed ψ θ hψ hθ S T f₀ h₀).1 w)`. Take `⟨⟨Tm, hT⟩, hall⟩` from `h`. Establish `hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm)` using `{ trans := fun Φ hΦ x hx => by`.

Rewrite using `[LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hT.trans Φ hΦ x hx, hA x]`. Conclude with `((GlobalTheory.SplitScalar.heisL ψ S T x).map_add _ _).symm`. Use `modul := fun Φ hΦ y hy => by`. Rewrite using `[LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hT.modul Φ hΦ y hy, hA y]`. Conclude with `((GlobalTheory.SplitScalar.heisL ψ S T y).map_add _ _).symm`.

Use `vac := by`. Rewrite using `[LinearMap.add_apply, LinearMap.comp_apply, hT.vac, hf0, add_zero] }`. Establish `e1 : f = Tm Φ` using `hall Tm hT`. Establish `e2 : f = (Tm + A ∘ₗ Tm) Φ` using `hall _ hT'`. Rewrite `e2` using `[LinearMap.add_apply, LinearMap.comp_apply, ← e1]`.

Establish `e3` using `congrFun (left_eq_add.1 e2) 0`. Rewrite `e3` using `[hA0, GlobalTheory.OrientedHeis.heisO_zero]`. Then use the resulting hypothesis.
-/
theorem isThetaFunO_of_thetaAt (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {e : AE D} {Λ : AddSubgroup (WO S T)}
    {c : ℂ} {f₀ Φ f : WO S T → ℂ} (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (h₀ : IsThetaFunO ψ S T f₀) : IsThetaFunO ψ S T f := by
  let U : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
      zero_mem' := GlobalTheory.OrientedHeis.theta_zero
      smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
  show f ∈ U
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  let A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    LinearMap.pi fun w => l ∘ₗ GlobalTheory.SplitScalar.heisL ψ S T w
  have hA0 : ∀ g w, A g w = l (heisO ψ S T w g) := fun _ _ => rfl
  have hA : ∀ u g, A (heisO ψ S T u g) = heisO ψ S T u (A g) := fun u g => by
    funext w
    rw [hA0, GlobalTheory.OrientedHeis.heisO_heisO, map_smul]
    rfl
  have hf0 : A f₀ = 0 := by
    funext w
    exact (Submodule.mem_dualAnnihilator l).1 hl _ ((GlobalTheory.ThetaClosed.thetaClosed ψ θ hψ hθ S T f₀ h₀).1 w)
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.trans Φ hΦ x hx, hA x]
        exact ((GlobalTheory.SplitScalar.heisL ψ S T x).map_add _ _).symm
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.modul Φ hΦ y hy, hA y]
        exact ((GlobalTheory.SplitScalar.heisL ψ S T y).map_add _ _).symm
      vac := by
        rw [LinearMap.add_apply, LinearMap.comp_apply, hT.vac, hf0, add_zero] }
  have e1 : f = Tm Φ := hall Tm hT
  have e2 : f = (Tm + A ∘ₗ Tm) Φ := hall _ hT'
  rw [LinearMap.add_apply, LinearMap.comp_apply, ← e1] at e2
  have e3 := congrFun (left_eq_add.1 e2) 0
  rwa [hA0, GlobalTheory.OrientedHeis.heisO_zero] at e3

variable {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)}
  {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
  {ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ}

/- English proof (translation)
Take `⟨⟨hψ, h0⟩, e, -, h⟩` from `h`. Conclude with `isThetaFunO_of_thetaAt hψ h0.inf h h0.theta`.
-/
theorem isThetaFunO_stepVec {LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank}
    {χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f) : IsThetaFunO ψ S T f := by
  obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := h
  exact isThetaFunO_of_thetaAt hψ h0.inf h h0.theta

/- English proof (translation)
Take `⟨⟨hψ, h0⟩, e, -, h⟩` from `h`. Conclude with `isThetaFunO_of_thetaAt hψ h0.inf h h0.theta`.
-/
theorem isThetaFunO_thPVec {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) : IsThetaFunO ψ S T f := by
  obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := h
  exact isThetaFunO_of_thetaAt hψ h0.inf h h0.theta

end GlobalTheory.VecTheta

end
