import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}

/- English proof (translation)
Simplify using `level := ⟨⊤, by simp, fun u _ _ => by funext w; simp [Heisenberg₂]⟩ cont := continuous_const smooth _ _ _ _ _ := contDiff_const`.
-/
theorem isThetaFun_zero : IsThetaFun ψ V W 0 where
  quasi γ w := by simp
  level := ⟨⊤, by simp, fun u _ _ => by funext w; simp [Heisenberg₂]⟩
  cont := continuous_const
  smooth _ _ _ _ _ := contDiff_const

/- English proof (translation)
Simplify using `only [Pi.add_apply, hf.quasi γ w, hg.quasi γ w, mul_add] level := by`. Take `⟨U, hUo, hU⟩` from `hf.level`. Take `⟨U', hU'o, hU'⟩` from `hg.level`. Use `⟨U ⊓ U', by simpa using hUo.inter hU'o, fun u hu hinf => ?_⟩` and prove the remaining obligations. Establish `e1` using `hU u (AddSubgroup.mem_inf.1 hu).1 hinf`.

Establish `e2` using `hU' u (AddSubgroup.mem_inf.1 hu).2 hinf`. Use function extensionality and compare the values at `w`. Establish `h1` using `congrFun e1 w`. Establish `h2` using `congrFun e2 w`. Simplify using `only [Heisenberg₂, Pi.add_apply] at h1 h2 ⊢`.

Rewrite using `[mul_add, h1, h2]`. Use `cont := hf.cont.add hg.cont`. Use `smooth k L hL hfin w := (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w)`.
-/
theorem isThetaFun_add {f g : WA V W → ℂ} (hf : IsThetaFun ψ V W f) (hg : IsThetaFun ψ V W g) :
    IsThetaFun ψ V W (f + g) where
  quasi γ w := by simp only [Pi.add_apply, hf.quasi γ w, hg.quasi γ w, mul_add]
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    obtain ⟨U', hU'o, hU'⟩ := hg.level
    refine ⟨U ⊓ U', by simpa using hUo.inter hU'o, fun u hu hinf => ?_⟩
    have e1 := hU u (AddSubgroup.mem_inf.1 hu).1 hinf
    have e2 := hU' u (AddSubgroup.mem_inf.1 hu).2 hinf
    funext w
    have h1 := congrFun e1 w
    have h2 := congrFun e2 w
    simp only [Heisenberg₂, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  cont := hf.cont.add hg.cont
  smooth k L hL hfin w := (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w)

/- English proof (translation)
Simplify using `only [Pi.smul_apply, smul_eq_mul, hf.quasi γ w, mul_left_comm] level := by`. Take `⟨U, hUo, hU⟩` from `hf.level`. Use `⟨U, hUo, fun u hu hinf => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Establish `h1` using `congrFun (hU u hu hinf) w`.

Simplify using `only [Heisenberg₂, Pi.smul_apply, smul_eq_mul] at h1 ⊢`. Rewrite using `[mul_left_comm, h1]`. Use `cont := continuous_const.mul hf.cont`. Use `smooth k L hL hfin w := contDiff_const.mul (hf.smooth k L hL hfin w)`.
-/
theorem isThetaFun_smul (c : ℂ) {f : WA V W → ℂ} (hf : IsThetaFun ψ V W f) :
    IsThetaFun ψ V W (c • f) where
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul, hf.quasi γ w, mul_left_comm]
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hinf => ?_⟩
    funext w
    have h1 := congrFun (hU u hu hinf) w
    simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [mul_left_comm, h1]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := contDiff_const.mul (hf.smooth k L hL hfin w)

/- English proof (translation)
Introduce `D ψ V W`. Use `⟨{ carrier := {f | IsThetaFun ψ V W f} add_mem' := fun hf hg => isThetaFun_add hf hg zero_mem' := isThetaFun_zero smul_mem' := fun c _ hf => isThetaFun_smul c hf }, fun f => Iff.rfl⟩` and prove the remaining obligations.
-/
theorem exists_thetaSubmodule : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D),
    ∃ M : Submodule ℂ (WA V W → ℂ), ∀ f, f ∈ M ↔ IsThetaFun ψ V W f := by
  intro D ψ V W
  refine ⟨{ carrier := {f | IsThetaFun ψ V W f}
            add_mem' := fun hf hg => isThetaFun_add hf hg
            zero_mem' := isThetaFun_zero
            smul_mem' := fun c _ hf => isThetaFun_smul c hf }, fun f => Iff.rfl⟩

end GlobalTheory.FockCompare
