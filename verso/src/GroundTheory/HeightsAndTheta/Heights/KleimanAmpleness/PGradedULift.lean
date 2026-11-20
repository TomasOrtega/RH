import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsPres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

/- English proof (translation)
Introduce `S _ N M _ _ _ _ 𝓜`. Set `e : M ≃ₗ[S] ULift.{u} M` to `(ULift.moduleEquiv (R := S)).symm`. Set `eP : M ≃ₗ[Poly S N] ULift.{u} M` to `(ULift.moduleEquiv (R := Poly S N)).symm`. Set `pc : ℤ → Submodule S (ULift.{u} M)` to `fun c => (𝓜.piece c).map (e : M →ₗ[S] ULift.{u} M)`. Establish `hpc : ∀ c, pc c = Submodule.orderIsoMapComap e (𝓜.piece c)` using `fun _ => rfl`.

Establish `hint : DirectSum.IsInternal pc`. Establish `h0` using `(DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 𝓜.isInternal`. Use `(DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `: pc = (Submodule.orderIsoMapComap e) ∘ 𝓜.piece` using `funext hpc`. Rewrite using `[this]`.

Conclude with `h0.1.map_orderIso _`. Establish `h1 : (⨆ c, pc c) = Submodule.orderIsoMapComap e (⨆ c, 𝓜.piece c)`. Rewrite using `[OrderIso.map_iSup]`. Both sides reduce to the same expression. Rewrite using `[h1, h0.2]`.

Conclude with `(Submodule.orderIsoMapComap e).map_top`. Set `𝓜' : GradedPMod S N (ULift.{u} M)` to `{ piece := pc isInternal := hint smul_mem := by`. Introduce `d c p m hp hm`. Take `⟨x, hx, rfl⟩` from `hm`. Use `⟨p • x, 𝓜.smul_mem d c p x hp hx, ?_⟩` and prove the remaining obligations.

Use `rfl }`. Use `⟨ULift.{u} M, inferInstance, inferInstance, inferInstance, inferInstance, 𝓜', ⟨eP.toLinearMap, fun c m hm => ⟨m, hm, rfl⟩⟩, ⟨eP.symm.toLinearMap, fun c m hm => ?_⟩, fun m => rfl, fun m => rfl⟩` and prove the remaining obligations. Take `⟨x, hx, rfl⟩` from `hm`. Conclude with `hx`.
-/
theorem GradedULift.proof : GradedULift.Statement.{u, v} := by
  intro S _ N M _ _ _ _ 𝓜
  let e : M ≃ₗ[S] ULift.{u} M := (ULift.moduleEquiv (R := S)).symm
  let eP : M ≃ₗ[Poly S N] ULift.{u} M := (ULift.moduleEquiv (R := Poly S N)).symm
  let pc : ℤ → Submodule S (ULift.{u} M) := fun c => (𝓜.piece c).map (e : M →ₗ[S] ULift.{u} M)
  have hpc : ∀ c, pc c = Submodule.orderIsoMapComap e (𝓜.piece c) := fun _ => rfl
  have hint : DirectSum.IsInternal pc := by
    have h0 := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 𝓜.isInternal
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨?_, ?_⟩
    · have : pc = (Submodule.orderIsoMapComap e) ∘ 𝓜.piece := funext hpc
      rw [this]
      exact h0.1.map_orderIso _
    · have h1 : (⨆ c, pc c) = Submodule.orderIsoMapComap e (⨆ c, 𝓜.piece c) := by
        rw [OrderIso.map_iSup]
        rfl
      rw [h1, h0.2]
      exact (Submodule.orderIsoMapComap e).map_top
  let 𝓜' : GradedPMod S N (ULift.{u} M) :=
    { piece := pc
      isInternal := hint
      smul_mem := by
        intro d c p m hp hm
        obtain ⟨x, hx, rfl⟩ := hm
        refine ⟨p • x, 𝓜.smul_mem d c p x hp hx, ?_⟩
        rfl }
  refine ⟨ULift.{u} M, inferInstance, inferInstance, inferInstance, inferInstance, 𝓜',
    ⟨eP.toLinearMap, fun c m hm => ⟨m, hm, rfl⟩⟩,
    ⟨eP.symm.toLinearMap, fun c m hm => ?_⟩, fun m => rfl, fun m => rfl⟩
  obtain ⟨x, hx, rfl⟩ := hm
  exact hx

end

end GroundTheory.Heights₂.Heights.Kleiman
