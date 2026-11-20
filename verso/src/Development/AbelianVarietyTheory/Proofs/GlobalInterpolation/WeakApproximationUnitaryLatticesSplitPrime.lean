import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces

noncomputable section

namespace GlobalTheory.MomN

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

/- English proof (translation)
Introduce `D p _ _ _ N N' L L' hAdm`. Set `_` to `D.host.cmStar`. Take `⟨hN, hN', hL, hL'⟩` from `hAdm`. Establish `hCM : PI.UG.IsCMUnram D.host.E` using `D.sp.cm.cmUnram`. Establish `hp : p.Prime` using `Fact.out`.

Take `⟨γ, M, hM, hEq, hLM⟩` from `Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N L hL`. Take `⟨γ', M', hM', hEq', hLM'⟩` from `Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N' L' hL'`. Conclude with `⟨γ, γ', M, M', ⟨hN, hN', hM, hM'⟩, hEq, hEq', hLM, hLM'⟩`.
-/
theorem weakApprox_split : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p ≠ 2 → jacobiSym (-(D.host.d : ℤ)) p = 1 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → letI := D.host.cmStar; ∃ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' M M' ∧ EqAt D p (StandardLatticesGL3.stdL D N) M ∧ EqAt D p (StandardLatticesGL3.stdL D N') M' ∧ L = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M ∧ L' = SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M' := by
  intro D p _ _ _ N N' L L' hAdm
  let _ := D.host.cmStar
  obtain ⟨hN, hN', hL, hL'⟩ := hAdm
  have hCM : PI.UG.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hp : p.Prime := Fact.out
  obtain ⟨γ, M, hM, hEq, hLM⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N L hL
  obtain ⟨γ', M', hM', hEq', hLM'⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N' L' hL'
  exact ⟨γ, γ', M, M', ⟨hN, hN', hM, hM'⟩, hEq, hEq', hLM, hLM'⟩

end GlobalTheory.MomN
