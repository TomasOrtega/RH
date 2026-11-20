import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InclTprodUpdate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift.ItNe

open GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace

/- English proof (translation)
Introduce `hHC D V W S S' M M' θ ω pt It hIt h'`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hIt.ne` to reduce the goal to its premises. Establish `key : ∀ φ (w : ∀ τ, M.H τ) (s : Finset D.what₂.Tau) (v : M'.Vec), (∀ τ ∉ s, (v τ : M'.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M' τ) → ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v))) = 0`.

Introduce `φ w s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `v hv`. Establish `e : PiTensorProduct.tprod ℂ v = GlobalTheory.Chain.IoLift.inclK h' (PiTensorProduct.tprod ℂ fun τ => ⟨v τ, hv τ (by simp)⟩)`.

Rewrite using `[GlobalTheory.Chain.IoLift.inclK, PiTensorProduct.map_tprod]`. Both sides reduce to the same expression. Rewrite using `[e, hcon, map_zero, map_zero]`. Consider the case `insert τ s hτ ih`. Introduce `v hv`.

Take `⟨c, hc⟩` from `hIt.bdd φ w`. Set `ℓ₀ : M'.sm τ →ₗ[ℂ] ℂ` to `(ellT M w ∘ₗ inclT M ∘ₗ It φ) ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v τ`. Take `⟨ℓ, hℓ⟩` from `LinearMap.exists_extend ℓ₀`. Establish `hℓv : ∀ y : M'.sm τ, ℓ (y : M'.H τ) = ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ (Function.update v τ y))))` using `fun y => by`. Use `LinearMap.congr_fun hℓ y` as an intermediate fact.

Simplify `this` using `[ℓ₀, MultilinearMap.toLinearMap_apply]`. Establish `hsob : Formalism.L2.Theta.Sobolev₂ (lieAt W τ) (M'.rep τ) ℓ`. Use `⟨[[]], c * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖, by simp, fun u hu => ?_⟩` and prove the remaining obligations. Establish `hy : u ∈ M'.sm τ` using `Submodule.subset_span hu`. Establish `h1` using `hc (Function.update v τ ⟨u, hy⟩)`.

Rewrite `h1` using `[← hℓv ⟨u, hy⟩]`. Establish `h2 : ∏ ρ, ‖((Function.update v τ ⟨u, hy⟩ ρ : M'.sm ρ) : M'.H ρ)‖ = ‖u‖ * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), Function.update_self]`. Use `congr 1`. Use `Finset.prod_congr rfl fun ρ hρ => ?_` and prove the remaining obligations.

Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hρ)]`. Rewrite `h1` using `[h2]`. Simplify using `only [List.map_cons, List.map_nil, List.foldr_nil, List.sum_cons, List.sum_nil, add_zero]`. Combine the equalities or inequalities in the displayed calculation. Establish `hk : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M' τ, ℓ u = 0`.

Introduce `u hu`. Establish `hy : u ∈ M'.sm τ` using `h' τ hu`. Rewrite using `[show u = ((⟨u, hy⟩ : M'.sm τ) : M'.H τ) from rfl, hℓv]`. Use `ih _ fun ρ hρ => ?_` and prove the remaining obligations. Distinguish the cases in `e : ρ = τ`.

Substitute `e` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `hu`. Rewrite using `[Function.update_of_ne e]; exact hv ρ (by simp [e, hρ])`. Establish `h0` using `GlobalTheory.KFiniteDense.eq_zero_of_kFin hHC D W S' M' τ ℓ hsob hk (v τ) (v τ).2`.

Rewrite `h0` using `[hℓv, Function.update_eq_self]`. Then use the resulting hypothesis. Use `LinearMap.ext fun φ => LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.zero_apply]`. Proceed by induction on `x using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r v`.

Rewrite using `[map_smul]`. Establish `h0 : It φ (PiTensorProduct.tprod ℂ v) = 0`. Use `(tensorLaw D V S M).inj ?_` and prove the remaining obligations. Rewrite using `[map_zero]`. Conclude with `(tensorLaw D V S M).sep _ fun w => key φ w Finset.univ v (by simp)`.

Rewrite using `[h0, smul_zero]`. Consider the case `add a b ha hb => rw [map_add, ha, hb, add_zero]`.
-/
theorem exists_ne_zero_inclK : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank → (WO V W → ℂ)) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsItW θ M M' ω pt It → ∀ h' : GlobalTheory.Chain.IoLift.KSm M', ∃ φ y, It φ (GlobalTheory.Chain.IoLift.inclK h' y) ≠ 0 := by
  classical
  intro hHC D V W S S' M M' θ ω pt It hIt h'
  by_contra hcon
  push_neg at hcon
  apply hIt.ne
  have key : ∀ φ (w : ∀ τ, M.H τ) (s : Finset D.what₂.Tau) (v : M'.Vec),
      (∀ τ ∉ s, (v τ : M'.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M' τ) →
      ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v))) = 0 := by
    intro φ w s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      have e : PiTensorProduct.tprod ℂ v =
          GlobalTheory.Chain.IoLift.inclK h' (PiTensorProduct.tprod ℂ fun τ => ⟨v τ, hv τ (by simp)⟩) := by
        rw [GlobalTheory.Chain.IoLift.inclK, PiTensorProduct.map_tprod]; rfl
      rw [e, hcon, map_zero, map_zero]
    | insert τ s hτ ih =>
      intro v hv
      obtain ⟨c, hc⟩ := hIt.bdd φ w
      let ℓ₀ : M'.sm τ →ₗ[ℂ] ℂ :=
        (ellT M w ∘ₗ inclT M ∘ₗ It φ) ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v τ
      obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
      have hℓv : ∀ y : M'.sm τ, ℓ (y : M'.H τ) =
          ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ (Function.update v τ y)))) := fun y => by
        have := LinearMap.congr_fun hℓ y
        simpa [ℓ₀, MultilinearMap.toLinearMap_apply] using this
      have hsob : Formalism.L2.Theta.Sobolev₂ (lieAt W τ) (M'.rep τ) ℓ := by
        refine ⟨[[]], c * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖, by simp, fun u hu => ?_⟩
        have hy : u ∈ M'.sm τ := Submodule.subset_span hu
        have h1 := hc (Function.update v τ ⟨u, hy⟩)
        rw [← hℓv ⟨u, hy⟩] at h1
        have h2 : ∏ ρ, ‖((Function.update v τ ⟨u, hy⟩ ρ : M'.sm ρ) : M'.H ρ)‖ =
            ‖u‖ * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖ := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), Function.update_self]
          congr 1
          refine Finset.prod_congr rfl fun ρ hρ => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
        rw [h2] at h1
        simp only [List.map_cons, List.map_nil, List.foldr_nil, List.sum_cons, List.sum_nil, add_zero]
        calc ‖ℓ u‖ ≤ c * (‖u‖ * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖) := h1
          _ = c * (∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖) * ‖u‖ := by ring
      have hk : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M' τ, ℓ u = 0 := by
        intro u hu
        have hy : u ∈ M'.sm τ := h' τ hu
        rw [show u = ((⟨u, hy⟩ : M'.sm τ) : M'.H τ) from rfl, hℓv]
        refine ih _ fun ρ hρ => ?_
        by_cases e : ρ = τ
        · subst e; rw [Function.update_self]; exact hu
        · rw [Function.update_of_ne e]; exact hv ρ (by simp [e, hρ])
      have h0 := GlobalTheory.KFiniteDense.eq_zero_of_kFin hHC D W S' M' τ ℓ hsob hk (v τ) (v τ).2
      rwa [hℓv, Function.update_eq_self] at h0
  refine LinearMap.ext fun φ => LinearMap.ext fun x => ?_
  simp only [LinearMap.zero_apply]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul]
    have h0 : It φ (PiTensorProduct.tprod ℂ v) = 0 := by
      refine (tensorLaw D V S M).inj ?_
      rw [map_zero]
      exact (tensorLaw D V S M).sep _ fun w => key φ w Finset.univ v (by simp)
    rw [h0, smul_zero]
  | add a b ha hb => rw [map_add, ha, hb, add_zero]

end GlobalTheory.Chain.IoLift.ItNe
