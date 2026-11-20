import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbD
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHkSmooth
open UpperTheory.V.Lit.Geo
open scoped ContDiff

/- English proof (translation)
Introduce `Γ V S _ _ _ _ d G W hW q`. Use `⟨fun w s p hp => ?_, fun w s p hp => ?_⟩` and prove the remaining obligations. Use `toOm_apply G (z := fun s => pb (flow (W s) 1) (w.1 s)) (fun s x hx => ?_) s hp` and prove the remaining obligations. Establish `hx' : flow (W s) 1 x ∈ G.Y` using `(hW.field s).2 x hx 1 ⟨zero_le_one, le_rfl⟩`. Establish `h1 : ContDiffAt ℝ ∞ (W s) x` using `(hW.field s).1.contDiffAt (G.isOpen.mem_nhds hx)`.

Establish `h2 : ContDiffAt ℝ ∞ (flow (W s) 1) x` using `contDiffAt_id.add (h1.const_smul (1 : ℝ))`. Establish `h3 : ContDiffAt ℝ ∞ (w.1 s) (flow (W s) 1 x)` using `(w.2 s).1.contDiffAt (G.isOpen.mem_nhds hx')`. Conclude with `(pbD V V (Fin d → ℂ) q _ _ x h2 h3).1.contDiffWithinAt`. Conclude with `toOm_apply G (z := fun s => hom (W s) (w.1 s)) (fun s => (hkSmooth V (Fin d → ℂ) G.Y G.isOpen (W s) (hW.field s) q (w.1 s) (w.2 s).1).2.2.2) s hp`.
-/
theorem UpperTheory.V.Lit.Geo.omApply :
    OmApply := by
  intro Γ V S _ _ _ _ d G W hW q
  refine ⟨fun w s p hp => ?_, fun w s p hp => ?_⟩
  · refine toOm_apply G (z := fun s => pb (flow (W s) 1) (w.1 s)) (fun s x hx => ?_) s hp
    have hx' : flow (W s) 1 x ∈ G.Y := (hW.field s).2 x hx 1 ⟨zero_le_one, le_rfl⟩
    have h1 : ContDiffAt ℝ ∞ (W s) x := (hW.field s).1.contDiffAt (G.isOpen.mem_nhds hx)
    have h2 : ContDiffAt ℝ ∞ (flow (W s) 1) x := contDiffAt_id.add (h1.const_smul (1 : ℝ))
    have h3 : ContDiffAt ℝ ∞ (w.1 s) (flow (W s) 1 x) := (w.2 s).1.contDiffAt (G.isOpen.mem_nhds hx')
    exact (pbD V V (Fin d → ℂ) q _ _ x h2 h3).1.contDiffWithinAt
  · exact toOm_apply G (z := fun s => hom (W s) (w.1 s))
      (fun s => (hkSmooth V (Fin d → ℂ) G.Y G.isOpen (W s) (hW.field s) q (w.1 s) (w.2 s).1).2.2.2) s hp
