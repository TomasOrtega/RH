import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.IrredSt

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace MainStatements.Flath2

/- English proof (translation)
Introduce `D V H _ _ _ π hπ w W hW`. Use `set ρ := π.comp (embArch D.sp.cm.sig V.gram w) with hρdef`. Establish `hρ : IsUnitaryRep ρ` using `isUnitaryRep_comp hπ.unitary (continuous_embArch _ _ _)`. Set `δ : IrrU (GArch D.sp.cm.sig V.gram w)` to `⟨W, hW.1.rep, isIrrUnitary_rep hρ hW⟩`. Use `⟨δ, ?_⟩` and prove the remaining obligations.

Use `show isoPart δ.π ρ ⊤ = ⊤`. Use `set P := isoPart δ.π ρ ⊤ with hPdef`. Establish `hP : IsSubrep ρ P` using `isSubrep_isoPart`. Establish `hcomm : ∀ g' : GA D V, projArch D.sp.cm.sig V.gram w g' = 1 → ∀ v ∈ P, π g' v ∈ P`. Introduce `g' hg' v hv`.

Establish `hle : P ≤ P.comap ((π g' : H →L[ℂ] H) : H →ₗ[ℂ] H)`. Use `isoPart_le (hP.1.preimage (π g').continuous) fun T hT x => ?_` and prove the remaining obligations. Use `show π g' (T x) ∈ P`. Establish `hT' : (π g').comp T ∈ homIn δ.π ρ ⊤`. Use `mem_homIn_top.2 fun h y => ?_` and prove the remaining obligations.

Establish `hc : Commute (embArch D.sp.cm.sig V.gram w h) g'` using `commute_embArch _ _ h hg'`. Establish `e1 : π g' (π (embArch D.sp.cm.sig V.gram w h) (T y)) = π (embArch D.sp.cm.sig V.gram w h) (π g' (T y))`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, hc.eq]`. Simplify using `only [ContinuousLinearMap.comp_apply]`. Rewrite using `[(mem_homIn_top.1 hT) h y]`.

Conclude with `e1`. Conclude with `apply_mem_isoPart hT' x`. Conclude with `hle hv`. Establish `hinv : IsSubrep π P`. Use `⟨hP.1, fun g v hv => ?_⟩` and prove the remaining obligations.

Use `set x := projArch D.sp.cm.sig V.gram w g`. Use `set g' : GA D V := (embArch D.sp.cm.sig V.gram w x)⁻¹ * g`. Establish `hg' : projArch D.sp.cm.sig V.gram w g' = 1`. Simplify using `[g', x, map_mul, map_inv]`. Establish `hg : g = embArch D.sp.cm.sig V.gram w x * g'` using `by simp [g']`.

Rewrite using `[hg, map_mul, ContinuousLinearMap.mul_apply]`. Conclude with `hP.2 x _ (hcomm g' hg' v hv)`. Establish `hne : P ≠ ⊥`. Take `⟨y, hyW, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW.2.1`. Introduce `hbot`.

Establish `hsub : W.subtypeL ∈ homIn δ.π ρ ⊤` using `mem_homIn_top.2 fun h z => rfl`. Establish `hm : W.subtypeL ⟨y, hyW⟩ ∈ P` using `apply_mem_isoPart hsub _`. Rewrite `hm` using `[hbot]`. Conclude with `hy0 ((Submodule.mem_bot ℂ).1 hm)`. Conclude with `(hπ.irred.2 P hinv).resolve_left hne`.
-/
theorem compSt : CompSt := by
  intro D V H _ _ _ π hπ w W hW
  set ρ := π.comp (embArch D.sp.cm.sig V.gram w) with hρdef
  have hρ : IsUnitaryRep ρ := isUnitaryRep_comp hπ.unitary (continuous_embArch _ _ _)
  let δ : IrrU (GArch D.sp.cm.sig V.gram w) := ⟨W, hW.1.rep, isIrrUnitary_rep hρ hW⟩
  refine ⟨δ, ?_⟩
  show isoPart δ.π ρ ⊤ = ⊤
  set P := isoPart δ.π ρ ⊤ with hPdef
  have hP : IsSubrep ρ P := isSubrep_isoPart

  have hcomm : ∀ g' : GA D V, projArch D.sp.cm.sig V.gram w g' = 1 → ∀ v ∈ P, π g' v ∈ P := by
    intro g' hg' v hv
    have hle : P ≤ P.comap ((π g' : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      refine isoPart_le (hP.1.preimage (π g').continuous) fun T hT x => ?_
      show π g' (T x) ∈ P
      have hT' : (π g').comp T ∈ homIn δ.π ρ ⊤ := by
        refine mem_homIn_top.2 fun h y => ?_
        have hc : Commute (embArch D.sp.cm.sig V.gram w h) g' := commute_embArch _ _ h hg'
        have e1 : π g' (π (embArch D.sp.cm.sig V.gram w h) (T y)) = π (embArch D.sp.cm.sig V.gram w h) (π g' (T y)) := by
          rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, hc.eq]
        simp only [ContinuousLinearMap.comp_apply]
        rw [(mem_homIn_top.1 hT) h y]
        exact e1
      exact apply_mem_isoPart hT' x
    exact hle hv
  have hinv : IsSubrep π P := by
    refine ⟨hP.1, fun g v hv => ?_⟩
    set x := projArch D.sp.cm.sig V.gram w g
    set g' : GA D V := (embArch D.sp.cm.sig V.gram w x)⁻¹ * g
    have hg' : projArch D.sp.cm.sig V.gram w g' = 1 := by
      simp [g', x, map_mul, map_inv]
    have hg : g = embArch D.sp.cm.sig V.gram w x * g' := by simp [g']
    rw [hg, map_mul, ContinuousLinearMap.mul_apply]
    exact hP.2 x _ (hcomm g' hg' v hv)
  have hne : P ≠ ⊥ := by
    obtain ⟨y, hyW, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.2.1
    intro hbot
    have hsub : W.subtypeL ∈ homIn δ.π ρ ⊤ := mem_homIn_top.2 fun h z => rfl
    have hm : W.subtypeL ⟨y, hyW⟩ ∈ P := apply_mem_isoPart hsub _
    rw [hbot] at hm
    exact hy0 ((Submodule.mem_bot ℂ).1 hm)
  exact (hπ.irred.2 P hinv).resolve_left hne

end MainStatements.Flath2
