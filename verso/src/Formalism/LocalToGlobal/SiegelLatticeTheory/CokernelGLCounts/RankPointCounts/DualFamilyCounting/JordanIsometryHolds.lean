import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemSpanSSelf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSpanHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsNearOfSmul
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.UniformizerValuationHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RebasingHolds

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

/- English proof (translation)
Introduce `K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd L L' hLl hLl' 𝔭 h𝔭 b a b' a' hb hb' hv`. Take `⟨P, hP, rfl⟩` from `exists_maximal_over hK hF h𝔭`. Take `⟨π, hπ, hval⟩` from `hU K F hK hF P hP`. Establish `hda` using `LocF.aniso_of_totPosDef hd`. Take `⟨-, hbL, hbo, hbn, hba⟩` from `hb`.

Take `⟨-, hbL', hbo', hbn', hba'⟩` from `hb'`. Establish `hsp` using `hJ K F V L hLl _ h𝔭 _ b hbL`. Establish `hsp'` using `hJ K F V L' hLl' _ h𝔭 _ b' hbL'`. Establish `hS` using `isHermSemilocal_locRing hK hP`. Take `⟨g, hg, -, hgm⟩` from `core_of_split hs hda (splitAt_of (hE K F V hK hF h hs hd P hP π hπ) (hR K V (locRing P) π h hS hπ hs hda)) _ (Fin _) le_rfl b b' (fun i => vF _ (a i)) 1 hbo hbo' (fun i => by rw [hbn i]; exact hval _ (hba i)) (fun i => by rw [hbn' i, hv i]; exact hval _ (hba' i)) (one_mem _) (fun …`.

Rewrite using `[hsp, hsp']`. Conclude with `⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)`. Use `⟨g, hg, gmap_eq_of_iff fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[← hbL, ← hbL', locF_eq_loc hK hF hP, locF_eq_loc hK hF hP, hL K F V hK hF P hP, hL K F V hK hF P hP]`. Conclude with `hgm v`.
-/
theorem jordanIsom_of (hE : ExactVec) (hR : Rebase) (hL : LocSpan) (hU : UnifVal)
    (hJ : JordSpan) : Formalism.L2.SG.Pf.Cnt.JordanIsom := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd L L' hLl hLl' 𝔭 h𝔭 b a b' a' hb hb' hv
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  obtain ⟨π, hπ, hval⟩ := hU K F hK hF P hP
  have hda := LocF.aniso_of_totPosDef hd
  obtain ⟨-, hbL, hbo, hbn, hba⟩ := hb
  obtain ⟨-, hbL', hbo', hbn', hba'⟩ := hb'
  have hsp := hJ K F V L hLl _ h𝔭 _ b hbL
  have hsp' := hJ K F V L' hLl' _ h𝔭 _ b' hbL'
  have hS := isHermSemilocal_locRing hK hP
  obtain ⟨g, hg, -, hgm⟩ := core_of_split hs hda
    (splitAt_of (hE K F V hK hF h hs hd P hP π hπ) (hR K V (locRing P) π h hS hπ hs hda))
    _ (Fin _) le_rfl b b' (fun i => vF _ (a i)) 1 hbo hbo'
    (fun i => by rw [hbn i]; exact hval _ (hba i))
    (fun i => by rw [hbn' i, hv i]; exact hval _ (hba' i)) (one_mem _)
    (fun v => by
      rw [hsp, hsp']
      exact ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)
  refine ⟨g, hg, gmap_eq_of_iff fun v => ?_⟩
  rw [← hbL, ← hbL', locF_eq_loc hK hF hP, locF_eq_loc hK hF hP, hL K F V hK hF P hP,
    hL K F V hK hF P hP]
  exact hgm v

end Formalism.L2.SG.Pf.G3

namespace Formalism.L2.SG.Pf.Cnt

/- English proof (translation)
The claim follows from `Formalism.L2.SG.Pf.G3.jordanIsom_of Formalism.L2.SG.Pf.TemperedBoundGL3.exact_vector_holds Formalism.L2.SG.Pf.TemperedBoundGL3.rebasing_holds Formalism.L2.SG.Pf.G3.local_span_holds Formalism.L2.SG.Pf.TemperedBoundGL3.uniformizer_valuation_holds Formalism.L2.SG.Pf.G3.jordan_span_h …`.
-/
theorem jordan_isometry_holds : JordanIsom :=
  Formalism.L2.SG.Pf.G3.jordanIsom_of Formalism.L2.SG.Pf.TemperedBoundGL3.exact_vector_holds Formalism.L2.SG.Pf.TemperedBoundGL3.rebasing_holds
    Formalism.L2.SG.Pf.G3.local_span_holds Formalism.L2.SG.Pf.TemperedBoundGL3.uniformizer_valuation_holds Formalism.L2.SG.Pf.G3.jordan_span_holds

end Formalism.L2.SG.Pf.Cnt
