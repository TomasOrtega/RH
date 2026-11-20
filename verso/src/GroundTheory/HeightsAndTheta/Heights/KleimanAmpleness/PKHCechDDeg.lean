import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHTheoremSAux
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace KHCechDDeg

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨m, t, a, ht, hm, rfl⟩` from `hx`. Rewrite using `[GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.cellRes_mk h]`. Conclude with `GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep.mk_mem_locPart m ⟨t.1, h t.2⟩ a ht hm`.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul s x _ hx => rw [LinearMap.map_smul_of_tower]`.

Conclude with `Submodule.smul_mem _ s hx`.
-/
theorem cellRes_mem_locPart {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} {c : K → ℤ}
    {J I : ∀ k, Finset (ι k)} (h : KH.cellMon S J ≤ KH.cellMon S I) {x : LocalizedModule (KH.cellMon S J) M}
    (hx : x ∈ KH.locPart ι 𝓜 (KH.cellMon S J) c) :
    KH.cellRes S M J I x ∈ KH.locPart ι 𝓜 (KH.cellMon S I) c := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.cellRes_mk h]
    exact GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep.mk_mem_locPart m ⟨t.1, h t.2⟩ a ht hm
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ s hx

/- English proof (translation)
Distinguish the cases in `hl : l = k`. Substitute `hl` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `Finset.erase_subset _ _`. Rewrite using `[Function.update_of_ne hl]`.
-/
theorem face_subset {K : Type} [DecidableEq K] {ι : K → Type} [∀ k, DecidableEq (ι k)]
    (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl
    rw [Function.update_self]
    exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]

end KHCechDDeg

/- English proof (translation)
Introduce `S _ K _ _ ι _ _ M _ _ _ _ 𝓜 c n φ hφ`. Use `Submodule.mem_pi.mpr fun I _ => ?_` and prove the remaining obligations. Simplify using `only [KH.cechD, LinearMap.pi_apply, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with hI`.

Express the relevant statement in the definitionally equal form `KH.faceSign I.1 k i • KH.cellRes S M _ I.1 (φ ⟨_, hI⟩) ∈ _`. Use `zsmul_mem (KHCechDDeg.cellRes_mem_locPart ?_ (Submodule.mem_pi.mp hφ _ (Set.mem_univ _))) _` and prove the remaining obligations. Conclude with `GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.cellMon_mono (KHCechDDeg.face_subset I.1 k i)`. Rewrite using `[LinearMap.zero_apply]`. Conclude with `zero_mem _`.
-/
theorem KHCechDDeg.full : KH.CechDDegStatement := by
  classical
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 c n φ hφ
  refine Submodule.mem_pi.mpr fun I _ => ?_
  simp only [KH.cechD, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ => ?_
  split_ifs with hI
  · change KH.faceSign I.1 k i • KH.cellRes S M _ I.1 (φ ⟨_, hI⟩) ∈ _
    refine zsmul_mem (KHCechDDeg.cellRes_mem_locPart ?_ (Submodule.mem_pi.mp hφ _ (Set.mem_univ _))) _
    exact GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.cellMon_mono
      (KHCechDDeg.face_subset I.1 k i)
  · rw [LinearMap.zero_apply]
    exact zero_mem _

end GroundTheory.Heights₂.Heights.Kleiman
