import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtFibreLift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGradedSubmodules
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtSkyscraper
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLocIdealKer
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

/- English proof (translation)
Introduce `S _ K _ _ ι _ _ M _ _ _ _ 𝓜 P d _ _ h𝓜 hP hH1 I hI x hx`. Establish `hPh : IsMultiHomogIdeal P` using `hP.1.2.1`. Take `⟨h𝓝', h𝓝''⟩` from `(hG S K ι M 𝓜 h𝓜).2 P hPh`. Establish `hyd : GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ x ∈ KH.locPart ι (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) (KH.cellMon S I.1) d`. Take `⟨m, t, a, ht, hm, rfl⟩` from `GenSESStep.locPart_normal h𝓜 hx`.

Rewrite using `[GenSESStep.locMap_mk]`. Conclude with `GenSESStep.mk_mem_locPart _ t a ht ⟨m, hm, rfl⟩`. Establish `hkill : ∀ p ∈ P, ∀ n : M ⧸ (P • ⊤ : Submodule (MRingOver S ι) M), p • n = 0`. Introduce `p hp n`. Proceed by induction on `n using Submodule.Quotient.induction_on with`.

Consider the case `H m`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.smul_mem_smul hp Submodule.mem_top`. Take `⟨z'', hz'', hz''I⟩` from `hSky S K ι _ _ P d h𝓝'' hP hkill I hI _ hyd`. Establish `hg : KH.IsMGradedMap S ι (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M).subtype` using `fun _ _ hm => hm`.

Establish `hh : KH.IsMGradedMap S ι 𝓜 (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ` using `fun _ m hm => ⟨m, hm, rfl⟩`. Take `⟨z, hz, hzmap⟩` from `(hSES S K ι _ M _ _ 𝓜 _ _ _ h𝓝' h𝓜 h𝓝'' hg hh (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) d 0).2.2.2.2.1 hH1 z'' hz''`. Use `⟨z, hz, ?_⟩` and prove the remaining obligations. Establish `hzI : z I ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d` using `Submodule.mem_pi.mp hz.1 I (Set.mem_univ _)`. Use `(hKer S K ι M 𝓜 P (KH.cellMon S I.1) d h𝓜 hPh (fun _ ht => GenSESStep.cellMon_homog ht) _ (sub_mem hx hzI)).2 ?_` and prove the remaining obligations.

Establish `e : GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ (z I) = z'' I` using `congrFun hzmap I`. Rewrite using `[map_sub]`. Express the relevant statement in the definitionally equal form `_ - GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ (z I) = 0`. Rewrite using `[e, hz''I, sub_self]`.
-/
theorem ClosedPtFibreLift.proof (hG : GradedSubmodules.Statement) (hSES : KH.CechSESStatement)
    (hSky : ClosedPtSkyscraper.Statement) (hKer : LocIdealKer.Statement) : ClosedPtFibreLift.Statement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 P d _ _ h𝓜 hP hH1 I hI x hx
  have hPh : IsMultiHomogIdeal P := hP.1.2.1
  obtain ⟨h𝓝', h𝓝''⟩ := (hG S K ι M 𝓜 h𝓜).2 P hPh

  have hyd : GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ x ∈
      KH.locPart ι (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) (KH.cellMon S I.1) d := by
    obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hx
    rw [GenSESStep.locMap_mk]
    exact GenSESStep.mk_mem_locPart _ t a ht ⟨m, hm, rfl⟩

  have hkill : ∀ p ∈ P, ∀ n : M ⧸ (P • ⊤ : Submodule (MRingOver S ι) M), p • n = 0 := by
    intro p hp n
    induction n using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hp Submodule.mem_top

  obtain ⟨z'', hz'', hz''I⟩ := hSky S K ι _ _ P d h𝓝'' hP hkill I hI _ hyd

  have hg : KH.IsMGradedMap S ι (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) 𝓜
      (P • ⊤ : Submodule (MRingOver S ι) M).subtype := fun _ _ hm => hm
  have hh : KH.IsMGradedMap S ι 𝓜 (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M))
      (P • ⊤ : Submodule (MRingOver S ι) M).mkQ := fun _ m hm => ⟨m, hm, rfl⟩
  obtain ⟨z, hz, hzmap⟩ := (hSES S K ι _ M _ _ 𝓜 _ _ _ h𝓝' h𝓜 h𝓝'' hg hh
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) d 0).2.2.2.2.1 hH1 z'' hz''
  refine ⟨z, hz, ?_⟩
  have hzI : z I ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d := Submodule.mem_pi.mp hz.1 I (Set.mem_univ _)

  refine (hKer S K ι M 𝓜 P (KH.cellMon S I.1) d h𝓜 hPh (fun _ ht => GenSESStep.cellMon_homog ht) _
    (sub_mem hx hzI)).2 ?_
  have e : GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ (z I) = z'' I :=
    congrFun hzmap I
  rw [map_sub]
  change _ - GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ (z I) = 0
  rw [e, hz''I, sub_self]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
