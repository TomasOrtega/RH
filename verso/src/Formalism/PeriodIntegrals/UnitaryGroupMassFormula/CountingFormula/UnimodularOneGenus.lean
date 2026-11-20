import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsIsomSelfDual
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.PairUnitLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsTraceNotMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnimodOneGenus
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.StdLatEqSpan

open NumberField

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.UG

open Formalism.HermitianLattices.Ext.L3.WA

/- English proof (translation)
Introduce `K _ _ _ V _ _ _ _ _ h hK hs hnd L M hLl hMl hLu hMu p hp`. Establish `hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K)` using `PI.UG.W.star_mem_range K`. Establish `huL` using `(Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs hstar L hLl.fg).2.mp hLu p hp`. Establish `huM` using `(Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs hstar M hMl.fg).2.mp hMu p hp`. Establish `hS` using `isHermSemilocal_locRing hK hp`.

Establish `hL'` using `isSelfDualMod_loc hLl hp.isPrime huL`. Establish `hM'` using `isSelfDualMod_loc hMl hp.isPrime huM`. Take `⟨g, hg, hiff⟩` from `exists_isom_selfDual hS hs hnd (fun w y hyw hw hy => hP K hK p hp V h hs w y hyw hw hy) hL' hM'`. Use `⟨g, hg, ?_⟩` and prove the remaining obligations. Use extensionality with `w`.

Simplify using `only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`. Conclude with `(hiff v).1 hv`. Introduce `hw`.

Use `⟨g.symm w, (hiff _).2 ?_, by simp⟩` and prove the remaining obligations. Simplify using `using hw`.
-/
theorem unimodOneGenus_of (hP : PairUnitLoc) : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.UnimodOneGenus := by
  intro K _ _ _ V _ _ _ _ _ h hK hs hnd L M hLl hMl hLu hMu p hp
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    PI.UG.W.star_mem_range K
  have huL := (Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs hstar L hLl.fg).2.mp hLu p hp
  have huM := (Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs hstar M hMl.fg).2.mp hMu p hp
  have hS := isHermSemilocal_locRing hK hp
  have hL' := isSelfDualMod_loc hLl hp.isPrime huL
  have hM' := isSelfDualMod_loc hMl hp.isPrime huM
  obtain ⟨g, hg, hiff⟩ := exists_isom_selfDual hS hs hnd
    (fun w y hyw hw hy => hP K hK p hp V h hs w y hyw hw hy) hL' hM'
  refine ⟨g, hg, ?_⟩
  ext w
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (hiff v).1 hv
  · intro hw
    refine ⟨g.symm w, (hiff _).2 ?_, by simp⟩
    simpa using hw

/- English proof (translation)
The claim follows from `unimodOneGenus_of pair_unit_local`.
-/
theorem unimodular_one_genus : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.UnimodOneGenus :=
  unimodOneGenus_of pair_unit_local

end PI.UnitaryGroupMassFormula.CntFormula.UG
