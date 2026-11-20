import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => let ⟨z, _, e⟩ := GlobalTheory.RingIface.exists_of_mem_FilD_nat l (n := 0) h; ⟨z, e⟩, fun ⟨y, e⟩ => e ▸ GlobalTheory.RingIface.alg_mem_FilD_zero l y⟩`.
-/
private theorem mem_FilD_zero (l : ℕ) [Fact l.Prime] (x : Per.BdR l) :
    x ∈ Per.FilD l 0 ↔ ∃ y : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) y = x :=
  ⟨fun h => let ⟨z, _, e⟩ := GlobalTheory.RingIface.exists_of_mem_FilD_nat l (n := 0) h; ⟨z, e⟩,
    fun ⟨y, e⟩ => e ▸ GlobalTheory.RingIface.alg_mem_FilD_zero l y⟩

/- English proof (translation)
Introduce `l _ Pl AI Td K`. Use `⟨fun x => ?_, fun y z h => ?_⟩` and prove the remaining obligations. Rewrite using `[Td.fil, mem_FilD_zero]`. Use `exists_congr fun y => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ↔ x = Td.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) y)`.

Rewrite using `[RingEquiv.eq_symm_apply, eq_comm]`. Conclude with `(GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1 (Td.eD.symm.injective h)`.
-/
theorem _root_.UpperTheory.KN.fil_zero_eq_range_cD_and_cD_injective :
    ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (K : FinExt l), (∀ x : Pl.R.BdR, x ∈ (Pl.PD K).Fil 0 ↔ ∃ y : Per.BdRp l, x = GlobalTheory.BKGal.JumpDR.cD Td y) ∧ Function.Injective (GlobalTheory.BKGal.JumpDR.cD Td) := by
  intro l _ Pl AI Td K
  refine ⟨fun x => ?_, fun y z h => ?_⟩
  · rw [Td.fil, mem_FilD_zero]
    refine exists_congr fun y => ?_
    change _ ↔ x = Td.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) y)
    rw [RingEquiv.eq_symm_apply, eq_comm]
  · exact (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1 (Td.eD.symm.injective h)
