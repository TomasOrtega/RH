import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeomSumOneAddPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrH1Description
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocyclePolesFrobeniusQCrystallineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachOfFrobeniusGammaStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.IntComplex

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `W`. Take `⟨χ, -, -, hγ, hX, hQ, -, -⟩` from `GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h`. Establish `hs : 1 ≤ s` using `h.1`. Take `⟨-, -, -, -, -, hact, -⟩` from `GlobalTheory.Cyc.XX_QQ_properties l ↥(OL LL) s hs`. Take `⟨-, b, hb⟩` from `hact (χ W.gam)`.

Use `⟨⟨1 + W.X * fun _ => b, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `W.γ₀ W.gam (W.Q i) = (1 + W.X i * b) * W.Q i`. Rewrite using `[hγ, hX, hQ, hb, mul_comm]`. Rewrite using `[add_sub_cancel_left]`.

Conclude with `Ideal.mem_span_singleton.2 (dvd_mul_right _ _)`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : (PowerSeries.X : PowerSeries ↥(OL LL)) ∣ GlobalTheory.Cyc.XX l ↥(OL LL) s := by`. Rewrite using `[PowerSeries.X_dvd_iff, GlobalTheory.Cyc.XX]`. Simplify using the standard rewrite rules. Use `⟨fun _ => c, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `W.X i = PowerSeries.X * c`. Rewrite using `[hX, hc]`.
-/
theorem ring_part (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) :
    let W := (HW l).W K s LL h
    (∃ w, W.γA W.gam W.Q = w * W.Q ∧ w - 1 ∈ Ideal.span {W.X}) ∧ ∃ b, W.X = letπ * b := by
  intro W
  obtain ⟨χ, -, -, hγ, hX, hQ, -, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  have hs : 1 ≤ s := h.1
  obtain ⟨-, -, -, -, -, hact, -⟩ := GlobalTheory.Cyc.XX_QQ_properties l ↥(OL LL) s hs
  obtain ⟨-, b, hb⟩ := hact (χ W.gam)
  refine ⟨⟨1 + W.X * fun _ => b, ?_, ?_⟩, ?_⟩
  · funext i
    change W.γ₀ W.gam (W.Q i) = (1 + W.X i * b) * W.Q i
    rw [hγ, hX, hQ, hb, mul_comm]
  · rw [add_sub_cancel_left]
    exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
  · obtain ⟨c, hc⟩ : (PowerSeries.X : PowerSeries ↥(OL LL)) ∣ GlobalTheory.Cyc.XX l ↥(OL LL) s := by
      rw [PowerSeries.X_dvd_iff, GlobalTheory.Cyc.XX]
      simp
    refine ⟨fun _ => c, ?_⟩
    funext i
    change W.X i = PowerSeries.X * c
    rw [hX, hc]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D HW F l _ K s LL h T M hh hT _`. Take `⟨h1, b, hb⟩` from `ring_part D HW l K s LL h`. Use `⟨h1, fun y z hy hz hc => ?_⟩` and prove the remaining obligations. Establish `hz' : z ∈ aN ((HW l).W K s LL h) T letπ`. Take `⟨x, hx, rfl⟩` from `hz`.

Use `⟨b • x, Submodule.smul_mem _ b hx, ?_⟩` and prove the remaining obligations. Simplify using `only [smulA, LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[hb, mul_smul]`. Use `⟨?_, fun h0 => ?_⟩` and prove the remaining obligations. Use `GlobalTheory.T.herrCocycle_poles_frobeniusQ_crystalline D HW F l K s LL h T hT (Multiset.replicate (mx M) 0) y z ?_ hz' hc` and prove the remaining obligations.

Rewrite using `[Multiset.map_replicate, Multiset.prod_replicate, pow_zero]`. Conclude with `hy`. Take `⟨m, hm⟩` from `((GlobalTheory.NL.HerrComplexH1.herr_H1_description D HW F l K s LL h T hT).1.2 ⟨(y, z), hc⟩).1 h0`. Establish `hm1 : y = ((HW l).W K s LL h).φD T m - m` using `congrArg Prod.fst hm`. Establish `hm2 : z = ((HW l).W K s LL h).γ T m - m` using `congrArg Prod.snd hm`.

Use `⟨m, GlobalTheory.T.mem_wach_of_frobenius_gamma D HW F l K s LL h T hT (mx M) m ?_ ?_, hm1, hm2⟩` and prove the remaining obligations. Conclude with `hm1 ▸ hy`. Conclude with `hm2 ▸ hz'`.
-/
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Pr2c D HW F := by
  intro D HW F l _ K s LL h T M hh hT _
  obtain ⟨h1, b, hb⟩ := ring_part D HW l K s LL h
  refine ⟨h1, fun y z hy hz hc => ?_⟩
  have hz' : z ∈ aN ((HW l).W K s LL h) T letπ := by
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨b • x, Submodule.smul_mem _ b hx, ?_⟩
    simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hb, mul_smul]
  refine ⟨?_, fun h0 => ?_⟩
  · refine GlobalTheory.T.herrCocycle_poles_frobeniusQ_crystalline D HW F l K s LL h T hT (Multiset.replicate (mx M) 0) y z ?_ hz' hc
    rw [Multiset.map_replicate, Multiset.prod_replicate, pow_zero]
    exact hy
  · obtain ⟨m, hm⟩ := ((GlobalTheory.NL.HerrComplexH1.herr_H1_description D HW F l K s LL h T hT).1.2 ⟨(y, z), hc⟩).1 h0
    have hm1 : y = ((HW l).W K s LL h).φD T m - m := congrArg Prod.fst hm
    have hm2 : z = ((HW l).W K s LL h).γ T m - m := congrArg Prod.snd hm
    refine ⟨m, GlobalTheory.T.mem_wach_of_frobenius_gamma D HW F l K s LL h T hT (mx M) m ?_ ?_, hm1, hm2⟩
    · exact hm1 ▸ hy
    · exact hm2 ▸ hz'

end GlobalTheory.NL.IntComplex
