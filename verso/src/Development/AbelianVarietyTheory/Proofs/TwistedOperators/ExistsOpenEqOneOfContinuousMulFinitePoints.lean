import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OpenKer

open GlobalTheory.AdelicU Filter Topology

/- English proof (translation)
Introduce `D T K hK F hF h1 hmul`. Use `haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin D.sp.cm.sig T.gram`. Establish `hc` using `continuous_ofFin D.sp.cm.sig T.gram`. Establish `hN : {y | ‖F (ofFin D.sp.cm.sig T.gram y) - 1‖ < 1 / 2} ∈ 𝓝 (1 : GFin D.sp.cm.sig T.gram)` using `(isOpen_lt (continuous_norm.comp ((hF.comp hc).sub continuous_const)) continuous_const).mem_nhds (by simp [h1])`. Establish `hK' : {y | ofFin D.sp.cm.sig T.gram y ∈ K} ∈ 𝓝 (1 : GFin D.sp.cm.sig T.gram)` using `(hK.preimage hc).mem_nhds (by simp [one_mem])`.

Take `⟨W, hW⟩` from `NonarchimedeanGroup.is_nonarchimedean _ (inter_mem hN hK')`. Use `⟨W.toSubgroup.comap (projFin D.sp.cm.sig T.gram), W.isOpen.preimage (continuous_projFin D.sp.cm.sig T.gram), ?_⟩` and prove the remaining obligations. Introduce `k hk hkf`. Establish `hkk : ∀ n : ℕ, ofFin D.sp.cm.sig T.gram (projFin D.sp.cm.sig T.gram (k ^ n)) = k ^ n` using `fun n => by`. Establish `h` using `ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig T.gram (k ^ n)`.

Rewrite `h` using `[mem_finPts.1 (pow_mem hkf n), map_one, one_mul]`. Then use the resulting hypothesis. Establish `hW' : ∀ n : ℕ, ‖F (k ^ n) - 1‖ < 1 / 2 ∧ k ^ n ∈ K` using `fun n => by`. Establish `: projFin D.sp.cm.sig T.gram (k ^ n) ∈ W`. Rewrite using `[map_pow]`. Conclude with `pow_mem (show projFin D.sp.cm.sig T.gram k ∈ W from hk) n`.

Establish `h` using `hW this`. Simplify using `only [Set.mem_inter_iff, Set.mem_setOf_eq, hkk n] at h`. Conclude with `h`. Establish `hpow : ∀ n : ℕ, F (k ^ n) = F k ^ n` using `fun n => by`. Proceed by induction on `n with`.

Consider the case `zero => simp [h1]`. Consider the case `succ n ih`. Rewrite using `[pow_succ, hmul _ (hW' n).2 (pow_mem hkf n) _ (by simpa using (hW' 1).2) hkf, ih, pow_succ]`. Conclude with `GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le fun m => by`. Rewrite using `[← hpow]`.

Conclude with `(hW' m).1.le`.
-/
theorem eq_one_on_finite_of_mul : ∀ {D : D7} (T : HSp D) (K : Subgroup (GA D T)), IsOpen (K : Set (GA D T)) → ∀ F : GA D T → ℂ, Continuous F → F 1 = 1 → (∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b) → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → F k = 1 := by
  intro D T K hK F hF h1 hmul
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin D.sp.cm.sig T.gram
  have hc := continuous_ofFin D.sp.cm.sig T.gram
  have hN : {y | ‖F (ofFin D.sp.cm.sig T.gram y) - 1‖ < 1 / 2} ∈ 𝓝 (1 : GFin D.sp.cm.sig T.gram) :=
    (isOpen_lt (continuous_norm.comp ((hF.comp hc).sub continuous_const)) continuous_const).mem_nhds
      (by simp [h1])
  have hK' : {y | ofFin D.sp.cm.sig T.gram y ∈ K} ∈ 𝓝 (1 : GFin D.sp.cm.sig T.gram) :=
    (hK.preimage hc).mem_nhds (by simp [one_mem])
  obtain ⟨W, hW⟩ := NonarchimedeanGroup.is_nonarchimedean _ (inter_mem hN hK')
  refine ⟨W.toSubgroup.comap (projFin D.sp.cm.sig T.gram),
    W.isOpen.preimage (continuous_projFin D.sp.cm.sig T.gram), ?_⟩
  intro k hk hkf
  have hkk : ∀ n : ℕ, ofFin D.sp.cm.sig T.gram (projFin D.sp.cm.sig T.gram (k ^ n)) = k ^ n := fun n => by
    have h := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig T.gram (k ^ n)
    rwa [mem_finPts.1 (pow_mem hkf n), map_one, one_mul] at h
  have hW' : ∀ n : ℕ, ‖F (k ^ n) - 1‖ < 1 / 2 ∧ k ^ n ∈ K := fun n => by
    have : projFin D.sp.cm.sig T.gram (k ^ n) ∈ W := by
      rw [map_pow]; exact pow_mem (show projFin D.sp.cm.sig T.gram k ∈ W from hk) n
    have h := hW this
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hkk n] at h
    exact h
  have hpow : ∀ n : ℕ, F (k ^ n) = F k ^ n := fun n => by
    induction n with
    | zero => simp [h1]
    | succ n ih =>
      rw [pow_succ, hmul _ (hW' n).2 (pow_mem hkf n) _ (by simpa using (hW' 1).2) hkf, ih, pow_succ]
  exact GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le fun m => by
    rw [← hpow]; exact (hW' m).1.le

end GlobalTheory.OpenKer
