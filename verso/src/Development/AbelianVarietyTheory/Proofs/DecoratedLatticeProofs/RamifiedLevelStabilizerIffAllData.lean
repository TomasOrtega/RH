import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SOnCols

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem ramIff_all : ∀ D : D7, RamIff D := by
  intro D k _ _ _ _ p n _ _ S β P g hg φ
  letI := Fintype.ofFinite 𝓀[k]ˣ
  have rp : ∀ x (F : GA D S → ℂ), β.rep x F = rTrans (β.gl x) F := fun _ _ => rfl
  rw [finsum_eq_sum_of_fintype]
  constructor
  · rintro ⟨Φ, ⟨he, hr, hc⟩, rfl⟩
    refine ⟨hc P, fun x hx => ?_, ?_⟩
    · rw [← rp, ← he x P, hx]
    · rw [← (mem_Mram Φ).1 hr P]
      exact Finset.sum_congr rfl fun s _ => by rw [← rp, ← he, hg]
  · rintro ⟨hc, hs, h0⟩
    let v : levelVec β.rep P := ⟨φ, fun x hx => hs x hx⟩
    have hv : ∀ x : GL n k, formOf β.rep P v (x • P) = β.rep x φ := formOf_smul β.rep P v
    refine ⟨formOf β.rep P v, ⟨formOf_mem _ _ _, (mem_Mram _).2 fun Q => ?_, fun Q => ?_⟩, by simpa using hv 1⟩
    · obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
      have : ∀ s : 𝓀[k]ˣ, formOf β.rep P v (s • h • P) = β.rep h (rTrans (β.gl (g s)) φ) := by
        intro s
        rw [← smul_comm h s P, ← hg, smul_smul, hv, map_mul, Module.End.mul_apply, rp (g s)]
      rw [Finset.sum_congr rfl fun s _ => this s, ← map_sum, h0, map_zero]
    · obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
      rw [hv, rp]
      exact ⟨fun γ hγ y => by simp only [rTrans]; rw [mul_assoc, hc.1 γ hγ], hc.2.comp (continuous_id.mul continuous_const)⟩

end GlobalTheory.SeeSaw

end
