import Formalism.WachLatticeTwists.TorsionKernelSplitting.WachTwistSplitTheoremStatedForm

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem rankLe : StatRankLe := by
  intro O _ _ _ Cs HV _ _ _ _ _ _ jT Fs Hf hfin hpre hker
  obtain ⟨s, hs, hli⟩ := exists_finset_linearIndependent_of_le_finrank
    (R := O) (M := Fs) le_rfl

  have hli2 : LinearIndependent O (fun x : s => jT ((x : Fs) : Cs)) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc k
    have h1 : jT ((∑ x : s, c x • (x : Fs) : Fs) : Cs) = 0 := by
      rw [← hc]
      simp
    obtain ⟨a, ha0, ha⟩ := hker _ (∑ x : s, c x • (x : Fs) : Fs).2 h1
    have h2 : ∑ x : s, (a * c x) • (x : Fs) = 0 := by
      have h4 : a • (∑ x : s, c x • (x : Fs) : Fs) = 0 := Subtype.ext ha
      rw [← h4, Finset.smul_sum]
      exact Finset.sum_congr rfl fun x _ => mul_smul _ _ _
    have h3 := hli (fun x => a * c x) h2 k
    exact (mul_eq_zero.1 h3).resolve_left ha0
  have hli3 : LinearIndependent (FractionRing O) (fun x : s => jT ((x : Fs) : Cs)) :=
    hli2.localization (FractionRing O) (nonZeroDivisors O)
  have hli4 : LinearIndependent (FractionRing O)
      (fun x : s => (⟨jT ((x : Fs) : Cs), hpre _ (x : Fs).2⟩ : Hf)) := by
    refine LinearIndependent.of_comp Hf.subtype ?_
    exact hli3
  have := hli4.fintype_card_le_finrank
  rw [Fintype.card_coe, hs] at this
  exact this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem kerTors : StatKerTors := by
  intro O _ _ _ D _ T₂ V A Cs HV _ _ _ _ _ _ _ _ _ _ ρ₂ ρV ρA i q Zc cls Fs clsV jT hseq hcls
    htor hj hV x hx hx0
  obtain ⟨hi, hex, hiE, hqE⟩ := hseq
  obtain ⟨hadd, hsmul, hB, hFs⟩ := hcls
  obtain ⟨a, ha, rfl⟩ := hFs x hx
  rw [hj a ha] at hx0
  obtain ⟨v, hv⟩ := hV a ha hx0
  obtain ⟨c, hc0, hc⟩ := htor (q v)
  rw [← map_smul] at hc
  obtain ⟨t, ht⟩ := (hex _).1 hc
  refine ⟨c, hc0, ?_⟩
  rw [← hsmul c a ha, hB _ (Zc.smul_mem c ha)]
  refine ⟨t, funext fun γ => hi ?_⟩
  show i (ρ₂ γ t - t) = i (c • a γ)
  have h1 : ρV γ v - v = i (a γ) := congrFun hv γ
  rw [map_sub, hiE γ t, ht, map_smul, map_smul, ← h1, smul_sub]

end Formalism.RepresentationBoundsCohomology.JS
