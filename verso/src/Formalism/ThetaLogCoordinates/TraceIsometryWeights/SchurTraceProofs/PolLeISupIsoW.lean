import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.LatData
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementB
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementC

namespace Formalism.InvariantFactorPaths.PW

open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

section gen

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isoW_eq_bot (G : GlW K V n) (W : Submodule K V) {S : Finset (Fin n → ℤ)}
    (hS : ∀ x ∈ W, ∀ μ ∉ S, G.comp μ x = 0) {μ : Fin n → ℤ} (hμ : μ ∉ S) : IsoW G W μ = ⊥ := by
  refine eq_bot_iff.mpr (sInf_le ⟨?_, ?_⟩)
  · rintro v ⟨hv, hvW⟩
    have h1 : G.comp μ v = v := hv.1
    rw [SetLike.mem_coe, Submodule.mem_bot, ← h1]
    exact hS v hvW μ hμ
  · intro a b x hx
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

end gen

variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Substitute using the available equality. A detailed English derivation is pending.
-/
theorem pol_le_iSup_isoW (LL L2 : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) :
    Pol p r L2 ≤ ⨆ μ, IsoW (GAe p LL j e) (Pol p r L2) μ := by
  classical
  obtain ⟨S, hS⟩ := GAe_pol_finW (p := p) LL L2 j e
  have key := Formalism.CountingSumsFrames.GlX.span_hw (GAe p LL j e) (GAe_pol_stable LL L2 j e) hS
    (ι := {v : MvPolynomial (Fin N × Fin r) ℚ_[p] // v ∈ Pol p r L2 ∧ v ≠ 0 ∧
      ∃ μ, (GAe p LL j e).IsHW μ v})
    (fun i => i.1) (fun i => i.2.2.2.choose) (fun i => i.2.2.2.choose_spec) (fun i => i.2.1) (fun i => i.2.2.1)
    (by
      intro μ v hv hw
      by_cases h0 : v = 0
      · rw [h0]; exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨v, hv, h0, μ, hw⟩, rfl⟩)
  refine key.trans (iSup_le fun i => ?_)
  refine le_trans ?_ (le_iSup _ i.2.2.2.choose)
  refine GlW.gS_le _ ?_ (GlW.gS_stable _ _)
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  subst hv
  exact GlW.subset_gS _ _ ⟨i.2.2.2.choose_spec, i.2.1⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem isoW_le_isoC (LL L2 : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    IsoW (GAe p LL j (enumC Cs)) (Pol p r L2) (la ∘ enumC Cs) ≤ IsoC p LL j Cs la := by
  rw [isoC_eq]
  unfold IsoW GlW.gS
  exact sInf_le_sInf fun U hU => ⟨fun v hv => hU.1 hv.1, hU.2⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem intP_of (hT : TypeInt) (hB : LatBasisPol) : IntP := by
  classical
  intro p _ N r LL j Cs T P hsat hP F hF
  obtain ⟨hPP, hran, hker⟩ := hP
  have D := polLatData_of hB (p := p) (r := r) LL LL j (enumC Cs)
  obtain ⟨S, hS⟩ := D.finW
  choose Q hQ1 hQ2 hQ3 using hT p _ Cs.card (GAe p LL j (enumC Cs)) (Pol p r LL) _ LL.total D
  have key : ∀ x ∈ Pol p r LL,
      P x = ∑ μ ∈ S.filter (fun μ => ∃ la ∈ T, la ∘ enumC Cs = μ), Q μ x := by
    intro x hx
    refine Submodule.iSup_induction _
      (motive := fun x => P x = ∑ μ ∈ S.filter (fun μ => ∃ la ∈ T, la ∘ enumC Cs = μ), Q μ x)
      (pol_le_iSup_isoW LL LL j (enumC Cs) hx) ?_ ?_ ?_
    · intro ν x hx
      by_cases hν : ν ∈ S
      · obtain ⟨la, hla⟩ := exists_ext Cs ν
        have hxC : x ∈ IsoC p LL j Cs la := isoW_le_isoC LL LL j Cs la (by rw [hla]; exact hx)
        by_cases hf : ∃ la' ∈ T, la' ∘ enumC Cs = ν
        · obtain ⟨la', hla'T, hla'⟩ := hf
          have hlaT : la ∈ T := (hsat la la' ((comp_eq_iff Cs la la').mp (hla.trans hla'.symm))).mpr hla'T
          have hxr : x ∈ LinearMap.range P := by
            rw [hran]; exact Submodule.mem_iSup_of_mem la (Submodule.mem_iSup_of_mem hlaT hxC)
          have hPx : P x = x := by
            obtain ⟨y, rfl⟩ := hxr
            exact LinearMap.congr_fun hPP y
          rw [hPx, Finset.sum_eq_single ν]
          · exact (hQ1 ν x hx).symm
          · intro μ _ hne
            exact hQ2 μ ν hne.symm x hx
          · intro hn
            exact absurd (Finset.mem_filter.mpr ⟨hν, la', hla'T, hla'⟩) hn
        · have hlaT : la ∉ T := fun h => hf ⟨la, h, hla⟩
          have hxk : x ∈ LinearMap.ker P := by
            rw [hker]; exact Submodule.mem_iSup_of_mem la (Submodule.mem_iSup_of_mem hlaT hxC)
          rw [LinearMap.mem_ker.mp hxk]
          symm
          refine Finset.sum_eq_zero fun μ hμ => ?_
          refine hQ2 μ ν ?_ x hx
          rintro rfl
          exact hf (Finset.mem_filter.mp hμ).2
      · rw [isoW_eq_bot _ _ hS hν, Submodule.mem_bot] at hx
        subst hx
        simp
    · simp
    · intro x y hx hy
      rw [map_add, hx, hy, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun μ _ => (map_add _ _ _).symm
  have hFp : F ∈ Pol p r LL := hF.1
  have hFi : F ∈ (IntPol p (Fin N × Fin r)).toAddSubgroup := hF.2
  rw [key F hFp, Finset.smul_sum, ← Submodule.mem_toAddSubgroup]
  exact AddSubgroup.sum_mem _ fun μ _ => hQ3 μ F hFi hFp

end Formalism.InvariantFactorPaths.PW
