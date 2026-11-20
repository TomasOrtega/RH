import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasCompactSupportDescend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantIntegralUnipotentCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallOpenCompactNormalStatement
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv
open scoped Pointwise

noncomputable section
namespace GlobalTheory.GamMul.UnitCell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
theorem setOf_eq_mul (N K : Subgroup (GL (Fin m) k)) :
    {g : GL (Fin m) k | ∃ u ∈ N, ∃ c ∈ K, g = u * c} = (N : Set (GL (Fin m) k)) * (K : Set (GL (Fin m) k)) := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_mul]
  exact ⟨fun ⟨u, hu, c, hc, e⟩ => ⟨u, hu, c, hc, e.symm⟩, fun ⟨u, hu, c, hc, e⟩ => ⟨u, hu, c, hc, e.symm⟩⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isTestFun_unitCell :
    IsTestFun (Set.indicator {g : GL (Fin m) k | ∃ u ∈ unipB k (Fin m), ∃ c ∈ KO k (Fin m), g = u * c}
      (fun _ => (1 : ℂ))) := by
  rw [setOf_eq_mul]
  exact InvInt.isTestFun_indicator

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem eq_zero_of_unitCell (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (hI : IsInvIntegral I)
    (h0 : I (Set.indicator {g : GL (Fin m) k | ∃ u ∈ unipB k (Fin m), ∃ c ∈ KO k (Fin m), g = u * c}
      (fun _ => (1 : ℂ))) = 0) (f : GL (Fin m) k → ℂ) (hf : IsTestFun f) : I f = 0 := by
  have hB : IsOpen ((Subtype.val : (⊤ : Subgroup (GL (Fin m) k)) → GL (Fin m) k) ⁻¹'
      (KO k (Fin m) : Set (GL (Fin m) k))) :=
    SplitFlip.isOpen_KO.preimage continuous_subtype_val
  refine GlobalTheory.T.invariant_integral_unipotent_compact (GL (Fin m) k) (unipB k (Fin m)) ⊤ (KO k (Fin m)) {F | IsTestFun F} ?_ ?_ ?_
    le_top SplitFlip.isCompact_KO hB I ?_ ?_ h0 f hf
  · intro F
    simp only [Set.mem_setOf_eq, IsTestFun]
    refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun ⟨C, hC, hs⟩ => ⟨C, hC, fun _ _ => Subgroup.mem_top _, hs⟩,
      fun ⟨C, hC, _, hs⟩ => ⟨C, hC, hs⟩⟩)
  · intro K _ hKc hKo
    have hKo' : IsOpen (K : Set (GL (Fin m) k)) :=
      hKo.preimage (continuous_id.subtype_mk (p := fun g => g ∈ (⊤ : Subgroup (GL (Fin m) k))) fun g => Subgroup.mem_top g)
    rw [setOf_eq_mul]
    exact ⟨InvInt.isClosed_unipB.mul_right_of_isCompact hKc, hKo'.mul_left⟩
  · intro U hU
    obtain ⟨_, K, hKo, hKc, hKU, hKO, hnorm, -⟩ := GlobalTheory.T.exists_small_open_compact_normal k m m 0 (Nat.add_zero m) U hU
    exact ⟨K, hKO, hKc, hKo.preimage continuous_subtype_val, hKU, hnorm⟩
  · intro F _ F' _ c c'
    have : (fun g => c * F g + c' * F' g) = c • F + c' • F' := rfl
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  · intro F hF x _
    exact hI F hF x

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ),
    IsTestFun (Set.indicator {g : GL (Fin m) k | ∃ u ∈ unipB k (Fin m), ∃ c ∈ KO k (Fin m), g = u * c}
      (fun _ => (1 : ℂ))) ∧
    (∀ (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ), IsInvIntegral I →
      I (Set.indicator {g : GL (Fin m) k | ∃ u ∈ unipB k (Fin m), ∃ c ∈ KO k (Fin m), g = u * c}
        (fun _ => (1 : ℂ))) = 0 → ∀ f, IsTestFun f → I f = 0) ∧
    ∃ (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ), IsInvIntegral I ∧
      I (Set.indicator {g : GL (Fin m) k | ∃ u ∈ unipB k (Fin m), ∃ c ∈ KO k (Fin m), g = u * c}
        (fun _ => (1 : ℂ))) = 1 := by
  intro k _ _ _ _ m
  refine ⟨isTestFun_unitCell, fun I hI h0 f hf => eq_zero_of_unitCell I hI h0 f hf, ?_⟩
  obtain ⟨I, f, hI, hf, hne⟩ := InvInt.exists_isInvIntegral k m
  set a := I (Set.indicator {g : GL (Fin m) k | ∃ u ∈ unipB k (Fin m), ∃ c ∈ KO k (Fin m), g = u * c}
    (fun _ => (1 : ℂ))) with ha
  have ha0 : a ≠ 0 := fun h => hne (eq_zero_of_unitCell I hI h f hf)
  refine ⟨a⁻¹ • I, fun F hF x => ?_, ?_⟩
  · simp only [LinearMap.smul_apply, hI F hF x]
  · rw [LinearMap.smul_apply, ← ha, smul_eq_mul, inv_mul_cancel₀ ha0]

end GlobalTheory.GamMul.UnitCell
