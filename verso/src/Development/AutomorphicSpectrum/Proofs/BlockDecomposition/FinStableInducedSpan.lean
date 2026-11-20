import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem act_fin_val {N : ℕ} (g : GL (Fin N) (Af E)) (φ : Sm E N) (x : GA E N) :
    (act (.fin g) φ).1 x = φ.1 (x * finGL E N g) := rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities.
-/
theorem memInd2_act_fin {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)}
    (g : GL (Fin (r + s)) (Af E)) {φ : Sm E (r + s)} (h : MemInd2 U₁ U₂ φ) :
    MemInd2 U₁ U₂ (act (.fin g) φ) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x y => ?_, fun k g' => ?_⟩
  · rw [act_fin_val, act_fin_val, mul_assoc, h1]
  · convert h2 k (g' * g) using 2 with m
    rw [act_fin_val, map_mul, mul_assoc, mul_assoc]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Express the relevant assertion in an equivalent form by its definition. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem indSpan_finStable (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) :
    FinStable (indSpan U₁ U₂) := by
  intro g φ hφ
  change φ ∈ Submodule.span ℂ _ at hφ
  change _ ∈ Submodule.span ℂ _
  induction hφ using Submodule.span_induction with
  | mem φ h => exact Submodule.subset_span (memInd2_act_fin g h)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

end GlobalTheory.CompanionTheory.LimV

end
