import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem UpperTheory.Reformulated.B.WeightThresholdDefs.core {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {L : Submodule (NumberField.RingOfIntegers K) V} (h : Submodule.span K (L : Set V) = ⊤) (x : V) :
    ∃ n : NumberField.RingOfIntegers K, n ≠ 0 ∧ (n : K) • x ∈ L := by
  have hx : x ∈ Submodule.span K (L : Set V) := h ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers K)) K (L : Set V) x hx
  refine ⟨t, nonZeroDivisors.coe_ne_zero t, ?_⟩
  rw [Submodule.span_eq, Submonoid.smul_def] at ht
  have : ((t : NumberField.RingOfIntegers K) : K) • x = (t : NumberField.RingOfIntegers K) • x :=
    algebraMap_smul K (t : NumberField.RingOfIntegers K) x
  rw [this]
  exact ht

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem :
    ∀ {D : Formalism.L2.Ker.Car} {N : ℕ}
    {L₁ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E)},
    Submodule.span D.host.E (↑L₁ : Set (Fin N → D.host.E)) = ⊤ →
      ∀ (x : Fin N → D.host.E),
        ∃ (n : NumberField.RingOfIntegers D.host.E),
          n ≠ (0 : NumberField.RingOfIntegers D.host.E) ∧
            (↑n : D.host.E) • x ∈
              L₁ := by
  intro D N L₁ h x
  exact UpperTheory.Reformulated.B.WeightThresholdDefs.core h x
