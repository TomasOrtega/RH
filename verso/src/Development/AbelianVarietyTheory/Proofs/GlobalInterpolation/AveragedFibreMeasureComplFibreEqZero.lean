import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibOfZero
open MeasureTheory Topology

namespace GlobalTheory.QuadFibre

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Apply an available result and prove the equalities needed to match it to the conclusion. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
-/
theorem fibOf_compl_fibre : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → ∀ t : K, GlobalTheory.QuadFibre.fibOf μ ν q U s t (q ⁻¹' {t})ᶜ = 0 := by
  intro K V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ q hq hh U s hs t
  obtain ⟨hUo, hUc, h1, hmul, hinv, hn, hsc, hsq⟩ := hs
  by_cases ht : t = 0
  · subst ht; rw [fibOf_zero]; rfl
  have hm : Measurable (fun x : V => s (t / q x) • x) := by
    have h1 : Measurable (fun x : V => s (t / q x)) :=
      hsc.measurable.comp (measurable_const.div hq.measurable)
    exact h1.smul measurable_id
  have hA : MeasurableSet (q ⁻¹' {t})ᶜ :=
    ((isClosed_singleton.preimage hq).measurableSet).compl
  rw [fibOf_ne _ _ _ _ _ ht, Measure.smul_apply, Measure.map_apply hm hA,
    Measure.restrict_apply (hm hA)]
  convert smul_zero _
  convert measure_empty (μ := μ)
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx1, u, hu, hx2⟩
  apply hx1
  have hu0 : u ≠ 0 := by
    intro h
    have := hn u hu
    rw [h] at this
    simp at this
  have hx2' : q x = t * u := by simpa using hx2.symm
  have h3 : t / q x = u⁻¹ := by rw [hx2']; field_simp
  show q (s (t / q x) • x) = t
  rw [hh, h3, hsq _ (hinv u hu), hx2']
  field_simp

end GlobalTheory.QuadFibre
