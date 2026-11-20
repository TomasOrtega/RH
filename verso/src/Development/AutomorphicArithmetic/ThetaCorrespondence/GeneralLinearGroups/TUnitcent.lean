import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

open MeasureTheory in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Equip the data with the indicated structure.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem UpperTheory.Lit.Cas.unitcent :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (p : ℝ), IsSmooth π → π.IsIrreducible → CoeffLp p π → UnitaryCentral π := by
  intro k _ _ _ _ N V _ _ π p hs hirr hLp t c hc
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨K, hKo, hKc, -⟩ := GlobalTheory.SqIntUnit.compactOpen_basis k N Set.univ Filter.univ_mem
  obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hs (GlobalTheory.SqIntUnit.compactOpen_basis k N) hv
  haveI hQ : IsTopologicalGroup (GL (Fin N) k ⧸ Subgroup.center (GL (Fin N) k)) := inferInstance
  letI : MeasurableSpace (AdGL k N) := borel _
  haveI : BorelSpace (AdGL k N) := ⟨rfl⟩
  let q : GL (Fin N) k → AdGL k N := QuotientGroup.mk
  have hqc : Continuous q := continuous_quot_mk
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe
  let K₀ : TopologicalSpace.PositiveCompacts (AdGL k N) :=
    ⟨⟨q '' (K : Set (GL (Fin N) k)), hKc.image hqc⟩, by
      refine ⟨q 1, ?_⟩
      rw [(hqo _ hKo).interior_eq]
      exact ⟨1, K.one_mem, rfl⟩⟩
  have hopen : IsOpen {g : GL (Fin N) k | (l : Module.Dual ℂ V) ∘ₗ π g = l} := by
    have h1 := l.2
    change IsOpen {g | π.dual g l = l} at h1
    have h2 : {g : GL (Fin N) k | (l : Module.Dual ℂ V) ∘ₗ π g = l} = (fun g => g⁻¹) ⁻¹' {g | π.dual g l = l} := by
      ext g
      simp [Representation.dual_apply, Module.Dual.transpose_apply]
    rw [h2]
    exact h1.preimage continuous_inv
  obtain ⟨F, hF, -⟩ := hLp (MeasureTheory.Measure.haarMeasure K₀)
    (MeasureTheory.Measure.isHaarMeasure_haarMeasure K₀) v l hopen
  have hz : (Matrix.GeneralLinearGroup.scalar (Fin N) t) ∈ Subgroup.center (GL (Fin N) k) := by
    rw [Subgroup.mem_center_iff]
    intro g
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_smul, Matrix.smul_mul, mul_comm]
  have hq : ((Matrix.GeneralLinearGroup.scalar (Fin N) t : GL (Fin N) k) : AdGL k N) = ((1 : GL (Fin N) k) : AdGL k N) := by
    rw [QuotientGroup.eq]
    simpa using hz
  have e1 := hF (Matrix.GeneralLinearGroup.scalar (Fin N) t)
  have e2 := hF 1
  rw [hq, e2, hc v, map_one] at e1
  simp only [Module.End.one_apply, map_smul, norm_smul] at e1
  have hlv : 0 < ‖(l : Module.Dual ℂ V) v‖ := norm_pos_iff.mpr hl
  have h3 : (‖c‖ - 1) * ‖(l : Module.Dual ℂ V) v‖ = 0 := by
    rw [sub_mul, one_mul, ← e1, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · linarith
