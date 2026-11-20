import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

open MeasureTheory in
/- English proof (translation)
Introduce `k _ _ _ _ N V _ _ π p hs hirr hLp t c hc`. Use `haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hirr`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Take `⟨K, hKo, hKc, -⟩` from `GlobalTheory.SqIntUnit.compactOpen_basis k N Set.univ Filter.univ_mem`. Take `⟨l, hl⟩` from `GlobalTheory.ContraRefl.exists_smooth_form_ne hs (GlobalTheory.SqIntUnit.compactOpen_basis k N) hv`.

Use `haveI hQ : IsTopologicalGroup (GL (Fin N) k ⧸ Subgroup.center (GL (Fin N) k)) := inferInstance`. Use `letI : MeasurableSpace (AdGL k N) := borel _`. Use `haveI : BorelSpace (AdGL k N) := ⟨rfl⟩`. Set `q : GL (Fin N) k → AdGL k N` to `QuotientGroup.mk`. Establish `hqc : Continuous q` using `continuous_quot_mk`.

Establish `hqo : IsOpenMap q` using `QuotientGroup.isOpenMap_coe`. Set `K₀ : TopologicalSpace.PositiveCompacts (AdGL k N)` to `⟨⟨q '' (K : Set (GL (Fin N) k)), hKc.image hqc⟩, by`. Use `⟨q 1, ?_⟩` and prove the remaining obligations. Rewrite using `[(hqo _ hKo).interior_eq]`. Conclude with `⟨1, K.one_mem, rfl⟩⟩`.

Establish `hopen : IsOpen {g : GL (Fin N) k | (l : Module.Dual ℂ V) ∘ₗ π g = l}`. Establish `h1` using `l.2`. Express the relevant statement in the definitionally equal form `IsOpen {g | π.dual g l = l} at h1`. Establish `h2 : {g : GL (Fin N) k | (l : Module.Dual ℂ V) ∘ₗ π g = l} = (fun g => g⁻¹) ⁻¹' {g | π.dual g l = l}`. Use extensionality with `g`.

Simplify using `[Representation.dual_apply, Module.Dual.transpose_apply]`. Rewrite using `[h2]`. Conclude with `h1.preimage continuous_inv`. Take `⟨F, hF, -⟩` from `hLp (MeasureTheory.Measure.haarMeasure K₀) (MeasureTheory.Measure.isHaarMeasure_haarMeasure K₀) v l hopen`. Establish `hz : (Matrix.GeneralLinearGroup.scalar (Fin N) t) ∈ Subgroup.center (GL (Fin N) k)`.

Rewrite using `[Subgroup.mem_center_iff]`. Introduce `g`. Use extensionality with `i j`. Simplify using `[Matrix.GeneralLinearGroup.scalar, Matrix.mul_smul, Matrix.smul_mul, mul_comm]`. Establish `hq : ((Matrix.GeneralLinearGroup.scalar (Fin N) t : GL (Fin N) k) : AdGL k N) = ((1 : GL (Fin N) k) : AdGL k N)`.

Rewrite using `[QuotientGroup.eq]`. Simplify using `using hz`. Establish `e1` using `hF (Matrix.GeneralLinearGroup.scalar (Fin N) t)`. Establish `e2` using `hF 1`. Rewrite `e1` using `[hq, e2, hc v, map_one]`.

Simplify using `only [Module.End.one_apply, map_smul, norm_smul] at e1`. Establish `hlv : 0 < ‖(l : Module.Dual ℂ V) v‖` using `norm_pos_iff.mpr hl`. Establish `h3 : (‖c‖ - 1) * ‖(l : Module.Dual ℂ V) v‖ = 0`. Rewrite using `[sub_mul, one_mul, ← e1, sub_self]`. Break down `mul_eq_zero.mp h3 with h | h` into its components or cases.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
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
