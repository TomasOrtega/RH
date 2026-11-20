import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.KirillovEndUnitaryOfTheoremA
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.LevelSmulSmul
import GroundTheory.AutomorphicForms.MeasuresGL

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.PfBern.Unit

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Take `⟨Pr, hPr⟩` from `LinearMap.exists_leftInverse_of_injective (testFn G).subtype (Submodule.ker_subtype _)`. Conclude with `⟨Pr, fun f => LinearMap.congr_fun hPr f⟩`.
-/
theorem exists_testProj : ∃ Pr : (G → ℂ) →ₗ[ℂ] testFn G, ∀ f : testFn G, Pr f = f := by
  obtain ⟨Pr, hPr⟩ := LinearMap.exists_leftInverse_of_injective (testFn G).subtype (Submodule.ker_subtype _)
  exact ⟨Pr, fun f => LinearMap.congr_fun hPr f⟩

/- English proof (translation)
Use `finiteDimensional_range_heckeLin μ hρ f` as an intermediate fact. Conclude with `Submodule.finiteDimensional_of_le (LinearMap.range_comp_le_range _ _)`.
-/
theorem fd_range_heckeLin_comp (μ : Measure G) [μ.IsHaarMeasure] {ρ : Representation ℂ G V}
    (hρ : IsAdmissible ρ) (f : locallyConstantCompactSupport G ℂ ℂ) (S : Module.End ℂ V) :
    FiniteDimensional ℂ (LinearMap.range (heckeLin μ hρ.1 f ∘ₗ S)) := by
  have := finiteDimensional_range_heckeLin μ hρ f
  exact Submodule.finiteDimensional_of_le (LinearMap.range_comp_le_range _ _)

def traceD (μ : Measure G) [μ.IsHaarMeasure] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
    (Pr : (G → ℂ) →ₗ[ℂ] testFn G) : Module.End ℂ V →ₗ[ℂ] (G → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun S f => finTrace (heckeLin μ hρ.1 (Pr f) ∘ₗ S))
    (fun S₁ S₂ f => by
      have := fd_range_heckeLin_comp μ hρ (Pr f) S₁
      have := fd_range_heckeLin_comp μ hρ (Pr f) S₂
      rw [LinearMap.comp_add]
      exact finTrace_add _ _)
    (fun c S f => by
      have := fd_range_heckeLin_comp μ hρ (Pr f) S
      rw [LinearMap.comp_smul, smul_eq_mul]
      exact finTrace_smul _ _)
    (fun S f₁ f₂ => by
      have := fd_range_heckeLin_comp μ hρ (Pr f₁) S
      have := fd_range_heckeLin_comp μ hρ (Pr f₂) S
      rw [map_add, heckeLin_add μ hρ.1, LinearMap.add_comp]
      exact finTrace_add _ _)
    (fun c S f => by
      have := fd_range_heckeLin_comp μ hρ (Pr f) S
      rw [map_smul, heckeLin_smul μ hρ.1, LinearMap.smul_comp, smul_eq_mul]
      exact finTrace_smul _ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem traceD_apply (μ : Measure G) [μ.IsHaarMeasure] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
    (Pr : (G → ℂ) →ₗ[ℂ] testFn G) (S : Module.End ℂ V) (f : G → ℂ) :
    traceD μ hρ Pr S f = finTrace (heckeLin μ hρ.1 (Pr f) ∘ₗ S) := rfl

/- English proof (translation)
Establish `e1 : Pr f = ⟨f, hf⟩` using `hPr ⟨f, hf⟩`. Establish `e2 : Pr (conjFn g f) = biTranslL g g ⟨f, hf⟩` using `hPr (biTranslL g g ⟨f, hf⟩)`. Rewrite using `[traceD_apply, traceD_apply, e1, e2]`. Use `finiteDimensional_range_heckeLin μ hρ ⟨f, hf⟩` as an intermediate fact. Establish `hB : heckeLin μ hρ.1 (biTranslL g g ⟨f, hf⟩) = (repEquiv ρ g).conj (heckeLin μ hρ.1 ⟨f, hf⟩)` using `LinearMap.ext fun v => by`.

Rewrite using `[LinearEquiv.conj_apply, heckeLin_apply, heckeAct_biTranslL μ hρ.1 g _ v]`. Both sides reduce to the same expression. Rewrite using `[hB]`. Use `fd_range_heckeLin_comp μ hρ ⟨f, hf⟩ (ρ g⁻¹ * S * ρ g)` as an intermediate fact. Rewrite using `[← finTrace_conj (repEquiv ρ g) (heckeLin μ hρ.1 ⟨f, hf⟩ ∘ₗ (ρ g⁻¹ * S * ρ g))]`.

Use `congr 1`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [LinearEquiv.conj_apply, LinearMap.comp_apply, Module.End.mul_apply]`. Use `congr 3`. Use `congr 1`.

Use `show ρ g (ρ g⁻¹ v) = v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.
-/
theorem traceD_equiv (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {ρ : Representation ℂ G V}
    (hρ : IsAdmissible ρ) (Pr : (G → ℂ) →ₗ[ℂ] testFn G) (hPr : ∀ f : testFn G, Pr f = f) (g : G)
    (S : Module.End ℂ V) (f : G → ℂ) (hf : f ∈ testFn G) :
    traceD μ hρ Pr (ρ g⁻¹ * S * ρ g) f = traceD μ hρ Pr S (conjFn g f) := by
  have e1 : Pr f = ⟨f, hf⟩ := hPr ⟨f, hf⟩
  have e2 : Pr (conjFn g f) = biTranslL g g ⟨f, hf⟩ := hPr (biTranslL g g ⟨f, hf⟩)
  rw [traceD_apply, traceD_apply, e1, e2]
  have := finiteDimensional_range_heckeLin μ hρ ⟨f, hf⟩
  have hB : heckeLin μ hρ.1 (biTranslL g g ⟨f, hf⟩) = (repEquiv ρ g).conj (heckeLin μ hρ.1 ⟨f, hf⟩) :=
    LinearMap.ext fun v => by
      rw [LinearEquiv.conj_apply, heckeLin_apply, heckeAct_biTranslL μ hρ.1 g _ v]
      rfl
  rw [hB]
  have := fd_range_heckeLin_comp μ hρ ⟨f, hf⟩ (ρ g⁻¹ * S * ρ g)
  rw [← finTrace_conj (repEquiv ρ g) (heckeLin μ hρ.1 ⟨f, hf⟩ ∘ₗ (ρ g⁻¹ * S * ρ g))]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, Module.End.mul_apply]
  congr 3
  congr 1
  show ρ g (ρ g⁻¹ v) = v
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Take `⟨Pr, hPr⟩` from `exists_testProj (G := G)`. Use `⟨traceD μ hρ Pr, fun g S f hf => traceD_equiv μ hρ Pr hPr g S f hf, fun S hS => ?_⟩` and prove the remaining obligations. Use `trace_faithful (μ := μ) hρ S fun f => ?_` and prove the remaining obligations. Use `hS f f.2` as an intermediate fact. Rewrite `this` using `[traceD_apply, hPr f]`. Then use the resulting hypothesis.
-/
theorem hasTraceDistr_of_admissible (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ) [ρ.IsIrreducible] : HasTraceDistr ρ := by
  obtain ⟨Pr, hPr⟩ := exists_testProj (G := G)
  refine ⟨traceD μ hρ Pr, fun g S f hf => traceD_equiv μ hρ Pr hPr g S f hf, fun S hS => ?_⟩
  refine trace_faithful (μ := μ) hρ S fun f => ?_
  have := hS f f.2
  rwa [traceD_apply, hPr f] at this

end Gen

/- English proof (translation)
Introduce `n V _ _ π hadm hirr`. Use `borelize (GL (Fin (n + 1)) k)`. Use `hirr` as an intermediate fact. Use `GroundTheory.Automorphic.Measures.isMulRightInvariant_GL k (n + 1) (Measure.haar : Measure (GL (Fin (n + 1)) k))` as an intermediate fact. Conclude with `hasTraceDistr_of_admissible (Measure.haar : Measure (GL (Fin (n + 1)) k)) hadm`.
-/
theorem traceDistrGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    TraceDistrGL k := by
  intro n V _ _ π hadm hirr
  borelize (GL (Fin (n + 1)) k)
  have := hirr
  have := GroundTheory.Automorphic.Measures.isMulRightInvariant_GL k (n + 1) (Measure.haar : Measure (GL (Fin (n + 1)) k))
  exact hasTraceDistr_of_admissible (Measure.haar : Measure (GL (Fin (n + 1)) k)) hadm

/- English proof (translation)
The claim follows from `kirillovEnd_of_theoremA k hA (traceDistrGL k)`.
-/
theorem kirillovEnd_of_theoremA' (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : TheoremA k) : KirillovEnd k :=
  kirillovEnd_of_theoremA k hA (traceDistrGL k)

end PositivityTheory.PfBern.Unit
