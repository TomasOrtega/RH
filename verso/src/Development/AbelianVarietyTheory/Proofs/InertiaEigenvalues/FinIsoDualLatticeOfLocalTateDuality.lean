import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientOfCompleteNakayama
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FreeModuleAdicCompleteSeparated
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactDvrAdicCompleteSeparatedUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatFiniteFreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFreeModuleCompactAdicDvrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleEqAddUniformizerSmulAddCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModUniformiserCocyclesFiniteClassesLocalStatement
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal ReciprocityTheory.ChartRestriction.T2

namespace GlobalTheory.FinIsoDualLattice

/- English proof (translation)
Introduce `p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hO i D hD`. Take `⟨hR, hC, hT2, hA, hpm, hp0⟩` from `hO`. Use `haveI := hR`. Use `haveI := hC`. Use `haveI := hT2`.

Use `haveI := hD.t2'`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨hFin, hFree⟩` from `GlobalTheory.T.dualLat_finite_free_of_isLatticeIn D.bT D.T hD.lat hD.perf`. Use `haveI := hFin`. Use `haveI := hFree`.

Take `⟨hcpl, hsep⟩` from `GlobalTheory.T.compact_dvr_adic_complete_separated_uniformizer hA ϖ hϖ`. Take `⟨hcT, hsT⟩` from `GlobalTheory.freeModule_adicComplete_separated ϖ hcpl hsep (↥D.T')`. Take `⟨hcomp, hopen, hemb⟩` from `GlobalTheory.T.finite_free_module_compact_adic_dvr hA (M := ↥D.T') ϖ hϖ`. Use `haveI := hcomp`. Establish `hρ : ContAction D.ρTl'` using `sub_contAction D.contT' D.T' D.stT'`.

Establish `hpϖ : (p : O) ∈ Ideal.span {ϖ}`. Rewrite using `[← Irreducible.maximalIdeal_eq hϖ]` and apply the resulting hypothesis. Take `⟨s, hs⟩` from `GlobalTheory.T.modUniformiser_cocycles_finite_classes_local hT hK i D.ρTl' hρ ϖ hpϖ hopen`. Establish `hl` using `GlobalTheory.T.cocycle_eq_add_uniformizer_smul_add_coboundary D.ρTl' hρ ϖ hemb.isEmbedding s hs`. Establish `hd : ∀ t : ↥D.T', d0 D.ρTl' t ∈ Z1 D.ρTl'` using `fun t => by`.

Use `⟨?_, fun g h => ?_⟩` and prove the remaining obligations. Conclude with `(hρ.comp (continuous_id.prodMk continuous_const)).sub continuous_const`. Simplify using `only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]`. Normalize the expressions using the abelian group laws. Set `d : ↥D.T' →ₗ[O] ↥(Z1 D.ρTl')` to `LinearMap.codRestrict _ (d0 D.ρTl') hd`.

Establish `hdN : LinearMap.range d ≤ (B1 D.ρTl').comap (Z1 D.ρTl').subtype`. Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `⟨t, rfl⟩`. Establish `hZ : ∀ c : ↥(Z1 D.ρTl'), (∀ n : ℕ, ∃ z : ↥(Z1 D.ρTl'), c = ϖ ^ n • z) → c = 0`. Introduce `c hc`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Conclude with `hsT _ fun n => by`. Take `⟨z, hz⟩` from `hc n`. Conclude with `⟨(z : G → ↥D.T') g, by rw [hz]; rfl⟩`.

Use `GlobalTheory.finite_quotient_of_complete_nakayama ϖ hcpl hcT hZ d _ hdN s fun c => ?_` and prove the remaining obligations. Take `⟨a, c', x, hx⟩` from `hl c`. Use `⟨a, c', x, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, d, LinearMap.codRestrict_apply]`. Conclude with `hx`.
-/
theorem finIso_of_localTateDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) : FinIso := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hO i D hD
  obtain ⟨hR, hC, hT2, hA, hpm, hp0⟩ := hO
  haveI := hR; haveI := hC; haveI := hT2; haveI := hD.t2'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hFin, hFree⟩ := GlobalTheory.T.dualLat_finite_free_of_isLatticeIn D.bT D.T hD.lat hD.perf
  haveI := hFin; haveI := hFree
  obtain ⟨hcpl, hsep⟩ := GlobalTheory.T.compact_dvr_adic_complete_separated_uniformizer hA ϖ hϖ
  obtain ⟨hcT, hsT⟩ := GlobalTheory.freeModule_adicComplete_separated ϖ hcpl hsep (↥D.T')
  obtain ⟨hcomp, hopen, hemb⟩ := GlobalTheory.T.finite_free_module_compact_adic_dvr hA (M := ↥D.T') ϖ hϖ
  haveI := hcomp
  have hρ : ContAction D.ρTl' := sub_contAction D.contT' D.T' D.stT'
  have hpϖ : (p : O) ∈ Ideal.span {ϖ} := by
    rwa [← Irreducible.maximalIdeal_eq hϖ]
  obtain ⟨s, hs⟩ := GlobalTheory.T.modUniformiser_cocycles_finite_classes_local hT hK i D.ρTl' hρ ϖ hpϖ hopen
  have hl := GlobalTheory.T.cocycle_eq_add_uniformizer_smul_add_coboundary D.ρTl' hρ ϖ hemb.isEmbedding s hs
  have hd : ∀ t : ↥D.T', d0 D.ρTl' t ∈ Z1 D.ρTl' := fun t => by
    refine ⟨?_, fun g h => ?_⟩
    · exact (hρ.comp (continuous_id.prodMk continuous_const)).sub continuous_const
    · simp only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]; abel
  let d : ↥D.T' →ₗ[O] ↥(Z1 D.ρTl') := LinearMap.codRestrict _ (d0 D.ρTl') hd
  have hdN : LinearMap.range d ≤ (B1 D.ρTl').comap (Z1 D.ρTl').subtype := by
    rintro _ ⟨t, rfl⟩; exact ⟨t, rfl⟩
  have hZ : ∀ c : ↥(Z1 D.ρTl'), (∀ n : ℕ, ∃ z : ↥(Z1 D.ρTl'), c = ϖ ^ n • z) → c = 0 := by
    intro c hc
    apply Subtype.ext; funext g
    exact hsT _ fun n => by
      obtain ⟨z, hz⟩ := hc n
      exact ⟨(z : G → ↥D.T') g, by rw [hz]; rfl⟩
  refine GlobalTheory.finite_quotient_of_complete_nakayama ϖ hcpl hcT hZ d _ hdN s fun c => ?_
  obtain ⟨a, c', x, hx⟩ := hl c
  refine ⟨a, c', x, Subtype.ext ?_⟩
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, d, LinearMap.codRestrict_apply]
  exact hx

end GlobalTheory.FinIsoDualLattice
