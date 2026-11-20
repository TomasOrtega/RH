import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

/- English proof (translation)
Introduce `K W ι _ _ _ J op Z μ hZ F hF hF0 ν hν`. Take `⟨s, hs⟩` from `Submodule.mem_iSup_iff_exists_finset.1 hF`. Establish `inv : ∀ (t : Finset J) i, ∀ G ∈ ⨆ j ∈ t, Z j, op i G ∈ ⨆ j ∈ t, Z j`. Introduce `t i`. Establish `hle : (⨆ j ∈ t, Z j) ≤ (⨆ j ∈ t, Z j).comap (op i)`.

Use `iSup₂_le fun j hj => ?_` and prove the remaining obligations. Introduce `G hG`. Rewrite using `[Submodule.mem_comap, hZ j i G hG]`. Conclude with `Submodule.smul_mem _ _ ((le_iSup₂ (f := fun j (_ : j ∈ t) => Z j) j hj) hG)`. Conclude with `fun G hG => hle hG`.

It suffices to establish `key : ∀ t : Finset J, ∀ G ∈ ⨆ j ∈ t, Z j, G ≠ 0 → (∀ i, op i G = ν i • G) → ∃ j, μ j = ν from key s F hs hF0 hν`. Introduce `t`. Use `Finset.induction_on t ?_ ?_` and prove the remaining obligations. Introduce `G hG hG0 _`. Simplify using `at hG`.

Conclude with `absurd hG hG0`. Introduce `a t ha ih G hG hG0 hGν`. Rewrite `hG` using `[Finset.iSup_insert, Submodule.mem_sup]`. Take `⟨H, hH, G', hG', rfl⟩` from `hG`. Distinguish the cases in `hμ : μ a = ν`.

Conclude with `⟨a, hμ⟩`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, μ a i ≠ ν i := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hμ (funext h)`.

Establish `e : (μ a i - ν i) • H = ν i • G' - op i G'`. Establish `h1` using `hGν i`. Rewrite `h1` using `[map_add, hZ a i H hH, smul_add]`. Rewrite using `[sub_smul, sub_eq_sub_iff_add_eq_add, h1, add_comm]`. Establish `hsub : (μ a i - ν i) • H ∈ ⨆ j ∈ t, Z j`.

Rewrite using `[e]`. Conclude with `sub_mem (Submodule.smul_mem _ _ hG') (inv t i G' hG')`. Establish `hH' : H ∈ ⨆ j ∈ t, Z j`. Establish `hne : μ a i - ν i ≠ 0` using `sub_ne_zero.mpr hi`. Establish `h2` using `Submodule.smul_mem _ (μ a i - ν i)⁻¹ hsub`.

Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ hne, one_smul]`. Then use the resulting hypothesis. Conclude with `ih (H + G') (add_mem hH' hG') hG0 hGν`.
-/
theorem UpperTheory.V.Hi.levelUR2EigPart :
    ∀ (K W ι : Type) [Field K] [AddCommGroup W] [Module K W] (J : Type 1) (op : ι → Module.End K W) (Z : J → Submodule K W) (μ : J → ι → K), (∀ j i, ∀ F ∈ Z j, op i F = μ j i • F) → ∀ F ∈ ⨆ j, Z j, F ≠ 0 → ∀ ν : ι → K, (∀ i, op i F = ν i • F) → ∃ j, μ j = ν := by
  intro K W ι _ _ _ J op Z μ hZ F hF hF0 ν hν
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hF
  have inv : ∀ (t : Finset J) i, ∀ G ∈ ⨆ j ∈ t, Z j, op i G ∈ ⨆ j ∈ t, Z j := by
    intro t i
    have hle : (⨆ j ∈ t, Z j) ≤ (⨆ j ∈ t, Z j).comap (op i) := by
      refine iSup₂_le fun j hj => ?_
      intro G hG
      rw [Submodule.mem_comap, hZ j i G hG]
      exact Submodule.smul_mem _ _ ((le_iSup₂ (f := fun j (_ : j ∈ t) => Z j) j hj) hG)
    exact fun G hG => hle hG
  suffices key : ∀ t : Finset J, ∀ G ∈ ⨆ j ∈ t, Z j, G ≠ 0 → (∀ i, op i G = ν i • G) → ∃ j, μ j = ν from
    key s F hs hF0 hν
  intro t
  refine Finset.induction_on t ?_ ?_
  · intro G hG hG0 _
    simp at hG
    exact absurd hG hG0
  · intro a t ha ih G hG hG0 hGν
    rw [Finset.iSup_insert, Submodule.mem_sup] at hG
    obtain ⟨H, hH, G', hG', rfl⟩ := hG
    by_cases hμ : μ a = ν
    · exact ⟨a, hμ⟩
    obtain ⟨i, hi⟩ : ∃ i, μ a i ≠ ν i := by
      by_contra h
      push_neg at h
      exact hμ (funext h)
    have e : (μ a i - ν i) • H = ν i • G' - op i G' := by
      have h1 := hGν i
      rw [map_add, hZ a i H hH, smul_add] at h1
      rw [sub_smul, sub_eq_sub_iff_add_eq_add, h1, add_comm]
    have hsub : (μ a i - ν i) • H ∈ ⨆ j ∈ t, Z j := by
      rw [e]
      exact sub_mem (Submodule.smul_mem _ _ hG') (inv t i G' hG')
    have hH' : H ∈ ⨆ j ∈ t, Z j := by
      have hne : μ a i - ν i ≠ 0 := sub_ne_zero.mpr hi
      have h2 := Submodule.smul_mem _ (μ a i - ν i)⁻¹ hsub
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
    exact ih (H + G') (add_mem hH' hG') hG0 hGν
