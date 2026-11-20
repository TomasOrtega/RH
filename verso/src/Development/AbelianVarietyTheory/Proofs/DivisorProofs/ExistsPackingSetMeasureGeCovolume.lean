import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open MeasureTheory
open scoped Pointwise

/- English proof (translation)
Introduce `H _ _ _ ν Γ _`. Distinguish the cases in `hF : HasFundamentalDomain Γ H ν`. Use `swap`. Use `⟨∅, MeasurableSet.empty, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[covolume, hF]`.

Introduce `γ _ y hy`. Conclude with `absurd hy (Set.notMem_empty y)`. Use `set s := hF.ExistsIsFundamentalDomain.choose with hs_def`. Establish `hs : IsFundamentalDomain Γ s ν` using `hF.ExistsIsFundamentalDomain.choose_spec`. Establish `hcov : covolume Γ H ν = ν s` using `by simp [covolume, hF, hs_def]`.

Take `⟨t, hts, htm, hte⟩` from `hs.nullMeasurableSet.exists_measurable_subset_ae_eq`. Establish `hsmul : ∀ g : Γ, (g • t : Set H) = (fun y => (g : H)⁻¹ * y) ⁻¹' t`. Introduce `g`. Use extensionality with `y`. Simplify using `[Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]`.

Establish `hmeas : ∀ g : Γ, MeasurableSet (g • t : Set H)`. Introduce `g`. Rewrite using `[hsmul g]`. Conclude with `(measurable_const_mul _) htm`. Set `U : Set H` to `⋃ g : {g : Γ // g ≠ 1}, (g.1 • t : Set H)`.

Establish `hUm : MeasurableSet U` using `MeasurableSet.iUnion (fun g => hmeas g.1)`. Establish `hnull : ν (t ∩ U) = 0`. Rewrite using `[Set.inter_iUnion]`. Use `measure_iUnion_null (fun g => ?_)` and prove the remaining obligations. Establish `h1` using `hs.aedisjoint (Ne.symm g.2 : (1 : Γ) ≠ g.1)`.

Establish `h2 : ν ((1 : Γ) • s ∩ g.1 • s) = 0` using `h1`. Rewrite `h2` using `[one_smul]`. Conclude with `measure_mono_null (Set.inter_subset_inter hts (Set.smul_set_mono hts)) h2`. Use `⟨t \ U, htm.diff hUm, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hcov, ← Set.sdiff_self_inter, measure_sdiff_null hnull]`.

Conclude with `(measure_congr hte).ge`. Introduce `γ hγ y hy hγy`. Assume the negation of the conclusion as `hne`. Establish `hne' : (⟨γ, hγ⟩ : Γ) ≠ 1` using `fun h => hne (congrArg Subtype.val h)`. Apply `hγy.2` to reduce the goal to its premises.

Use `Set.mem_iUnion.2 ⟨⟨⟨γ, hγ⟩, hne'⟩, ?_⟩` and prove the remaining obligations. Conclude with `⟨y, hy.1, rfl⟩`.
-/
theorem packing_set_covolume_le :
    ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) (Γ : Subgroup H), Countable Γ → ∃ F : Set H, MeasurableSet F ∧ covolume Γ H ν ≤ ν F ∧ ∀ γ ∈ Γ, ∀ y ∈ F, γ * y ∈ F → γ = 1 := by
  intro H _ _ _ ν Γ _
  classical
  by_cases hF : HasFundamentalDomain Γ H ν
  swap
  · refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
    · simp [covolume, hF]
    · intro γ _ y hy; exact absurd hy (Set.notMem_empty y)
  · set s := hF.ExistsIsFundamentalDomain.choose with hs_def
    have hs : IsFundamentalDomain Γ s ν := hF.ExistsIsFundamentalDomain.choose_spec
    have hcov : covolume Γ H ν = ν s := by simp [covolume, hF, hs_def]
    obtain ⟨t, hts, htm, hte⟩ := hs.nullMeasurableSet.exists_measurable_subset_ae_eq
    have hsmul : ∀ g : Γ, (g • t : Set H) = (fun y => (g : H)⁻¹ * y) ⁻¹' t := by
      intro g; ext y
      simp [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
    have hmeas : ∀ g : Γ, MeasurableSet (g • t : Set H) := by
      intro g; rw [hsmul g]; exact (measurable_const_mul _) htm
    let U : Set H := ⋃ g : {g : Γ // g ≠ 1}, (g.1 • t : Set H)
    have hUm : MeasurableSet U := MeasurableSet.iUnion (fun g => hmeas g.1)
    have hnull : ν (t ∩ U) = 0 := by
      rw [Set.inter_iUnion]
      refine measure_iUnion_null (fun g => ?_)
      have h1 := hs.aedisjoint (Ne.symm g.2 : (1 : Γ) ≠ g.1)
      have h2 : ν ((1 : Γ) • s ∩ g.1 • s) = 0 := h1
      rw [one_smul] at h2
      exact measure_mono_null (Set.inter_subset_inter hts (Set.smul_set_mono hts)) h2
    refine ⟨t \ U, htm.diff hUm, ?_, ?_⟩
    · rw [hcov, ← Set.sdiff_self_inter, measure_sdiff_null hnull]
      exact (measure_congr hte).ge
    · intro γ hγ y hy hγy
      by_contra hne
      have hne' : (⟨γ, hγ⟩ : Γ) ≠ 1 := fun h => hne (congrArg Subtype.val h)
      apply hγy.2
      refine Set.mem_iUnion.2 ⟨⟨⟨γ, hγ⟩, hne'⟩, ?_⟩
      exact ⟨y, hy.1, rfl⟩

end GlobalTheory
