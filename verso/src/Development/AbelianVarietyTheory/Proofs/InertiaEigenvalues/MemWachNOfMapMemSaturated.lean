import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatOverProductPowerSeriesRingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeComapOfExactFlatStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachKernelIntersectionFreeOfBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachKernelMemFrobeniusSpanAfterQPowStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.KerSat

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D HW F l _ K s LL h W E T₀ T₁ T₂ ι π h0 h1 h2 hses x hx`. Establish `hex` using `GlobalTheory.EtaleExact.DD_exact D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h T₀ T₁ T₂ ι π hses`. Establish `key` using `GlobalTheory.T.wachModule_uniqueness_characterisation D HW F l K s LL h T₀ h0`. Take `⟨hinj, hexact, hsurj⟩ : Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧ Function.Surjective (W.map π)` from `hex`. Use `haveI := GlobalTheory.EtaleExact.finite_OL LL`.

Use `haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)`. Use `haveI := ((D.loc l).PD K).finK₀`. Use `haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩`. Use `haveI : Module.Flat (AA K LL) W.EE := GlobalTheory.T.flat_over_product_power_series_ring _ _ W.EE ((D.loc l).PD K).p W.EE_π W.EE_complete W.EE_dense W.EE_sat`. Establish `hbc : IsBaseChange W.EE ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).subtype` using `GlobalTheory.T.isBaseChange_comap_of_exact_flat (AA K LL) W.EE _ _ _ (W.map ι) (W.map π) (W.N T₁) (W.N T₂) hinj hexact hsurj (W.N_base T₁ h1) (W.N_base T₂ h2) (fun y hy => W.map_N π h1 h2 y hy)`.

Establish `hcomp : ∀ z, W.map π (W.map ι z) = 0` using `fun z => (hexact _).2 ⟨z, rfl⟩`. Establish `hA : ∀ (a : AA K LL) (z : W.DD T₀), W.map ι (a • z) = a • W.map ι z` using `fun a z => ((W.map ι).restrictScalars (AA K LL)).map_smul a z`. Establish `hAπ : ∀ (a : AA K LL) (z : W.DD T₁), W.map π (a • z) = a • W.map π z` using `fun a z => ((W.map π).restrictScalars (AA K LL)).map_smul a z`. Establish `hπc : ∀ y : W.DD T₁, W.map π ((letπ : AA K LL) • y) = 0 → W.map π y = 0`. Introduce `y hy`.

Rewrite `hy` using `[hAπ, ← algebraMap_smul W.EE (letπ : AA K LL)]`. Conclude with `(W.EE_π.smul_left_cancel).mp (hy.trans (smul_zero _).symm)`. Establish `hγ : ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), W.γ T₀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))`. Introduce `y hy`. Use `show W.map ι (W.γD T₀ W.gam y) ∈ W.N T₁`.

Rewrite using `[W.map_γ]`. Conclude with `W.N_Γ T₁ W.gam _ hy`. Establish `hγπ : ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), W.γ T₀ y - y ∈ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).map (smulA W T₀ letπ)`. Introduce `y hy`. Express the relevant statement in the definitionally equal form `W.map ι y ∈ W.N T₁ at hy`.

Take `⟨z, hz, hzeq⟩` from `W.N_π T₁ W.gam _ hy`. Establish `h3 : W.map π z = 0`. Apply `hπc` to reduce the goal to its premises. Rewrite using `[← hzeq, map_sub, W.map_γ, hcomp, map_zero, sub_zero]`. Take `⟨z₀, rfl⟩` from `(hexact z).1 h3`.

Use `⟨z₀, hz, ?_⟩` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `W.map ι ((letπ : AA K LL) • z₀) = W.map ι (W.γD T₀ W.gam y - y)`. Rewrite using `[hA, map_sub, W.map_γ, hzeq]`. Establish `hφ : ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), ∃ k : ℕ, W.Q ^ k • W.φD T₀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))`.

Introduce `y hy`. Take `⟨k, hk⟩` from `W.N_φ T₁ _ hy`. Use `⟨k, ?_⟩` and prove the remaining obligations. Use `show W.map ι (W.Q ^ k • W.φD T₀ y) ∈ W.N T₁`. Rewrite using `[hA, W.map_φ]`.

Conclude with `hk`. Establish `hfree` using `GlobalTheory.T.wachKernel_intersection_free_of_baseChange D HW F l K s LL h T₀ T₁ T₂ ι π h0 h1 h2 hses hbc`. Establish `hspan` using `GlobalTheory.T.wachKernel_mem_frobeniusSpan_after_Q_pow D HW F l K s LL h T₀ T₁ T₂ ι π h0 h1 h2 hses`. Establish `heq` using `key _ hfree hbc hγ hγπ hφ hspan`. Rewrite using `[← heq]`.

Conclude with `hx`.
-/
theorem mem_N_of_map_mem : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀ := by
  intro D HW F l _ K s LL h W E T₀ T₁ T₂ ι π h0 h1 h2 hses x hx
  have hex := GlobalTheory.EtaleExact.DD_exact D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h T₀ T₁ T₂ ι π hses
  have key := GlobalTheory.T.wachModule_uniqueness_characterisation D HW F l K s LL h T₀ h0
  obtain ⟨hinj, hexact, hsurj⟩ : Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) := hex
  haveI := GlobalTheory.EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  haveI : Module.Flat (AA K LL) W.EE :=
    GlobalTheory.T.flat_over_product_power_series_ring _ _ W.EE ((D.loc l).PD K).p W.EE_π W.EE_complete W.EE_dense W.EE_sat
  have hbc : IsBaseChange W.EE ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).subtype :=
    GlobalTheory.T.isBaseChange_comap_of_exact_flat (AA K LL) W.EE _ _ _ (W.map ι) (W.map π) (W.N T₁) (W.N T₂) hinj hexact hsurj
      (W.N_base T₁ h1) (W.N_base T₂ h2) (fun y hy => W.map_N π h1 h2 y hy)
  have hcomp : ∀ z, W.map π (W.map ι z) = 0 := fun z => (hexact _).2 ⟨z, rfl⟩
  have hA : ∀ (a : AA K LL) (z : W.DD T₀), W.map ι (a • z) = a • W.map ι z := fun a z =>
    ((W.map ι).restrictScalars (AA K LL)).map_smul a z
  have hAπ : ∀ (a : AA K LL) (z : W.DD T₁), W.map π (a • z) = a • W.map π z := fun a z =>
    ((W.map π).restrictScalars (AA K LL)).map_smul a z
  have hπc : ∀ y : W.DD T₁, W.map π ((letπ : AA K LL) • y) = 0 → W.map π y = 0 := by
    intro y hy
    rw [hAπ, ← algebraMap_smul W.EE (letπ : AA K LL)] at hy
    exact (W.EE_π.smul_left_cancel).mp (hy.trans (smul_zero _).symm)
  have hγ : ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), W.γ T₀ y ∈
      (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)) := by
    intro y hy
    show W.map ι (W.γD T₀ W.gam y) ∈ W.N T₁
    rw [W.map_γ]
    exact W.N_Γ T₁ W.gam _ hy
  have hγπ : ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), W.γ T₀ y - y ∈
      ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).map (smulA W T₀ letπ) := by
    intro y hy
    change W.map ι y ∈ W.N T₁ at hy
    obtain ⟨z, hz, hzeq⟩ := W.N_π T₁ W.gam _ hy
    have h3 : W.map π z = 0 := by
      apply hπc
      rw [← hzeq, map_sub, W.map_γ, hcomp, map_zero, sub_zero]
    obtain ⟨z₀, rfl⟩ := (hexact z).1 h3
    refine ⟨z₀, hz, ?_⟩
    apply hinj
    change W.map ι ((letπ : AA K LL) • z₀) = W.map ι (W.γD T₀ W.gam y - y)
    rw [hA, map_sub, W.map_γ, hzeq]
  have hφ : ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), ∃ k : ℕ, W.Q ^ k • W.φD T₀ y ∈
      (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)) := by
    intro y hy
    obtain ⟨k, hk⟩ := W.N_φ T₁ _ hy
    refine ⟨k, ?_⟩
    show W.map ι (W.Q ^ k • W.φD T₀ y) ∈ W.N T₁
    rw [hA, W.map_φ]
    exact hk
  have hfree := GlobalTheory.T.wachKernel_intersection_free_of_baseChange D HW F l K s LL h T₀ T₁ T₂ ι π h0 h1 h2 hses hbc
  have hspan := GlobalTheory.T.wachKernel_mem_frobeniusSpan_after_Q_pow D HW F l K s LL h T₀ T₁ T₂ ι π h0 h1 h2 hses
  have heq := key _ hfree hbc hγ hγπ hφ hspan
  rw [← heq]
  exact hx

end GlobalTheory.NL.KerSat
