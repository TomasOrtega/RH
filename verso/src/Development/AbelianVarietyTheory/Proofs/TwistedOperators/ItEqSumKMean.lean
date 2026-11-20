import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultTEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift

/- English proof (translation)
Introduce `D V W S S' M M' θ ω pt It hIt τ n c φ φs v u hc hω hu`. Use `(M'.ds τ).1` as an intermediate fact. Establish `hU` using `(M'.ds τ).2.2.1`. Rewrite using `[← sub_eq_zero]`. Use `inclT_injective M ?_` and prove the remaining obligations.

Rewrite using `[map_zero]`. Use `ellT_separates M _ fun w => ?_` and prove the remaining obligations. Set `l : Fin n → (M'.sm τ →ₗ[ℂ] ℂ)` to `fun i => ellT M w ∘ₗ inclT M ∘ₗ It (φs i) ∘ₗ (PiTensorProduct.tprod ℂ (s := fun ρ => M'.sm ρ)).toLinearMap v τ`. Establish `hl : ∀ i x, l i x = ellT M w (inclT M (It (φs i) (PiTensorProduct.tprod ℂ (Function.update v τ x))))` using `fun _ _ => rfl`. Establish `hb : ∀ i, ∃ C : ℝ, ∀ x, ‖l i x‖ ≤ C * ‖x‖` using `fun i => by`.

Take `⟨C, hC⟩` from `hIt.bdd (φs i) w`. Use `⟨C * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hl]`. Use `(hC _).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), mul_assoc, Function.update_self]`.

Use `congr 2`. Use `Finset.prod_congr rfl fun ρ hρ => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hρ)]`. Use `choose L hL _ using fun i => exists_extension_norm_eq (M'.sm τ) ((l i).mkContinuousOfExistsBound (hb i))`. Establish `hL' : ∀ i (x : M'.sm τ), L i x = l i x` using `hL`.

Establish `hk : ∀ k : Formalism.REAL.KG (M'.ε τ), Formalism.REAL.toMK k ∈ Formalism.MainNotions.S.UJset (M'.ε τ)` using `fun k => (Formalism.REAL.maximal_compact_facts _ _).1 _ k.2`. Establish `hcm : Continuous fun k : Formalism.REAL.KG (M'.ε τ) => Formalism.REAL.toMK k` using `Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)`. Establish `hx : Continuous fun k : Formalism.REAL.KG (M'.ε τ) => M'.σ τ (Formalism.REAL.toMK k) (v τ)` using `(hU.2.2 _).comp_continuous hcm hk`. Establish `hint : ∀ i, Integrable (fun k : Formalism.REAL.KG (M'.ε τ) => c i k • M'.σ τ (Formalism.REAL.toMK k) (v τ)) (Formalism.REAL.muK (M'.ε τ))` using `fun i => integrableOn_univ.1 (((hc i).smul hx).continuousOn.integrableOn_compact isCompact_univ)`. Establish `key : ∀ k : Formalism.REAL.KG (M'.ε τ), ∑ i, L i (c i k • M'.σ τ (Formalism.REAL.toMK k) (v τ)) = ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v)))` using `fun k => by`.

Establish `hs : M'.σ τ (Formalism.REAL.toMK k) (v τ) ∈ M'.sm τ` using `(GlobalTheory.SmVec.sm_eq M' τ).ge (GlobalTheory.SmVec.sigma_mem (M'.fr_unit τ) (M'.fr_gram τ) hU ((GlobalTheory.SmVec.sm_eq M' τ).le (v τ).2) (hk k))`. Establish `hr : M'.rep τ ((M'.fr τ)⁻¹ * Formalism.REAL.toMK k * M'.fr τ) = M'.σ τ (Formalism.REAL.toMK k)` using `GlobalTheory.SmVec.trRep_conj (σ := M'.σ τ) (M'.fr_unit τ) _`. Establish `h1` using `hIt.invK τ _ (GlobalTheory.SmVec.conj_mem_UH (M'.fr_unit τ) (M'.fr_gram τ) (hk k)) φ _ (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ (Function.update v τ ⟨_, hs⟩)) (hω k).symm (by`. Unfold `inclT`. Rewrite using `[PiTensorProduct.map_tprod, PiTensorProduct.map_tprod, actT_pure, hr]`.

Use `congr 1`. Use function extensionality and compare the values at `ρ`. Distinguish the cases in `h : ρ = τ`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Function.update_of_ne h])`. Rewrite using `[← h1, map_sum, LinearMap.sum_apply, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, LinearMap.smul_apply, map_smul, map_smul, ← hl, ← hL']`. Rewrite using `[map_sub, map_sub, map_sum, map_sum, sub_eq_zero]`.

Establish `h2 : ∀ i, ellT M w (inclT M (It (φs i) (PiTensorProduct.tprod ℂ (Function.update v τ (u i))))) = ∫ k, L i (c i k • M'.σ τ (Formalism.REAL.toMK k) (v τ)) ∂(Formalism.REAL.muK (M'.ε τ))` using `fun i => by`. Rewrite using `[← hl, ← hL', hu, kMean, (L i).integral_comp_comm (hint i)]`. Simplify using `only [h2]`. Rewrite using `[← integral_finsetSum _ fun i _ => (L i).integrable_comp (hint i)]`. Simplify using `only [key]`.

Simplify using the standard rewrite rules.
-/
theorem it_eq_sum_kMean : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank → WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsItW θ M M' ω pt It → ∀ (τ : D.what₂.Tau) (n : ℕ) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ) (φ : PolF D W.rank V.rank) (φs : Fin n → PolF D W.rank V.rank) (v : M'.Vec) (u : Fin n → M'.sm τ), (∀ i, Continuous (c i)) → (∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) (pt φ) = pt (∑ i, c i k • φs i)) → (∀ i, (u i : M'.H τ) = kMean M' τ (c i) (v τ)) → It φ (PiTensorProduct.tprod ℂ v) = ∑ i, It (φs i) (PiTensorProduct.tprod ℂ (Function.update v τ (u i))) := by
  intro D V W S S' M M' θ ω pt It hIt τ n c φ φs v u hc hω hu
  have := (M'.ds τ).1
  have hU := (M'.ds τ).2.2.1
  rw [← sub_eq_zero]
  refine inclT_injective M ?_
  rw [map_zero]
  refine ellT_separates M _ fun w => ?_
  let l : Fin n → (M'.sm τ →ₗ[ℂ] ℂ) := fun i => ellT M w ∘ₗ inclT M ∘ₗ It (φs i) ∘ₗ
    (PiTensorProduct.tprod ℂ (s := fun ρ => M'.sm ρ)).toLinearMap v τ
  have hl : ∀ i x, l i x = ellT M w (inclT M (It (φs i) (PiTensorProduct.tprod ℂ (Function.update v τ x)))) :=
    fun _ _ => rfl
  have hb : ∀ i, ∃ C : ℝ, ∀ x, ‖l i x‖ ≤ C * ‖x‖ := fun i => by
    obtain ⟨C, hC⟩ := hIt.bdd (φs i) w
    refine ⟨C * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖, fun x => ?_⟩
    rw [hl]
    refine (hC _).trans (le_of_eq ?_)
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), mul_assoc, Function.update_self]
    congr 2
    refine Finset.prod_congr rfl fun ρ hρ => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
  choose L hL _ using fun i => exists_extension_norm_eq (M'.sm τ) ((l i).mkContinuousOfExistsBound (hb i))
  have hL' : ∀ i (x : M'.sm τ), L i x = l i x := hL
  have hk : ∀ k : Formalism.REAL.KG (M'.ε τ), Formalism.REAL.toMK k ∈ Formalism.MainNotions.S.UJset (M'.ε τ) :=
    fun k => (Formalism.REAL.maximal_compact_facts _ _).1 _ k.2
  have hcm : Continuous fun k : Formalism.REAL.KG (M'.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hx : Continuous fun k : Formalism.REAL.KG (M'.ε τ) => M'.σ τ (Formalism.REAL.toMK k) (v τ) :=
    (hU.2.2 _).comp_continuous hcm hk
  have hint : ∀ i, Integrable (fun k : Formalism.REAL.KG (M'.ε τ) => c i k • M'.σ τ (Formalism.REAL.toMK k) (v τ))
      (Formalism.REAL.muK (M'.ε τ)) := fun i =>
    integrableOn_univ.1 (((hc i).smul hx).continuousOn.integrableOn_compact isCompact_univ)
  have key : ∀ k : Formalism.REAL.KG (M'.ε τ), ∑ i, L i (c i k • M'.σ τ (Formalism.REAL.toMK k) (v τ)) =
      ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v))) := fun k => by
    have hs : M'.σ τ (Formalism.REAL.toMK k) (v τ) ∈ M'.sm τ :=
      (GlobalTheory.SmVec.sm_eq M' τ).ge
        (GlobalTheory.SmVec.sigma_mem (M'.fr_unit τ) (M'.fr_gram τ) hU ((GlobalTheory.SmVec.sm_eq M' τ).le (v τ).2) (hk k))
    have hr : M'.rep τ ((M'.fr τ)⁻¹ * Formalism.REAL.toMK k * M'.fr τ) = M'.σ τ (Formalism.REAL.toMK k) :=
      GlobalTheory.SmVec.trRep_conj (σ := M'.σ τ) (M'.fr_unit τ) _
    have h1 := hIt.invK τ _ (GlobalTheory.SmVec.conj_mem_UH (M'.fr_unit τ) (M'.fr_gram τ) (hk k)) φ _
      (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ (Function.update v τ ⟨_, hs⟩)) (hω k).symm (by
        unfold inclT
        rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod, actT_pure, hr]
        congr 1
        funext ρ
        by_cases h : ρ = τ
        · subst h; simp
        · simp [Function.update_of_ne h])
    rw [← h1, map_sum, LinearMap.sum_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, LinearMap.smul_apply, map_smul, map_smul, ← hl, ← hL']
  rw [map_sub, map_sub, map_sum, map_sum, sub_eq_zero]
  have h2 : ∀ i, ellT M w (inclT M (It (φs i) (PiTensorProduct.tprod ℂ (Function.update v τ (u i))))) =
      ∫ k, L i (c i k • M'.σ τ (Formalism.REAL.toMK k) (v τ)) ∂(Formalism.REAL.muK (M'.ε τ)) := fun i => by
    rw [← hl, ← hL', hu, kMean, (L i).integral_comp_comm (hint i)]
  simp only [h2]
  rw [← integral_finsetSum _ fun i _ => (L i).integrable_comp (hint i)]
  simp only [key]
  simp

end GlobalTheory.Chain.IoLift

end
