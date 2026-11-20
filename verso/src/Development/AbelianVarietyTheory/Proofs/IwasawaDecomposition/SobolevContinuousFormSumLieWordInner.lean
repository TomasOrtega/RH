import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

/- English proof (translation)
Establish `hk : LinearMap.ker Φ ≤ LinearMap.ker ℓ` using `fun w hw => by`. Use `h w` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker.1 hw, norm_zero, mul_zero]`. Conclude with `norm_le_zero_iff.1 this`. Set `f₀ : LinearMap.range Φ →ₗ[ℂ] ℂ` to `(LinearMap.ker Φ).liftQ ℓ hk ∘ₗ Φ.quotKerEquivRange.symm.toLinearMap`.

Establish `hf : ∀ w, f₀ ⟨Φ w, LinearMap.mem_range_self Φ w⟩ = ℓ w` using `fun w => by`. Simplify using `only [f₀, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image]`. Both sides reduce to the same expression. Establish `hb : ∀ x, ‖f₀ x‖ ≤ C * ‖x‖`. Introduce and unpack `⟨_, w, rfl⟩`.

Conclude with `(congrArg norm (hf w)).le.trans (h w)`. Take `⟨g, hg, -⟩` from `exists_extension_norm_eq (LinearMap.range Φ) (f₀.mkContinuous C hb)`. Conclude with `⟨g, fun w => (hg ⟨Φ w, LinearMap.mem_range_self Φ w⟩).trans (hf w)⟩`.
-/
theorem exists_factor_of_bound {V E : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Φ : V →ₗ[ℂ] E) (ℓ : V →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ w, ‖ℓ w‖ ≤ C * ‖Φ w‖) :
    ∃ Λ : E →L[ℂ] ℂ, ∀ w, Λ (Φ w) = ℓ w := by
  have hk : LinearMap.ker Φ ≤ LinearMap.ker ℓ := fun w hw => by
    have := h w
    rw [LinearMap.mem_ker.1 hw, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let f₀ : LinearMap.range Φ →ₗ[ℂ] ℂ := (LinearMap.ker Φ).liftQ ℓ hk ∘ₗ Φ.quotKerEquivRange.symm.toLinearMap
  have hf : ∀ w, f₀ ⟨Φ w, LinearMap.mem_range_self Φ w⟩ = ℓ w := fun w => by
    simp only [f₀, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hb : ∀ x, ‖f₀ x‖ ≤ C * ‖x‖ := by
    rintro ⟨_, w, rfl⟩
    exact (congrArg norm (hf w)).le.trans (h w)
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range Φ) (f₀.mkContinuous C hb)
  exact ⟨g, fun w => (hg ⟨Φ w, LinearMap.mem_range_self Φ w⟩).trans (hf w)⟩

/- English proof (translation)
Use `⟨fun i => (InnerProductSpace.toDual ℂ H).symm (Λ.comp (ContinuousLinearMap.single ℂ (fun _ => H) i)), fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]`. Rewrite using `[← map_sum, Finset.univ_sum_single]`.
-/
theorem exists_inner_of_pi {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {m : ℕ}
    (Λ : (Fin m → H) →L[ℂ] ℂ) : ∃ a : Fin m → H, ∀ x, Λ x = ∑ i, ⟪a i, x i⟫_ℂ := by
  refine ⟨fun i => (InnerProductSpace.toDual ℂ H).symm (Λ.comp (ContinuousLinearMap.single ℂ (fun _ => H) i)),
    fun x => ?_⟩
  simp only [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
  rw [← map_sum, Finset.univ_sum_single]

/- English proof (translation)
Introduce `n ε H _ _ _ σ P G hP h hσ ℓ ⟨S, C, hS, hC⟩`. Establish `hG` using `gram_unit hP h`. Establish `hπ` using `isURepOn_trRep hP h hσ`. Establish `hl : ∀ i : Fin S.length, ∀ X ∈ S.get i, X ∈ lieG G` using `fun i => hS _ (List.get_mem S i)`. Set `Φ : smSub G (trRep σ P) →ₗ[ℂ] (Fin S.length → H)` to `{ toFun := fun w i => word (trRep σ P) (S.get i) w map_add' := fun v w => funext fun i => word_add hG hπ (hl i) v.2 w.2 map_smul' := fun c w => funext fun i => word_smul hG hπ (hl i) c w.2 }`.

Establish `hb : ∀ w, ‖(ℓ ∘ₗ (smSub G (trRep σ P)).subtype) w‖ ≤ (|C| * S.length) * ‖Φ w‖` using `fun w => by`. Use `(hC w w.2).trans ?_` and prove the remaining obligations. Establish `h1 : (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖).sum ≤ S.length * ‖Φ w‖`. Use `List.sum_le_card_nsmul (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖) ‖Φ w‖ (by` as an intermediate fact. Introduce `x hx`.

Take `⟨l, hl', rfl⟩` from `List.mem_map.1 hx`. Take `⟨i, rfl⟩` from `List.get_of_mem hl'`. Conclude with `norm_le_pi_norm (Φ w) i)`. Simplify using `using this`. Establish `h0 : 0 ≤ (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖).sum` using `List.sum_nonneg fun x hx => by`.

Take `⟨l, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `norm_nonneg _`. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul (le_abs_self C) h1 h0 (abs_nonneg C)`. Take `⟨Λ, hΛ⟩` from `exists_factor_of_bound Φ _ _ hb`.

Take `⟨a, ha⟩` from `exists_inner_of_pi Λ`. Conclude with `⟨S.length, S.get, a, hl, fun w hw => (hΛ ⟨w, hw⟩).symm.trans (ha _)⟩`.
-/
theorem sobCont_repr : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → ∃ (m : ℕ) (ls : Fin m → List (Matrix (Fin n) (Fin n) ℂ)) (a : Fin m → H), (∀ i, ∀ X ∈ ls i, X ∈ lieG G) ∧ ∀ w ∈ smSub G (trRep σ P), ℓ w = ∑ i, ⟪a i, word (trRep σ P) (ls i) w⟫_ℂ := by
  intro n ε H _ _ _ σ P G hP h hσ ℓ ⟨S, C, hS, hC⟩
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  have hl : ∀ i : Fin S.length, ∀ X ∈ S.get i, X ∈ lieG G := fun i => hS _ (List.get_mem S i)
  let Φ : smSub G (trRep σ P) →ₗ[ℂ] (Fin S.length → H) :=
    { toFun := fun w i => word (trRep σ P) (S.get i) w
      map_add' := fun v w => funext fun i => word_add hG hπ (hl i) v.2 w.2
      map_smul' := fun c w => funext fun i => word_smul hG hπ (hl i) c w.2 }
  have hb : ∀ w, ‖(ℓ ∘ₗ (smSub G (trRep σ P)).subtype) w‖ ≤ (|C| * S.length) * ‖Φ w‖ := fun w => by
    refine (hC w w.2).trans ?_
    have h1 : (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖).sum ≤ S.length * ‖Φ w‖ := by
      have := List.sum_le_card_nsmul (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖) ‖Φ w‖ (by
        intro x hx
        obtain ⟨l, hl', rfl⟩ := List.mem_map.1 hx
        obtain ⟨i, rfl⟩ := List.get_of_mem hl'
        exact norm_le_pi_norm (Φ w) i)
      simpa using this
    have h0 : 0 ≤ (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    rw [mul_assoc]
    exact mul_le_mul (le_abs_self C) h1 h0 (abs_nonneg C)
  obtain ⟨Λ, hΛ⟩ := exists_factor_of_bound Φ _ _ hb
  obtain ⟨a, ha⟩ := exists_inner_of_pi Λ
  exact ⟨S.length, S.get, a, hl, fun w hw => (hΛ ⟨w, hw⟩).symm.trans (ha _)⟩

end GlobalTheory.SmVec
