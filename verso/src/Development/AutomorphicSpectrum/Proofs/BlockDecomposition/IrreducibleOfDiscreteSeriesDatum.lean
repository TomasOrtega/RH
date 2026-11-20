import Mathlib
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

noncomputable section

open Finset Matrix

namespace GlobalTheory.CompanionTheory.RgDsHilb

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.RgDs PositivityTheory.RgDs.Hilb

variable {n : ℕ}

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ S := hS.1`. Establish `hirr : ∀ S' : Submodule ℂ H, S' ≤ S.map A → Formalism.MainNotions.S.IsKStableOn ε σ S' → S' = ⊥ ∨ S' = S.map A`. Introduce `S' hS' hK'`. Establish `hTK : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ S'.comap A)`. Introduce `g hg v hv`.

Rewrite `hv`, the goal using `[Submodule.mem_inf]`. Use `⟨hS.2.1 g hg v hv.1, ?_⟩` and prove the remaining obligations. Use `show A (σ g v) ∈ S'`. Rewrite using `[← hcomm g hg v]`. Conclude with `hK' g hg _ hv.2`.

Break down `hS.2.2.1 (S ⊓ S'.comap A) inf_le_left hTK with h | h` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Take `⟨w, hw, rfl⟩` from `hS' hx`.

Establish `hwT : w ∈ S ⊓ S'.comap A` using `Submodule.mem_inf.2 ⟨hw, hx⟩`. Rewrite `hwT` using `[h]`. Rewrite using `[(Submodule.mem_bot ℂ).1 hwT, map_zero]`. Conclude with `Submodule.zero_mem _`. Use `right`.

Use `le_antisymm hS' ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Establish `hwT : w ∈ S ⊓ S'.comap A` using `by rw [h]; exact hw`. Conclude with `(Submodule.mem_inf.1 hwT).2`. Use `⟨inferInstance, ?_, hirr, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `g hg _ ⟨w, hw, rfl⟩`. Conclude with `⟨σ g w, hS.2.1 g hg w hw, (hcomm g hg w).symm⟩`. Take `⟨v, hv, hv0, hwt⟩` from `hS.2.2.2.1`. Use `⟨A v, ⟨v, hv, rfl⟩, fun h => hv0 (hinj v hv h), ?_⟩` and prove the remaining obligations. Introduce `θ hθ`.

Rewrite using `[hcomm _ hθ, hwt θ hθ, map_smul]`. Introduce and unpack `μ _ ⟨w, hw, rfl⟩ hne hwt`. Use `hS.2.2.2.2 μ w hw (fun h => hne (by rw [h, map_zero])) ?_` and prove the remaining obligations. Introduce `θ hθ`. Establish `h1 : A (σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) w - Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • w) = 0`.

Rewrite using `[map_sub, map_smul, ← hcomm _ hθ, hwt θ hθ, sub_self]`. Establish `h2` using `hinj _ (Submodule.sub_mem _ (hS.2.1 _ hθ w hw) (Submodule.smul_mem _ _ hw)) h1`. Conclude with `sub_eq_zero.1 h2`.
-/
theorem isKTypeOf_map_of_injOn {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Λ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : Formalism.MainNotions.S.IsKTypeOf ε σ Λ S) (A : H →ₗ[ℂ] H)
    (hcomm : ∀ k ∈ Kset ε, ∀ v, σ k (A v) = A (σ k v))
    (hinj : ∀ w ∈ S, A w = 0 → w = 0) :
    Formalism.MainNotions.S.IsKTypeOf ε σ Λ (S.map A) := by
  haveI : FiniteDimensional ℂ S := hS.1
  have hirr : ∀ S' : Submodule ℂ H, S' ≤ S.map A → Formalism.MainNotions.S.IsKStableOn ε σ S' →
      S' = ⊥ ∨ S' = S.map A := by
    intro S' hS' hK'
    have hTK : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ S'.comap A) := by
      intro g hg v hv
      rw [Submodule.mem_inf] at hv ⊢
      refine ⟨hS.2.1 g hg v hv.1, ?_⟩
      show A (σ g v) ∈ S'
      rw [← hcomm g hg v]
      exact hK' g hg _ hv.2
    rcases hS.2.2.1 (S ⊓ S'.comap A) inf_le_left hTK with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hS' hx
      have hwT : w ∈ S ⊓ S'.comap A := Submodule.mem_inf.2 ⟨hw, hx⟩
      rw [h] at hwT
      rw [(Submodule.mem_bot ℂ).1 hwT, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨w, hw, rfl⟩
      have hwT : w ∈ S ⊓ S'.comap A := by rw [h]; exact hw
      exact (Submodule.mem_inf.1 hwT).2
  refine ⟨inferInstance, ?_, hirr, ?_, ?_⟩
  · rintro g hg _ ⟨w, hw, rfl⟩
    exact ⟨σ g w, hS.2.1 g hg w hw, (hcomm g hg w).symm⟩
  · obtain ⟨v, hv, hv0, hwt⟩ := hS.2.2.2.1
    refine ⟨A v, ⟨v, hv, rfl⟩, fun h => hv0 (hinj v hv h), ?_⟩
    intro θ hθ
    rw [hcomm _ hθ, hwt θ hθ, map_smul]
  · rintro μ _ ⟨w, hw, rfl⟩ hne hwt
    refine hS.2.2.2.2 μ w hw (fun h => hne (by rw [h, map_zero])) ?_
    intro θ hθ
    have h1 : A (σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) w -
        Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • w) = 0 := by
      rw [map_sub, map_smul, ← hcomm _ hθ, hwt θ hθ, sub_self]
    have h2 := hinj _ (Submodule.sub_mem _ (hS.2.1 _ hθ w hw) (Submodule.smul_mem _ _ hw)) h1
    exact sub_eq_zero.1 h2

/- English proof (translation)
Introduce `hDatum n ε lam T Ψ hP _hst huniq W hWle hWc hWG`. Establish `hσ` using `rreg_isURepOn ε`. Establish `hD` using `isDerivedOn_smE hσ`. Establish `hV1 : Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) (V1 ε Ψ)` using `hDatum n ε lam T Ψ hP`. Establish `: CompleteSpace W` using `hWc.completeSpace_coe`.

Establish `hWo : ∀ g ∈ UJset ε, ∀ x ∈ Wᗮ, rreg ε g x ∈ Wᗮ`. Introduce `g hg`. Take `⟨g', hg', hgg⟩` from `UnitaryGroupOfForm.inv_mem_UJ hg`. Conclude with `UnitaryGroupOfForm.orth_stable hσ hg hg' hgg W (hWG g' hg')`. Establish `hK : Formalism.MainNotions.S.IsKStableOn ε (rreg ε) (V1 ε Ψ ⊓ Wᗮ)`.

Introduce `k hk x hx`. Conclude with `⟨hV1.2.1 k hk x hx.1, hWo k (UnitaryGroupOfForm.K_mem_UJ hk) x hx.2⟩`. Establish `hmem : ∀ v ∈ datumV ε Ψ T.w, ((v : smD ε (rreg ε)) : L2 ε) ∈ V1 ε Ψ` using `fun v hv => Submodule.mem_map_of_mem hv`. Break down `hV1.2.2.1 (V1 ε Ψ ⊓ Wᗮ) inf_le_left hK with h0 | hV'` into its components or cases. Use `right`.

Use `le_antisymm hWle (UnitaryGroupOfForm.closGen_le hD W hWc hWG _ ?_)` and prove the remaining obligations. Establish `hcomm : ∀ k ∈ Kset ε, ∀ v, rreg ε k (W.starProjection.toLinearMap v) = W.starProjection.toLinearMap (rreg ε k v)`. Introduce `k hk v`. Establish `hkU` using `UnitaryGroupOfForm.K_mem_UJ hk`. Conclude with `(UnitaryGroupOfForm.proj_comm W (rreg ε k) (hWG k hkU) (hWo k hkU) v).symm`.

Establish `hinj : ∀ w ∈ V1 ε Ψ, W.starProjection.toLinearMap w = 0 → w = 0`. Introduce `w hw h`. Establish `hwo : w ∈ Wᗮ`. Use `W.sub_starProjection_mem_orthogonal w` as an intermediate fact. Establish `h' : W.starProjection w = 0` using `h`.

Rewrite `this` using `[h', sub_zero]`. Then use the resulting hypothesis. Establish `: w ∈ V1 ε Ψ ⊓ Wᗮ` using `⟨hw, hwo⟩`. Rewrite `this` using `[h0]`. Conclude with `(Submodule.mem_bot ℂ).1 this`. Establish `hle : (V1 ε Ψ).map W.starProjection.toLinearMap ≤ W`.

Introduce and unpack `_ ⟨w, -, rfl⟩`. Conclude with `W.starProjection_apply_mem w`. Establish `heq` using `huniq _ (hle.trans hWle) (isKTypeOf_map_of_injOn hV1 _ hcomm hinj)`. Introduce `v hv`. Establish `hv' : ((v : smD ε (rreg ε)) : L2 ε) ∈ (V1 ε Ψ).map W.starProjection.toLinearMap`.

Rewrite using `[heq]`. Conclude with `hmem v hv`. Conclude with `hle hv'`. Use `left`. Establish `hle : Hlam ε Ψ T.w ≤ Wᗮ` using `UnitaryGroupOfForm.closGen_le hD Wᗮ (Submodule.isClosed_orthogonal W) hWo _ (fun v hv => (show ((v : smD ε (rreg ε)) : L2 ε) ∈ V1 ε Ψ ⊓ Wᗮ by`.

Rewrite using `[hV']`. Conclude with `hmem v hv).2)`. Rewrite using `[eq_bot_iff, ← Submodule.inf_orthogonal_eq_bot W]`. Conclude with `le_inf le_rfl (hWle.trans hle)`.
-/
theorem stepIrred_of_stepDatum : StepDatum → StepIrred := by
  intro hDatum n ε lam T Ψ hP _hst huniq W hWle hWc hWG
  classical
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV1 : Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) (V1 ε Ψ) := hDatum n ε lam T Ψ hP
  have : CompleteSpace W := hWc.completeSpace_coe
  have hWo : ∀ g ∈ UJset ε, ∀ x ∈ Wᗮ, rreg ε g x ∈ Wᗮ := by
    intro g hg
    obtain ⟨g', hg', hgg⟩ := UnitaryGroupOfForm.inv_mem_UJ hg
    exact UnitaryGroupOfForm.orth_stable hσ hg hg' hgg W (hWG g' hg')
  have hK : Formalism.MainNotions.S.IsKStableOn ε (rreg ε) (V1 ε Ψ ⊓ Wᗮ) := by
    intro k hk x hx
    exact ⟨hV1.2.1 k hk x hx.1, hWo k (UnitaryGroupOfForm.K_mem_UJ hk) x hx.2⟩
  have hmem : ∀ v ∈ datumV ε Ψ T.w, ((v : smD ε (rreg ε)) : L2 ε) ∈ V1 ε Ψ :=
    fun v hv => Submodule.mem_map_of_mem hv
  rcases hV1.2.2.1 (V1 ε Ψ ⊓ Wᗮ) inf_le_left hK with h0 | hV'
  · right
    refine le_antisymm hWle (UnitaryGroupOfForm.closGen_le hD W hWc hWG _ ?_)
    have hcomm : ∀ k ∈ Kset ε, ∀ v, rreg ε k (W.starProjection.toLinearMap v) =
        W.starProjection.toLinearMap (rreg ε k v) := by
      intro k hk v
      have hkU := UnitaryGroupOfForm.K_mem_UJ hk
      exact (UnitaryGroupOfForm.proj_comm W (rreg ε k) (hWG k hkU) (hWo k hkU) v).symm
    have hinj : ∀ w ∈ V1 ε Ψ, W.starProjection.toLinearMap w = 0 → w = 0 := by
      intro w hw h
      have hwo : w ∈ Wᗮ := by
        have := W.sub_starProjection_mem_orthogonal w
        have h' : W.starProjection w = 0 := h
        rwa [h', sub_zero] at this
      have : w ∈ V1 ε Ψ ⊓ Wᗮ := ⟨hw, hwo⟩
      rw [h0] at this
      exact (Submodule.mem_bot ℂ).1 this
    have hle : (V1 ε Ψ).map W.starProjection.toLinearMap ≤ W := by
      rintro _ ⟨w, -, rfl⟩
      exact W.starProjection_apply_mem w
    have heq := huniq _ (hle.trans hWle) (isKTypeOf_map_of_injOn hV1 _ hcomm hinj)
    intro v hv
    have hv' : ((v : smD ε (rreg ε)) : L2 ε) ∈ (V1 ε Ψ).map W.starProjection.toLinearMap := by
      rw [heq]; exact hmem v hv
    exact hle hv'
  · left
    have hle : Hlam ε Ψ T.w ≤ Wᗮ :=
      UnitaryGroupOfForm.closGen_le hD Wᗮ (Submodule.isClosed_orthogonal W) hWo _
        (fun v hv => (show ((v : smD ε (rreg ε)) : L2 ε) ∈ V1 ε Ψ ⊓ Wᗮ by
          rw [hV']; exact hmem v hv).2)
    rw [eq_bot_iff, ← Submodule.inf_orthogonal_eq_bot W]
    exact le_inf le_rfl (hWle.trans hle)

end GlobalTheory.CompanionTheory.RgDsHilb
