import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerKAvgNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfBoundedKorbitDimensionStatement

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.KAvgRank

open GlobalTheory.TypeSum.KCoef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

/- English proof (translation)
Rewrite using `[kAvg, ← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hσ he w), kAvg, ← integral_mul_left_eq_self (fun k => e (k₀⁻¹ * k) • σ (toMK k) w) k₀]`. Simplify using `only [map_smul, inv_mul_cancel_left, sigma_K_mul hσ]`.
-/
theorem sigma_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (k₀ : KG ε) (w : H) :
    σ (toMK k₀) (kAvg ε σ e w) = kAvg ε σ (fun k => e (k₀⁻¹ * k)) w := by
  rw [kAvg, ← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hσ he w), kAvg,
    ← integral_mul_left_eq_self (fun k => e (k₀⁻¹ * k) • σ (toMK k) w) k₀]
  simp only [map_smul, inv_mul_cancel_left, sigma_K_mul hσ]

/- English proof (translation)
Set `L : F →ₗ[ℂ] H` to `{ toFun := fun φ => kAvg ε σ φ w map_add' := fun x y => by`. Simplify using `only [kAvg, Submodule.coe_add, Pi.add_apply, add_smul]`. Conclude with `integral_add (integrable_avg hσ (hc _ x.2) w) (integrable_avg hσ (hc _ y.2) w)`. Use the proof step `map_smul' := fun c x => by`. Simplify using `only [kAvg, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_assoc]`.

Conclude with `integral_smul _ _ }`. Use `⟨LinearMap.range L, inferInstance, LinearMap.finrank_range_le L, ⟨⟨e, he⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `k hk _ ⟨φ, rfl⟩`. Take `⟨k₀, rfl⟩ : k ∈ Set.range (fun k : KG ε => toMK k)` from `by rw [range_toMK]; exact hk`. Conclude with `⟨⟨_, hl φ φ.2 k₀⁻¹⟩, (sigma_kAvg hσ (hc _ φ.2) k₀ w).symm⟩`.
-/
theorem exists_stable (hσ : IsURepOn (UJset ε) σ) {F : Submodule ℂ (KG ε → ℂ)} [FiniteDimensional ℂ F]
    (hc : ∀ φ ∈ F, Continuous φ) (hl : ∀ φ ∈ F, ∀ k₀ : KG ε, (fun k => φ (k₀ * k)) ∈ F) {e : KG ε → ℂ} (he : e ∈ F)
    (w : H) : ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ Module.finrank ℂ F ∧
      kAvg ε σ e w ∈ S ∧ IsKStableOn ε σ S := by
  let L : F →ₗ[ℂ] H :=
    { toFun := fun φ => kAvg ε σ φ w
      map_add' := fun x y => by
        simp only [kAvg, Submodule.coe_add, Pi.add_apply, add_smul]
        exact integral_add (integrable_avg hσ (hc _ x.2) w) (integrable_avg hσ (hc _ y.2) w)
      map_smul' := fun c x => by
        simp only [kAvg, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_assoc]
        exact integral_smul _ _ }
  refine ⟨LinearMap.range L, inferInstance, LinearMap.finrank_range_le L, ⟨⟨e, he⟩, rfl⟩, ?_⟩
  rintro k hk _ ⟨φ, rfl⟩
  obtain ⟨k₀, rfl⟩ : k ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hk
  exact ⟨⟨_, hl φ φ.2 k₀⁻¹⟩, (sigma_kAvg hσ (hc _ φ.2) k₀ w).symm⟩

/- English proof (translation)
Rewrite using `[← S.orthogonal_orthogonal, Submodule.mem_orthogonal']`. Introduce `u hu`. Rewrite using `[ContinuousLinearMap.adjoint_inner_left, hQ, inner_kAvg hσ he]`. Establish `: ∀ k : KG ε, ⟪z, σ (toMK k) u⟫_ℂ = 0` using `fun k => by`. Establish `h` using `inner_K hσ k⁻¹ u z`.

Rewrite `h` using `[inv_inv]`. Rewrite using `[← h]`. Conclude with `Submodule.inner_right_of_mem_orthogonal (hK _ (toMK_mem_K _) z hz) hu`. Simplify using `[this]`.
-/
theorem adjoint_mem (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) {Q : H →L[ℂ] H}
    (hQ : ∀ w, Q w = kAvg ε σ e w) {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hK : IsKStableOn ε σ S) {z : H}
    (hz : z ∈ S) : ContinuousLinearMap.adjoint Q z ∈ S := by
  rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal']
  intro u hu
  rw [ContinuousLinearMap.adjoint_inner_left, hQ, inner_kAvg hσ he]
  have : ∀ k : KG ε, ⟪z, σ (toMK k) u⟫_ℂ = 0 := fun k => by
    have h := inner_K hσ k⁻¹ u z
    rw [inv_inv] at h
    rw [← h]
    exact Submodule.inner_right_of_mem_orthogonal (hK _ (toMK_mem_K _) z hz) hu
  simp [this]

end GlobalTheory.TypeSum.KAvgRank

namespace GlobalTheory.TypeSum

/- English proof (translation)
Introduce `n ε H _ _ _ σ h e ⟨F, hF, heF, hc, ht⟩`. Establish `hσ` using `h.1`. Take `⟨Q, hQ⟩` from `KCoef.exists_clm_kAvg hσ (hc e heF)`. Set `U : Submodule ℂ H` to `LinearMap.range (Q : H →ₗ[ℂ] H)`. Establish `hU : ∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ Module.finrank ℂ F ∧ u ∈ S ∧ IsKStableOn ε σ S`.

Introduce and unpack `_ ⟨w, rfl⟩`. Use `KAvgRank.exists_stable hσ hc (fun φ hφ k₀ => (ht φ hφ k₀).1) heF w` as an intermediate fact. Rewrite `this` using `[← hQ]`. Then use the resulting hypothesis. Use `haveI : FiniteDimensional ℂ U := GlobalTheory.T.finiteDimensional_of_bounded_Korbit_dimension n ε H σ h U _ hU`. Set `b` to `stdOrthonormalBasis ℂ U`.

Use `⟨_, fun j => (b j : H), fun j => ContinuousLinearMap.adjoint Q (b j), ?_, fun j => ?_, fun j => ?_, fun w => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `exact b.orthonormal.comp_linearIsometry U.subtypeₗᵢ`. Take `⟨S, h1, -, h2, h3⟩` from `hU _ (b j).2`. Conclude with `⟨S, h1, h2, h3⟩`. Take `⟨S, h1, -, h2, h3⟩` from `hU _ (b j).2`.

Conclude with `⟨S, h1, KAvgRank.adjoint_mem hσ (hc e heF) hQ h3 h2, h3⟩`. Use `congrArg Subtype.val (b.sum_repr' ⟨Q w, ⟨w, rfl⟩⟩)` as an intermediate fact. Rewrite using `[← hQ]`. Simplify using `only [ContinuousLinearMap.adjoint_inner_left]`. Simplify using `using this.symm`.
-/
theorem kAvg_finite_rank : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ e : KG ε → ℂ, KFinFun ε e → ∃ (m : ℕ) (a c : Fin m → H), Orthonormal ℂ a ∧ (∀ j, IsKFin ε σ (a j)) ∧ (∀ j, IsKFin ε σ (c j)) ∧ ∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j := by
  intro n ε H _ _ _ σ h e ⟨F, hF, heF, hc, ht⟩
  have hσ := h.1
  obtain ⟨Q, hQ⟩ := KCoef.exists_clm_kAvg hσ (hc e heF)
  let U : Submodule ℂ H := LinearMap.range (Q : H →ₗ[ℂ] H)
  have hU : ∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ Module.finrank ℂ F ∧
      u ∈ S ∧ IsKStableOn ε σ S := by
    rintro _ ⟨w, rfl⟩
    have := KAvgRank.exists_stable hσ hc (fun φ hφ k₀ => (ht φ hφ k₀).1) heF w
    rwa [← hQ] at this
  haveI : FiniteDimensional ℂ U := GlobalTheory.T.finiteDimensional_of_bounded_Korbit_dimension n ε H σ h U _ hU
  let b := stdOrthonormalBasis ℂ U
  refine ⟨_, fun j => (b j : H), fun j => ContinuousLinearMap.adjoint Q (b j), ?_, fun j => ?_, fun j => ?_,
    fun w => ?_⟩
  · exact b.orthonormal.comp_linearIsometry U.subtypeₗᵢ
  · obtain ⟨S, h1, -, h2, h3⟩ := hU _ (b j).2
    exact ⟨S, h1, h2, h3⟩
  · obtain ⟨S, h1, -, h2, h3⟩ := hU _ (b j).2
    exact ⟨S, h1, KAvgRank.adjoint_mem hσ (hc e heF) hQ h3 h2, h3⟩
  · have := congrArg Subtype.val (b.sum_repr' ⟨Q w, ⟨w, rfl⟩⟩)
    rw [← hQ]
    simp only [ContinuousLinearMap.adjoint_inner_left]
    simpa using this.symm

end GlobalTheory.TypeSum
