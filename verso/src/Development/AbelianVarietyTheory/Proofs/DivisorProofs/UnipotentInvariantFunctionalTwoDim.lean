import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFirstApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantInducedIso
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FullRankCoinv.JacReduce

open GlobalTheory.FullRankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rtr {n d : ℕ} (M : GL (Fin d) k) :
    (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ) where
  toFun Ψ := fun Y => Ψ (Y * M.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rtr_apply {n d : ℕ} (M : GL (Fin d) k) (Ψ : Matrix (Fin n) (Fin d) k → ℂ) :
    rtr M Ψ = fun Y => Ψ (Y * M.1) := rfl

/- English proof (translation)
Set `e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k` to `{ toFun := fun x => x * M.1 invFun := fun x => x * (M⁻¹).1 left_inv := fun x => by simp [Matrix.mul_assoc] right_inv := fun x => by simp [Matrix.mul_assoc] continuous_toFun := Continuous.matrix_mul continuous_id continuous_const continuous_invFun := Continuous.matrix_mul continuo …`. Conclude with `⟨hΨ.1.comp_continuous e.continuous, hΨ.2.comp_homeomorph e⟩`.
-/
theorem sb_rtr {n d : ℕ} (M : GL (Fin d) k) {Ψ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k)) : rtr M Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := by
  let e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k :=
    { toFun := fun x => x * M.1
      invFun := fun x => x * (M⁻¹).1
      left_inv := fun x => by simp [Matrix.mul_assoc]
      right_inv := fun x => by simp [Matrix.mul_assoc]
      continuous_toFun := Continuous.matrix_mul continuous_id continuous_const
      continuous_invFun := Continuous.matrix_mul continuous_id continuous_const }
  exact ⟨hΨ.1.comp_continuous e.continuous, hΨ.2.comp_homeomorph e⟩

/- English proof (translation)
Use `⟨sb_rtr M hΨ.1, fun Y hY => hΨ.2 (Y * M.1) ?_⟩` and prove the remaining obligations. Establish `hM : IsUnit (M.1).det` using `(Matrix.isUnit_iff_isUnit_det _).1 M.isUnit`. Rewrite using `[Matrix.rank_mul_eq_left_of_isUnit_det _ _ hM]` and apply the resulting hypothesis.
-/
theorem fullRk_rtr {n d : ℕ} (M : GL (Fin d) k) {Ψ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΨ : Ψ ∈ fullRk k n d) : rtr M Ψ ∈ fullRk k n d := by
  refine ⟨sb_rtr M hΨ.1, fun Y hY => hΨ.2 (Y * M.1) ?_⟩
  have hM : IsUnit (M.1).det := (Matrix.isUnit_iff_isUnit_det _).1 M.isUnit
  rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hM]

/- English proof (translation)
Use function extensionality and compare the values at `Y`. Simplify using `[rtr_apply, lact, Matrix.mul_assoc]`.
-/
theorem rtr_lact {n d : ℕ} (ν : kˣ →* ℂˣ) (M : GL (Fin d) k) (g : GL (Fin n) k)
    (Ψ : Matrix (Fin n) (Fin d) k → ℂ) : rtr M (lact ν g Ψ) = lact ν g (rtr M Ψ) := by
  funext Y; simp [rtr_apply, lact, Matrix.mul_assoc]

def diffSp (n d : ℕ) (ν : kˣ →* ℂˣ) : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ) :=
  Submodule.span ℂ {z | ∃ (g : GL (Fin n) k) (Ψ' : Matrix (Fin n) (Fin d) k → ℂ),
    Ψ' ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) ∧ z = lact ν g Ψ' - Ψ'}

/- English proof (translation)
Establish `: diffSp n d ν ≤ (diffSp n d ν).comap (rtr M)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `z ⟨g, Ψ', hΨ', rfl⟩`. Use `Submodule.subset_span ⟨g, rtr M Ψ', sb_rtr M hΨ', ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, rtr_lact]`.

Conclude with `this hΨ`.
-/
theorem rtr_diffSp {n d : ℕ} (ν : kˣ →* ℂˣ) (M : GL (Fin d) k) {Ψ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΨ : Ψ ∈ diffSp n d ν) : rtr M Ψ ∈ diffSp n d ν := by
  have : diffSp n d ν ≤ (diffSp n d ν).comap (rtr M) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨g, Ψ', hΨ', rfl⟩
    refine Submodule.subset_span ⟨g, rtr M Ψ', sb_rtr M hΨ', ?_⟩
    rw [map_sub, rtr_lact]
  exact this hΨ

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `z ⟨g, Ψ, hΨ, rfl⟩`. Conclude with `Submodule.subset_span ⟨g, Ψ, hΨ.1, rfl⟩`.
-/
theorem augRk_le_diffSp (n d : ℕ) (ν : kˣ →* ℂˣ) : augRk n d ν ≤ diffSp (k := k) n d ν := by
  refine Submodule.span_le.2 ?_
  rintro z ⟨g, Ψ, hΨ, rfl⟩
  exact Submodule.subset_span ⟨g, Ψ, hΨ.1, rfl⟩

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `z ⟨g, Ψ, hΨ, rfl⟩`. Conclude with `hA g Ψ hΨ`.
-/
theorem diffSp_le_ker {n d : ℕ} (ν : kˣ →* ℂˣ) (Λ₀ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hA : ∀ (g : GL (Fin n) k), ∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k), Λ₀ (lact ν g Ψ - Ψ) = 0) :
    diffSp n d ν ≤ LinearMap.ker Λ₀ := by
  refine Submodule.span_le.2 ?_
  rintro z ⟨g, Ψ, hΨ, rfl⟩
  exact hA g Ψ hΨ

end GlobalTheory.FullRankCoinv.JacReduce

open GlobalTheory.FullRankCoinv.JacReduce in

/- English proof (translation)
Introduce `hInd KP k _ _ _ _ n d ν hn hnd hs hu Λ₀ hA hB hC`. Take `⟨Z, hZ1, hZ2, hZ3, hZ4⟩` from `GlobalTheory.FullRankCoinv.fibre_coinvariants k n d ν (by omega) hs`. Establish `hker0` using `diffSp_le_ker ν Λ₀ hA`. Set `F` to `GlobalTheory.FullRankCoinv.fullRk k n d`. Set `Z' : F →ₗ[ℂ] (GL (Fin d) k → ℂ)` to `Z ∘ₗ F.subtype`.

Set `L' : F →ₗ[ℂ] ℂ` to `Λ₀ ∘ₗ F.subtype`. Establish `hker : LinearMap.ker Z' ≤ LinearMap.ker L'`. Introduce `Ψ hΨ`. Rewrite `hΨ`, the goal using `[LinearMap.mem_ker]`. Conclude with `hker0 (augRk_le_diffSp n d ν (hZ3 Ψ.1 Ψ.2 hΨ))`.

Set `ℓ₁ : LinearMap.range Z' →ₗ[ℂ] ℂ` to `(LinearMap.ker Z').liftQ L' hker ∘ₗ Z'.quotKerEquivRange.symm.toLinearMap`. Take `⟨ℓ, hℓ⟩` from `LinearMap.exists_extend ℓ₁`. Establish `key : ∀ Ψ (hΨ : Ψ ∈ F), ℓ (Z Ψ) = Λ₀ Ψ`. Introduce `Ψ hΨ`. Establish `h1` using `LinearMap.congr_fun hℓ ⟨Z' ⟨Ψ, hΨ⟩, LinearMap.mem_range_self _ _⟩`.

Establish `h2 : Z'.quotKerEquivRange.symm ⟨Z' ⟨Ψ, hΨ⟩, LinearMap.mem_range_self _ _⟩ = Submodule.Quotient.mk ⟨Ψ, hΨ⟩`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply the tactic sequence `first | rfl | simp [LinearMap.quotKerEquivRange_apply_mk, Z']`. Simplify using `only [ℓ₁, LinearMap.comp_apply, LinearEquiv.coe_coe, h2, Submodule.liftQ_apply] at h1`.

Conclude with `h1`. Establish `hN : ∀ u : GL (Fin d) k, GlobalTheory.JacBlock₂.IsUnipStd u → ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ℓ (fun h => f (h * u)) = ℓ f`. Introduce `u hu' f hf`. Take `⟨Ψ, hΨ, rfl⟩` from `hZ2 f hf`. Rewrite using `[← hZ4 Ψ hΨ u]`.

Use `key _ (fullRk_rtr u hΨ)` as an intermediate fact. Rewrite `this` using `[rtr_apply]`. Rewrite using `[this, key _ hΨ]`. Conclude with `hB u hu' Ψ hΨ.1`. Introduce `Ψ hΨ`.

Take `⟨Ψ₀, hΨ₀, hdiff⟩` from `hC Ψ hΨ`. Take `⟨p, q, hpq⟩` from `hInd KP k n d ν hn hnd hs hu ℓ hN (Z Ψ₀) (hZ1 Ψ₀ hΨ₀)`. Use `⟨p, q, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← hpq x, ← hZ4 Ψ₀ hΨ₀]`. Establish `h3` using `key _ (fullRk_rtr (GlobalTheory.JacBlock₂.diagFirst x) hΨ₀)`.

Rewrite `h3` using `[rtr_apply]`. Rewrite using `[h3]`. Establish `h4` using `hker0 (rtr_diffSp ν (GlobalTheory.JacBlock₂.diagFirst x) hdiff)`. Rewrite `h4` using `[LinearMap.mem_ker, map_sub, map_sub, sub_eq_zero, rtr_apply, rtr_apply]`. Conclude with `h4`.
-/
theorem GlobalTheory.FullRankCoinv.JacReduce.jac_reduce : (GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ν : kˣ →* ℂˣ), 1 ≤ n → 2 * n < d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
  ∀ ℓ : (GL (Fin d) k → ℂ) →ₗ[ℂ] ℂ,
    (∀ u : GL (Fin d) k, GlobalTheory.JacBlock₂.IsUnipStd u → ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ℓ (fun h => f (h * u)) = ℓ f) →
    ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ∃ p q : ℂ, ∀ x : kˣ,
      ℓ (fun h => f (h * GlobalTheory.JacBlock₂.diagFirst x)) = p + q * (((ν x)⁻¹ : ℂˣ) : ℂ) * GlobalTheory.SplitFlip.apow x (((d : ℂ) - 2 * (n : ℂ)) / 2)) → (GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ν : kˣ →* ℂˣ), 1 ≤ n → 2 * n < d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
  ∀ Λ₀ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ,
    (∀ (g : GL (Fin n) k), ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), Λ₀ (GlobalTheory.FullRankCoinv.lact ν g Ψ - Ψ) = 0) →
    (∀ u : GL (Fin d) k, GlobalTheory.JacBlock₂.IsUnipStd u → ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), Λ₀ (fun Y => Ψ (Y * u.1)) = Λ₀ Ψ) →
    (∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Ψ₀ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
      Ψ - Ψ₀ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin n) k) (Ψ' : Matrix (Fin n) (Fin d) k → ℂ),
        Ψ' ∈ SB (Matrix (Fin n) (Fin d) k) ∧ z = GlobalTheory.FullRankCoinv.lact ν g Ψ' - Ψ'}) →
    ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ p q : ℂ, ∀ x : kˣ,
      Λ₀ (fun Y => Ψ (Y * (GlobalTheory.JacBlock₂.diagFirst x).1)) = p + q * (((ν x)⁻¹ : ℂˣ) : ℂ) * GlobalTheory.SplitFlip.apow x (((d : ℂ) - 2 * (n : ℂ)) / 2)) := by
  intro hInd KP k _ _ _ _ n d ν hn hnd hs hu Λ₀ hA hB hC
  obtain ⟨Z, hZ1, hZ2, hZ3, hZ4⟩ := GlobalTheory.FullRankCoinv.fibre_coinvariants k n d ν (by omega) hs
  have hker0 := diffSp_le_ker ν Λ₀ hA
  let F := GlobalTheory.FullRankCoinv.fullRk k n d
  let Z' : F →ₗ[ℂ] (GL (Fin d) k → ℂ) := Z ∘ₗ F.subtype
  let L' : F →ₗ[ℂ] ℂ := Λ₀ ∘ₗ F.subtype
  have hker : LinearMap.ker Z' ≤ LinearMap.ker L' := by
    intro Ψ hΨ
    rw [LinearMap.mem_ker] at hΨ ⊢
    exact hker0 (augRk_le_diffSp n d ν (hZ3 Ψ.1 Ψ.2 hΨ))
  let ℓ₁ : LinearMap.range Z' →ₗ[ℂ] ℂ :=
    (LinearMap.ker Z').liftQ L' hker ∘ₗ Z'.quotKerEquivRange.symm.toLinearMap
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₁
  have key : ∀ Ψ (hΨ : Ψ ∈ F), ℓ (Z Ψ) = Λ₀ Ψ := by
    intro Ψ hΨ
    have h1 := LinearMap.congr_fun hℓ ⟨Z' ⟨Ψ, hΨ⟩, LinearMap.mem_range_self _ _⟩
    have h2 : Z'.quotKerEquivRange.symm ⟨Z' ⟨Ψ, hΨ⟩, LinearMap.mem_range_self _ _⟩ =
        Submodule.Quotient.mk ⟨Ψ, hΨ⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      apply Subtype.ext
      first | rfl | simp [LinearMap.quotKerEquivRange_apply_mk, Z']
    simp only [ℓ₁, LinearMap.comp_apply, LinearEquiv.coe_coe, h2, Submodule.liftQ_apply] at h1
    exact h1
  have hN : ∀ u : GL (Fin d) k, GlobalTheory.JacBlock₂.IsUnipStd u → ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν,
      ℓ (fun h => f (h * u)) = ℓ f := by
    intro u hu' f hf
    obtain ⟨Ψ, hΨ, rfl⟩ := hZ2 f hf
    rw [← hZ4 Ψ hΨ u]
    have := key _ (fullRk_rtr u hΨ)
    rw [rtr_apply] at this
    rw [this, key _ hΨ]
    exact hB u hu' Ψ hΨ.1
  intro Ψ hΨ
  obtain ⟨Ψ₀, hΨ₀, hdiff⟩ := hC Ψ hΨ
  obtain ⟨p, q, hpq⟩ := hInd KP k n d ν hn hnd hs hu ℓ hN (Z Ψ₀) (hZ1 Ψ₀ hΨ₀)
  refine ⟨p, q, fun x => ?_⟩
  rw [← hpq x, ← hZ4 Ψ₀ hΨ₀]
  have h3 := key _ (fullRk_rtr (GlobalTheory.JacBlock₂.diagFirst x) hΨ₀)
  rw [rtr_apply] at h3
  rw [h3]
  have h4 := hker0 (rtr_diffSp ν (GlobalTheory.JacBlock₂.diagFirst x) hdiff)
  rw [LinearMap.mem_ker, map_sub, map_sub, sub_eq_zero, rtr_apply, rtr_apply] at h4
  exact h4
