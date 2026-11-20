import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmulMemOfIsIntegral

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

namespace GlobalTheory.TransvLevel

/- English proof (translation)
Simplify using `only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_smul_left {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/- English proof (translation)
Introduce `E _ _ _ r X m hm v hv hiso b hb hbi`. Establish `hξ' : IsCMField.complexConj E X.ξ0 = -X.ξ0` using `X.ξ0_im`. Establish `hκc : IsCMField.complexConj E X.κ0 = -X.κ0`. Apply the tactic sequence `rcases X.κ0_xi with h | h <;> simp [h, hξ', map_ofNat]`. Establish `hb' : IsCMField.complexConj E b = b` using `hb`.

Establish `hmκ : IsIntegral ℤ ((m : E) * X.κ0)`. Break down `X.κ0_xi with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `hm`. Rewrite using `[h, mul_neg]`.

Conclude with `hm.neg`. Use `set α : E := ((X.g * X.NA * X.NC * m : ℕ) : E) * b * X.κ0 with hαdef`. Establish `hα : cc α = -α`. Simplify using `[hαdef, cc, hb', hκc]`. Establish `key : ∀ x ∈ X.Λ, (b * ((m : E) * X.κ0) * herm X.Gm ((X.NA : E) • x) v) • ((X.NC : E) • v) ∈ X.Λ` using `fun x hx => GlobalTheory.FlagData.smul_mem_of_isIntegral _ ((hbi.mul hmκ).mul (X.L'_int _ (X.NA_sub x hx) _ hv)) (X.NC_sub v hv)`.

Establish `e : ∀ x, (α * herm X.Gm x v) • v = (X.g : E) • ((b * ((m : E) * X.κ0) * herm X.Gm ((X.NA : E) • x) v) • ((X.NC : E) • v))`. Introduce `x`. Rewrite using `[smul_smul, smul_smul, hαdef, herm_smul_left]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `key' : ∀ x ∈ X.Λ, (α * herm X.Gm x v) • v ∈ X.Λ` using `fun x hx => by`. Rewrite using `[e]`. Conclude with `GlobalTheory.FlagData.smul_mem_of_isIntegral _ (isIntegral_natCast _) (key x hx)`. Use `⟨GlobalTheory.FlagData.transv X.Gm hiso α, X.cong _ ⟨GlobalTheory.FlagData.herm_transvMat X.Gm_herm hiso hα, fun x => ?_⟩ (fun x hx => ?_), fun τ => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `x ∈ X.Λ ↔ transvMat X.Gm v α *ᵥ x ∈ X.Λ`. Rewrite using `[GlobalTheory.FlagData.transvMat_mulVec]`. Use `⟨fun hx => Submodule.add_mem _ hx (key' x hx), fun hx => ?_⟩` and prove the remaining obligations. Establish `h` using `key' _ hx`. Rewrite `h` using `[GlobalTheory.FlagData.herm_add_smul_left, hiso, mul_zero, add_zero]`.

Simplify using `using Submodule.sub_mem _ hx h`. Use `⟨_, key x hx, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `transvMat X.Gm v α *ᵥ x - x = _`. Rewrite using `[GlobalTheory.FlagData.transvMat_mulVec, add_sub_cancel_left, e]`. Express the relevant statement in the definitionally equal form `(transvMat X.Gm v α).map τ.1 = _`.

Use `TransvectionPeriodicity.transvMat_map X.toData v τ α _ ?_` and prove the remaining obligations. Rewrite using `[hαdef, map_mul, map_mul, TransvectionPeriodicity.emb_kappa X.toData τ, map_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem transv_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (m : ℕ), IsIntegral ℤ ((m : E) * (2 * X.ξ0)) → ∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ X.Γ, ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ ((((X.g * X.NA * X.NC * m : ℕ) : ℝ) : ℂ) * τ.1 b) := by
  intro E _ _ _ r X m hm v hv hiso b hb hbi
  have hξ' : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
  have hκc : IsCMField.complexConj E X.κ0 = -X.κ0 := by
    rcases X.κ0_xi with h | h <;> simp [h, hξ', map_ofNat]
  have hb' : IsCMField.complexConj E b = b := hb
  have hmκ : IsIntegral ℤ ((m : E) * X.κ0) := by
    rcases X.κ0_xi with h | h
    · rw [h]; exact hm
    · rw [h, mul_neg]; exact hm.neg
  set α : E := ((X.g * X.NA * X.NC * m : ℕ) : E) * b * X.κ0 with hαdef
  have hα : cc α = -α := by
    simp [hαdef, cc, hb', hκc]
  have key : ∀ x ∈ X.Λ,
      (b * ((m : E) * X.κ0) * herm X.Gm ((X.NA : E) • x) v) • ((X.NC : E) • v) ∈ X.Λ := fun x hx =>
    GlobalTheory.FlagData.smul_mem_of_isIntegral _
      ((hbi.mul hmκ).mul (X.L'_int _ (X.NA_sub x hx) _ hv)) (X.NC_sub v hv)
  have e : ∀ x, (α * herm X.Gm x v) • v =
      (X.g : E) • ((b * ((m : E) * X.κ0) * herm X.Gm ((X.NA : E) • x) v) • ((X.NC : E) • v)) := by
    intro x
    rw [smul_smul, smul_smul, hαdef, herm_smul_left]
    congr 1
    push_cast
    ring
  have key' : ∀ x ∈ X.Λ, (α * herm X.Gm x v) • v ∈ X.Λ := fun x hx => by
    rw [e]
    exact GlobalTheory.FlagData.smul_mem_of_isIntegral _ (isIntegral_natCast _) (key x hx)
  refine ⟨GlobalTheory.FlagData.transv X.Gm hiso α, X.cong _
    ⟨GlobalTheory.FlagData.herm_transvMat X.Gm_herm hiso hα, fun x => ?_⟩ (fun x hx => ?_), fun τ => ?_⟩
  · change x ∈ X.Λ ↔ transvMat X.Gm v α *ᵥ x ∈ X.Λ
    rw [GlobalTheory.FlagData.transvMat_mulVec]
    refine ⟨fun hx => Submodule.add_mem _ hx (key' x hx), fun hx => ?_⟩
    have h := key' _ hx
    rw [GlobalTheory.FlagData.herm_add_smul_left, hiso, mul_zero, add_zero] at h
    simpa using Submodule.sub_mem _ hx h
  · refine ⟨_, key x hx, ?_⟩
    change transvMat X.Gm v α *ᵥ x - x = _
    rw [GlobalTheory.FlagData.transvMat_mulVec, add_sub_cancel_left, e]
  · change (transvMat X.Gm v α).map τ.1 = _
    refine TransvectionPeriodicity.transvMat_map X.toData v τ α _ ?_
    rw [hαdef, map_mul, map_mul, TransvectionPeriodicity.emb_kappa X.toData τ, map_natCast]
    push_cast
    ring

end GlobalTheory.TransvLevel
