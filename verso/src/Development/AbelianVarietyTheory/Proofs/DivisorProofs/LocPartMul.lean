import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp

noncomputable section

namespace GlobalTheory.OrbDesc

variable {H : Type} [Group H]

/- English proof (translation)
Unfold `GlobalTheory.LKLoc.locPart`. Use extensionality with `g`. Simplify using `only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hg, k, hk, rfl⟩`.

Use `⟨hg, l * k * l⁻¹, L.mul_mem (L.mul_mem hl hk) (L.inv_mem hl), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨hg, k, hk, rfl⟩`. Use `⟨hg, l⁻¹ * k * l, L.mul_mem (L.mul_mem (L.inv_mem hl) hk) hl, ?_⟩` and prove the remaining obligations. Use `hT _ hg t ht` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem locPart_mul {T L : Subgroup H} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) {t x l : H} (ht : t ∈ T)
    (hl : l ∈ L) : GlobalTheory.LKLoc.locPart T L (t * x * l) = GlobalTheory.LKLoc.locPart T L x := by
  unfold GlobalTheory.LKLoc.locPart
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hg, k, hk, rfl⟩
    refine ⟨hg, l * k * l⁻¹, L.mul_mem (L.mul_mem hl hk) (L.inv_mem hl), ?_⟩
    calc x * (l * k * l⁻¹) * x⁻¹ = t⁻¹ * ((t * x * l * k * (t * x * l)⁻¹) * t) := by group
      _ = t⁻¹ * (t * (t * x * l * k * (t * x * l)⁻¹)) := by rw [hT _ hg t ht]
      _ = t * x * l * k * (t * x * l)⁻¹ := by group
  · rintro ⟨hg, k, hk, rfl⟩
    refine ⟨hg, l⁻¹ * k * l, L.mul_mem (L.mul_mem (L.inv_mem hl) hk) hl, ?_⟩
    have := hT _ hg t ht
    calc t * x * l * (l⁻¹ * k * l) * (t * x * l)⁻¹ = t * (x * k * x⁻¹) * t⁻¹ := by group
      _ = (x * k * x⁻¹) * t * t⁻¹ := by rw [← this]
      _ = x * k * x⁻¹ := by group

/- English proof (translation)
Unfold `wt`. Rewrite using `[locPart_mul hT ht hl, hΨr l hl, hΨl t ht]`.
-/
theorem wt_mul {T L : Subgroup H} (U : Subgroup H) {Ψ : H → ℂ} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hΨl : ∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) (hΨr : ∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) {t x l : H} (ht : t ∈ T)
    (hl : l ∈ L) : wt T L U Ψ (t * x * l) = wt T L U Ψ x := by
  unfold wt
  rw [locPart_mul hT ht hl, hΨr l hl, hΨl t ht]

/- English proof (translation)
Take `⟨t, ht, l, hl, h⟩` from `(DoubleCoset.eq T L _ _).1 (DoubleCoset.out_eq' T L (DoubleCoset.mk T L x))`. Conclude with `(wt_mul U hT hΨl hΨr ht hl).symm.trans (congrArg _ h.symm)`.
-/
theorem wt_out {T L : Subgroup H} (U : Subgroup H) {Ψ : H → ℂ} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hΨl : ∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) (hΨr : ∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) (x : H) :
    wt T L U Ψ (Quotient.out (DoubleCoset.mk T L x)) = wt T L U Ψ x := by
  obtain ⟨t, ht, l, hl, h⟩ := (DoubleCoset.eq T L _ _).1 (DoubleCoset.out_eq' T L (DoubleCoset.mk T L x))
  exact (wt_mul U hT hΨl hΨr ht hl).symm.trans (congrArg _ h.symm)

end GlobalTheory.OrbDesc
