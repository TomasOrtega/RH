import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

/- English proof (translation)
Unfold `ext0`. Distinguish the cases in `ha : a ∈ H`. Establish `h1 : (y : G)⁻¹ * a * y ∈ H` using `H.mul_mem (H.mul_mem (H.inv_mem y.2) ha) y.2`. Rewrite using `[dif_pos ha, dif_pos h1]`. Conclude with `hψ ⟨a, ha⟩ y`.

Establish `h1 : ¬ (y : G)⁻¹ * a * y ∈ H`. Introduce `h`. Apply `ha` to reduce the goal to its premises. Establish `h2 : (y : G) * ((y : G)⁻¹ * a * y) * (y : G)⁻¹ ∈ H` using `H.mul_mem (H.mul_mem y.2 h) (H.inv_mem y.2)`. Establish `h3 : (y : G) * ((y : G)⁻¹ * a * y) * (y : G)⁻¹ = a` using `by group`.

Rewrite `h2` using `[h3]`. Then use the resulting hypothesis. Rewrite using `[dif_neg ha, dif_neg h1]`.
-/
theorem subgroupFunctionExtendByZero_conj_of_mem {L G : Type} [Field L] [Group G] (H : Subgroup G) (ψ : H → L)
    (hψ : ∀ h x : H, ψ (x⁻¹ * h * x) = ψ h) (a : G) (y : H) :
    ext0 H ψ ((y : G)⁻¹ * a * y) = ext0 H ψ a := by
  unfold ext0
  by_cases ha : a ∈ H
  · have h1 : (y : G)⁻¹ * a * y ∈ H := H.mul_mem (H.mul_mem (H.inv_mem y.2) ha) y.2
    rw [dif_pos ha, dif_pos h1]
    exact hψ ⟨a, ha⟩ y
  · have h1 : ¬ (y : G)⁻¹ * a * y ∈ H := by
      intro h
      apply ha
      have h2 : (y : G) * ((y : G)⁻¹ * a * y) * (y : G)⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem y.2 h) (H.inv_mem y.2)
      have h3 : (y : G) * ((y : G)⁻¹ * a * y) * (y : G)⁻¹ = a := by group
      rwa [h3] at h2
    rw [dif_neg ha, dif_neg h1]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, y⟩ ⟨q', y'⟩ h`. Simplify using `only at h`. Establish `hq : q = q'`. Establish `h1 : ((q.out * (y : G) : G) : G ⧸ H) = ((q'.out * (y' : G) : G) : G ⧸ H)` using `by rw [h]`.

Rewrite `h1` using `[QuotientGroup.mk_mul_of_mem _ y.2, QuotientGroup.mk_mul_of_mem _ y'.2, QuotientGroup.out_eq', QuotientGroup.out_eq']`. Conclude with `h1`. Substitute `hq` using the available equality. Establish `: y = y'` using `Subtype.ext (mul_left_cancel h)`. Rewrite using `[this]`.

Introduce `x`. Take `⟨y, hy⟩` from `QuotientGroup.mk_out_eq_mul H x`. Use `⟨((x : G ⧸ H), y⁻¹), ?_⟩` and prove the remaining obligations. Simplify using `[hy]`.
-/
theorem out_mul_bijective {G : Type} [Group G] (H : Subgroup G) :
    Function.Bijective (fun p : (G ⧸ H) × H => p.1.out * (p.2 : G)) := by
  constructor
  · rintro ⟨q, y⟩ ⟨q', y'⟩ h
    simp only at h
    have hq : q = q' := by
      have h1 : ((q.out * (y : G) : G) : G ⧸ H) = ((q'.out * (y' : G) : G) : G ⧸ H) := by rw [h]
      rw [QuotientGroup.mk_mul_of_mem _ y.2, QuotientGroup.mk_mul_of_mem _ y'.2,
        QuotientGroup.out_eq', QuotientGroup.out_eq'] at h1
      exact h1
    subst hq
    have : y = y' := Subtype.ext (mul_left_cancel h)
    rw [this]
  · intro x
    obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul H x
    refine ⟨((x : G ⧸ H), y⁻¹), ?_⟩
    simp [hy]

/- English proof (translation)
Introduce `L _ _ G _ _ H ψ hψ g`. Use `Fintype.ofFinite G` as an intermediate fact. Use `Fintype.ofFinite (G ⧸ H)` as an intermediate fact. Use `Fintype.ofFinite H` as an intermediate fact. Establish `hc : (Nat.card H : L) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`.

Unfold `ind`. Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← (out_mul_bijective H).sum_comp (fun x : G => ext0 H ψ (x⁻¹ * g * x)), Fintype.sum_prod_type]`. Establish `h1 : ∀ q : G ⧸ H, ∑ y : H, ext0 H ψ ((q.out * (y : G))⁻¹ * g * (q.out * (y : G))) = (Nat.card H : L) * ext0 H ψ (q.out⁻¹ * g * q.out)`. Introduce `q`. Establish `h2 : ∀ y : H, ext0 H ψ ((q.out * (y : G))⁻¹ * g * (q.out * (y : G))) = ext0 H ψ (q.out⁻¹ * g * q.out)`.

Introduce `y`. Rewrite using `[← subgroupFunctionExtendByZero_conj_of_mem H ψ hψ (q.out⁻¹ * g * q.out) y]`. Use `congr 1`. Use `group`. Simplify using `only [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]`.

Simplify using `only [h1]`. Rewrite using `[← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]`.
-/
theorem ind_eq_finsum_cosets : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), (∀ h x : H, ψ (x⁻¹ * h * x) = ψ h) → ∀ g : G, ind H ψ g = ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out) := by
  intro L _ _ G _ _ H ψ hψ g
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite (G ⧸ H)
  have := Fintype.ofFinite H
  have hc : (Nat.card H : L) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  unfold ind
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← (out_mul_bijective H).sum_comp (fun x : G => ext0 H ψ (x⁻¹ * g * x)), Fintype.sum_prod_type]
  have h1 : ∀ q : G ⧸ H, ∑ y : H, ext0 H ψ ((q.out * (y : G))⁻¹ * g * (q.out * (y : G)))
      = (Nat.card H : L) * ext0 H ψ (q.out⁻¹ * g * q.out) := by
    intro q
    have h2 : ∀ y : H, ext0 H ψ ((q.out * (y : G))⁻¹ * g * (q.out * (y : G)))
        = ext0 H ψ (q.out⁻¹ * g * q.out) := by
      intro y
      rw [← subgroupFunctionExtendByZero_conj_of_mem H ψ hψ (q.out⁻¹ * g * q.out) y]
      congr 1
      group
    simp only [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  simp only [h1]
  rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end GlobalTheory.BI
