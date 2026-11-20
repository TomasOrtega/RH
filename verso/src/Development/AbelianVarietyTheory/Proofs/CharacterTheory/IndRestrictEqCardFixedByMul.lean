import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedClassFunctionFromSubgroupEqFinsumCosets
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

/- English proof (translation)
Use `conv_rhs => rw [← QuotientGroup.out_eq' q]`. Rewrite using `[MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, ← H.inv_mem_iff]`. Simplify using `only [mul_inv_rev, inv_inv, mul_assoc]`.
-/
theorem out_conj_mem_iff_smul_eq {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    q.out⁻¹ * g * q.out ∈ H ↔ g • q = q := by
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, ← H.inv_mem_iff]
  simp only [mul_inv_rev, inv_inv, mul_assoc]

/- English proof (translation)
Introduce `L _ _ G _ _ H χ hχ g`. Establish `: Fintype (G ⧸ H)` using `Fintype.ofFinite _`. Establish `hψ : ∀ h x : H, (fun h : H => χ h) (x⁻¹ * h * x) = (fun h : H => χ h) h`. Introduce `h x`. Simplify using `using hχ h x`.

Establish `hterm : ∀ q : G ⧸ H, ext0 H (fun h : H => χ h) (q.out⁻¹ * g * q.out) = (if g • q = q then (1 : L) else 0) * χ g`. Introduce `q`. Unfold `ext0`. Distinguish the cases in `hq : g • q = q`. Establish `hm` using `(out_conj_mem_iff_smul_eq H g q).2 hq`.

Rewrite using `[dif_pos hm, if_pos hq, one_mul]`. Conclude with `hχ g q.out`. Establish `hm : q.out⁻¹ * g * q.out ∉ H` using `fun h => hq ((out_conj_mem_iff_smul_eq H g q).1 h)`. Rewrite using `[dif_neg hm, if_neg hq, zero_mul]`. Rewrite using `[ind_eq_finsum_cosets L G H _ hψ g, finsum_eq_sum_of_fintype]`.

Repeatedly rewrite using `[hterm]`. Rewrite using `[← Finset.sum_mul, Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Both sides reduce to the same expression.
-/
theorem ind_restrict_eq_card_fixedBy_mul : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (χ : G → L), (∀ g x : G, χ (x⁻¹ * g * x) = χ g) → ∀ g : G, ind H (fun h : H => χ h) g = (Nat.card (MulAction.fixedBy (G ⧸ H) g) : L) * χ g := by
  intro L _ _ G _ _ H χ hχ g
  classical
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hψ : ∀ h x : H, (fun h : H => χ h) (x⁻¹ * h * x) = (fun h : H => χ h) h := by
    intro h x
    simpa using hχ h x
  have hterm : ∀ q : G ⧸ H, ext0 H (fun h : H => χ h) (q.out⁻¹ * g * q.out)
      = (if g • q = q then (1 : L) else 0) * χ g := by
    intro q
    unfold ext0
    by_cases hq : g • q = q
    · have hm := (out_conj_mem_iff_smul_eq H g q).2 hq
      rw [dif_pos hm, if_pos hq, one_mul]
      exact hχ g q.out
    · have hm : q.out⁻¹ * g * q.out ∉ H := fun h => hq ((out_conj_mem_iff_smul_eq H g q).1 h)
      rw [dif_neg hm, if_neg hq, zero_mul]
  rw [ind_eq_finsum_cosets L G H _ hψ g, finsum_eq_sum_of_fintype]
  simp_rw [hterm]
  rw [← Finset.sum_mul, Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

end GlobalTheory.BI
