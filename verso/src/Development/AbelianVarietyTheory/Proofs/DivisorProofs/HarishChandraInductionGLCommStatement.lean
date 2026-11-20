import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLComm
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
/- English proof (translation)
Unfold `hc hcTw`. Simplify using `only [GlobalTheory.HCCommF.gal_id]`. Use `congr 1`. Rewrite using `[← finsum_comp_equiv (Equiv.mulLeft p)]`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Simplify using `only [Equiv.coe_mulLeft, mul_inv_rev, mul_assoc, inv_mul_cancel_left]`.
-/
private lemma hc_conj_invariant {F : Type} [Field F] (a b n : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (x p : GL (Fin n) F) :
    hc a b α β n (p * x * p⁻¹) = hc a b α β n x := by
  unfold hc hcTw
  simp only [GlobalTheory.HCCommF.gal_id]
  congr 1
  rw [← finsum_comp_equiv (Equiv.mulLeft p)]
  congr 1
  funext y
  simp only [Equiv.coe_mulLeft, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

/- English proof (translation)
Take `⟨w, rfl⟩ : ∃ w, z = GlobalTheory.HCCommF.aflipG w` from `⟨GlobalTheory.HCCommF.aflipG z, (GlobalTheory.HCCommF.aflipG_aflipG z).symm⟩`. Rewrite using `[GlobalTheory.HCCommF.aflipG_aflipG, GlobalTheory.HCCommF.inPar_aflip]`. Unfold `tlG brG`. Rewrite using `[GlobalTheory.HCCommF.aflipG_coe, GlobalTheory.HCCommF.tl_aflip, GlobalTheory.HCCommF.br_aflip, GlobalTheory.HCCommF.class_aflip hβ, GlobalTheory.HCCommF.class_aflip hα, mul_comm (β _)]`.
-/
private lemma inPar_swap_eq_inPar_aflipG {F : Type} [Field F] (a b : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β) (z : GL (Fin (a + b)) F) :
    (if InPar b z then β (tlG b z) * α (brG b a z) else 0) =
      (if InPar a (GlobalTheory.HCCommF.aflipG z) then
        α (tlG a (GlobalTheory.HCCommF.aflipG z)) * β (brG a b (GlobalTheory.HCCommF.aflipG z)) else 0) := by
  obtain ⟨w, rfl⟩ : ∃ w, z = GlobalTheory.HCCommF.aflipG w :=
    ⟨GlobalTheory.HCCommF.aflipG z, (GlobalTheory.HCCommF.aflipG_aflipG z).symm⟩
  rw [GlobalTheory.HCCommF.aflipG_aflipG, GlobalTheory.HCCommF.inPar_aflip]
  unfold tlG brG
  rw [GlobalTheory.HCCommF.aflipG_coe, GlobalTheory.HCCommF.tl_aflip, GlobalTheory.HCCommF.br_aflip,
    GlobalTheory.HCCommF.class_aflip hβ, GlobalTheory.HCCommF.class_aflip hα, mul_comm (β _)]

/- English proof (translation)
Unfold `hc hcTw`. Simplify using `only [GlobalTheory.HCCommF.gal_id]`. Establish `hcard : Nat.card {p : GL (Fin (a + b)) F // InPar b p} = Nat.card {p : GL (Fin (a + b)) F // InPar a p}` using `Nat.card_congr (Equiv.subtypeEquiv (GlobalTheory.HCCommF.aflipE (F := F) (a + b)) (fun p => by show InPar b p ↔ InPar a (GlobalTheory.HCCommF.aflipG p) conv_lhs => rw [← GlobalTheory.HCCommF.aflipG_aflipG p]`. Conclude with `GlobalTheory.HCCommF.inPar_aflip _))`. Rewrite using `[hcard]`.

Use `congr 1`. Use `conv_rhs => rw [← finsum_comp_equiv ((GlobalTheory.HCCommF.aflipE (F := F) (a + b)).trans (Equiv.inv _))]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[inPar_swap_eq_inPar_aflipG a b α β hα hβ]`.

Establish `h : GlobalTheory.HCCommF.aflipG (y⁻¹ * x * y) = ((GlobalTheory.HCCommF.aflipG y)⁻¹)⁻¹ * GlobalTheory.HCCommF.aflipG x * (GlobalTheory.HCCommF.aflipG y)⁻¹`. Rewrite using `[inv_inv, GlobalTheory.HCCommF.aflipG_mul, GlobalTheory.HCCommF.aflipG_mul, GlobalTheory.HCCommF.aflipG_inv, mul_assoc]`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
private lemma hc_swap_eq_hc_aflipG {F : Type} [Field F] (a b : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β) (x : GL (Fin (a + b)) F) :
    hc b a β α (a + b) x = hc a b α β (a + b) (GlobalTheory.HCCommF.aflipG x) := by
  unfold hc hcTw
  simp only [GlobalTheory.HCCommF.gal_id]
  have hcard : Nat.card {p : GL (Fin (a + b)) F // InPar b p} =
      Nat.card {p : GL (Fin (a + b)) F // InPar a p} :=
    Nat.card_congr (Equiv.subtypeEquiv (GlobalTheory.HCCommF.aflipE (F := F) (a + b)) (fun p => by
      show InPar b p ↔ InPar a (GlobalTheory.HCCommF.aflipG p)
      conv_lhs => rw [← GlobalTheory.HCCommF.aflipG_aflipG p]
      exact GlobalTheory.HCCommF.inPar_aflip _))
  rw [hcard]
  congr 1
  conv_rhs => rw [← finsum_comp_equiv ((GlobalTheory.HCCommF.aflipE (F := F) (a + b)).trans (Equiv.inv _))]
  congr 1
  funext y
  rw [inPar_swap_eq_inPar_aflipG a b α β hα hβ]
  have h : GlobalTheory.HCCommF.aflipG (y⁻¹ * x * y) =
      ((GlobalTheory.HCCommF.aflipG y)⁻¹)⁻¹ * GlobalTheory.HCCommF.aflipG x * (GlobalTheory.HCCommF.aflipG y)⁻¹ := by
    rw [inv_inv, GlobalTheory.HCCommF.aflipG_mul, GlobalTheory.HCCommF.aflipG_mul, GlobalTheory.HCCommF.aflipG_inv, mul_assoc]
  rw [h]
  rfl

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `F _ _ a b n α β hα hβ hn`. Substitute `hn` using the available equality. Use function extensionality and compare the values at `x`. Rewrite using `[hc_swap_eq_hc_aflipG a b α β hα hβ x]`. Take `⟨p, hp⟩` from `GlobalTheory.HCCommF.aflipG_conj x`.

Rewrite using `[hp, hc_conj_invariant]`.
-/
theorem _root_.GlobalTheory.T.harishChandraInductionGL_comm : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsCl α → IsCl β → n = a + b → hc a b α β n = hc b a β α n := by
  intro F _ _ a b n α β hα hβ hn
  subst hn
  funext x
  rw [hc_swap_eq_hc_aflipG a b α β hα hβ x]
  obtain ⟨p, hp⟩ := GlobalTheory.HCCommF.aflipG_conj x
  rw [hp, hc_conj_invariant]
