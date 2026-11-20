import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

noncomputable section

namespace GlobalTheory.TopLevelInv

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(u ᵥ* κ.val) ⬝ᵥ ((κ⁻¹).val *ᵥ y) = u ⬝ᵥ y`. Rewrite using `[dotProduct_mulVec, vecMul_vecMul, Units.mul_inv, vecMul_one]`.
-/
theorem pairing_gl_inv {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (κ : GL n k) (u y : n → k) :
    ∑ r, (∑ s, u s * κ.val s r) * (∑ t, (κ⁻¹).val r t * y t) = ∑ r, u r * y r := by
  change (u ᵥ* κ.val) ⬝ᵥ ((κ⁻¹).val *ᵥ y) = u ⬝ᵥ y
  rw [dotProduct_mulVec, vecMul_vecMul, Units.mul_inv, vecMul_one]

/- English proof (translation)
Introduce `hx hx1 he hst`. Unfold `phase`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hi` using `i.2`. Break down `Nat.lt_or_ge i.val j with h | h` into its components or cases.

Establish `hxi : x' i = x i` using `hx _ (by omega) (by omega)`. Establish `hei : e' i = e i` using `he _ (by omega)`. Establish `hc : colVar x' e' i = colVar x e i`. Use function extensionality and compare the values at `r`. Simplify using `only [colVar, hxi, hei]`.

Establish `hch : ch (stepPt (x' i) (e' i)) = ch (stepPt (x i) (e i))` using `by rw [hxi, hei]`. Rewrite using `[hch, hc]`. Use `congr 1`. Use `split_ifs with hev`. Establish `hr : rowVar x' e' (i + 1) = rowVar x e (i + 1)`.

Establish `hne : (i : ℕ) + 1 ≠ j`. Introduce `h'`. Rewrite `hev` using `[show Γ.m - 2 - (i : ℕ) = 1 by omega]`. Conclude with `Nat.not_even_one hev`. Use function extensionality and compare the values at `s`.

Establish `h1 : x' (i + 1) = x (i + 1)` using `hx _ hne (by omega)`. Simplify using `only [rowVar, h1]`. Use `split_ifs with h3`. Rewrite using `[he ⟨(i : ℕ) + 1, h3⟩ (by simpa using hne)]`. Both sides reduce to the same expression.

Rewrite using `[hr]`. Both sides reduce to the same expression. Take `⟨i, hi'⟩` from `i`. Establish `hij : i = j` using `by simp only at h hi; omega`. Substitute `hij` using the available equality.

Establish `h0 : Γ.m - 2 - i = 0` using `by omega`. Establish `hch : ∀ z : Matrix (Fin (topRank Γ (i + 1)) ⊕ Fin (Γ.m - 2 - i)) (Fin (topRank Γ i) ⊕ Fin (Γ.m - 2 - i + 1)) k, ch z = 0`. Introduce `z`. Use `haveI : IsEmpty (Fin (Γ.m - 2 - i)) := ⟨fun l => by have := l.2; omega⟩`. Simplify using `[ch]`.

Rewrite using `[hch, hch, zero_add, zero_add]`. Simplify using `only [Fin.val_mk]`. Rewrite using `[if_pos (by rw [h0]; exact ⟨0, rfl⟩), if_pos (by rw [h0]; exact ⟨0, rfl⟩)]`. Establish `hrow : ∀ (z : ColArgs Γ) (f : Vars Γ) s, rowVar z f (i + 1) s = z (i + 1) (topLast Γ (i + 1 + 1)) s`. Introduce `z f s`.

Simplify using `only [rowVar]`. Rewrite using `[dif_neg (by omega)]`. Simplify using `only [hrow, hx1, colVar, Fin.val_mk, hst, map_inv]`. Rewrite using `[← map_inv]`. Establish `hv : ∀ (g : GL (Fin (topRank Γ (i + 1))) k) a b, (embX (Γ.m - 2 - i) g).val (Sum.inl a) (Sum.inl b) = g.val a b` using `fun _ _ _ => rfl`.

Establish `hv2 : ∀ (g : GL (Fin (topRank Γ (i + 1))) k) a b, (embX (Γ.m - 2 - i) g).val (Sum.inl a) (Sum.inr b) = 0` using `fun _ _ _ => rfl`. Simplify using `only [Matrix.mul_apply, Fintype.sum_sum_type, hv, hv2, zero_mul, Finset.sum_const_zero, add_zero]`. Conclude with `(pairing_gl_inv κ _ _).symm`.
-/
theorem phase_eq_of_lastMove {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (j : ℕ) (hB : j + 2 = Γ.m)
    (κ : GL (Fin (topRank Γ (j + 1))) k) (x x' : ColArgs Γ) (e e' : Vars Γ) :
    (∀ i, i ≠ j → i ≠ j + 1 → x' i = x i) → x' (j + 1) = x (j + 1) * κ.val →
    (∀ i : Fin (Γ.m - 1), i.val ≠ j → e' i = e i) →
    stepPt (x' j) (e' ⟨j, by omega⟩) = ((embX (Γ.m - 2 - j) κ)⁻¹).val * stepPt (x j) (e ⟨j, by omega⟩) →
    phase x e = phase x' e' := by
  intro hx hx1 he hst
  unfold phase
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.2
  rcases Nat.lt_or_ge i.val j with h | h
  · have hxi : x' i = x i := hx _ (by omega) (by omega)
    have hei : e' i = e i := he _ (by omega)
    have hc : colVar x' e' i = colVar x e i := by
      funext r; simp only [colVar, hxi, hei]
    have hch : ch (stepPt (x' i) (e' i)) = ch (stepPt (x i) (e i)) := by rw [hxi, hei]
    rw [hch, hc]
    congr 1
    split_ifs with hev
    · have hr : rowVar x' e' (i + 1) = rowVar x e (i + 1) := by
        have hne : (i : ℕ) + 1 ≠ j := by
          intro h'
          rw [show Γ.m - 2 - (i : ℕ) = 1 by omega] at hev
          exact Nat.not_even_one hev
        funext s
        have h1 : x' (i + 1) = x (i + 1) := hx _ hne (by omega)
        simp only [rowVar, h1]
        split_ifs with h3
        · rw [he ⟨(i : ℕ) + 1, h3⟩ (by simpa using hne)]
        · rfl
      rw [hr]
    · rfl
  · obtain ⟨i, hi'⟩ := i
    have hij : i = j := by simp only at h hi; omega
    subst hij
    have h0 : Γ.m - 2 - i = 0 := by omega
    have hch : ∀ z : Matrix (Fin (topRank Γ (i + 1)) ⊕ Fin (Γ.m - 2 - i)) (Fin (topRank Γ i) ⊕ Fin (Γ.m - 2 - i + 1)) k,
        ch z = 0 := by
      intro z
      haveI : IsEmpty (Fin (Γ.m - 2 - i)) := ⟨fun l => by have := l.2; omega⟩
      simp [ch]
    rw [hch, hch, zero_add, zero_add]
    simp only [Fin.val_mk]
    rw [if_pos (by rw [h0]; exact ⟨0, rfl⟩), if_pos (by rw [h0]; exact ⟨0, rfl⟩)]
    have hrow : ∀ (z : ColArgs Γ) (f : Vars Γ) s, rowVar z f (i + 1) s = z (i + 1) (topLast Γ (i + 1 + 1)) s := by
      intro z f s
      simp only [rowVar]
      rw [dif_neg (by omega)]
    simp only [hrow, hx1, colVar, Fin.val_mk, hst, map_inv]
    rw [← map_inv]
    have hv : ∀ (g : GL (Fin (topRank Γ (i + 1))) k) a b,
        (embX (Γ.m - 2 - i) g).val (Sum.inl a) (Sum.inl b) = g.val a b := fun _ _ _ => rfl
    have hv2 : ∀ (g : GL (Fin (topRank Γ (i + 1))) k) a b,
        (embX (Γ.m - 2 - i) g).val (Sum.inl a) (Sum.inr b) = 0 := fun _ _ _ => rfl
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, hv, hv2, zero_mul, Finset.sum_const_zero, add_zero]
    exact (pairing_gl_inv κ _ _).symm

end GlobalTheory.TopLevelInv
