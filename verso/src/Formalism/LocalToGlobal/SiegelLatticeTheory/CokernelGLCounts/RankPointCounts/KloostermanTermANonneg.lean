import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints

set_option linter.dupNamespace false

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Asm

variable {D : D7} {X : HidaSetting D}

/- English proof (translation)
Establish `hHb : ∀ c, 0 < Hb large₂.sc.b c D.R.m D.R.f` using `fun c => by unfold Hb Scale.b; positivity`. Establish `h1 : 0 ≤ C / (D.R.k : ℝ)` using `div_nonneg hC (Nat.cast_nonneg _)`. Unfold `k2A1`. Conclude with `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg (hHb C).le _)) (Real.rpow_nonneg (hHb Ch).le _)) (Real.rpow_nonneg (hHb C).le _)) (Real.rpow_nonneg (hHb Cc).le _)`.
-/
theorem kloostermanTermA_nonneg (large₂ : SizeData₂ D) {C Ch Cc : ℝ} (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (hCc : 0 ≤ Cc) (j : ℕ) :
    0 ≤ k2A1 large₂ C Ch Cc j := by
  have hHb : ∀ c, 0 < Hb large₂.sc.b c D.R.m D.R.f := fun c => by unfold Hb Scale.b; positivity
  have h1 : 0 ≤ C / (D.R.k : ℝ) := div_nonneg hC (Nat.cast_nonneg _)
  unfold k2A1
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg h1 _)
    (Real.rpow_nonneg (hHb C).le _)) (Real.rpow_nonneg (hHb Ch).le _)) (Real.rpow_nonneg (hHb C).le _))
    (Real.rpow_nonneg (hHb Cc).le _)

/- English proof (translation)
Establish `hH : H1C large₂ CH = large₂.sc.b ^ (CH * (D.R.m : ℝ))` using `rfl`. Rewrite `hDel`, `hcos` using `[hH]`. Establish `hHb : ∀ c, 0 < Hb large₂.sc.b c D.R.m D.R.f` using `fun c => by unfold Hb Scale.b; positivity`. Establish `hk : (0 : ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`. Establish `hrk : D.R.rS + 3 ≤ D.R.k`.

Use `D.R.m_add_three_le_k` as an intermediate fact. Unfold `Ranks.rS`. Use linear arithmetic over natural numbers and integers. Establish `hrkR : (D.R.rS : ℝ) + 3 ≤ D.R.k` using `by exact_mod_cast hrk`. Establish `hjr : (j : ℝ) ≤ D.R.rS` using `by exact_mod_cast (Finset.mem_Icc.1 hj).2`.

Establish `hS1 : ∀ δ, 1 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ`. Introduce `δ`. Unfold `k2S`. Use `Finset.prod_induction _ (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun τ _ => ?_` and prove the remaining obligations. Unfold `k2sg`.

Conclude with `(Finset.le_fold_max 1).2 (Or.inl le_rfl)`. Establish `hK0 : 0 ≤ ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4))` using `mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg hC hk) _) (Real.rpow_nonneg (hHb C).le _)) (Real.rpow_nonneg (hHb Ch).le _)`. Establish `hK : 0 ≤ ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)` using `mul_nonneg hK0 (Real.rpow_nonneg (hHb C).le _)`. Establish `key : ∀ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ ≤ (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ …`. Introduce `δ hδ`.

Take `⟨t, ht, hjt, hlt⟩` from `hTm δ hδ`. Take `⟨hΔ0, hΔle⟩` from `hDel t ht`. Rewrite `hΔ0`, `hΔle` using `[hjt, hlt]`. Establish `hS` using `hS1 δ`. Establish `hS0 : 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ` using `by linarith`.

Establish `e1 : k2Del D j δ ^ (-(((D.R.k : ℝ) - 1 - j) / 2)) * k2Del D j δ ^ ((D.R.k : ℝ) / 2) = k2Del D j δ ^ (((j : ℝ) + 1) / 2)`. Rewrite using `[← Real.rpow_add hΔ0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(Cs * D.R.k)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (Cp * D.R.k) = k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k)`.

Rewrite using `[← Real.rpow_add (by linarith)]; congr 1; ring`. Establish `b1 : k2Del D j δ ^ (((j : ℝ) + 1) / 2) ≤ Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_natCast (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ) 2, ← Real.rpow_mul hS0]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `b2 : k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k) ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ)))`. Rewrite using `[← Real.rpow_add (by linarith)]`. Apply `Real.rpow_le_rpow_of_exponent_le hS` to reduce the goal to its premises.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hCs hk]`. Combine the equalities or inequalities in the displayed calculation. Unfold `k2a k2e`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * k2Del D j δ ^ (((j : ℝ) + 1) / 2) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k) …`.

Use `_ ≤ ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * (Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ( …`. Use `_ = (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ …`. Use `_ ≤ (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ …`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem label_sum {large₂ : SizeData₂ D} {Y : Full X} {u : D.what₂.Word} {CH Cs C Ch Cp Cc : ℝ}
    (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (hCs : Cp + 4 ≤ Cs)
    (hDel : ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.rS)
    (hcos : ∀ T : Finset (ℕ → D.host.E), (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
      ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)))
    (T : Finset (ℕ → D.host.E)) (hTm : ∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) :
    ∑ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ ≤ k2A1 large₂ C Ch Cc j := by
  have hH : H1C large₂ CH = large₂.sc.b ^ (CH * (D.R.m : ℝ)) := rfl
  rw [hH] at hDel hcos
  have hHb : ∀ c, 0 < Hb large₂.sc.b c D.R.m D.R.f := fun c => by unfold Hb Scale.b; positivity
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hrk : D.R.rS + 3 ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    unfold Ranks.rS
    omega
  have hrkR : (D.R.rS : ℝ) + 3 ≤ D.R.k := by exact_mod_cast hrk
  have hjr : (j : ℝ) ≤ D.R.rS := by exact_mod_cast (Finset.mem_Icc.1 hj).2
  have hS1 : ∀ δ, 1 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := by
    intro δ
    unfold k2S
    refine Finset.prod_induction _ (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
      le_rfl fun τ _ => ?_
    unfold k2sg
    exact (Finset.le_fold_max 1).2 (Or.inl le_rfl)
  have hK0 : 0 ≤ ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg hC hk) _) (Real.rpow_nonneg (hHb C).le _))
      (Real.rpow_nonneg (hHb Ch).le _)
  have hK : 0 ≤ ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) := mul_nonneg hK0 (Real.rpow_nonneg (hHb C).le _)
  have key : ∀ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ ≤
      (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) := by
    intro δ hδ
    obtain ⟨t, ht, hjt, hlt⟩ := hTm δ hδ
    obtain ⟨hΔ0, hΔle⟩ := hDel t ht
    rw [hjt, hlt] at hΔ0 hΔle
    have hS := hS1 δ
    have hS0 : 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := by linarith
    have e1 : k2Del D j δ ^ (-(((D.R.k : ℝ) - 1 - j) / 2)) * k2Del D j δ ^ ((D.R.k : ℝ) / 2) =
        k2Del D j δ ^ (((j : ℝ) + 1) / 2) := by
      rw [← Real.rpow_add hΔ0]; congr 1; ring
    have e2 : k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(Cs * D.R.k)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (Cp * D.R.k) = k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k) := by
      rw [← Real.rpow_add (by linarith)]; congr 1; ring
    have b1 : k2Del D j δ ^ (((j : ℝ) + 1) / 2) ≤ Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1) := by
      calc k2Del D j δ ^ (((j : ℝ) + 1) / 2) ≤ (Hb large₂.sc.b C D.R.m D.R.f * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ 2) ^ (((j : ℝ) + 1) / 2) :=
            Real.rpow_le_rpow hΔ0.le hΔle (by positivity)
        _ = Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ 2) ^ (((j : ℝ) + 1) / 2) :=
            Real.mul_rpow (hHb C).le (by positivity)
        _ = Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1) := by
            rw [← Real.rpow_natCast (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ) 2, ← Real.rpow_mul hS0]; congr 2; push_cast; ring
    have b2 : k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k) ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) := by
      rw [← Real.rpow_add (by linarith)]
      apply Real.rpow_le_rpow_of_exponent_le hS
      nlinarith [mul_le_mul_of_nonneg_right hCs hk]
    calc k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ
        = ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * (k2Del D j δ ^ (-(((D.R.k : ℝ) - 1 - j) / 2)) * k2Del D j δ ^ ((D.R.k : ℝ) / 2)) *
            (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(Cs * D.R.k)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (Cp * D.R.k)) := by
          unfold k2a k2e; ring
      _ = ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * k2Del D j δ ^ (((j : ℝ) + 1) / 2) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k) := by rw [e1, e2]
      _ ≤ ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * (Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b1 hK0) (Real.rpow_nonneg hS0 _)
      _ = (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) *
            (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k)) := by ring
      _ ≤ (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) :=
          mul_le_mul_of_nonneg_left b2 hK
  calc ∑ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ
      ≤ ∑ δ ∈ T, (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) :=
        Finset.sum_le_sum key
    _ = (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * ∑ δ ∈ T, k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)) :=
        mul_le_mul_of_nonneg_left (hcos T hTm) hK
    _ = k2A1 large₂ C Ch Cc j := by unfold k2A1; ring

/- English proof (translation)
Establish `hHb : ∀ c, 0 < Hb large₂.sc.b c D.R.m D.R.f` using `fun c => by unfold Hb Scale.b; positivity`. Establish `hk : (0 : ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`. Establish `hSpos : ∀ j δ, 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ`. Introduce `j δ`. Unfold `k2S`.

Use `Finset.prod_nonneg fun τ _ => ?_` and prove the remaining obligations. Unfold `k2sg`. Conclude with `le_trans zero_le_one ((Finset.le_fold_max 1).2 (Or.inl le_rfl))`. Establish `hA0 : ∀ j δ, (∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) → 0 ≤ k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ`. Introduce and unpack `j δ ⟨t, ht, rfl, rfl⟩`.

Establish `hΔ` using `(hDel t ht).1`. Unfold `k2a k2e`. Conclude with `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg hC hk) _) (Real.rpow_nonneg hΔ.le _)) (Real.rpow_nonneg (hHb C).le _)) (Real.rpow_nonneg (hSpos _ _) _)) (mul_nonneg (mul_nonneg (Real.rpow_nonneg hΔ.le _) (Real.rpow_nonneg (hHb Ch).le _)) (Real.rpow_no …`. Establish `hT1 : ∀ δ ∈ S.image (fun p => labT p.1), ∃ t ∈ relSet Y u, jT t = j' ∧ labT t = δ`. Introduce `δ hδ`.

Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 hδ`. Conclude with `⟨p.1, (hS p hp).1.1, (hS p hp).2.1, rfl⟩`. Establish `hT2 : ∀ δ ∈ S.image (fun p => labT p.2), ∃ t ∈ relSet Y u, jT t = j'' ∧ labT t = δ`. Introduce `δ hδ`. Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 hδ`.

Conclude with `⟨p.2, (hS p hp).1.2.1, (hS p hp).2.2, rfl⟩`. Establish `hmap : ∀ p ∈ S, (labT p.1, labT p.2) ∈ S.image (fun p => labT p.1) ×ˢ S.image (fun p => labT p.2)` using `fun p hp => Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩`. Establish `hL1` using `label_sum hC hCh hCs hDel j' hj' (hcos j' hj') _ hT1`. Establish `hL2` using `label_sum hC hCh hCs hDel j'' hj'' (hcos j'' hj'') _ hT2`. Establish `hs1` using `Finset.sum_nonneg fun δ hδ => hA0 _ _ (hT1 δ hδ)`.

Establish `hs2` using `Finset.sum_nonneg fun δ hδ => hA0 _ _ (hT2 δ hδ)`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hmap]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun l _ => hType j' hj' j'' hj'' l.1 l.2 _ fun p hp => ?_` and prove the remaining obligations. Take `⟨hpS, hpl⟩` from `Finset.mem_filter.1 hp`.

Take `⟨h1, h2, h3⟩` from `hS p hpS`. Conclude with `⟨h1, h2, h3, congrArg Prod.fst hpl, congrArg Prod.snd hpl⟩`. Use `_ = dpiC X u * massC Y u * ((∑ δ ∈ S.image (fun p => labT p.1), k2a large₂ CH Cs C j' δ * k2e large₂ CH Ch Cp j' δ) * (∑ δ ∈ S.image (fun p => labT p.2), k2a large₂ CH Cs C j'' δ * k2e large₂ CH Ch Cp j'' δ)) := by`. Rewrite using `[← Finset.mul_sum, Finset.sum_product, Finset.sum_mul_sum]`. Use `_ ≤ dpiC X u * massC Y u * (k2A1 large₂ C Ch Cc j' * k2A1 large₂ C Ch Cc j'') := mul_le_mul_of_nonneg_left (mul_le_mul hL1 hL2 hs2 (hs1.trans hL1)) hK`.
-/
theorem rank_bound {large₂ : SizeData₂ D} {Y : Full X} {u : D.what₂.Word} {CH Cs C Ch Cp Cc : ℝ}
    (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (hCs : Cp + 4 ≤ Cs) (hK : 0 ≤ dpiC X u * massC Y u)
    (hType : TypeAt large₂ Y u CH Cs C Ch Cp)
    (hDel : ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2)
    (hcos : ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E),
      (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
      ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)))
    (j' : ℕ) (hj' : j' ∈ Finset.Icc 1 D.R.rS) (j'' : ℕ) (hj'' : j'' ∈ Finset.Icc 1 D.R.rS)
    (S : Finset (GTu Y u × GTu Y u))
    (hS : ∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'') :
    ∑ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤
      dpiC X u * massC Y u * (k2A1 large₂ C Ch Cc j' * k2A1 large₂ C Ch Cc j'') := by
  have hHb : ∀ c, 0 < Hb large₂.sc.b c D.R.m D.R.f := fun c => by unfold Hb Scale.b; positivity
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hSpos : ∀ j δ, 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := by
    intro j δ
    unfold k2S
    refine Finset.prod_nonneg fun τ _ => ?_
    unfold k2sg
    exact le_trans zero_le_one ((Finset.le_fold_max 1).2 (Or.inl le_rfl))
  have hA0 : ∀ j δ, (∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
      0 ≤ k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ := by
    rintro j δ ⟨t, ht, rfl, rfl⟩
    have hΔ := (hDel t ht).1
    unfold k2a k2e
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg hC hk) _)
      (Real.rpow_nonneg hΔ.le _)) (Real.rpow_nonneg (hHb C).le _)) (Real.rpow_nonneg (hSpos _ _) _))
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hΔ.le _) (Real.rpow_nonneg (hHb Ch).le _))
        (Real.rpow_nonneg (hSpos _ _) _))
  have hT1 : ∀ δ ∈ S.image (fun p => labT p.1), ∃ t ∈ relSet Y u, jT t = j' ∧ labT t = δ := by
    intro δ hδ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hδ
    exact ⟨p.1, (hS p hp).1.1, (hS p hp).2.1, rfl⟩
  have hT2 : ∀ δ ∈ S.image (fun p => labT p.2), ∃ t ∈ relSet Y u, jT t = j'' ∧ labT t = δ := by
    intro δ hδ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hδ
    exact ⟨p.2, (hS p hp).1.2.1, (hS p hp).2.2, rfl⟩
  have hmap : ∀ p ∈ S, (labT p.1, labT p.2) ∈
      S.image (fun p => labT p.1) ×ˢ S.image (fun p => labT p.2) := fun p hp =>
    Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hL1 := label_sum hC hCh hCs hDel j' hj' (hcos j' hj') _ hT1
  have hL2 := label_sum hC hCh hCs hDel j'' hj'' (hcos j'' hj'') _ hT2
  have hs1 := Finset.sum_nonneg fun δ hδ => hA0 _ _ (hT1 δ hδ)
  have hs2 := Finset.sum_nonneg fun δ hδ => hA0 _ _ (hT2 δ hδ)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc _ ≤ ∑ l ∈ S.image (fun p => labT p.1) ×ˢ S.image (fun p => labT p.2),
        dpiC X u * massC Y u * ((k2a large₂ CH Cs C j' l.1 * k2e large₂ CH Ch Cp j' l.1) *
          (k2a large₂ CH Cs C j'' l.2 * k2e large₂ CH Ch Cp j'' l.2)) := by
        refine Finset.sum_le_sum fun l _ => hType j' hj' j'' hj'' l.1 l.2 _ fun p hp => ?_
        obtain ⟨hpS, hpl⟩ := Finset.mem_filter.1 hp
        obtain ⟨h1, h2, h3⟩ := hS p hpS
        exact ⟨h1, h2, h3, congrArg Prod.fst hpl, congrArg Prod.snd hpl⟩
    _ = dpiC X u * massC Y u *
          ((∑ δ ∈ S.image (fun p => labT p.1), k2a large₂ CH Cs C j' δ * k2e large₂ CH Ch Cp j' δ) *
           (∑ δ ∈ S.image (fun p => labT p.2), k2a large₂ CH Cs C j'' δ * k2e large₂ CH Ch Cp j'' δ)) := by
        rw [← Finset.mul_sum, Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ dpiC X u * massC Y u * (k2A1 large₂ C Ch Cc j' * k2A1 large₂ C Ch Cc j'') :=
        mul_le_mul_of_nonneg_left (mul_le_mul hL1 hL2 hs2 (hs1.trans hL1)) hK

/- English proof (translation)
Establish `hne : ∀ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≠ 0 → p.1.relevant ∧ p.2.relevant`. Introduce `p hp hF`. Assume the negation of the conclusion as `h`. Apply `hF` to reduce the goal to its premises. Break down `not_and_or.1 h with h1 | h1` into its components or cases.

Rewrite using `[hIrr _ (hS p hp).1 h1, norm_zero, zero_mul]`. Rewrite using `[hIrr _ (hS p hp).2.1 h1, norm_zero, mul_zero]`. Establish `hmap : ∀ p ∈ S.filter (fun p => p.1.relevant ∧ p.2.relevant), (jT p.1, jT p.2) ∈ Finset.Icc 1 D.R.rS ×ˢ Finset.Icc 1 D.R.rS`. Introduce `p hp`. Take `⟨hpS, h1, h2⟩` from `Finset.mem_filter.1 hp`.

Establish `r1 : p.1 ∈ relSet Y u` using `Set.mem_inter (hS p hpS).1 h1`. Establish `r2 : p.2 ∈ relSet Y u` using `Set.mem_inter (hS p hpS).2.1 h2`. Apply the tactic sequence `refine Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hJ _ r1, ?_⟩, Finset.mem_Icc.2 ⟨hJ _ r2, ?_⟩⟩ <;>`. Conclude with `Nat.sub_le _ _`. Rewrite using `[← Finset.sum_filter_of_ne hne, ← Finset.sum_fiberwise_of_maps_to hmap]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun l hl => rank_bound hC hCh hCs hK hType hDel hcos l.1 (Finset.mem_product.1 hl).1 l.2 (Finset.mem_product.1 hl).2 _ fun p hp => ?_` and prove the remaining obligations. Take `⟨hpF, hpl⟩` from `Finset.mem_filter.1 hp`. Take `⟨hpS, h1, h2⟩` from `Finset.mem_filter.1 hpF`. Conclude with `⟨⟨Set.mem_inter (hS p hpS).1 h1, Set.mem_inter (hS p hpS).2.1 h2, (hS p hpS).2.2⟩, congrArg Prod.fst hpl, congrArg Prod.snd hpl⟩`.

Use `_ = dpiC X u * massC Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by`. Rewrite using `[← Finset.mul_sum, Finset.sum_product, sq, Finset.sum_mul_sum]`.
-/
theorem fin_bound {large₂ : SizeData₂ D} {Y : Full X} {u : D.what₂.Word} {CH Cs C Ch Cp Cc : ℝ}
    (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (hCs : Cp + 4 ≤ Cs) (hK : 0 ≤ dpiC X u * massC Y u)
    (hIrr : ∀ t ∈ (Y.tO u u).degSet, ¬ t.relevant → (Y.tO u u).vec t = 0)
    (hJ : ∀ t ∈ relSet Y u, 1 ≤ jT t)
    (hType : TypeAt large₂ Y u CH Cs C Ch Cp)
    (hDel : ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2)
    (hcos : ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E),
      (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
      ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)))
    (S : Finset (GTu Y u × GTu Y u)) (hS : ∀ p ∈ S, p ∈ (Y.tO u u).allPairs (Y.tO u u).degSet) :
    ∑ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤
      dpiC X u * massC Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
  have hne : ∀ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≠ 0 →
      p.1.relevant ∧ p.2.relevant := by
    intro p hp hF
    by_contra h
    apply hF
    rcases not_and_or.1 h with h1 | h1
    · rw [hIrr _ (hS p hp).1 h1, norm_zero, zero_mul]
    · rw [hIrr _ (hS p hp).2.1 h1, norm_zero, mul_zero]
  have hmap : ∀ p ∈ S.filter (fun p => p.1.relevant ∧ p.2.relevant),
      (jT p.1, jT p.2) ∈ Finset.Icc 1 D.R.rS ×ˢ Finset.Icc 1 D.R.rS := by
    intro p hp
    obtain ⟨hpS, h1, h2⟩ := Finset.mem_filter.1 hp
    have r1 : p.1 ∈ relSet Y u := Set.mem_inter (hS p hpS).1 h1
    have r2 : p.2 ∈ relSet Y u := Set.mem_inter (hS p hpS).2.1 h2
    refine Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hJ _ r1, ?_⟩, Finset.mem_Icc.2 ⟨hJ _ r2, ?_⟩⟩ <;>
      exact Nat.sub_le _ _
  rw [← Finset.sum_filter_of_ne hne, ← Finset.sum_fiberwise_of_maps_to hmap]
  calc _ ≤ ∑ l ∈ Finset.Icc 1 D.R.rS ×ˢ Finset.Icc 1 D.R.rS,
        dpiC X u * massC Y u * (k2A1 large₂ C Ch Cc l.1 * k2A1 large₂ C Ch Cc l.2) := by
        refine Finset.sum_le_sum fun l hl => rank_bound hC hCh hCs hK hType hDel hcos l.1
          (Finset.mem_product.1 hl).1 l.2 (Finset.mem_product.1 hl).2 _ fun p hp => ?_
        obtain ⟨hpF, hpl⟩ := Finset.mem_filter.1 hp
        obtain ⟨hpS, h1, h2⟩ := Finset.mem_filter.1 hpF
        exact ⟨⟨Set.mem_inter (hS p hpS).1 h1, Set.mem_inter (hS p hpS).2.1 h2, (hS p hpS).2.2⟩,
          congrArg Prod.fst hpl, congrArg Prod.snd hpl⟩
    _ = dpiC X u * massC Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_product, sq, Finset.sum_mul_sum]

/- English proof (translation)
Introduce `Cg cb Cw cT CT C0`. Take `⟨CH, Ch, Cp, hCH, hCh, hCp, hT⟩` from `hTy Cg cb Cw cT CT C0`. Take `⟨Ct₀, hT2⟩` from `hT (Cp + 4) le_rfl`. Take `⟨Cd₀, hD2⟩` from `hDl Cg cb Cw cT CT C0 CH hCH`. Use `set C := max (max Ct₀ Cd₀) 0 with hCdef`.

Establish `hC0 : 0 ≤ C` using `le_max_right _ _`. Take `⟨C'₁, Cl₁, hT3⟩` from `hT2 C (le_trans (le_max_left _ _) (le_max_left _ _))`. Take `⟨C'₂, Cl₂, hD3⟩` from `hD2 C (le_trans (le_max_right _ _) (le_max_left _ _))`. Take `⟨Cc, hCc, C'₃, Cl₃, hC3⟩` from `hCo Cg cb Cw cT CT C0 CH hCH`. Take `⟨C'₄, Cl₄, hP4⟩` from `hPg Cg cb Cw cT CT C0`.

Use `⟨max (max C'₁ C'₂) (max C'₃ C'₄), max (max (max Cl₁ Cl₂) (max Cl₃ Cl₄)) (k2C0 (k2Cf C Ch Cc)), fun C' Cl h1 h2 D large₂ X Y u hH hTie => ?_⟩` and prove the remaining obligations. Establish `a1 : C'₁ ≤ C'` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1`. Establish `a2 : C'₂ ≤ C'` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h1`. Establish `a3 : C'₃ ≤ C'` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h1`. Establish `a4 : C'₄ ≤ C'` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h1`.

Establish `b1 : Cl₁ ≤ Cl` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) h2`. Establish `b2 : Cl₂ ≤ Cl` using `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) h2`. Establish `b3 : Cl₃ ≤ Cl` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) h2`. Establish `b4 : Cl₄ ≤ Cl` using `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) h2`. Establish `b5 : k2C0 (k2Cf C Ch Cc) ≤ Cl` using `le_trans (le_max_right _ _) h2`.

Establish `tAt` using `hT3 C' Cl a1 b1 D large₂ X Y u hH hTie`. Establish `dAt` using `hD3 C' Cl a2 b2 D large₂ X Y u hH hTie`. Establish `cAt` using `hC3 C' Cl a3 b3 D large₂ X Y u hH hTie`. Establish `pg` using `hP4 C' Cl a4 b4 D large₂ X Y hH`. Take `⟨hΓ, hdim⟩` from `hDim D X Y u hTie`.

Establish `hJ` using `hJP Cg cb Cw cT CT C0 C' Cl D large₂ X Y u hH hTie`. Take `⟨hL, -, -, -, hWd, -⟩` from `hTie`. Establish `hF` using `hFE D X Y u u`. Establish `hI` using `hOI D X Y u u (hFold D X Y u hL hWd) (hFold D X Y u hL hWd) hF`. Establish `hIrr` using `hIV D X Y u hF hI`.

Establish `hdpi : 0 ≤ dpiC X u` using `Nat.cast_nonneg _`. Establish `hmass : 0 ≤ massC Y u` using `Finset.sum_nonneg fun Λ _ => by unfold wRow; positivity`. Establish `hK : 0 ≤ dpiC X u * massC Y u` using `mul_nonneg hdpi hmass`. Use `set B := dpiC X u * massC Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 with hB`. Use `set g : GTu Y u × GTu Y u → ℝ := ((Y.tO u u).allPairs (Y.tO u u).degSet).indicator (fun p => ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖) with hg`.

Establish `hg0 : ∀ p, 0 ≤ g p` using `fun p => Set.indicator_nonneg (fun p _ => by positivity) p`. Establish `hfin : ∀ s : Finset (GTu Y u × GTu Y u), ∑ p ∈ s, g p ≤ B`. Introduce `s`. Establish `: ∑ p ∈ s, g p = ∑ p ∈ s.filter (fun p => p ∈ (Y.tO u u).allPairs (Y.tO u u).degSet), ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖`. Rewrite using `[Finset.sum_filter]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `fin_bound hC0 hCh (le_refl _) hK hIrr hJ tAt dAt cAt _ (fun p hp => (Finset.mem_filter.1 hp).2)`. Establish `hsum : Summable g` using `summable_of_sum_le hg0 hfin`. Establish `htsum : Formalism.L2.SG.RowsOther.ampSum (Y.tO u u) ((Y.tO u u).allPairs (Y.tO u u).degSet) ≤ B` using `tsum_le_of_sum_le' (mul_nonneg hK (sq_nonneg _)) hfin`.

Use `⟨hsum, ?_⟩` and prove the remaining obligations. Establish `hPg0 : 0 ≤ Formalism.L2.SG.RowsConc.PgC Y` using `Finset.prod_nonneg fun v _ => by positivity`. Establish `hdu : 0 ≤ Formalism.L2.SG.RowsConc.duC X Y u` using `Nat.cast_nonneg _`. Establish `hCf : 1 ≤ k2Cf C Ch Cc` using `by unfold k2Cf; nlinarith [sq_nonneg C, sq_nonneg Ch, sq_nonneg Cc]`. Establish `hk : k2C0 (k2Cf C Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k`.

Establish `hL0 : 0 ≤ large₂.sc.L`. Rewrite using `[← log_scale_eq_L]; exact Real.log_nonneg (by linarith [two_le_scale_b large₂ (D := D)])`. Establish `hm6 : 0 ≤ (D.R.m : ℝ) ^ 6 * large₂.sc.L` using `mul_nonneg (by positivity) hL0`. Use `hH.2.1` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.

Establish `hA : (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 ≤ k2B D large₂ (k2Cf C Ch Cc)`. Unfold `k2B`. Conclude with `pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => kloostermanTermA_nonneg large₂ hC0 hCh hCc j) (Finset.sum_le_sum fun j hj => rank_contribution_le large₂ hC0 j hj) 2`. Establish `hclose` using `final_bound_closes D large₂ (k2Cf C Ch Cc) hCf _ hdu hk`. Establish `hGB : (Y.tO u u).Gam1 * B ≤ Formalism.L2.SG.RowsConc.duC X Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2`.

Establish `e : (Y.tO u u).Gam1 * B = ((Y.tO u u).Gam1 * massC Y u * dpiC X u) * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2`. Rewrite using `[hB]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_le_mul_of_nonneg_right hdim (sq_nonneg _)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem pairsDegCutC_of_cut (hFold : FoldOKC) (hFE : FundExistsC) (hOI : OOIntAllC)
    (hIV : IrrVecC) (hJP : JPosC) (hTy : TypeC) (hDl : DelC) (hCo : CosetsC) (hDim : DimFormC) (hPg : PgLeC) :
    Formalism.L2.SG.RowsConc.PairsDegCutC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨CH, Ch, Cp, hCH, hCh, hCp, hT⟩ := hTy Cg cb Cw cT CT C0
  obtain ⟨Ct₀, hT2⟩ := hT (Cp + 4) le_rfl
  obtain ⟨Cd₀, hD2⟩ := hDl Cg cb Cw cT CT C0 CH hCH
  set C := max (max Ct₀ Cd₀) 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  obtain ⟨C'₁, Cl₁, hT3⟩ := hT2 C (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨C'₂, Cl₂, hD3⟩ := hD2 C (le_trans (le_max_right _ _) (le_max_left _ _))
  obtain ⟨Cc, hCc, C'₃, Cl₃, hC3⟩ := hCo Cg cb Cw cT CT C0 CH hCH
  obtain ⟨C'₄, Cl₄, hP4⟩ := hPg Cg cb Cw cT CT C0
  refine ⟨max (max C'₁ C'₂) (max C'₃ C'₄), max (max (max Cl₁ Cl₂) (max Cl₃ Cl₄)) (k2C0 (k2Cf C Ch Cc)),
    fun C' Cl h1 h2 D large₂ X Y u hH hTie => ?_⟩
  have a1 : C'₁ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
  have a2 : C'₂ ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h1
  have a3 : C'₃ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h1
  have a4 : C'₄ ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h1
  have b1 : Cl₁ ≤ Cl := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) h2
  have b2 : Cl₂ ≤ Cl := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) h2
  have b3 : Cl₃ ≤ Cl := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) h2
  have b4 : Cl₄ ≤ Cl := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) h2
  have b5 : k2C0 (k2Cf C Ch Cc) ≤ Cl := le_trans (le_max_right _ _) h2
  have tAt := hT3 C' Cl a1 b1 D large₂ X Y u hH hTie
  have dAt := hD3 C' Cl a2 b2 D large₂ X Y u hH hTie
  have cAt := hC3 C' Cl a3 b3 D large₂ X Y u hH hTie
  have pg := hP4 C' Cl a4 b4 D large₂ X Y hH
  obtain ⟨hΓ, hdim⟩ := hDim D X Y u hTie
  have hJ := hJP Cg cb Cw cT CT C0 C' Cl D large₂ X Y u hH hTie
  obtain ⟨hL, -, -, -, hWd, -⟩ := hTie
  have hF := hFE D X Y u u
  have hI := hOI D X Y u u (hFold D X Y u hL hWd) (hFold D X Y u hL hWd) hF
  have hIrr := hIV D X Y u hF hI
  have hdpi : 0 ≤ dpiC X u := Nat.cast_nonneg _
  have hmass : 0 ≤ massC Y u := Finset.sum_nonneg fun Λ _ => by unfold wRow; positivity
  have hK : 0 ≤ dpiC X u * massC Y u := mul_nonneg hdpi hmass
  set B := dpiC X u * massC Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 with hB
  set g : GTu Y u × GTu Y u → ℝ := ((Y.tO u u).allPairs (Y.tO u u).degSet).indicator
    (fun p => ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖) with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => Set.indicator_nonneg (fun p _ => by positivity) p
  have hfin : ∀ s : Finset (GTu Y u × GTu Y u), ∑ p ∈ s, g p ≤ B := by
    intro s
    have : ∑ p ∈ s, g p = ∑ p ∈ s.filter (fun p => p ∈ (Y.tO u u).allPairs (Y.tO u u).degSet),
        ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ := by
      rw [Finset.sum_filter]
      rfl
    rw [this]
    exact fin_bound hC0 hCh (le_refl _) hK hIrr hJ tAt dAt cAt _ (fun p hp => (Finset.mem_filter.1 hp).2)
  have hsum : Summable g := summable_of_sum_le hg0 hfin
  have htsum : Formalism.L2.SG.RowsOther.ampSum (Y.tO u u) ((Y.tO u u).allPairs (Y.tO u u).degSet) ≤ B :=
    tsum_le_of_sum_le' (mul_nonneg hK (sq_nonneg _)) hfin
  refine ⟨hsum, ?_⟩
  have hPg0 : 0 ≤ Formalism.L2.SG.RowsConc.PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hdu : 0 ≤ Formalism.L2.SG.RowsConc.duC X Y u := Nat.cast_nonneg _
  have hCf : 1 ≤ k2Cf C Ch Cc := by unfold k2Cf; nlinarith [sq_nonneg C, sq_nonneg Ch, sq_nonneg Cc]
  have hk : k2C0 (k2Cf C Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k := by
    have hL0 : 0 ≤ large₂.sc.L := by
      rw [← log_scale_eq_L]; exact Real.log_nonneg (by linarith [two_le_scale_b large₂ (D := D)])
    have hm6 : 0 ≤ (D.R.m : ℝ) ^ 6 * large₂.sc.L := mul_nonneg (by positivity) hL0
    have := hH.2.1
    calc k2C0 (k2Cf C Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L = k2C0 (k2Cf C Ch Cc) * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) := by ring
      _ ≤ Cl * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) := mul_le_mul_of_nonneg_right b5 hm6
      _ = Cl * (D.R.m : ℝ) ^ 6 * large₂.sc.L := by ring
      _ ≤ _ := this
  have hA : (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 ≤ k2B D large₂ (k2Cf C Ch Cc) := by
    unfold k2B
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => kloostermanTermA_nonneg large₂ hC0 hCh hCc j)
      (Finset.sum_le_sum fun j hj => rank_contribution_le large₂ hC0 j hj) 2
  have hclose := final_bound_closes D large₂ (k2Cf C Ch Cc) hCf _ hdu hk
  have hGB : (Y.tO u u).Gam1 * B ≤
      Formalism.L2.SG.RowsConc.duC X Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
    have e : (Y.tO u u).Gam1 * B =
        ((Y.tO u u).Gam1 * massC Y u * dpiC X u) * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
      rw [hB]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hdim (sq_nonneg _)
  calc Formalism.L2.SG.RowsConc.PgC Y * ((Y.tO u u).Gam1 *
        Formalism.L2.SG.RowsOther.ampSum (Y.tO u u) ((Y.tO u u).allPairs (Y.tO u u).degSet))
      ≤ Formalism.L2.SG.RowsConc.PgC Y * ((Y.tO u u).Gam1 * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htsum hΓ) hPg0
    _ ≤ Formalism.L2.SG.RowsConc.PgC Y *
        (Formalism.L2.SG.RowsConc.duC X Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2) :=
        mul_le_mul_of_nonneg_left hGB hPg0
    _ ≤ 2 * (Formalism.L2.SG.RowsConc.duC X Y u * k2B D large₂ (k2Cf C Ch Cc)) :=
        mul_le_mul pg (mul_le_mul_of_nonneg_left hA hdu) (mul_nonneg hdu (sq_nonneg _)) (by norm_num)
    _ = 2 * Formalism.L2.SG.RowsConc.duC X Y u * k2B D large₂ (k2Cf C Ch Cc) := by ring
    _ ≤ _ := hclose

end Asm

end Formalism.L2.SG.KappaOffDiagonal
