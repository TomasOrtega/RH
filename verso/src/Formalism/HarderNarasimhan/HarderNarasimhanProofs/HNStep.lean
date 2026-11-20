import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax

open Module Submodule

noncomputable section

namespace Formalism.HN

/- English proof (translation)
Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `AddSubgroup.mem_map.mp hx`. Conclude with `AddSubgroup.mem_map.mpr ⟨y, h hy, rfl⟩`.
-/
theorem imageLattice_mono {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E) {A B : Submodule R V}
    (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hx
  exact AddSubgroup.mem_map.mpr ⟨y, h hy, rfl⟩

universe u v w in
/- English proof (translation)
Introduce `R V E _ _ _ _ _ _ ρ L hL θ`. Take `⟨hsub, hmono, hsat_eq, -, -, hbot, -, -⟩` from `h6 R V E ρ L hL`. Take `⟨g, hg⟩ : ∃ g : Submodule R V → ℝ, ∀ N, g N = deg ρ N - θ * (rk ρ N : ℝ)` from `⟨_, fun _ => rfl⟩`. Establish `sm : ∀ A B : Submodule R V, A ≤ L → B ≤ L → g A + g B ≤ g (A ⊔ B) + g (A ⊓ B)`. Introduce `A B hA hB`.

Take `⟨hr, hd⟩` from `h1 R V E ρ L A B hL hA hB`. Establish `hr' : (rk ρ (A ⊔ B) : ℝ) + rk ρ (A ⊓ B) = rk ρ A + rk ρ B`. Conclude with `hr` after adjusting the coercions. Establish `hθ : θ * (rk ρ (A ⊔ B) : ℝ) + θ * rk ρ (A ⊓ B) = θ * rk ρ A + θ * rk ρ B`. Rewrite using `[← mul_add, ← mul_add, hr']`.

Simplify using `only [hg]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `charP : ∀ M : Submodule R V, M ≤ L → M ≠ ⊥ → (θ ≤ muMin ρ M ↔ ∀ N ≤ M, g N ≤ g M)`. Introduce `M hM hM0`. Rewrite using `[(h2 R V E ρ M (hsub M hM) hM0).2.1 θ]`.

Use `forall_congr' fun N => imp_congr_right fun _ => ?_` and prove the remaining obligations. Simplify using `only [hg, mul_sub]`. Apply the tactic sequence `constructor <;> intro h <;> linarith`. Establish `supP : ∀ A B : Submodule R V, A ≤ L → B ≤ L → (∀ N ≤ A, g N ≤ g A) → (∀ N ≤ B, g N ≤ g B) → ∀ N ≤ A ⊔ B, g N ≤ g (A ⊔ B)`. Introduce `A B hA hB pA pB N hN`.

Establish `hNL : N ≤ L` using `hN.trans (sup_le hA hB)`. Establish `e1` using `sm N A hNL hA`. Establish `e2` using `pA (N ⊓ A) inf_le_right`. Establish `e3` using `sm (N ⊔ A) B (sup_le hNL hA) hB`. Establish `e4` using `pB ((N ⊔ A) ⊓ B) inf_le_right`.

Establish `e5 : N ⊔ A ⊔ B = A ⊔ B`. Rewrite using `[sup_assoc]`. Conclude with `sup_eq_right.mpr hN`. Rewrite `e3` using `[e5]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨t, htS, htF⟩` from `h4 R V E ρ L {N | N ≤ L ∧ N ≠ ⊥ ∧ θ ≤ muMin ρ N} hL (fun N hN => hN.1)`. Establish `hFdef : hnStep ρ L θ = t.sup id` using `htF`. Establish `memS : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → θ ≤ muMin ρ N → N ≤ hnStep ρ L θ` using `fun N a b c => le_sSup (s := {N | N ≤ L ∧ N ≠ ⊥ ∧ θ ≤ muMin ρ N}) (show N ≤ L ∧ N ≠ ⊥ ∧ θ ≤ muMin ρ N from ⟨a, b, c⟩)`. Establish `PF : t.sup id ≤ L ∧ ∀ N ≤ t.sup id, g N ≤ g (t.sup id)`. Use `Finset.sup_induction (p := fun M => M ≤ L ∧ ∀ N ≤ M, g N ≤ g M) ?_ ?_ ?_` and prove the remaining obligations.

Use `⟨bot_le, fun N hN => ?_⟩` and prove the remaining obligations. Rewrite using `[le_bot_iff.mp hN]`. Introduce and unpack `A ⟨hA, pA⟩ B ⟨hB, pB⟩`. Conclude with `⟨sup_le hA hB, supP A B hA hB pA pB⟩`. Introduce `M hM`.

Establish `hM' : M ≤ L ∧ M ≠ ⊥ ∧ θ ≤ muMin ρ M` using `htS (Finset.mem_coe.mpr hM)`. Conclude with `⟨hM'.1, (charP M hM'.1 hM'.2.1).mp hM'.2.2⟩`. Rewrite `PF` using `[← hFdef]`. Take `⟨FL, PF⟩` from `PF`. Use `clear hFdef htF htS`.

Use `set F := hnStep ρ L θ with hFset`. Use `clear_value F`. Establish `rkpos_of : IsSat ρ L F → ∀ X : Submodule R V, F < X → X ≤ L → rk ρ F < rk ρ X`. Introduce `hs X hX hXL`. Break down `(hmono F X hX.le hXL).1.lt_or_eq with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd (hsat_eq F X hs hX.le hXL h.symm) hX.ne'`. Establish `Fsat : IsSat ρ L F`. Take `⟨F', hFF', hF'L, himg⟩` from `h5 R V E ρ L F hL FL`. Take `⟨hsatimg, -, hrkimg⟩` from `Formalism.F.saturProps E (zl ρ L) (zl ρ F) hL.2 (imageLattice_mono ρ FL)`.

Establish `hF'sat : IsSat ρ L F'`. Unfold `IsSat`. Rewrite using `[himg]`. Conclude with `⟨hF'L, hsatimg⟩`. Establish `hrk : rk ρ F' = rk ρ F` using `by show Formalism.F.rk (zl ρ F') = Formalism.F.rk (zl ρ F)`.

Rewrite using `[himg]`. Conclude with `hrkimg`. Distinguish the cases in `hF'0 : F' = ⊥`. Establish `hF0 : F = ⊥`. Rewrite using `[eq_bot_iff, ← hF'0]`.

Conclude with `hFF'`. Rewrite using `[hF0]`. Conclude with `hbot`. Establish `PF' : ∀ N ≤ F', g N ≤ g F'`. Introduce `M hM`.

Establish `hML : M ≤ L` using `hM.trans hF'L`. Establish `e1` using `sm M F hML FL`. Establish `e2` using `PF (M ⊓ F) inf_le_right`. Establish `hX : M ⊔ F ≤ F'` using `sup_le hM hFF'`. Establish `r1` using `(hmono F (M ⊔ F) le_sup_right (hX.trans hF'L)).1`.

Establish `r2` using `(hmono (M ⊔ F) F' hX hF'L).1`. Establish `hreq : rk ρ (M ⊔ F) = rk ρ F'` using `by omega`. Establish `d` using `(hmono (M ⊔ F) F' hX hF'L).2 hreq`. Establish `e3 : g (M ⊔ F) ≤ g F'`. Simplify using `only [hg, hreq]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmem` using `memS F' hF'L hF'0 ((charP F' hF'L hF'0).mpr PF')`. Rewrite `hF'sat` using `[le_antisymm hmem hFF']`. Conclude with `hF'sat`.

Use `⟨Fsat, fun hF0 => (charP F FL hF0).mpr PF, memS, ?_⟩` and prove the remaining obligations. Introduce `N hFN hNL`. Use `not_le.mp fun hcon => ?_` and prove the remaining obligations. Establish `rkpos` using `rkpos_of Fsat`. Establish `hFL : F ≠ L` using `(lt_of_lt_of_le hFN hNL).ne`.

Take `⟨N₀, hFN₀, hN₀sat, hmax⟩` from `h3 R V E ρ L F hL Fsat hFL`. Establish `hN₀L : N₀ ≤ L`. Unfold `IsSat at hN₀sat`. Conclude with `hN₀sat.1`. Establish `hr₀ : (rk ρ F : ℝ) < rk ρ N₀` using `by exact_mod_cast rkpos N₀ hFN₀ hN₀L`.

Establish `hr : (rk ρ F : ℝ) < rk ρ N` using `by exact_mod_cast rkpos N hFN hNL`. Establish `key` using `hmax N hFN hNL`. Establish `hμ : θ * ((rk ρ N₀ : ℝ) - rk ρ F) ≤ deg ρ N₀ - deg ρ F`. Use `not_lt.mp fun hlt => ?_` and prove the remaining obligations. Establish `a1` using `mul_lt_mul_of_pos_right hlt (sub_pos.mpr hr)`.

Establish `a2` using `mul_le_mul_of_nonneg_right hcon (sub_pos.mpr hr₀).le`. Use the polynomial consequences of the given equalities and inequalities. Establish `PN₀ : ∀ M ≤ N₀, g M ≤ g N₀`. Introduce `M hM`. Establish `hML : M ≤ L` using `hM.trans hN₀L`.

Establish `e1` using `sm M F hML FL`. Establish `e2` using `PF (M ⊓ F) inf_le_right`. Establish `hX : M ⊔ F ≤ N₀` using `sup_le hM hFN₀.le`. Establish `hXN₀ : g (M ⊔ F) ≤ g N₀`. Break down `(le_sup_right : F ≤ M ⊔ F).lt_or_eq with hlt | heq` into its components or cases.

Establish `hrX₀ : (rk ρ (M ⊔ F) : ℝ) ≤ rk ρ N₀`. Conclude with `(hmono _ _ hX hN₀L).1` after adjusting the coercions. Establish `k2` using `hmax (M ⊔ F) hlt (hX.trans hN₀L)`. Establish `hpos : 0 < (rk ρ N₀ : ℝ) - rk ρ F` using `sub_pos.mpr hr₀`. Establish `hm : ((rk ρ N₀ : ℝ) - rk ρ F) * g (M ⊔ F) ≤ ((rk ρ N₀ : ℝ) - rk ρ F) * g N₀`.

Simplify using `only [hg]`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hμ) (sub_nonneg.mpr hrX₀)]`. Conclude with `le_of_mul_le_mul_left hm hpos`. Rewrite using `[← heq]`. Simplify using `only [hg]`.

Combine the linear relations using `[mul_sub θ (rk ρ N₀ : ℝ) (rk ρ F)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN₀0 : N₀ ≠ ⊥` using `ne_bot_of_gt hFN₀`. Establish `hle` using `memS N₀ hN₀L hN₀0 ((charP N₀ hN₀L hN₀0).mpr PN₀)`. Conclude with `absurd (le_antisymm hle hFN₀.le) hFN₀.ne'`.
-/
theorem hnStep_of (h1 : DegSupermod.{u, v, w}) (h2 : MuChar.{u, v, w}) (h3 : RatioMax.{u, v, w})
    (h4 : FinSup.{u, v, w}) (h5 : SatR.{u, v, w}) (h6 : SatBasic.{u, v, w}) :
    HNStep.{u, v, w} := by
  intro R V E _ _ _ _ _ _ ρ L hL θ
  obtain ⟨hsub, hmono, hsat_eq, -, -, hbot, -, -⟩ := h6 R V E ρ L hL
  obtain ⟨g, hg⟩ : ∃ g : Submodule R V → ℝ, ∀ N, g N = deg ρ N - θ * (rk ρ N : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have sm : ∀ A B : Submodule R V, A ≤ L → B ≤ L → g A + g B ≤ g (A ⊔ B) + g (A ⊓ B) := by
    intro A B hA hB
    obtain ⟨hr, hd⟩ := h1 R V E ρ L A B hL hA hB
    have hr' : (rk ρ (A ⊔ B) : ℝ) + rk ρ (A ⊓ B) = rk ρ A + rk ρ B := by
      exact_mod_cast hr
    have hθ : θ * (rk ρ (A ⊔ B) : ℝ) + θ * rk ρ (A ⊓ B) = θ * rk ρ A + θ * rk ρ B := by
      rw [← mul_add, ← mul_add, hr']
    simp only [hg]
    linarith
  have charP : ∀ M : Submodule R V, M ≤ L → M ≠ ⊥ →
      (θ ≤ muMin ρ M ↔ ∀ N ≤ M, g N ≤ g M) := by
    intro M hM hM0
    rw [(h2 R V E ρ M (hsub M hM) hM0).2.1 θ]
    refine forall_congr' fun N => imp_congr_right fun _ => ?_
    simp only [hg, mul_sub]
    constructor <;> intro h <;> linarith
  have supP : ∀ A B : Submodule R V, A ≤ L → B ≤ L → (∀ N ≤ A, g N ≤ g A) →
      (∀ N ≤ B, g N ≤ g B) → ∀ N ≤ A ⊔ B, g N ≤ g (A ⊔ B) := by
    intro A B hA hB pA pB N hN
    have hNL : N ≤ L := hN.trans (sup_le hA hB)
    have e1 := sm N A hNL hA
    have e2 := pA (N ⊓ A) inf_le_right
    have e3 := sm (N ⊔ A) B (sup_le hNL hA) hB
    have e4 := pB ((N ⊔ A) ⊓ B) inf_le_right
    have e5 : N ⊔ A ⊔ B = A ⊔ B := by
      rw [sup_assoc]; exact sup_eq_right.mpr hN
    rw [e5] at e3
    linarith
  obtain ⟨t, htS, htF⟩ := h4 R V E ρ L {N | N ≤ L ∧ N ≠ ⊥ ∧ θ ≤ muMin ρ N} hL
    (fun N hN => hN.1)
  have hFdef : hnStep ρ L θ = t.sup id := htF
  have memS : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → θ ≤ muMin ρ N →
      N ≤ hnStep ρ L θ := fun N a b c =>
    le_sSup (s := {N | N ≤ L ∧ N ≠ ⊥ ∧ θ ≤ muMin ρ N})
      (show N ≤ L ∧ N ≠ ⊥ ∧ θ ≤ muMin ρ N from ⟨a, b, c⟩)
  have PF : t.sup id ≤ L ∧ ∀ N ≤ t.sup id, g N ≤ g (t.sup id) := by
    refine Finset.sup_induction (p := fun M => M ≤ L ∧ ∀ N ≤ M, g N ≤ g M) ?_ ?_ ?_
    · refine ⟨bot_le, fun N hN => ?_⟩
      rw [le_bot_iff.mp hN]
    · rintro A ⟨hA, pA⟩ B ⟨hB, pB⟩
      exact ⟨sup_le hA hB, supP A B hA hB pA pB⟩
    · intro M hM
      have hM' : M ≤ L ∧ M ≠ ⊥ ∧ θ ≤ muMin ρ M := htS (Finset.mem_coe.mpr hM)
      exact ⟨hM'.1, (charP M hM'.1 hM'.2.1).mp hM'.2.2⟩
  rw [← hFdef] at PF
  obtain ⟨FL, PF⟩ := PF
  clear hFdef htF htS
  set F := hnStep ρ L θ with hFset
  clear_value F
  have rkpos_of : IsSat ρ L F → ∀ X : Submodule R V, F < X → X ≤ L →
      rk ρ F < rk ρ X := by
    intro hs X hX hXL
    rcases (hmono F X hX.le hXL).1.lt_or_eq with h | h
    · exact h
    · exact absurd (hsat_eq F X hs hX.le hXL h.symm) hX.ne'
  have Fsat : IsSat ρ L F := by
    obtain ⟨F', hFF', hF'L, himg⟩ := h5 R V E ρ L F hL FL
    obtain ⟨hsatimg, -, hrkimg⟩ := Formalism.F.saturProps E (zl ρ L)
      (zl ρ F) hL.2 (imageLattice_mono ρ FL)
    have hF'sat : IsSat ρ L F' := by
      unfold IsSat
      rw [himg]
      exact ⟨hF'L, hsatimg⟩
    have hrk : rk ρ F' = rk ρ F := by
      show Formalism.F.rk (zl ρ F') = Formalism.F.rk (zl ρ F)
      rw [himg]
      exact hrkimg
    by_cases hF'0 : F' = ⊥
    · have hF0 : F = ⊥ := by
        rw [eq_bot_iff, ← hF'0]
        exact hFF'
      rw [hF0]
      exact hbot
    · have PF' : ∀ N ≤ F', g N ≤ g F' := by
        intro M hM
        have hML : M ≤ L := hM.trans hF'L
        have e1 := sm M F hML FL
        have e2 := PF (M ⊓ F) inf_le_right
        have hX : M ⊔ F ≤ F' := sup_le hM hFF'
        have r1 := (hmono F (M ⊔ F) le_sup_right (hX.trans hF'L)).1
        have r2 := (hmono (M ⊔ F) F' hX hF'L).1
        have hreq : rk ρ (M ⊔ F) = rk ρ F' := by omega
        have d := (hmono (M ⊔ F) F' hX hF'L).2 hreq
        have e3 : g (M ⊔ F) ≤ g F' := by
          simp only [hg, hreq]
          linarith
        linarith
      have hmem := memS F' hF'L hF'0 ((charP F' hF'L hF'0).mpr PF')
      rw [le_antisymm hmem hFF'] at hF'sat
      exact hF'sat
  refine ⟨Fsat, fun hF0 => (charP F FL hF0).mpr PF, memS, ?_⟩
  intro N hFN hNL
  refine not_le.mp fun hcon => ?_
  have rkpos := rkpos_of Fsat
  have hFL : F ≠ L := (lt_of_lt_of_le hFN hNL).ne
  obtain ⟨N₀, hFN₀, hN₀sat, hmax⟩ := h3 R V E ρ L F hL Fsat hFL
  have hN₀L : N₀ ≤ L := by
    unfold IsSat at hN₀sat
    exact hN₀sat.1
  have hr₀ : (rk ρ F : ℝ) < rk ρ N₀ := by exact_mod_cast rkpos N₀ hFN₀ hN₀L
  have hr : (rk ρ F : ℝ) < rk ρ N := by exact_mod_cast rkpos N hFN hNL
  have key := hmax N hFN hNL
  have hμ : θ * ((rk ρ N₀ : ℝ) - rk ρ F) ≤ deg ρ N₀ - deg ρ F := by
    refine not_lt.mp fun hlt => ?_
    have a1 := mul_lt_mul_of_pos_right hlt (sub_pos.mpr hr)
    have a2 := mul_le_mul_of_nonneg_right hcon (sub_pos.mpr hr₀).le
    nlinarith
  have PN₀ : ∀ M ≤ N₀, g M ≤ g N₀ := by
    intro M hM
    have hML : M ≤ L := hM.trans hN₀L
    have e1 := sm M F hML FL
    have e2 := PF (M ⊓ F) inf_le_right
    have hX : M ⊔ F ≤ N₀ := sup_le hM hFN₀.le
    have hXN₀ : g (M ⊔ F) ≤ g N₀ := by
      rcases (le_sup_right : F ≤ M ⊔ F).lt_or_eq with hlt | heq
      · have hrX₀ : (rk ρ (M ⊔ F) : ℝ) ≤ rk ρ N₀ := by
          exact_mod_cast (hmono _ _ hX hN₀L).1
        have k2 := hmax (M ⊔ F) hlt (hX.trans hN₀L)
        have hpos : 0 < (rk ρ N₀ : ℝ) - rk ρ F := sub_pos.mpr hr₀
        have hm : ((rk ρ N₀ : ℝ) - rk ρ F) * g (M ⊔ F) ≤
            ((rk ρ N₀ : ℝ) - rk ρ F) * g N₀ := by
          simp only [hg]
          nlinarith [mul_nonneg (sub_nonneg.mpr hμ) (sub_nonneg.mpr hrX₀)]
        exact le_of_mul_le_mul_left hm hpos
      · rw [← heq]
        simp only [hg]
        linarith [mul_sub θ (rk ρ N₀ : ℝ) (rk ρ F)]
    linarith
  have hN₀0 : N₀ ≠ ⊥ := ne_bot_of_gt hFN₀
  have hle := memS N₀ hN₀L hN₀0 ((charP N₀ hN₀L hN₀0).mpr PN₀)
  exact absurd (le_antisymm hle hFN₀.le) hFN₀.ne'

end Formalism.HN
