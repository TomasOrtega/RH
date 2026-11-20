import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusOldformTraceToGammaZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OldformTraceToGammaOneEqHeckeUlLevelRaisingStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OldformLevelRaisingSlashSlashNebentypusStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusSlashOldformLevelRaisingMatrixStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusSlashIntDiagTwoMatrixLevelRaiseStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlEqNebentypusOldformTraceSubDiagStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspidalAtAllCuspsSL2SlashIntMatrixStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormIsCuspidalAtAllCuspsSL2Statement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFormGammaOneOfNebentypusCuspidalStatement

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

/- English proof (translation)
Introduce `N l k hN hl hlN hk χ f hf`. Establish `hN0 : 0 < N` using `by omega`. Establish `hl0 : 0 < l` using `hl.pos`. Take `⟨u, v, huv⟩ : IsCoprime (l : ℤ) (N : ℤ)` from `Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN)`. Establish `h : (l : ℤ) * u - N * (-v) = 1` using `by linear_combination huv`.

Use `haveI : NeZero N := ⟨hN0.ne'⟩`. Use `haveI : NeZero l := ⟨hl0.ne'⟩`. Use `haveI : (Lev N l).FiniteIndex := by unfold Lev; infer_instance`. Use `set W := wOld N l (-v) u with hW`. Use `set D := dg (l : ℤ) 1 with hD`.

Establish `hWdet : 0 < W.det`. Rewrite using `[hW, wOld, Matrix.det_fin_two_of]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hDdet : 0 < D.det`. Rewrite using `[hD, dg, Matrix.det_fin_two_of]`.

Simplify using `using hl0`. Use `set F : ℍ → ℂ := ⇑f with hFdef`. Establish `hF : ChiInv (k : ℤ) N (N * l) χ F` using `hf`. Establish `cF : CuspAll (k : ℤ) F` using `GlobalTheory.T.cuspForm_isCuspidalAtAllCuspsSL2 (Lev N l) k f`. Use `set G := F ∣[(k : ℤ)] toGL W with hGdef`.

Establish `hG : ChiInv (k : ℤ) N (N * l) χ G` using `GlobalTheory.T.nebentypus_slash_oldformLevelRaisingMatrix N l k (-v) u h χ F hl0 hF`. Establish `cG : CuspAll (k : ℤ) G` using `GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix k W F hWdet cF`. Establish `cTr : ∀ H, CuspAll (k : ℤ) H → CuspAll (k : ℤ) (trOld k N l (-v) u h H)`. Introduce `H hH`. Unfold `trOld`.

Use `cuspAll_add hH ?_` and prove the remaining obligations. Proceed by induction on `(Finset.range l) using Finset.induction_on with`. Consider the case `empty => simpa using cuspAll_smul 0 hH`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj]`.

Use `cuspAll_add ?_ ih` and prove the remaining obligations. Rewrite using `[slash_SL_eq]`. Conclude with `GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix k _ H (by simp [mat]) hH`. Use `set A := trOld k N l (-v) u h F with hAdef`. Use `set B := trOld k N l (-v) u h G with hBdef`.

Establish `hA : ChiInv (k : ℤ) N N χ A` using `GlobalTheory.T.nebentypus_oldformTraceToGammaOne N l k (-v) u h χ F hN0 hl hF`. Establish `hB : ChiInv (k : ℤ) N N χ B` using `GlobalTheory.T.nebentypus_oldformTraceToGammaOne N l k (-v) u h χ G hN0 hl hG`. Establish `cA : CuspAll (k : ℤ) A` using `cTr F cF`. Establish `cB : CuspAll (k : ℤ) B` using `cTr G cG`. Use `set C := B ∣[(k : ℤ)] toGL D with hCdef`.

Establish `hC : ChiInv (k : ℤ) N (N * l) χ C` using `GlobalTheory.T.nebentypus_slash_intDiagTwoMatrix_levelRaise N l k χ B hl0 hB`. Establish `cC : CuspAll (k : ℤ) C` using `GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix k D B hDdet cB`. Establish `hTC : ChiInv (k : ℤ) N N χ (trOld k N l (-v) u h C)` using `GlobalTheory.T.nebentypus_oldformTraceToGammaOne N l k (-v) u h χ C hN0 hl hC`. Establish `cTC : CuspAll (k : ℤ) (trOld k N l (-v) u h C)` using `cTr C cC`. Use `set c₁ : ℂ := χ (l : ZMod N) with hc₁`.

Use `set p : ℂ := (l : ℂ) ^ ((k : ℤ) - 2) with hp`. Establish `h₁ : ChiInv (k : ℤ) N N χ (c₁ ^ 2 • trOld k N l (-v) u h C + (-(c₁ * p)) • A)` using `chiInv_add (chiInv_smul _ hTC) (chiInv_smul _ hA)`. Take `⟨f₁, hf₁⟩` from `GlobalTheory.T.exists_cuspForm_gammaOne_of_nebentypus_cuspidal N k χ (c₁ ^ 2 • trOld k N l (-v) u h C + (-(c₁ * p)) • A) hN0 (cuspAll_add (cuspAll_smul _ cTC) (cuspAll_smul _ cA)) h₁`. Take `⟨f₂, hf₂⟩` from `GlobalTheory.T.exists_cuspForm_gammaOne_of_nebentypus_cuspidal N k χ (-(c₁ ^ 2) • B) hN0 (cuspAll_smul _ cB) (chiInv_smul _ hB)`. Use `⟨f₁, f₂, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hf₁]`. Conclude with `h₁ γ hγ`. Rewrite using `[hf₂]`. Conclude with `chiInv_smul _ hB γ hγ`. Rewrite using `[hf₁, hf₂]`.

Establish `e1` using `GlobalTheory.T.oldformTraceToGammaOne_eq_heckeUl_levelRaising N l k (-v) u h F hl0`. Establish `e2` using `GlobalTheory.T.oldformTraceToGammaOne_eq_heckeUl_levelRaising N l k (-v) u h G hl0`. Establish `e3` using `GlobalTheory.T.oldformLevelRaising_slash_slash_nebentypus N l k (-v) u h χ F hl0 hF`. Establish `e4` using `GlobalTheory.T.heckeUl_eq_nebentypus_oldformTrace_sub_diag N l k (-v) u h χ B hl0 hB`. Rewrite `e1` using `[← hAdef, ← hGdef]`.

Rewrite `e2` using `[← hBdef, e3]`. Rewrite `e4` using `[← hCdef]`. Establish `cb : c₁ * χ (u : ZMod N) = 1`. Rewrite using `[hc₁, ← map_mul]`. Establish `h2` using `congrArg (Int.cast : ℤ → ZMod N) h`.

Move the coercions through the operations in `at h2`. Rewrite `h2` using `[ZMod.natCast_self]`. Rewrite using `[show ((l : ZMod N) * (u : ZMod N)) = 1 by linear_combination h2, map_one]`. Establish `hl' : (l : ℂ) ≠ 0` using `by exact_mod_cast hl0.ne'`. Establish `pp : p * (l : ℂ) ^ (2 - (k : ℤ)) = 1`.

Rewrite using `[hp, ← zpow_add₀ hl']`. Simplify using the standard rewrite rules. Establish `hUG : UlF k l G = p • (A - F)`. Rewrite using `[e1, add_sub_cancel_left, smul_smul, pp, one_smul]`. Establish `hUF : UlF k l F = c₁ • (B - G)`.

Establish `key : c₁ * (l : ℂ) ^ (2 - (k : ℤ)) * ((l : ℂ) ^ ((k : ℤ) - 2) * χ (u : ZMod N)) = 1`. Rewrite using `[← hp]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e2, add_sub_cancel_left, ulF_smul k l hl0, smul_smul, smul_smul, key, one_smul]`. Establish `hpk : (l : ℂ) ^ (k - 2) = p`.

Rewrite using `[hp, show ((k : ℤ) - 2) = ((k - 2 : ℕ) : ℤ) by omega, zpow_natCast]`. Rewrite using `[hpk, hUF, ulF_smul k l hl0, ulF_sub k l hl0, e4, hUG, smul_slash_toGL k D hDdet, ← hCdef]`. Use function extensionality and compare the values at `τ`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.HeckeFamilyMatrices.ulSq_old : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Lev N l) (k : ℤ)),
  (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 (N * l) → ⇑f ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f) →
  ∃ f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ),
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₁ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₁) ∧
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₂ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₂) ∧
    UlF (k : ℤ) l (UlF (k : ℤ) l ⇑f) - (χ l * (l : ℂ) ^ (k - 2)) • ⇑f = ⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1) := by
  intro N l k hN hl hlN hk χ f hf
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  obtain ⟨u, v, huv⟩ : IsCoprime (l : ℤ) (N : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN)
  have h : (l : ℤ) * u - N * (-v) = 1 := by linear_combination huv
  haveI : NeZero N := ⟨hN0.ne'⟩
  haveI : NeZero l := ⟨hl0.ne'⟩
  haveI : (Lev N l).FiniteIndex := by unfold Lev; infer_instance
  set W := wOld N l (-v) u with hW
  set D := dg (l : ℤ) 1 with hD
  have hWdet : 0 < W.det := by
    rw [hW, wOld, Matrix.det_fin_two_of]; nlinarith
  have hDdet : 0 < D.det := by
    rw [hD, dg, Matrix.det_fin_two_of]; simpa using hl0
  set F : ℍ → ℂ := ⇑f with hFdef
  have hF : ChiInv (k : ℤ) N (N * l) χ F := hf
  have cF : CuspAll (k : ℤ) F := GlobalTheory.T.cuspForm_isCuspidalAtAllCuspsSL2 (Lev N l) k f
  set G := F ∣[(k : ℤ)] toGL W with hGdef
  have hG : ChiInv (k : ℤ) N (N * l) χ G := GlobalTheory.T.nebentypus_slash_oldformLevelRaisingMatrix N l k (-v) u h χ F hl0 hF
  have cG : CuspAll (k : ℤ) G := GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix k W F hWdet cF
  have cTr : ∀ H, CuspAll (k : ℤ) H → CuspAll (k : ℤ) (trOld k N l (-v) u h H) := by
    intro H hH
    unfold trOld
    refine cuspAll_add hH ?_
    induction (Finset.range l) using Finset.induction_on with
    | empty => simpa using cuspAll_smul 0 hH
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      refine cuspAll_add ?_ ih
      rw [slash_SL_eq]
      exact GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix k _ H (by simp [mat]) hH
  set A := trOld k N l (-v) u h F with hAdef
  set B := trOld k N l (-v) u h G with hBdef
  have hA : ChiInv (k : ℤ) N N χ A := GlobalTheory.T.nebentypus_oldformTraceToGammaOne N l k (-v) u h χ F hN0 hl hF
  have hB : ChiInv (k : ℤ) N N χ B := GlobalTheory.T.nebentypus_oldformTraceToGammaOne N l k (-v) u h χ G hN0 hl hG
  have cA : CuspAll (k : ℤ) A := cTr F cF
  have cB : CuspAll (k : ℤ) B := cTr G cG
  set C := B ∣[(k : ℤ)] toGL D with hCdef
  have hC : ChiInv (k : ℤ) N (N * l) χ C := GlobalTheory.T.nebentypus_slash_intDiagTwoMatrix_levelRaise N l k χ B hl0 hB
  have cC : CuspAll (k : ℤ) C := GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix k D B hDdet cB
  have hTC : ChiInv (k : ℤ) N N χ (trOld k N l (-v) u h C) := GlobalTheory.T.nebentypus_oldformTraceToGammaOne N l k (-v) u h χ C hN0 hl hC
  have cTC : CuspAll (k : ℤ) (trOld k N l (-v) u h C) := cTr C cC
  set c₁ : ℂ := χ (l : ZMod N) with hc₁
  set p : ℂ := (l : ℂ) ^ ((k : ℤ) - 2) with hp
  have h₁ : ChiInv (k : ℤ) N N χ (c₁ ^ 2 • trOld k N l (-v) u h C + (-(c₁ * p)) • A) :=
    chiInv_add (chiInv_smul _ hTC) (chiInv_smul _ hA)
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.T.exists_cuspForm_gammaOne_of_nebentypus_cuspidal N k χ (c₁ ^ 2 • trOld k N l (-v) u h C + (-(c₁ * p)) • A) hN0
    (cuspAll_add (cuspAll_smul _ cTC) (cuspAll_smul _ cA)) h₁
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.T.exists_cuspForm_gammaOne_of_nebentypus_cuspidal N k χ (-(c₁ ^ 2) • B) hN0 (cuspAll_smul _ cB) (chiInv_smul _ hB)
  refine ⟨f₁, f₂, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩
  · rw [hf₁]; exact h₁ γ hγ
  · rw [hf₂]; exact chiInv_smul _ hB γ hγ
  rw [hf₁, hf₂]
  have e1 := GlobalTheory.T.oldformTraceToGammaOne_eq_heckeUl_levelRaising N l k (-v) u h F hl0
  have e2 := GlobalTheory.T.oldformTraceToGammaOne_eq_heckeUl_levelRaising N l k (-v) u h G hl0
  have e3 := GlobalTheory.T.oldformLevelRaising_slash_slash_nebentypus N l k (-v) u h χ F hl0 hF
  have e4 := GlobalTheory.T.heckeUl_eq_nebentypus_oldformTrace_sub_diag N l k (-v) u h χ B hl0 hB
  rw [← hAdef, ← hGdef] at e1
  rw [← hBdef, e3] at e2
  rw [← hCdef] at e4
  have cb : c₁ * χ (u : ZMod N) = 1 := by
    rw [hc₁, ← map_mul]
    have h2 := congrArg (Int.cast : ℤ → ZMod N) h
    push_cast at h2
    rw [ZMod.natCast_self] at h2
    rw [show ((l : ZMod N) * (u : ZMod N)) = 1 by linear_combination h2, map_one]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
  have pp : p * (l : ℂ) ^ (2 - (k : ℤ)) = 1 := by
    rw [hp, ← zpow_add₀ hl']; simp
  have hUG : UlF k l G = p • (A - F) := by
    rw [e1, add_sub_cancel_left, smul_smul, pp, one_smul]
  have hUF : UlF k l F = c₁ • (B - G) := by
    have key : c₁ * (l : ℂ) ^ (2 - (k : ℤ)) * ((l : ℂ) ^ ((k : ℤ) - 2) * χ (u : ZMod N)) = 1 := by
      rw [← hp]
      calc c₁ * (l : ℂ) ^ (2 - (k : ℤ)) * (p * χ (u : ZMod N))
          = (p * (l : ℂ) ^ (2 - (k : ℤ))) * (c₁ * χ (u : ZMod N)) := by ring
        _ = 1 := by rw [pp, cb, one_mul]
    rw [e2, add_sub_cancel_left, ulF_smul k l hl0, smul_smul, smul_smul, key, one_smul]
  have hpk : (l : ℂ) ^ (k - 2) = p := by
    rw [hp, show ((k : ℤ) - 2) = ((k - 2 : ℕ) : ℤ) by omega, zpow_natCast]
  rw [hpk, hUF, ulF_smul k l hl0, ulF_sub k l hl0, e4, hUG, smul_slash_toGL k D hDdet, ← hCdef]
  funext τ
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
