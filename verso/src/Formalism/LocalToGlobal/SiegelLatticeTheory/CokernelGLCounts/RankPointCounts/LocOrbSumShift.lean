import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SupportLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SmoothBigCellSectionsExist

noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbSumPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups MeasureTheory
open Formalism.L2.SG.LsDatumB
open Classical

section ShiftPf

variable {D : Formalism.BasicNotions.D7}

/- English proof (translation)
Introduce `a s t x y h1 h2 h3 h4 h5 h6 h7`. Rewrite using `[← Formalism.L2.SG.Pf.blkTop_eq δ T T' p a s t x y h1 h2 h3 h4 h5 h6 h7]`. Unfold `blkTop`. Rewrite using `[if_neg]`. Introduce and unpack `⟨hs, rfl⟩`.

Use linear arithmetic over natural numbers and integers.
-/
theorem blkMod_eq (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) :
    ∀ a s t x y, 1 ≤ a → a - 1 ≤ x → a - 1 ≤ y → x + y + 1 = 2 * (a - 1) + s → x ≤ D.R.rS → y ≤ D.R.rS →
      ¬ (x = D.R.rS ∧ y = D.R.rS) →
        blkMod δ T T' p a s t = Formalism.L2.SG.Pf.rho δ p x * Formalism.L2.SG.Pf.rho δ p y * Formalism.L2.SG.Pf.kap p *
          (D.s.atP p).ιE t := by
  intro a s t x y h1 h2 h3 h4 h5 h6 h7
  rw [← Formalism.L2.SG.Pf.blkTop_eq δ T T' p a s t x y h1 h2 h3 h4 h5 h6 h7]
  unfold blkTop
  rw [if_neg]
  rintro ⟨hs, rfl⟩
  omega

/- English proof (translation)
Establish `hn' : ¬ ((x : ℕ) = D.R.rS ∧ (y : ℕ) = D.R.rS)` using `fun h => hn ⟨Fin.ext (by rw [Fin.val_last]; exact h.1), Fin.ext (by rw [Fin.val_last]; exact h.2)⟩`. Establish `e` using `Formalism.L2.SG.Pf.ptEntry_scale (D.s.atP p).ιE (blkMod δ T T' p) (Formalism.L2.SG.Pf.rho δ p) (Formalism.L2.SG.Pf.kap p) D.R.rS (blkMod_eq δ T T' p) w.1 1 x y le_rfl (by have := x.isLt; omega) (by have := y.isLt; omega) (by simpa using hn')`. Simplify using `only [Nat.sub_self, zero_add] at e`. Apply the tactic sequence `show ptEntry (mapBlocks (blkMod δ T T' p) 1 w.1) x y = _`. Rewrite using `[e]`.

Both sides reduce to the same expression.
-/
theorem modMat_off (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (x y : Fin (D.R.rS + 1)) (hn : ¬ (x = Fin.last D.R.rS ∧ y = Fin.last D.R.rS)) :
    modMat δ T T' p w x y = Formalism.L2.SG.Pf.rho δ p x * Formalism.L2.SG.Pf.rho δ p y * Formalism.L2.SG.Pf.kap p *
      (D.s.atP p).ιE (ptMat w x y) := by
  have hn' : ¬ ((x : ℕ) = D.R.rS ∧ (y : ℕ) = D.R.rS) := fun h =>
    hn ⟨Fin.ext (by rw [Fin.val_last]; exact h.1), Fin.ext (by rw [Fin.val_last]; exact h.2)⟩
  have e := Formalism.L2.SG.Pf.ptEntry_scale (D.s.atP p).ιE (blkMod δ T T' p) (Formalism.L2.SG.Pf.rho δ p)
    (Formalism.L2.SG.Pf.kap p) D.R.rS (blkMod_eq δ T T' p) w.1 1
    x y le_rfl (by have := x.isLt; omega) (by have := y.isLt; omega) (by simpa using hn')
  simp only [Nat.sub_self, zero_add] at e
  show ptEntry (mapBlocks (blkMod δ T T' p) 1 w.1) x y = _
  rw [e]
  rfl

/- English proof (translation)
Apply the tactic sequence `show ptEntry (mapBlocks (blkMod δ T T' p) 1 w.1) D.R.rS D.R.rS = _`. Establish `hs' : ((mapBlocks (blkMod δ T T' p) 1 l0).map Prod.snd).sum = D.R.rS`. Rewrite using `[Formalism.L2.SG.Pf.mapBlocks_snd, hs]`. Rewrite using `[hb, Formalism.L2.SG.Pf.mapBlocks_append, Formalism.L2.SG.Pf.ptEntry_append_ge _ _ _ _ hs'.le, if_pos hs'.le, hs', Nat.sub_self, hs, add_comm]`. Simplify using `[mapBlocks, ptEntry]`.
-/
theorem modMat_last (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (l0 : List (D.host.E × ℕ)) (t : D.host.E) (hb : w.1 = l0 ++ [(t, 1)]) (hs : (l0.map Prod.snd).sum = D.R.rS) :
    modMat δ T T' p w (Fin.last _) (Fin.last _) = blkMod δ T T' p (D.R.rS + 1) 1 t := by
  show ptEntry (mapBlocks (blkMod δ T T' p) 1 w.1) D.R.rS D.R.rS = _
  have hs' : ((mapBlocks (blkMod δ T T' p) 1 l0).map Prod.snd).sum = D.R.rS := by
    rw [Formalism.L2.SG.Pf.mapBlocks_snd, hs]
  rw [hb, Formalism.L2.SG.Pf.mapBlocks_append, Formalism.L2.SG.Pf.ptEntry_append_ge _ _ _ _ hs'.le, if_pos hs'.le, hs',
    Nat.sub_self, hs, add_comm]
  simp [mapBlocks, ptEntry]

/- English proof (translation)
Establish `hs' : ((mapBlocks f 1 l0).map Prod.snd).sum = (l0.map Prod.snd).sum`. Rewrite using `[Formalism.L2.SG.Pf.mapBlocks_snd]`. Establish `hle : ((mapBlocks f 1 l0).map Prod.snd).sum ≤ D.R.rS` using `by rw [hs']; omega`. Rewrite using `[hb, Formalism.L2.SG.Pf.mapBlocks_append, Formalism.L2.SG.Pf.ptEntry_append_ge _ _ _ _ hle, if_pos hle, hs']`. Simplify using `only [mapBlocks, ptEntry]`.

Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem corner_zero {B : Type} [Zero B] (f : ℕ → ℕ → D.host.E → B) (w : Point D.host.E (D.R.rS + 1))
    (l0 : List (D.host.E × ℕ)) (t : D.host.E) (s : ℕ) (hb : w.1 = l0 ++ [(t, s)])
    (hs : (l0.map Prod.snd).sum + s = D.R.rS + 1) (h2 : 2 ≤ s) :
    ptEntry (mapBlocks f 1 w.1) D.R.rS D.R.rS = 0 := by
  have hs' : ((mapBlocks f 1 l0).map Prod.snd).sum = (l0.map Prod.snd).sum := by
    rw [Formalism.L2.SG.Pf.mapBlocks_snd]
  have hle : ((mapBlocks f 1 l0).map Prod.snd).sum ≤ D.R.rS := by rw [hs']; omega
  rw [hb, Formalism.L2.SG.Pf.mapBlocks_append, Formalism.L2.SG.Pf.ptEntry_append_ge _ _ _ _ hle, if_pos hle, hs']
  simp only [mapBlocks, ptEntry]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Establish `hne : w.1 ≠ []`. Introduce `h`. Use `w.2.2` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`.

Take `⟨l0, b, hb⟩ : ∃ l0 b, w.1 = l0 ++ [b]` from `⟨w.1.dropLast, w.1.getLast hne, (List.dropLast_append_getLast hne).symm⟩`. Take `⟨t, s⟩` from `b`. Establish `hmem` using `w.2.1 (t, s) (by rw [hb]; simp)`. Establish `hsum : (l0.map Prod.snd).sum + s = D.R.rS + 1`. Use `w.2.2` as an intermediate fact.

Rewrite `this` using `[hb]`. Simplify using `using this`. Use `⟨l0, t, s, hb, hsum, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Establish `hs1 : s = 1` using `by have := hmem.2; omega`.

Substitute `hs1` using the available equality. Use `Formalism.L2.SG.Pf.dmin_snoc w l0 t hb (by omega)` as an intermediate fact. Rewrite `this` using `[h0, zero_mul]`. Conclude with `Formalism.MainNotions.BridgeLemma.Dmin_top_ne w this`.
-/
theorem last_big (w : Point D.host.E (D.R.rS + 1)) (h0 : Dmin w D.R.rS = 0) :
    ∃ l0 t s, w.1 = l0 ++ [(t, s)] ∧ (l0.map Prod.snd).sum + s = D.R.rS + 1 ∧ 2 ≤ s := by
  have hne : w.1 ≠ [] := by
    intro h
    have := w.2.2
    rw [h] at this
    simp at this
  obtain ⟨l0, b, hb⟩ : ∃ l0 b, w.1 = l0 ++ [b] :=
    ⟨w.1.dropLast, w.1.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  obtain ⟨t, s⟩ := b
  have hmem := w.2.1 (t, s) (by rw [hb]; simp)
  have hsum : (l0.map Prod.snd).sum + s = D.R.rS + 1 := by
    have := w.2.2
    rw [hb] at this
    simpa using this
  refine ⟨l0, t, s, hb, hsum, ?_⟩
  by_contra hlt
  have hs1 : s = 1 := by have := hmem.2; omega
  subst hs1
  have := Formalism.L2.SG.Pf.dmin_snoc w l0 t hb (by omega)
  rw [h0, zero_mul] at this
  exact Formalism.MainNotions.BridgeLemma.Dmin_top_ne w this

/- English proof (translation)
Introduce `a ha`. Use extensionality with `x y`. Rewrite using `[Matrix.add_apply]`. Distinguish the cases in `hc : x = Fin.last D.R.rS ∧ y = Fin.last D.R.rS`. Take `⟨rfl, rfl⟩` from `hc`.

Establish `hsh : shM δ T T' p w (Fin.last _) (Fin.last _) = cornerSh δ T T' p w` using `by simp [shM]`. Rewrite using `[hsh]`. Distinguish the cases in `h0 : Dmin w D.R.rS = 0`. Establish `hc0 : cornerSh δ T T' p w = 0` using `by unfold cornerSh; rw [if_pos h0]`. Rewrite using `[hc0, add_zero]`.

Take `⟨l0, t, s, hb, hs, h2⟩` from `last_big w h0`. Establish `e1` using `corner_zero (blkTop δ T T' p) w l0 t s hb hs h2`. Establish `e2` using `corner_zero (blkMod δ T T' p) w l0 t s hb hs h2`. Apply the tactic sequence `show Loc.ptEntryL a.blocks D.R.rS D.R.rS = ptEntry (mapBlocks (blkMod δ T T' p) 1 w.1) D.R.rS D.R.rS`. Rewrite using `[Formalism.L2.SG.Pf.ptEntryL_eq, Formalism.L2.SG.Pf.modPt_blocks δ T T' p w a ha, e1, e2]`.

Take `⟨l0, t, hb, hs⟩` from `Formalism.L2.SG.Pf.last_one w h0`. Rewrite using `[Formalism.L2.SG.Pf.amat_last δ T T' p w a ha l0 t hb hs, modMat_last δ T T' p w l0 t hb hs]`. Unfold `cornerSh`. Rewrite using `[if_neg h0, Formalism.L2.SG.Pf.zeta_snoc w h0 l0 t hb hs]`. Unfold `blkTop`.

Rewrite using `[if_pos ⟨by omega, rfl⟩]`. Rewrite using `[Formalism.L2.SG.Pf.amat_eq δ T T' p w a ha x y hc, modMat_off δ T T' p w x y hc]`. Establish `: shM δ T T' p w x y = 0` using `by simp only [shM, Matrix.of_apply]; rw [if_neg hc]`. Rewrite using `[this, add_zero]`.
-/
theorem modShift_holds (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) :
    ModShift δ T T' p w := by
  intro a ha
  ext x y
  rw [Matrix.add_apply]
  by_cases hc : x = Fin.last D.R.rS ∧ y = Fin.last D.R.rS
  · obtain ⟨rfl, rfl⟩ := hc
    have hsh : shM δ T T' p w (Fin.last _) (Fin.last _) = cornerSh δ T T' p w := by simp [shM]
    rw [hsh]
    by_cases h0 : Dmin w D.R.rS = 0
    · have hc0 : cornerSh δ T T' p w = 0 := by unfold cornerSh; rw [if_pos h0]
      rw [hc0, add_zero]
      obtain ⟨l0, t, s, hb, hs, h2⟩ := last_big w h0
      have e1 := corner_zero (blkTop δ T T' p) w l0 t s hb hs h2
      have e2 := corner_zero (blkMod δ T T' p) w l0 t s hb hs h2
      show Loc.ptEntryL a.blocks D.R.rS D.R.rS = ptEntry (mapBlocks (blkMod δ T T' p) 1 w.1) D.R.rS D.R.rS
      rw [Formalism.L2.SG.Pf.ptEntryL_eq, Formalism.L2.SG.Pf.modPt_blocks δ T T' p w a ha, e1, e2]
    · obtain ⟨l0, t, hb, hs⟩ := Formalism.L2.SG.Pf.last_one w h0
      rw [Formalism.L2.SG.Pf.amat_last δ T T' p w a ha l0 t hb hs, modMat_last δ T T' p w l0 t hb hs]
      unfold cornerSh
      rw [if_neg h0, Formalism.L2.SG.Pf.zeta_snoc w h0 l0 t hb hs]
      unfold blkTop
      rw [if_pos ⟨by omega, rfl⟩]
  · rw [Formalism.L2.SG.Pf.amat_eq δ T T' p w a ha x y hc, modMat_off δ T T' p w x y hc]
    have : shM δ T T' p w x y = 0 := by simp only [shM, Matrix.of_apply]; rw [if_neg hc]
    rw [this, add_zero]

end ShiftPf

end Formalism.L2.SG.Pf.LocOrbSumPf
