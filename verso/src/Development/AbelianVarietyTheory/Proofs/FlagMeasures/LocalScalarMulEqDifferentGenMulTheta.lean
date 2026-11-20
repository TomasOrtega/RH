import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

/- English proof (translation)
Introduce `D X Y u u' _ _ w F00 F'0 FP _ _ _ G c t₀ ρ U U' _`. Establish `hg : gS D ≠ 0` using `by show D.host.g 0 * D.host.g 1 ≠ 0`. Conclude with `Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero`. Use `⟨hg, fun p => ?_⟩` and prove the remaining obligations. Establish `hE : ((gS D : ℕ) : D.host.E) ≠ 0` using `Nat.cast_ne_zero.mpr hg`.

Use `haveI : Nontrivial (D.s.atP p).Ep := Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)`. Set `cp : (D.s.atP p).Fp` to `(G.c p).val`. Establish `hc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep cp = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) * (D.s.atP p).ιE (uP p : D.host.E)` using `c.c_eq p`. Establish `hu : ((uP p : ℚ) : D.host.E) * ((gS D : ℕ) : D.host.E) = ((gpart p : ℕ) : D.host.E)`. Rewrite using `[uP, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, div_mul_cancel₀ _ hE]`.

Establish `h1 : cp * ((gS D : ℕ) : (D.s.atP p).Fp) = (Y.δ p) * ((gpart p : ℕ) : (D.s.atP p).Fp)`. Apply `(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, map_natCast, map_natCast, hc, mul_assoc]`. Use `congr 1`. Rewrite using `[← map_natCast (D.s.atP p).ιE, ← map_natCast (D.s.atP p).ιE, ← map_mul, hu]`.

Establish `h2 : ((G.S p).th : (D.s.atP p).Fp) = ((gpart p : ℕ) : (D.s.atP p).Fp)`. Establish `hA` using `(Y.agree p).2.2.2.2.2`. Establish `hs` using `D.s_split p`. Establish `wc` using `c.c p`. Apply the tactic sequence `rcases hM : (Y.M p).split with _ | g <;> rcases hD : (D.s.atP p).split with _ | sg`.

Establish `hgg : (G.S p).gg = false` using `wc.gg_none hM`. Establish `hn : Loc.resChar p ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ)`. Rewrite using `[← hs, hD]`. Simplify using the standard rewrite rules. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn`.

Establish `hgp : gpart p = 1` using `by unfold gpart; rw [if_neg hn.1, if_neg hn.2]`. Rewrite using `[Frames.th, hgg, hgp]`. Conclude with `(if_neg (by decide)).trans Nat.cast_one.symm`. Simplify using `[hM, hD] at hA`. Simplify using `[hM, hD] at hA`.

Establish `hgs` using `wc.gg_some g hM`. Simplify using `only [hM, hD] at hA`. Establish `hn : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)`. Rewrite using `[← hs, hD]`. Simplify using the standard rewrite rules.

Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hn`. Establish `hq` using `sg.q_eq`. Establish `hgp : gpart p = Loc.resChar p`. Unfold `gpart`. Break down `hn with h | h` into its components or cases.

Rewrite using `[if_pos h, h]`. Distinguish the cases in `h0 : Loc.resChar p = D.host.g 0`. Rewrite using `[if_pos h0, h0]`. Rewrite using `[if_neg h0, if_pos h, h]`. Simplify using `only [Frames.th, hgs.1, if_true, hgs.2, hA.2, hgp]`.

Conclude with `hq`. Conclude with `h1.trans (congrArg (Y.δ p * ·) h2.symm)`.
-/
theorem GCoord.c_mul_gS_eq_delta_theta : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → gS D ≠ 0 ∧ ∀ p, (G.c p : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) * (gS D : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) = (show ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp from Y.δ p) * (G.S p).th := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ _ G c t₀ ρ U U' _
  have hg : gS D ≠ 0 := by
    show D.host.g 0 * D.host.g 1 ≠ 0
    exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  refine ⟨hg, fun p => ?_⟩

  have hE : ((gS D : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr hg
  haveI : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  let cp : (D.s.atP p).Fp := (G.c p).val
  have hc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep cp =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) * (D.s.atP p).ιE (uP p : D.host.E) := c.c_eq p
  have hu : ((uP p : ℚ) : D.host.E) * ((gS D : ℕ) : D.host.E) = ((gpart p : ℕ) : D.host.E) := by
    rw [uP, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, div_mul_cancel₀ _ hE]
  have h1 : cp * ((gS D : ℕ) : (D.s.atP p).Fp) = (Y.δ p) * ((gpart p : ℕ) : (D.s.atP p).Fp) := by
    apply (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective
    rw [map_mul, map_mul, map_natCast, map_natCast, hc, mul_assoc]
    congr 1
    rw [← map_natCast (D.s.atP p).ιE, ← map_natCast (D.s.atP p).ιE, ← map_mul, hu]

  have h2 : ((G.S p).th : (D.s.atP p).Fp) = ((gpart p : ℕ) : (D.s.atP p).Fp) := by
    have hA := (Y.agree p).2.2.2.2.2
    have hs := D.s_split p
    have wc := c.c p
    rcases hM : (Y.M p).split with _ | g <;> rcases hD : (D.s.atP p).split with _ | sg
    ·
      have hgg : (G.S p).gg = false := wc.gg_none hM
      have hn : Loc.resChar p ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
        rw [← hs, hD]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have hgp : gpart p = 1 := by unfold gpart; rw [if_neg hn.1, if_neg hn.2]
      rw [Frames.th, hgg, hgp]
      exact (if_neg (by decide)).trans Nat.cast_one.symm
    · simp [hM, hD] at hA
    · simp [hM, hD] at hA
    · have hgs := wc.gg_some g hM
      simp only [hM, hD] at hA
      have hn : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
        rw [← hs, hD]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      have hq := sg.q_eq
      have hgp : gpart p = Loc.resChar p := by
        unfold gpart
        rcases hn with h | h
        · rw [if_pos h, h]
        · by_cases h0 : Loc.resChar p = D.host.g 0
          · rw [if_pos h0, h0]
          · rw [if_neg h0, if_pos h, h]
      simp only [Frames.th, hgs.1, if_true, hgs.2, hA.2, hgp]
      exact hq
  exact h1.trans (congrArg (Y.δ p * ·) h2.symm)

end GlobalTheory.HL
