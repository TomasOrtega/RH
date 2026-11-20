import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDeeperLevelIffReductionsSymmetricUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableDiagonalModSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingVectorsIntegralInFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentNeOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

/- English proof (translation)
Break down `X with ⟨⟨I⟩⟩` into its components or cases. Simplify using `only at h ⊢`. Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem hT_eq_hY {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (x y : Fin (Yc D 0).rank → EAf D) : hT X h x y = hY D x y := by
  rcases X with ⟨⟨I⟩⟩
  dsimp only at h ⊢
  subst h
  rfl

/- English proof (translation)
Take `⟨β₀, h₀⟩` from `GlobalTheory.StdFrames.exists_base (Yc D 0)`. Establish `hU` using `GlobalTheory.StdFrames.unimod_of_isSD (GlobalTheory.StdFrames.isSD_one h₀)`. Establish `hF` using `flag_pair_int X h β₀ h₀ PP`. Use `set U := colMat (pairAt X h PP) with hUdef`. Use `set W := colMat (flagAt X h PP) with hWdef`.

Use `set J := GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM (Yc D 0).gram with hJ`. Establish `e1 : hY D (pairAt X h PP a) (flagAt X h PP c) = (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W) a c`. Simplify using `only [Matrix.mul_apply, Formalism.UG.hform, Formalism.UG.cT, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply, hY]`. Rewrite using `[Finset.sum_comm]`. Both sides reduce to the same expression.

Use `set A' := (β₀⁻¹).val * U with hAdef`. Use `set B' := (β₀⁻¹).val * W with hBdef`. Use `set G' := Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val with hGdef`. Establish `hU' : U = β₀.val * A'` using `by rw [hAdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Establish `hW' : W = β₀.val * B'` using `by rw [hBdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`.

Establish `hX' : Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W = Formalism.UG.cT (GlobalTheory.StdFrames.sg D) A' * G' * B'`. Rewrite using `[hGdef, hU', hW', GlobalTheory.StdFrames.cT_mul']`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e1, hX']`. Simplify using `only [Matrix.mul_apply]`.

Use `sum_mem fun j _ => mul_mem (sum_mem fun i _ => mul_mem ?_ ?_) ?_` and prove the remaining obligations. Conclude with `Formalism.UG.P.csDual_sig_mem _ (hF i a).2`. Conclude with `hU.1 i j`. Conclude with `(hF j c).1`.
-/
theorem hY_pair_flag_int {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (PP : Pl D.host.E) (a c : Fin (Yc D 0).rank) :
    hY D (pairAt X h PP a) (flagAt X h PP c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨β₀, h₀⟩ := GlobalTheory.StdFrames.exists_base (Yc D 0)
  have hU := GlobalTheory.StdFrames.unimod_of_isSD (GlobalTheory.StdFrames.isSD_one h₀)
  have hF := flag_pair_int X h β₀ h₀ PP
  set U := colMat (pairAt X h PP) with hUdef
  set W := colMat (flagAt X h PP) with hWdef
  set J := GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM (Yc D 0).gram with hJ
  have e1 : hY D (pairAt X h PP a) (flagAt X h PP c) = (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W) a c := by
    simp only [Matrix.mul_apply, Formalism.UG.hform, Formalism.UG.cT, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply, hY]
    rw [Finset.sum_comm]
    rfl
  set A' := (β₀⁻¹).val * U with hAdef
  set B' := (β₀⁻¹).val * W with hBdef
  set G' := Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val with hGdef
  have hU' : U = β₀.val * A' := by rw [hAdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hW' : W = β₀.val * B' := by rw [hBdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hX' : Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W = Formalism.UG.cT (GlobalTheory.StdFrames.sg D) A' * G' * B' := by
    rw [hGdef, hU', hW', GlobalTheory.StdFrames.cT_mul']
    simp only [Matrix.mul_assoc]
  rw [e1, hX']
  simp only [Matrix.mul_apply]
  refine sum_mem fun j _ => mul_mem (sum_mem fun i _ => mul_mem ?_ ?_) ?_
  · exact Formalism.UG.P.csDual_sig_mem _ (hF i a).2
  · exact hU.1 i j
  · exact (hF j c).1

end GlobalTheory.SeeConjChar

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R X h hL PP hPP a c`. Establish `hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal`. Take `⟨l, hl⟩` from `(hL.Pg PP).1 hPP`. Use `R.C.P.overP hl` as an intermediate fact. Rewrite using `[Nat.cast_mul]`.

Use `fin_cases l`. Conclude with `PP.asIdeal.mul_mem_right _ this`. Conclude with `PP.asIdeal.mul_mem_left _ this`. Establish `hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1`. Establish `e` using `X.n_eq`.

Rewrite `e` using `[h]`. Establish `e2` using `Formalism.L2.DIV.ranks_r_sym D`. Express the relevant statement in the definitionally equal form `(Formalism.L2.SG.InstExistsPf.instOf D).n = _`. Use linear arithmetic over natural numbers and integers. Establish `hsm : SmallAt PP (hY D (pairAt X h PP a) (flagAt X h PP c) - if a = c then sgnD D.R.rS D.R.k a else 0)`.

Distinguish the cases in `he : GlobalTheory.StdFrames.cpt PP (ewT X h) = 1`. Unfold `pairAt flagAt`. Rewrite using `[if_pos he, if_pos he]`. Conclude with `flagV_pair_table (hY D) (SmallAt PP) _ _ _ hn _ _ _ _ _ (pairTable_of_cpt_one X h PP hg he) a c`. Unfold `pairAt flagAt`.

Rewrite using `[if_neg he, if_neg he]`. Conclude with `flagV_pair_table (hY D) (SmallAt PP) _ _ _ hn _ _ _ _ _ (pairTable_rev X h PP hg he) a c`. Establish `hint` using `hY_pair_flag_int X h PP a c`. Establish `hs : (if a = c then sgnD D.R.rS D.R.k a else 0 : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E`. Unfold `sgnD`.

Use `split_ifs`. Use `exacts [neg_mem (one_mem _), one_mem _, zero_mem _]`. Establish `key : Formalism.L2.DIV.resS D.host.F PP ⟨_, hint⟩ - Formalism.L2.DIV.resS D.host.F PP ⟨_, hs⟩ = 0`. Rewrite using `[← map_sub]`. Conclude with `(GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP _).2 hsm`.

Establish `hres : Formalism.L2.DIV.resS D.host.F PP ⟨_, hs⟩ = if a = c then sgnD D.R.rS D.R.k a else 0`. Distinguish the cases in `hac : a = c`. Substitute `hac` using the available equality. Distinguish the cases in `hz : a.1 = D.R.rS + D.R.k`. Establish `e : (⟨_, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = -1` using `Subtype.ext (by simp [sgnD, hz])`.

Rewrite using `[e, map_neg, map_one]`. Simplify using `[sgnD, hz]`. Establish `e : (⟨_, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1` using `Subtype.ext (by simp [sgnD, hz])`. Rewrite using `[e, map_one]`. Simplify using `[sgnD, hz]`.

Establish `e : (⟨_, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 0` using `Subtype.ext (by simp [hac])`. Rewrite using `[e, map_zero]`. Simplify using `[hac]`. Unfold `resT`. Rewrite using `[hT_eq_hY, dif_pos hint, ← hres]`.

Conclude with `sub_eq_zero.1 key`.
-/
theorem resT_hT_pair_flag : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → ∀ PP ∈ R.Pg, ∀ a c : Fin (Yc D 0).rank, GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h (pairAt X h PP a) (flagAt X h PP c)) = if a = c then sgnD D.R.rS D.R.k a else 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R X h hL PP hPP a c
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    obtain ⟨l, hl⟩ := (hL.Pg PP).1 hPP
    have := R.C.P.overP hl
    rw [Nat.cast_mul]
    fin_cases l
    · exact PP.asIdeal.mul_mem_right _ this
    · exact PP.asIdeal.mul_mem_left _ this
  have hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
    have e := X.n_eq
    rw [h] at e
    have e2 := Formalism.L2.DIV.ranks_r_sym D
    change (Formalism.L2.SG.InstExistsPf.instOf D).n = _
    omega
  have hsm : SmallAt PP (hY D (pairAt X h PP a) (flagAt X h PP c) - if a = c then sgnD D.R.rS D.R.k a else 0) := by
    by_cases he : GlobalTheory.StdFrames.cpt PP (ewT X h) = 1
    · unfold pairAt flagAt
      rw [if_pos he, if_pos he]
      exact flagV_pair_table (hY D) (SmallAt PP) _ _ _ hn _ _ _ _ _ (pairTable_of_cpt_one X h PP hg he) a c
    · unfold pairAt flagAt
      rw [if_neg he, if_neg he]
      exact flagV_pair_table (hY D) (SmallAt PP) _ _ _ hn _ _ _ _ _ (pairTable_rev X h PP hg he) a c
  have hint := hY_pair_flag_int X h PP a c
  have hs : (if a = c then sgnD D.R.rS D.R.k a else 0 : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    unfold sgnD
    split_ifs
    exacts [neg_mem (one_mem _), one_mem _, zero_mem _]
  have key : Formalism.L2.DIV.resS D.host.F PP ⟨_, hint⟩ - Formalism.L2.DIV.resS D.host.F PP ⟨_, hs⟩ = 0 := by
    rw [← map_sub]
    exact (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP _).2 hsm
  have hres : Formalism.L2.DIV.resS D.host.F PP ⟨_, hs⟩ = if a = c then sgnD D.R.rS D.R.k a else 0 := by
    by_cases hac : a = c
    · subst hac
      by_cases hz : a.1 = D.R.rS + D.R.k
      · have e : (⟨_, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = -1 := Subtype.ext (by simp [sgnD, hz])
        rw [e, map_neg, map_one]
        simp [sgnD, hz]
      · have e : (⟨_, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 := Subtype.ext (by simp [sgnD, hz])
        rw [e, map_one]
        simp [sgnD, hz]
    · have e : (⟨_, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 0 := Subtype.ext (by simp [hac])
      rw [e, map_zero]
      simp [hac]
  unfold resT
  rw [hT_eq_hY, dif_pos hint, ← hres]
  exact sub_eq_zero.1 key

end GlobalTheory.SeeConjChar
