import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeChoiceClausesOfWeakCharacterisationAtFaceAl
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FourMulQLeCondN

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun.SetAtModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

/- English proof (translation)
Establish `h1` using `p.charW.tup.mu_off`. Establish `h2` using `p.charW.tup.mu_used`. Establish `: (Set.univ : Set p.P.T) ⊆ insert p.P.A3.A.μ0 (p.R.mu '' (p.R.twPl : Set _))` using `fun t _ => by`. Break down `h2 t with h | ⟨w, rfl⟩` into its components or cases. Conclude with `Or.inl h`.

Distinguish the cases in `hw : w ∈ p.R.twPl`. Conclude with `Or.inr ⟨w, hw, rfl⟩`. Conclude with `Or.inl (h1 w hw)`. Conclude with `Set.finite_univ_iff.1 ((((p.R.twPl).finite_toSet.image _).insert _).subset this)`.
-/
theorem finite_tup (p : PtAt ex Csz) : Finite p.P.T := by
  classical
  have h1 := p.charW.tup.mu_off
  have h2 := p.charW.tup.mu_used
  have : (Set.univ : Set p.P.T) ⊆ insert p.P.A3.A.μ0 (p.R.mu '' (p.R.twPl : Set _)) := fun t _ => by
    rcases h2 t with h | ⟨w, rfl⟩
    · exact Or.inl h
    · by_cases hw : w ∈ p.R.twPl
      · exact Or.inr ⟨w, hw, rfl⟩
      · exact Or.inl (h1 w hw)
  exact Set.finite_univ_iff.1 ((((p.R.twPl).finite_toSet.image _).insert _).subset this)

set_option maxHeartbeats 1600000 in

/- English proof (translation)
The claim follows from `hs eser := he host := p.host hF := p.hF core := (GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D _ _ _ _ _ _ p.R p.F p.charW hp.exAt).1 mu_off := p.charW.tup.mu_off mu_used := p.charW.tup.mu_used mu_ne := p.charW.tup.mu_ne mu_conj := p.charW.tup.mu_ …`.
-/
theorem setting_of_size (p : PtAt ex Csz) (hp : p.Rows) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) (he : GlobalTheory.GLq.ESerTie D) :
    HidaSetting L p.R.toRealDat p.F.lv2 where
  size := hs
  eser := he
  host := p.host
  hF := p.hF
  core := (GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D _ _ _ _ _ _ p.R p.F p.charW hp.exAt).1
  mu_off := p.charW.tup.mu_off
  mu_used := p.charW.tup.mu_used
  mu_ne := p.charW.tup.mu_ne
  mu_conj := p.charW.tup.mu_conj
  mu_on := p.charW.tup.mu_on
  grp := p.charW.base.grp.record
  guard := p.qGuard
  fin := finite_tup p
  fullY := p.charW.fullY
  fullX := p.charW.fullX
  std := p.stdChar
  stdX := p.stdX
  betaX := p.betaStd.2

/- English proof (translation)
The claim follows from `h.imp fun _ _ _ a => evPt_imp a fun _ _ _ p hp b he => setting_of_size p hp b he`.
-/
theorem setAt_of_sizeAt (h : SizeAt) : SetAt :=
  h.imp fun _ _ _ a => evPt_imp a fun _ _ _ p hp b he => setting_of_size p hp b he

section Sizes

variable {D : D7} {L : SizeData₂ D}

/- English proof (translation)
Establish `key : ∀ τ i, 0 ≤ (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v i ∧ (((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v i : ℤ) : ℝ) ≤ L.Sc` using `fun τ i => by dsimp only [GlobalTheory.SignedHC.GridData.ofHCParam]`. Unfold `GlobalTheory.SignedHC.GridData.extend`. Use `split_ifs with h2`. Take `⟨h0, h1⟩` from `L.cloud_v τ ⟨i - 2, h2⟩`. Use `⟨Int.floor_nonneg.mpr (by exact_mod_cast h0), ?_⟩` and prove the remaining obligations.

Establish `hf` using `Int.floor_le ((D.hc τ).v ⟨i - 2, h2⟩)`. Establish `hf' : (((⌊(D.hc τ).v ⟨i - 2, h2⟩⌋ : ℤ) : ℚ) : ℝ) ≤ (((D.hc τ).v ⟨i - 2, h2⟩ : ℚ) : ℝ)` using `by exact_mod_cast hf`. Move the coercions through the operations in `at hf' ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨le_rfl, by simpa using L.Sc_pos.le⟩`.

Establish `h0` using `L.Sc_pos.le`. Establish `hL : cloudLen D ≤ ⌊L.Sc⌋₊`. Unfold `cloudLen`. Use `Finset.sup_le fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.le_floor_iff h0]`.

Take `⟨a0, a1⟩` from `key τ 2`. Take `⟨b0, -⟩` from `key τ D.R.k`. Generalize the expression as in `(GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 = u at *`. Generalize the expression as in `(GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k = v at *`. Establish `h : ((u - v).toNat : ℤ) ≤ u` using `by omega`.

Establish `h' : (((u - v).toNat : ℤ) : ℝ) ≤ ((u : ℤ) : ℝ)` using `by exact_mod_cast h`. Move the coercions through the operations in `at h'`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cloudLen_le (L : SizeData₂ D) : (cloudLen D : ℝ) ≤ L.Sc := by
  have key : ∀ τ i, 0 ≤ (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v i ∧
      (((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v i : ℤ) : ℝ) ≤ L.Sc := fun τ i => by
    dsimp only [GlobalTheory.SignedHC.GridData.ofHCParam]
    unfold GlobalTheory.SignedHC.GridData.extend
    split_ifs with h2
    · obtain ⟨h0, h1⟩ := L.cloud_v τ ⟨i - 2, h2⟩
      refine ⟨Int.floor_nonneg.mpr (by exact_mod_cast h0), ?_⟩
      have hf := Int.floor_le ((D.hc τ).v ⟨i - 2, h2⟩)
      have hf' : (((⌊(D.hc τ).v ⟨i - 2, h2⟩⌋ : ℤ) : ℚ) : ℝ) ≤ (((D.hc τ).v ⟨i - 2, h2⟩ : ℚ) : ℝ) := by exact_mod_cast hf
      push_cast at hf' ⊢
      linarith
    · exact ⟨le_rfl, by simpa using L.Sc_pos.le⟩
  have h0 := L.Sc_pos.le
  have hL : cloudLen D ≤ ⌊L.Sc⌋₊ := by
    unfold cloudLen
    refine Finset.sup_le fun τ _ => ?_
    rw [Nat.le_floor_iff h0]
    obtain ⟨a0, a1⟩ := key τ 2
    obtain ⟨b0, -⟩ := key τ D.R.k
    generalize (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 = u at *
    generalize (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k = v at *
    have h : ((u - v).toNat : ℤ) ≤ u := by omega
    have h' : (((u - v).toNat : ℤ) : ℝ) ≤ ((u : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  calc (cloudLen D : ℝ) ≤ (⌊L.Sc⌋₊ : ℝ) := by exact_mod_cast hL
    _ ≤ L.Sc := Nat.floor_le h0

/- English proof (translation)
Establish `h1` using `D.R.rank_add_five_le`. Establish `h2` using `D.R.three_m_lt_t`. Establish `h3` using `D.R.m_add_three_le_k`. Establish `hr : D.R.r + 5 ≤ D.R.t` using `h1`. Establish `hk : D.R.k ≤ D.R.t` using `by omega`.

Use `set t := D.R.t with ht`. Establish `hN : bigN D ≤ 5 * t ^ 2`. Unfold `bigN sLen`. Establish `: D.R.m * (t + (D.R.r + 6) + 1) ≤ t * (3 * t)` using `Nat.mul_le_mul (by omega) (by omega)`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hn : nRk D ≤ t` using `by unfold nRk; omega`. Establish `hs : sLen D ≤ 2 * t` using `by unfold sLen; omega`. Establish `t1 : (132 : ℝ) ≤ t` using `by exact_mod_cast (by omega : 132 ≤ t)`. Establish `hN' : (bigN D : ℝ) ≤ 5 * (t : ℝ) ^ 2` using `by exact_mod_cast hN`. Establish `hn' : (nRk D : ℝ) ≤ t` using `by exact_mod_cast hn`.

Establish `hs' : (sLen D : ℝ) ≤ 2 * t` using `by exact_mod_cast hs`. Establish `hm' : (D.R.m : ℝ) ≤ t` using `by exact_mod_cast (by omega : D.R.m ≤ t)`. Establish `hm1 : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (by omega : 1 ≤ D.R.m)`. Establish `a1 : (bigN D : ℝ) ^ 3 ≤ (t : ℝ) ^ 7`. Combine the equalities or inequalities in the displayed calculation.

Establish `a2 : (nRk D : ℝ) ^ 7 ≤ (t : ℝ) ^ 7` using `pow_le_pow_left₀ (by positivity) hn' 7`. Establish `a3 : (nRk D : ℝ) ^ 3 ≤ (t : ℝ) ^ 7` using `(pow_le_pow_left₀ (by positivity) hn' 3).trans (pow_le_pow_right₀ (by linarith) (by norm_num))`. Establish `a4 : 132 * (t : ℝ) ^ 3 ≤ (t : ℝ) ^ 7`. Combine the equalities or inequalities in the displayed calculation. Establish `a5 : (t : ℝ) ≤ (t : ℝ) ^ 3` using `le_self_pow₀ (by linarith) (by norm_num)`.

Establish `a6 : (t : ℝ) ^ 7 ≤ (t : ℝ) ^ 7 * B` using `le_mul_of_one_le_right (by positivity) hB`. Establish `a7 : (nRk D : ℝ) ^ 3 * Real.sqrt (cloudLen D) ≤ (t : ℝ) ^ 7 * B` using `by gcongr`. Establish `a8 : Real.sqrt D.R.m ≤ t` using `(Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩)`. Establish `a9 : (nRk D : ℝ) ^ 2 * Real.sqrt D.R.m ≤ (t : ℝ) ^ 3`. Combine the equalities or inequalities in the displayed calculation.

Unfold `gap`. Use `push_cast`. Use `max_le (max_le ((Nat.ceil_lt_add_one (by positivity)).le.trans ?_) ?_) ((Nat.ceil_lt_add_one (by positivity)).le.trans ?_)` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gap_le (D : D7) (B : ℝ) (hB : 1 ≤ B) (hc : Real.sqrt (cloudLen D) ≤ B) (hm : 44 ≤ D.R.m) :
    (gap D 1 : ℝ) ≤ 4 * (D.R.t : ℝ) ^ 7 * B := by
  have h1 := D.R.rank_add_five_le
  have h2 := D.R.three_m_lt_t
  have h3 := D.R.m_add_three_le_k
  have hr : D.R.r + 5 ≤ D.R.t := h1
  have hk : D.R.k ≤ D.R.t := by omega
  set t := D.R.t with ht
  have hN : bigN D ≤ 5 * t ^ 2 := by
    unfold bigN sLen
    have : D.R.m * (t + (D.R.r + 6) + 1) ≤ t * (3 * t) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hn : nRk D ≤ t := by unfold nRk; omega
  have hs : sLen D ≤ 2 * t := by unfold sLen; omega
  have t1 : (132 : ℝ) ≤ t := by exact_mod_cast (by omega : 132 ≤ t)
  have hN' : (bigN D : ℝ) ≤ 5 * (t : ℝ) ^ 2 := by exact_mod_cast hN
  have hn' : (nRk D : ℝ) ≤ t := by exact_mod_cast hn
  have hs' : (sLen D : ℝ) ≤ 2 * t := by exact_mod_cast hs
  have hm' : (D.R.m : ℝ) ≤ t := by exact_mod_cast (by omega : D.R.m ≤ t)
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have a1 : (bigN D : ℝ) ^ 3 ≤ (t : ℝ) ^ 7 := by
    calc (bigN D : ℝ) ^ 3 ≤ (5 * (t : ℝ) ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) hN' 3
      _ = 125 * (t : ℝ) ^ 6 := by ring
      _ ≤ t * (t : ℝ) ^ 6 := by gcongr; linarith
      _ = _ := by ring
  have a2 : (nRk D : ℝ) ^ 7 ≤ (t : ℝ) ^ 7 := pow_le_pow_left₀ (by positivity) hn' 7
  have a3 : (nRk D : ℝ) ^ 3 ≤ (t : ℝ) ^ 7 :=
    (pow_le_pow_left₀ (by positivity) hn' 3).trans (pow_le_pow_right₀ (by linarith) (by norm_num))
  have a4 : 132 * (t : ℝ) ^ 3 ≤ (t : ℝ) ^ 7 := by
    calc 132 * (t : ℝ) ^ 3 ≤ t * (t : ℝ) ^ 3 := by gcongr
      _ = (t : ℝ) ^ 4 := by ring
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have a5 : (t : ℝ) ≤ (t : ℝ) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have a6 : (t : ℝ) ^ 7 ≤ (t : ℝ) ^ 7 * B := le_mul_of_one_le_right (by positivity) hB
  have a7 : (nRk D : ℝ) ^ 3 * Real.sqrt (cloudLen D) ≤ (t : ℝ) ^ 7 * B := by gcongr
  have a8 : Real.sqrt D.R.m ≤ t := (Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩)
  have a9 : (nRk D : ℝ) ^ 2 * Real.sqrt D.R.m ≤ (t : ℝ) ^ 3 := by
    calc (nRk D : ℝ) ^ 2 * Real.sqrt D.R.m ≤ (t : ℝ) ^ 2 * t := by gcongr
      _ = _ := by ring
  unfold gap
  push_cast
  refine max_le (max_le ((Nat.ceil_lt_add_one (by positivity)).le.trans ?_) ?_) ((Nat.ceil_lt_add_one (by positivity)).le.trans ?_)
  · linarith
  · linarith
  · linarith

/- English proof (translation)
Establish `x1` using `L.sc.one_lt_alt`. Establish `x0 : 0 < L.sc.x` using `by linarith`. Establish `hb1 : 1 ≤ L.sc.b` using `Real.one_le_exp (Real.rpow_nonneg x0.le _)`. Establish `hn : (1 : ℝ) ≤ D.R.n` using `by exact_mod_cast D.R.n_pos'`. Establish `hb' : L.sc.b' ≤ L.sc.b`.

Unfold `Scale.b' Scale.a`. Rewrite using `[div_le_iff₀ (by linarith)]; nlinarith`. Establish `hb0 : 0 < L.sc.b'` using `by unfold Scale.b' Scale.a; have : 0 < L.sc.X' := by linarith`. Check the signs of the components of the expression. Establish `hq : L.sc.b' / L.sc.x ≤ L.sc.b'` using `div_le_self hb0.le x1.le`.

Establish `hw : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x`. Unfold `Scale.w''`. Conclude with `div_le_div_of_nonneg_left hb0.le x0 (by nlinarith)`. Establish `hw0 : 0 < L.sc.w'' D.R.n` using `by unfold Scale.w''; positivity`. Establish `ht : (1 : ℝ) ≤ D.R.t` using `L.t_win.1`.

Establish `he : L.etaSz < L.sc.w'' D.R.n`. Establish `h1` using `P.teta`. Establish `h2 : L.sc.w'' D.R.n / L.sc.x < L.sc.w'' D.R.n` using `div_lt_self hw0 x1`. Use `L.etaSz_pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hwj : wj D (l.1 + 1) τ = (((D.hc τ).e l : ℚ) : ℝ)`. Unfold `wj`. Rewrite using `[dif_pos (by simp)]`. Both sides reduce to the same expression. Establish `hbT : ∀ t, (L.bT t : ℝ) ≤ 2 * L.sc.b'` using `fun t => by`.

Establish `h1` using `P.bT_le t`. Establish `h2` using `P.rho_le`. Establish `hLa : 0 ≤ L.LaG` using `(Real.rpow_nonneg x0.le _).trans hS.2.2.2.2.2.2.2.2.1.1`. Establish `h3 : L.sc.x ^ (-2 : ℝ) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos x1.le (by norm_num)`. Establish `h4 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k`.

Use `P.Crho_pos` as an intermediate fact. Use `Real.log_nonneg x1.le` as an intermediate fact. Check the signs of the components of the expression. Unfold `LevelStarExponents.rhoP at h2`. Establish `h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1`.

Establish `: 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b'` using `by ring`. Use the polynomial consequences of the given equalities and inequalities. Establish `key : L.sc.w'' D.R.n ≤ (((D.hc τ).e l : ℚ) : ℝ) ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * L.sc.b`.

Rewrite using `[← hwj]`. Distinguish the cases in `h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by`. Unfold `Host.topPlaces at h1`. Simplify using `using h1`.

Use `L.win_top (l.1 + 1) (by omega) l.2 τ ⟨t, ht1⟩ ht2.symm` as an intermediate fact. Establish `a` using `L.bT_ge ⟨t, ht1⟩`. Establish `b` using `hbT ⟨t, ht1⟩`. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`. Distinguish the cases in `h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces`.

Use `L.win_thick (l.1 + 1) (by omega) l.2 τ h2` as an intermediate fact. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`. Use `L.win_thin (l.1 + 1) (by omega) l.2 τ ⟨(D.eTau τ).2, h1, h2⟩` as an intermediate fact. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`. Use `⟨?_, key.2⟩` and prove the remaining obligations.

Use `(abs_le.1 (L.be_close τ l l)).1` as an intermediate fact. Move the coercions through the operations in `at this`. Establish `: (0 : ℝ) < (((D.hc τ).b l : ℚ) : ℝ)` using `by linarith [key.1]`. Conclude with `this` after adjusting the coercions.
-/
theorem hc_bounds (P : ParameterChoice' D L) (hS : SizesAt L) (hx : L.sc.x ≤ L.sc.X') (τ) (l : Fin D.R.m) :
    0 < (D.hc τ).b l ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * L.sc.b := by
  have x1 := L.sc.one_lt_alt
  have x0 : 0 < L.sc.x := by linarith
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg x0.le _)
  have hn : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.n_pos'
  have hb' : L.sc.b' ≤ L.sc.b := by
    unfold Scale.b' Scale.a
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hb0 : 0 < L.sc.b' := by unfold Scale.b' Scale.a; have : 0 < L.sc.X' := by linarith
                               positivity
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb0.le x1.le
  have hw : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
    unfold Scale.w''
    exact div_le_div_of_nonneg_left hb0.le x0 (by nlinarith)
  have hw0 : 0 < L.sc.w'' D.R.n := by unfold Scale.w''; positivity
  have ht : (1 : ℝ) ≤ D.R.t := L.t_win.1
  have he : L.etaSz < L.sc.w'' D.R.n := by
    have h1 := P.teta
    have h2 : L.sc.w'' D.R.n / L.sc.x < L.sc.w'' D.R.n := div_lt_self hw0 x1
    have := L.etaSz_pos
    nlinarith
  have hwj : wj D (l.1 + 1) τ = (((D.hc τ).e l : ℚ) : ℝ) := by
    unfold wj
    rw [dif_pos (by simp)]
    rfl
  have hbT : ∀ t, (L.bT t : ℝ) ≤ 2 * L.sc.b' := fun t => by
    have h1 := P.bT_le t
    have h2 := P.rho_le
    have hLa : 0 ≤ L.LaG := (Real.rpow_nonneg x0.le _).trans hS.2.2.2.2.2.2.2.2.1.1
    have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos x1.le (by norm_num)
    have h4 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
      have := P.Crho_pos; have := Real.log_nonneg x1.le; positivity
    unfold LevelStarExponents.rhoP at h2
    have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 := by
      have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
      linarith
    have : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
    nlinarith
  have key : L.sc.w'' D.R.n ≤ (((D.hc τ).e l : ℚ) : ℝ) ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * L.sc.b := by
    rw [← hwj]
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      obtain ⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by
        unfold Host.topPlaces at h1
        simpa using h1
      have := L.win_top (l.1 + 1) (by omega) l.2 τ ⟨t, ht1⟩ ht2.symm
      have a := L.bT_ge ⟨t, ht1⟩
      have b := hbT ⟨t, ht1⟩
      constructor <;> linarith [this.1, this.2]
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · have := L.win_thick (l.1 + 1) (by omega) l.2 τ h2
        constructor <;> linarith [this.1, this.2]
      · have := L.win_thin (l.1 + 1) (by omega) l.2 τ ⟨(D.eTau τ).2, h1, h2⟩
        constructor <;> linarith [this.1, this.2]
  refine ⟨?_, key.2⟩
  have := (abs_le.1 (L.be_close τ l l)).1
  push_cast at this
  have : (0 : ℝ) < (((D.hc τ).b l : ℚ) : ℝ) := by linarith [key.1]
  exact_mod_cast this

end Sizes

section Main

variable {D : D7} {L : SizeData₂ D}

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `x1` using `L.sc.one_lt_alt`. Establish `x0 : 0 < L.sc.x` using `by linarith`. Establish `e0` using `L.sc.eps_pos`. Establish `e1` using `L.sc.eps_lt`. Establish `mono : ∀ a b : ℝ, a ≤ b → L.sc.x ^ a ≤ L.sc.x ^ b` using `fun a b h => Real.rpow_le_rpow_of_exponent_le x1.le h`.

Use `set z := L.sc.x ^ (L.sc.eps / 4) with hzdef`. Establish `hL : L.sc.L = z ^ 4`. Rewrite using `[hzdef, ← Real.rpow_natCast, ← Real.rpow_mul x0.le]`. Unfold `Scale.L`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `z3 : 512 ≤ z ^ 3` using `by have := pow_le_pow_left₀ (by norm_num) hz 3; linarith`. Establish `hLz : 512 * z ≤ L.sc.L` using `by rw [hL]; nlinarith only [hz, z3]`. Use `set s := L.sc.x ^ ((1 : ℝ) / 4) with hsdef`.

Establish `hs4 : L.sc.x = s ^ 4`. Rewrite using `[hsdef, ← Real.rpow_natCast, ← Real.rpow_mul x0.le]`. Evaluate the numerical expressions. Establish `s0 : 0 ≤ s` using `Real.rpow_nonneg x0.le _`. Establish `s44 : 44 ≤ s`.

Assume the negation of the conclusion as `h`. Use `pow_lt_pow_left₀ (not_le.1 h) s0 (n := 4) (by norm_num)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hδ : L.sc.delta1 ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos x1.le (by linarith)`. Establish `hm2 : (D.R.m : ℝ) ≤ 2 * s ^ 2`.

Use `hm1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩) (by norm_num))` and prove the remaining obligations. Establish `: (s ^ 2) ^ 2 = L.sc.x` using `by rw [hs4]; ring`. Rewrite using `[this]`. Conclude with `mul_le_of_le_one_right x0.le hδ`. Establish `m44 : 44 ≤ D.R.m`.

Establish `h1 : s ≤ Real.sqrt (L.sc.x * L.sc.delta1)`. Use `Real.le_sqrt_of_sq_le ?_` and prove the remaining obligations. Establish `a : s ^ 2 = L.sc.x ^ ((1 : ℝ) / 2)`. Rewrite using `[hsdef, ← Real.rpow_natCast, ← Real.rpow_mul x0.le]`. Evaluate the numerical expressions.

Establish `b : L.sc.x * L.sc.delta1 = L.sc.x ^ (1 + -(L.sc.eps / 8))`. Rewrite using `[Real.rpow_add x0, Real.rpow_one]`. Both sides reduce to the same expression. Rewrite using `[a, b]; exact mono _ _ (by linarith)`. Conclude with `(by linarith : (44 : ℝ) ≤ D.R.m)` after adjusting the coercions.

Establish `hn2 : s ^ 8 * L.sc.L ≤ D.R.n`. Use `le_trans ?_ ((mono (2 + L.sc.eps) _ (by linarith)).trans hn)` and prove the remaining obligations. Rewrite using `[Real.rpow_add x0, Real.rpow_two]`. Establish `: L.sc.x ^ 2 = s ^ 8` using `by rw [hs4]; ring`. Rewrite using `[this]`.

Conclude with `le_rfl`. Establish `hk2 : s ^ 18 * L.sc.L ^ 2 ≤ D.R.k`. Use `le_trans (le_of_eq ?_) ((mono (1 / 4 * (18 : ℕ) + L.sc.eps * (2 : ℕ)) _ (by push_cast; linarith)).trans hk)` and prove the remaining obligations. Rewrite using `[Real.rpow_add x0, Real.rpow_mul x0.le, Real.rpow_mul x0.le, Real.rpow_natCast, Real.rpow_natCast]`. Both sides reduce to the same expression.

Establish `L1 : 1 ≤ L.sc.L` using `by linarith`. Establish `r1` using `D.R.rank_add_five_le`. Establish `r2` using `D.R.three_m_lt_t`. Establish `r3` using `D.R.m_add_three_le_k`. Establish `r4 : D.R.f ≤ D.R.k` using `D.R.f_le_k`.

Establish `r5 : D.R.f = 2 * D.R.n` using `rfl`. Establish `r6 : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `n1 : 1 ≤ D.R.n` using `D.R.n_pos'`. Establish `kt : (D.R.k : ℝ) ≤ D.R.t` using `by exact_mod_cast (by omega : D.R.k ≤ D.R.t)`. Establish `nt : (D.R.n : ℝ) ≤ D.R.t` using `by exact_mod_cast (by omega : D.R.n ≤ D.R.t)`.

Establish `ft : (D.R.f : ℝ) ≤ D.R.t` using `by exact_mod_cast (by omega : D.R.f ≤ D.R.t)`. Establish `mt : (D.R.m : ℝ) + 1 ≤ D.R.t` using `by exact_mod_cast (by omega : D.R.m + 1 ≤ D.R.t)`. Establish `t132 : (132 : ℝ) ≤ D.R.t` using `by exact_mod_cast (by omega : 132 ≤ D.R.t)`. Establish `n1' : (1 : ℝ) ≤ D.R.n` using `by exact_mod_cast n1`. Establish `k4 : (4 : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : 4 ≤ D.R.k)`.

Establish `q1 : (1 : ℝ) ≤ D.host.q` using `by exact_mod_cast D.host.hyp.1.one_le`. Establish `d1 : (1 : ℝ) ≤ D.host.d` using `by exact_mod_cast D.host.hyp.2.1.one_le`. Establish `cE : (LevelStarExponents.condE D : ℝ) = D.host.QS * D.host.q * D.host.d` using `by unfold LevelStarExponents.condE; push_cast; ring`. Establish `qd1 : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d` using `one_le_mul_of_one_le_of_one_le q1 d1`. Establish `dc : (D.host.d : ℝ) ≤ LevelStarExponents.condE D`.

Rewrite using `[cE]; exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le (UpperTheory.Ram.Rd.one_le_QS_real D.host) q1)`. Take `⟨-, -, c1, -, c2, -, c3, c4⟩` from `hS.2.2.2.2.2.2.1`. Establish `c1' : Real.log D.host.q ≤ z` using `c1.trans (mono _ _ (by unfold szTh; linarith))`. Establish `c2' : Real.log D.host.d ≤ z` using `c2.trans (mono _ _ (by unfold szTh; linarith))`. Establish `logt : Real.log D.R.t ≤ z` using `(Real.log_le_log (by linarith) P.t_le_eta).trans P.logeta`.

Establish `lrd : Real.log D.host.rdE ≤ Real.log (LevelStarExponents.condE D)`. Rewrite using `[cE]`. Conclude with `Real.log_le_log (UpperTheory.Ram.Rd.rdE_pos D.host) (UpperTheory.Ram.Rd.rdE_le_cond D.host)`. Establish `lc : Real.log (LevelStarExponents.condE D) ≤ L.sc.L / 100`. Rewrite using `[cE]`.

Establish `a` using `UpperTheory.Ram.Rd.log_cond_le D.host`. Establish `b` using `Real.log_le_log (by linarith) nt`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `b0 : 0 < L.sc.b` using `Real.exp_pos _`. Use `set B := Real.sqrt L.sc.b with hBdef`.

Establish `hB2 : B ^ 2 = L.sc.b` using `Real.sq_sqrt b0.le`. Establish `hcond : (LevelStarExponents.condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 ≤ B`. Rewrite using `[hBdef, Real.sqrt_eq_rpow]`. Conclude with `P.condE_le`. Establish `c36 : (LevelStarExponents.condE D : ℝ) ≤ (LevelStarExponents.condE D : ℝ) ^ 36` using `le_self_pow₀ (by linarith) (by norm_num)`.

Establish `t9 : (D.R.t : ℝ) ^ 9 ≤ (D.R.t : ℝ) ^ 150` using `pow_le_pow_right₀ (by linarith) (by norm_num)`. Establish `hdB : (D.host.d : ℝ) * (D.R.t : ℝ) ^ 9 ≤ B` using `(mul_le_mul (dc.trans c36) t9 (by positivity) (by positivity)).trans hcond`. Establish `t9' : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 9` using `one_le_pow₀ (by linarith)`. Establish `htB : (D.R.t : ℝ) ^ 9 ≤ B` using `(le_mul_of_one_le_left (by positivity) d1).trans hdB`. Establish `B1 : 1 ≤ B` using `t9'.trans htB`.

Establish `Bb : B ≤ L.sc.b` using `by nlinarith only [B1, hB2]`. Establish `xX : L.sc.x ≤ L.sc.X'`. Establish `a : L.sc.x ≤ D.R.k`. Use `le_trans ?_ hk` and prove the remaining obligations. Use `conv_lhs => rw [← Real.rpow_one L.sc.x]`.

Conclude with `mono _ _ (by linarith)`. Establish `b : Real.log L.sc.x ≤ L.sc.x ^ (L.sc.eps / 3)` using `(Real.log_le_log x0 (a.trans kt)).trans (logt.trans (mono _ _ (by linarith)))`. Conclude with `(Real.log_le_iff_le_exp x0).1 b`. Establish `hw : L.sc.w'' D.R.n ≤ L.sc.b`. Unfold `Scale.w'' Scale.b' Scale.a`.

Rewrite using `[div_le_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hSc : 4 * L.Sc ≤ L.sc.b` using `by nlinarith only [P.kS_le, L.Sc_pos, hw, k4]`. Use `⟨⟨P, T, hC⟩, hS, ?_, m44, ?_, ?_, ?_, fun i => ?_, ?_, lrd, lc, ?_, hc_bounds P hS xX, hc⟩` and prove the remaining obligations. Establish `a : (D.R.m : ℝ) ^ 4 ≤ (2 * s ^ 2) ^ 4` using `pow_le_pow_left₀ (by positivity) hm2 4`.

Establish `b : (D.R.f : ℝ) = 2 * D.R.n` using `by rw [r5]; push_cast; ring`. Establish `c : 0 ≤ s ^ 8` using `by positivity`. Establish `: (D.R.m : ℝ) ^ 4 ≤ D.R.f`. Establish `d : s ^ 8 * 8 ≤ s ^ 8 * L.sc.L` using `mul_le_mul_of_nonneg_left (by linarith) c`. Combine the linear relations using `only [a, b, d, hn2]`.

Conclude with `this` after adjusting the coercions. Establish `a : (D.R.m : ℝ) ^ 3 ≤ (2 * s ^ 2) ^ 3` using `pow_le_pow_left₀ (by positivity) hm2 3`. Establish `b : Real.log D.host.rdE ≤ L.sc.L` using `by linarith`. Establish `c : 0 ≤ Real.log D.host.rdE` using `Real.log_nonneg c3`. Establish `d : 8 ≤ s ^ 4` using `by linarith`.

Combine the equalities or inequalities in the displayed calculation. Establish `a : (D.R.N D.R.m : ℝ) ≤ (D.R.t : ℝ) ^ 3`. Unfold `Ranks.N`. Use `push_cast`. Establish `: (D.R.m : ℝ) * (D.R.t + 1) ≤ D.R.t * (D.R.t + 1)` using `mul_le_mul_of_nonneg_right (by linarith only [mt]) (by positivity)`.

Use polynomial arithmetic with `only [this, kt, t132, mul_nonneg (sub_nonneg.2 t132) (sq_nonneg (D.R.t : ℝ))]`. Establish `m' : (D.R.m : ℝ) ≤ D.R.t` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `: (0 : ℝ) < D.host.g i` using `by exact_mod_cast (D.host.g_prime i).pos`.

Combine the linear relations using `[(Real.log_le_iff_le_exp this).2 (hg i)]`. Establish `: (0 : ℝ) < q0 D` using `by exact_mod_cast (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos`. Conclude with `((Real.log_le_iff_le_exp this).2 hq.le).trans (mono _ _ (by linarith))`. Establish `a` using `gap_le D B B1 (Real.sqrt_le_sqrt (by linarith [cloudLen_le L, L.Sc_pos])) m44`. Establish `b : ((D.R.m : ℝ) + 1) * gap D 1 ≤ D.R.t * (4 * (D.R.t : ℝ) ^ 7 * B)` using `by gcongr`.

Establish `c : 16 * (D.R.t : ℝ) ^ 8 ≤ B`. Use `le_trans ?_ htB` and prove the remaining obligations. Rewrite using `[pow_succ' _ 8]`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `d : D.R.t * (4 * (D.R.t : ℝ) ^ 7 * B) = (16 * (D.R.t : ℝ) ^ 8) * B / 4` using `by ring`. Establish `e : (16 * (D.R.t : ℝ) ^ 8) * B ≤ B * B` using `by gcongr`. Establish `f : B * B = L.sc.b` using `by rw [← hB2]; ring`. Combine the linear relations using `only [b, d, e, f, hSc, Bb, B1]`.
-/
theorem sizeRows_of (P : ParameterChoice' D L) (T : ParamsT D L P) (hC : P.CnW = 10) (hS : SizesAt L)
    (hn : L.sc.x ^ (2 + 8 * L.sc.eps) ≤ (D.R.n : ℝ))
    (hm0 : Real.sqrt (L.sc.x * L.sc.delta1) ≤ (D.R.m : ℝ)) (hm1 : (D.R.m : ℝ) ≤ 2 * Real.sqrt (L.sc.x * L.sc.delta1))
    (hk : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ (D.R.k : ℝ))
    (hg : ∀ j : Fin 2, ((D.host.g j : ℕ) : ℝ) ≤ Real.exp (9 * L.sc.L)) (hq : ((q0 D : ℕ) : ℝ) < L.sc.X') (hc : D.host.ccK = ⊤)
    (hz : 8 ≤ L.sc.x ^ (L.sc.eps / 4)) (hx : 44 ^ 4 ≤ L.sc.x) : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L := by
  have x1 := L.sc.one_lt_alt
  have x0 : 0 < L.sc.x := by linarith
  have e0 := L.sc.eps_pos
  have e1 := L.sc.eps_lt
  have mono : ∀ a b : ℝ, a ≤ b → L.sc.x ^ a ≤ L.sc.x ^ b := fun a b h => Real.rpow_le_rpow_of_exponent_le x1.le h
  set z := L.sc.x ^ (L.sc.eps / 4) with hzdef
  have hL : L.sc.L = z ^ 4 := by
    rw [hzdef, ← Real.rpow_natCast, ← Real.rpow_mul x0.le]; unfold Scale.L; congr 1; push_cast; ring
  have z3 : 512 ≤ z ^ 3 := by have := pow_le_pow_left₀ (by norm_num) hz 3; linarith
  have hLz : 512 * z ≤ L.sc.L := by rw [hL]; nlinarith only [hz, z3]
  set s := L.sc.x ^ ((1 : ℝ) / 4) with hsdef
  have hs4 : L.sc.x = s ^ 4 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul x0.le]; norm_num
  have s0 : 0 ≤ s := Real.rpow_nonneg x0.le _
  have s44 : 44 ≤ s := by
    by_contra h
    have := pow_lt_pow_left₀ (not_le.1 h) s0 (n := 4) (by norm_num)
    linarith
  have hδ : L.sc.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos x1.le (by linarith)
  have hm2 : (D.R.m : ℝ) ≤ 2 * s ^ 2 := by
    refine hm1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩) (by norm_num))
    have : (s ^ 2) ^ 2 = L.sc.x := by rw [hs4]; ring
    rw [this]; exact mul_le_of_le_one_right x0.le hδ
  have m44 : 44 ≤ D.R.m := by
    have h1 : s ≤ Real.sqrt (L.sc.x * L.sc.delta1) := by
      refine Real.le_sqrt_of_sq_le ?_
      have a : s ^ 2 = L.sc.x ^ ((1 : ℝ) / 2) := by
        rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul x0.le]; norm_num
      have b : L.sc.x * L.sc.delta1 = L.sc.x ^ (1 + -(L.sc.eps / 8)) := by
        rw [Real.rpow_add x0, Real.rpow_one]; rfl
      rw [a, b]; exact mono _ _ (by linarith)
    exact_mod_cast (by linarith : (44 : ℝ) ≤ D.R.m)
  have hn2 : s ^ 8 * L.sc.L ≤ D.R.n := by
    refine le_trans ?_ ((mono (2 + L.sc.eps) _ (by linarith)).trans hn)
    rw [Real.rpow_add x0, Real.rpow_two]
    have : L.sc.x ^ 2 = s ^ 8 := by rw [hs4]; ring
    rw [this]; exact le_rfl
  have hk2 : s ^ 18 * L.sc.L ^ 2 ≤ D.R.k := by
    refine le_trans (le_of_eq ?_) ((mono (1 / 4 * (18 : ℕ) + L.sc.eps * (2 : ℕ)) _ (by push_cast; linarith)).trans hk)
    rw [Real.rpow_add x0, Real.rpow_mul x0.le, Real.rpow_mul x0.le, Real.rpow_natCast, Real.rpow_natCast]; rfl
  have L1 : 1 ≤ L.sc.L := by linarith
  have r1 := D.R.rank_add_five_le
  have r2 := D.R.three_m_lt_t
  have r3 := D.R.m_add_three_le_k
  have r4 : D.R.f ≤ D.R.k := D.R.f_le_k
  have r5 : D.R.f = 2 * D.R.n := rfl
  have r6 : D.R.r = D.R.k + D.R.m - 1 := rfl
  have n1 : 1 ≤ D.R.n := D.R.n_pos'
  have kt : (D.R.k : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.k ≤ D.R.t)
  have nt : (D.R.n : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.n ≤ D.R.t)
  have ft : (D.R.f : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.f ≤ D.R.t)
  have mt : (D.R.m : ℝ) + 1 ≤ D.R.t := by exact_mod_cast (by omega : D.R.m + 1 ≤ D.R.t)
  have t132 : (132 : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : 132 ≤ D.R.t)
  have n1' : (1 : ℝ) ≤ D.R.n := by exact_mod_cast n1
  have k4 : (4 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 4 ≤ D.R.k)
  have q1 : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_le
  have d1 : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_le
  have cE : (LevelStarExponents.condE D : ℝ) = D.host.QS * D.host.q * D.host.d := by unfold LevelStarExponents.condE; push_cast; ring
  have qd1 : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := one_le_mul_of_one_le_of_one_le q1 d1
  have dc : (D.host.d : ℝ) ≤ LevelStarExponents.condE D := by
    rw [cE]; exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le (UpperTheory.Ram.Rd.one_le_QS_real D.host) q1)
  obtain ⟨-, -, c1, -, c2, -, c3, c4⟩ := hS.2.2.2.2.2.2.1
  have c1' : Real.log D.host.q ≤ z := c1.trans (mono _ _ (by unfold szTh; linarith))
  have c2' : Real.log D.host.d ≤ z := c2.trans (mono _ _ (by unfold szTh; linarith))
  have logt : Real.log D.R.t ≤ z := (Real.log_le_log (by linarith) P.t_le_eta).trans P.logeta
  have lrd : Real.log D.host.rdE ≤ Real.log (LevelStarExponents.condE D) := by
    rw [cE]; exact Real.log_le_log (UpperTheory.Ram.Rd.rdE_pos D.host) (UpperTheory.Ram.Rd.rdE_le_cond D.host)
  have lc : Real.log (LevelStarExponents.condE D) ≤ L.sc.L / 100 := by
    rw [cE]
    have a := UpperTheory.Ram.Rd.log_cond_le D.host
    have b := Real.log_le_log (by linarith) nt
    linarith
  have b0 : 0 < L.sc.b := Real.exp_pos _
  set B := Real.sqrt L.sc.b with hBdef
  have hB2 : B ^ 2 = L.sc.b := Real.sq_sqrt b0.le
  have hcond : (LevelStarExponents.condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 ≤ B := by
    rw [hBdef, Real.sqrt_eq_rpow]; exact P.condE_le
  have c36 : (LevelStarExponents.condE D : ℝ) ≤ (LevelStarExponents.condE D : ℝ) ^ 36 := le_self_pow₀ (by linarith) (by norm_num)
  have t9 : (D.R.t : ℝ) ^ 9 ≤ (D.R.t : ℝ) ^ 150 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hdB : (D.host.d : ℝ) * (D.R.t : ℝ) ^ 9 ≤ B :=
    (mul_le_mul (dc.trans c36) t9 (by positivity) (by positivity)).trans hcond
  have t9' : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 9 := one_le_pow₀ (by linarith)
  have htB : (D.R.t : ℝ) ^ 9 ≤ B := (le_mul_of_one_le_left (by positivity) d1).trans hdB
  have B1 : 1 ≤ B := t9'.trans htB
  have Bb : B ≤ L.sc.b := by nlinarith only [B1, hB2]
  have xX : L.sc.x ≤ L.sc.X' := by
    have a : L.sc.x ≤ D.R.k := by
      refine le_trans ?_ hk
      conv_lhs => rw [← Real.rpow_one L.sc.x]
      exact mono _ _ (by linarith)
    have b : Real.log L.sc.x ≤ L.sc.x ^ (L.sc.eps / 3) :=
      (Real.log_le_log x0 (a.trans kt)).trans (logt.trans (mono _ _ (by linarith)))
    exact (Real.log_le_iff_le_exp x0).1 b
  have hw : L.sc.w'' D.R.n ≤ L.sc.b := by
    unfold Scale.w'' Scale.b' Scale.a
    rw [div_le_iff₀ (by positivity)]
    calc L.sc.x * L.sc.b / L.sc.X' ≤ L.sc.x * L.sc.b := div_le_self (by positivity) (by linarith)
      _ ≤ L.sc.b * (L.sc.x * D.R.n) := by linarith only [mul_nonneg (mul_pos x0 b0).le (sub_nonneg.2 n1')]
  have hSc : 4 * L.Sc ≤ L.sc.b := by nlinarith only [P.kS_le, L.Sc_pos, hw, k4]
  refine ⟨⟨P, T, hC⟩, hS, ?_, m44, ?_, ?_, ?_, fun i => ?_, ?_, lrd, lc, ?_, hc_bounds P hS xX, hc⟩
  · have a : (D.R.m : ℝ) ^ 4 ≤ (2 * s ^ 2) ^ 4 := pow_le_pow_left₀ (by positivity) hm2 4
    have b : (D.R.f : ℝ) = 2 * D.R.n := by rw [r5]; push_cast; ring
    have c : 0 ≤ s ^ 8 := by positivity
    have : (D.R.m : ℝ) ^ 4 ≤ D.R.f := by
      have d : s ^ 8 * 8 ≤ s ^ 8 * L.sc.L := mul_le_mul_of_nonneg_left (by linarith) c
      linarith only [a, b, d, hn2]
    exact_mod_cast this
  · have a : (D.R.m : ℝ) ^ 3 ≤ (2 * s ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) hm2 3
    have b : Real.log D.host.rdE ≤ L.sc.L := by linarith
    have c : 0 ≤ Real.log D.host.rdE := Real.log_nonneg c3
    have d : 8 ≤ s ^ 4 := by linarith
    calc L.sc.x ^ 2 * (D.R.m : ℝ) ^ 3 * L.sc.L * Real.log D.host.rdE ≤ L.sc.x ^ 2 * (2 * s ^ 2) ^ 3 * L.sc.L * L.sc.L := by gcongr
      _ = 8 * (s ^ 14 * L.sc.L ^ 2) := by rw [show L.sc.x ^ 2 = s ^ 8 by rw [hs4]; ring]; ring
      _ ≤ s ^ 4 * (s ^ 14 * L.sc.L ^ 2) := by gcongr
      _ = s ^ 18 * L.sc.L ^ 2 := by ring
      _ ≤ _ := hk2
  · have a : (D.R.N D.R.m : ℝ) ≤ (D.R.t : ℝ) ^ 3 := by
      unfold Ranks.N; push_cast
      have : (D.R.m : ℝ) * (D.R.t + 1) ≤ D.R.t * (D.R.t + 1) := mul_le_mul_of_nonneg_right (by linarith only [mt]) (by positivity)
      nlinarith only [this, kt, t132, mul_nonneg (sub_nonneg.2 t132) (sq_nonneg (D.R.t : ℝ))]
    have m' : (D.R.m : ℝ) ≤ D.R.t := by linarith
    calc (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d ≤ D.R.t * D.R.t * ((D.R.t : ℝ) ^ 3) ^ 2 * D.host.d := by gcongr
      _ = D.host.d * (D.R.t : ℝ) ^ 8 := by ring
      _ ≤ D.host.d * (D.R.t : ℝ) ^ 9 := by gcongr; linarith; norm_num
      _ ≤ _ := hdB.trans Bb
  · calc D.R.f * D.R.m ≤ (D.R.r + 1) * (D.R.r + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ = (D.R.r + 1) ^ 2 := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by norm_num)
  · have : (0 : ℝ) < D.host.g i := by exact_mod_cast (D.host.g_prime i).pos
    linarith [(Real.log_le_iff_le_exp this).2 (hg i)]
  · have : (0 : ℝ) < q0 D := by exact_mod_cast (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
    exact ((Real.log_le_iff_le_exp this).2 hq.le).trans (mono _ _ (by linarith))
  · have a := gap_le D B B1 (Real.sqrt_le_sqrt (by linarith [cloudLen_le L, L.Sc_pos])) m44
    have b : ((D.R.m : ℝ) + 1) * gap D 1 ≤ D.R.t * (4 * (D.R.t : ℝ) ^ 7 * B) := by gcongr
    have c : 16 * (D.R.t : ℝ) ^ 8 ≤ B := by
      refine le_trans ?_ htB
      rw [pow_succ' _ 8]; gcongr; linarith
    have d : D.R.t * (4 * (D.R.t : ℝ) ^ 7 * B) = (16 * (D.R.t : ℝ) ^ 8) * B / 4 := by ring
    have e : (16 * (D.R.t : ℝ) ^ 8) * B ≤ B * B := by gcongr
    have f : B * B = L.sc.b := by rw [← hB2]; ring
    linarith only [b, d, e, f, hSc, Bb, B1]

/- English proof (translation)
Use `⟨max (44 ^ 4) ((8 : ℝ) ^ (4 / eps)), fun x hx h0 i => ?_⟩` and prove the remaining obligations. Take `⟨⟨hn, -⟩, ⟨hm0, hm1⟩, hk, -⟩` from `h.2.1 x hx i`. Take `⟨hc, -, hg, -⟩` from `h.1.2.2.2.2.2.2.2.2 x hx i`. Establish `ex` using `Fm.L_x x i hx`. Establish `ee` using `Fm.L_eps x i`.

Use `sizeRows_of (Fm.params x hx i) (Fm.parT x hx i) (Fm.fixed.2.2.2.2.2.2.2 x hx i).1 (Fm.sizes x hx i) (by rw [ex, ee]; exact hn) (by rw [ex]; exact hm0) (by rw [ex]; exact hm1) (by rw [ex, ee]; exact hk) hg (h.2.2.1 x hx i) hc ?_ (by rw [ex]; exact le_of_max_le_left h0)` and prove the remaining obligations. Rewrite using `[ex, ee]`. Establish `e1 : (8 : ℝ) = ((8 : ℝ) ^ (4 / eps)) ^ (eps / 4)`. Rewrite using `[← Real.rpow_mul (by norm_num), show 4 / eps * (eps / 4) = 1 by field_simp, Real.rpow_one]`. Rewrite using `[e1]`.

Conclude with `Real.rpow_le_rpow (by positivity) (le_of_max_le_right h0) (by positivity)`.
-/
theorem sizeRows_fam {eps : ℝ} (he : 0 < eps) (Fm : FamP eps) (h : FamHyp Fm) :
    ∃ x₀ : ℝ, ∀ x, Fm.x1 < x → x₀ ≤ x → ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows (Fm.L x i) := by
  refine ⟨max (44 ^ 4) ((8 : ℝ) ^ (4 / eps)), fun x hx h0 i => ?_⟩
  obtain ⟨⟨hn, -⟩, ⟨hm0, hm1⟩, hk, -⟩ := h.2.1 x hx i
  obtain ⟨hc, -, hg, -⟩ := h.1.2.2.2.2.2.2.2.2 x hx i
  have ex := Fm.L_x x i hx
  have ee := Fm.L_eps x i
  refine sizeRows_of (Fm.params x hx i) (Fm.parT x hx i) (Fm.fixed.2.2.2.2.2.2.2 x hx i).1 (Fm.sizes x hx i)
    (by rw [ex, ee]; exact hn) (by rw [ex]; exact hm0) (by rw [ex]; exact hm1) (by rw [ex, ee]; exact hk) hg
    (h.2.2.1 x hx i) hc ?_ (by rw [ex]; exact le_of_max_le_left h0)
  rw [ex, ee]
  have e1 : (8 : ℝ) = ((8 : ℝ) ^ (4 / eps)) ^ (eps / 4) := by
    rw [← Real.rpow_mul (by norm_num), show 4 / eps * (eps / 4) = 1 by field_simp, Real.rpow_one]
  rw [e1]
  exact Real.rpow_le_rpow (by positivity) (le_of_max_le_right h0) (by positivity)

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_pos, fun _ he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hF _ => let ⟨x₀, h⟩ := sizeRows_fam he Fm hF ⟨x₀, fun x hx h0 i _ _ => h x hx h0 i⟩⟩⟩`.
-/
theorem sizeAt : SizeAt :=
  ⟨1, one_pos, fun _ he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hF _ =>
    let ⟨x₀, h⟩ := sizeRows_fam he Fm hF
    ⟨x₀, fun x hx h0 i _ _ => h x hx h0 i⟩⟩⟩

/- English proof (translation)
The claim follows from `setAt_of_sizeAt sizeAt`.
-/
theorem setAt : SetAt := setAt_of_sizeAt sizeAt

/- English proof (translation)
The claim follows from `setAt.atPt hQ`.
-/
theorem atPt_of_big {Q : ChP} (hQ : Big Q) : AtPt Q := setAt.atPt hQ

end Main

end GlobalTheory.BigTop.Fun.SetAtModel

end
