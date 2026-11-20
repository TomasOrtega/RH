import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageConjugateValuesHeckeOperators
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLatticeStabilizerParamsOffSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLevelSphericalOffSet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParametersBoundedEigenfunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorInverseCosetConjEigenvalueStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsParamFunVIffIsSysParamDOfLevel
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqMain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainEigenPartHasHeckeParameters
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

namespace GlobalTheory.ChainTw.LevelYZero
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

/- English proof (translation)
Establish `e : Formalism.L2.DIV.lev D.sp.cm V.gram β L = Formalism.L2.DIV.lev D.sp.cm V.gram β L'` using `Subgroup.ext h`. Unfold `levS Lev.levG`. Rewrite using `[e]`.
-/
theorem levS_congr {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L L' : LevDat D.host.E ℂ V.rank)
    (h : ∀ x, x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L ↔ x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L') :
    levS V β L = levS V β L' := by
  have e : Formalism.L2.DIV.lev D.sp.cm V.gram β L = Formalism.L2.DIV.lev D.sp.cm V.gram β L' := Subgroup.ext h
  unfold levS Lev.levG
  rw [e]

/- English proof (translation)
Unfold `Lev.levChi Formalism.L2.DIV.levFn`. Simplify using `[LevCh.dat0, Lev.datY]`. Conclude with `Lev.subgroupCharExtension_one_apply _ _`.
-/
theorem principalRowLevelCharacter_trivial (k : GA D (Yc D 0)) : Lev.levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) k = 1 := by
  unfold Lev.levChi Formalism.L2.DIV.levFn
  simp [LevCh.dat0, Lev.datY]
  exact Lev.subgroupCharExtension_one_apply _ _

/- English proof (translation)
Use `levS_congr _ _ _ fun x => ?_` and prove the remaining obligations. Use `show (x ∈ parLev _ _ _ _ ∧ _) ↔ (x ∈ parLev _ _ _ _ ∧ _)`. Unfold `LevCh.datYt LevCh.dat0`. Rewrite using `[Formalism.IndefR.Eqv.Act.mem_parLev_datY_noQ Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 R.Pg (R.Q t) R.triv R.chi (R.xiR t) (fun _ => 1) Lev.Frm.B x]`. Both sides reduce to the same expression.
-/
theorem levS_datYt (t : T) : levS (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  refine levS_congr _ _ _ fun x => ?_
  show (x ∈ parLev _ _ _ _ ∧ _) ↔ (x ∈ parLev _ _ _ _ ∧ _)
  unfold LevCh.datYt LevCh.dat0
  rw [Formalism.IndefR.Eqv.Act.mem_parLev_datY_noQ Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 R.Pg (R.Q t) R.triv R.chi
    (R.xiR t) (fun _ => 1) Lev.Frm.B x]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `k`. Rewrite using `[Formalism.IndefR.Eqv.Act.flag_character_eq_principal, principalRowLevelCharacter_trivial]`. Unfold `Lev.levChi Formalism.L2.DIV.levFn`. Simplify using `[LevCh.dat0, Lev.datY, Lev.flag1L, Lev.withP]`. Conclude with `Lev.subgroupCharExtension_one_apply _ _`.
-/
theorem levChi_datYt (t : T) : Lev.levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = Lev.levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  funext k
  rw [Formalism.IndefR.Eqv.Act.flag_character_eq_principal, principalRowLevelCharacter_trivial]
  unfold Lev.levChi Formalism.L2.DIV.levFn
  simp [LevCh.dat0, Lev.datY, Lev.flag1L, Lev.withP]
  exact Lev.subgroupCharExtension_one_apply _ _

/- English proof (translation)
Unfold `Lev.levChi Formalism.L2.DIV.levFn`. Simplify using `[flat, comR, twR, Lev.datY]`. Conclude with `Lev.subgroupCharExtension_one_apply _ _`.
-/
theorem levChi_flat (t : T) (hr : D.R.r ≤ (stY R t 0).V.rank) (k : GA D (Yc D 0)) :
    Lev.levChi (flat (comR R t) (twR R t) 0 (stY R t 0) hr).V (flat (comR R t) (twR R t) 0 (stY R t 0) hr).β
      (flat (comR R t) (twR R t) 0 (stY R t 0) hr).L k = 1 := by
  unfold Lev.levChi Formalism.L2.DIV.levFn
  simp [flat, comR, twR, Lev.datY]
  exact Lev.subgroupCharExtension_one_apply _ _

open Classical in

/- English proof (translation)
Establish `hbt : ∀ (κ : Type) [CommRing κ] (g : GL (Fin (Yc D 0).rank) κ), g ∈ blockTri (blkOf (n` using `(Yc D 0).rank) D.R.r D.R.t) := by`. Introduce `κ _ g`. Use `show (g : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) κ).BlockTriangular _`. Introduce `i j hij`. Establish `hi : i.val < D.R.r` using `lt_of_lt_of_le i.2 Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le`.

Establish `hj : j.val < D.R.r` using `lt_of_lt_of_le j.2 Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le`. Simplify using `[blkOf, hi, hj] at hij`. Use `levS_congr _ _ _ fun x => ?_` and prove the remaining obligations. Use `show (x ∈ parLev _ _ _ _ ∧ _) ↔ (x ∈ parLev _ _ _ _ ∧ _)`. Simplify using `only [LevCh.dat0, Lev.datY, eq_self_iff_true, if_true, ite_true, parLev, Subgroup.mem_inf, Subgroup.mem_iInf, mem_parah]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨⟨⟨hU, hSt⟩, hPg⟩, -⟩, hT⟩`. Use `⟨⟨⟨⟨hU, hSt⟩, fun i hi => hPg i (Finset.mem_union_left _ hi)⟩, fun i hi => absurd hi (Finset.notMem_empty _)⟩, ?_⟩` and prove the remaining obligations. Use `show _ ∈ (⊥ : Subgroup (G0 R.Pg D.R.r))`. Rewrite using `[Subgroup.mem_bot]`.

Use function extensionality and compare the values at `PP`. Conclude with `hT ⟨PP.1, Finset.mem_union_left _ PP.2⟩ PP.2`. Introduce and unpack `⟨⟨⟨⟨hU, hSt⟩, -⟩, -⟩, hT⟩`. Use `⟨⟨⟨⟨hU, hSt⟩, fun i _ => ⟨hSt, hbt _ _⟩⟩, fun i hi => absurd hi (Finset.notMem_empty _)⟩, fun PP hP => ?_⟩` and prove the remaining obligations. Conclude with `congrFun (Subgroup.mem_bot.1 (show _ ∈ (⊥ : Subgroup (G0 R.Pg D.R.r)) from hT)) ⟨PP.1, hP⟩`.
-/
theorem levS_flat_gen (Q : Finset (Pl D.host.E)) (hr : D.R.r ≤ (Yc D 0).rank)
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    levS (Yc D 0) (R.βY 0) (Lev.datY (Yc D 0).rank D.R.r D.R.t 0 hr (R.Pg ∪ Q) ∅ ⟨trivAt R.Pg (R.Pg ∪ Q) D.R.r, 1⟩ χ ξ
      Lev.Frm.B) = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  have hbt : ∀ (κ : Type) [CommRing κ] (g : GL (Fin (Yc D 0).rank) κ), g ∈ blockTri (blkOf (n := (Yc D 0).rank) D.R.r D.R.t) := by
    intro κ _ g
    show (g : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) κ).BlockTriangular _
    intro i j hij
    have hi : i.val < D.R.r := lt_of_lt_of_le i.2 Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le
    have hj : j.val < D.R.r := lt_of_lt_of_le j.2 Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le
    simp [blkOf, hi, hj] at hij
  refine levS_congr _ _ _ fun x => ?_
  show (x ∈ parLev _ _ _ _ ∧ _) ↔ (x ∈ parLev _ _ _ _ ∧ _)
  simp only [LevCh.dat0, Lev.datY, eq_self_iff_true, if_true, ite_true, parLev, Subgroup.mem_inf, Subgroup.mem_iInf, mem_parah]
  constructor
  · rintro ⟨⟨⟨⟨hU, hSt⟩, hPg⟩, -⟩, hT⟩
    refine ⟨⟨⟨⟨hU, hSt⟩, fun i hi => hPg i (Finset.mem_union_left _ hi)⟩, fun i hi => absurd hi (Finset.notMem_empty _)⟩, ?_⟩
    show _ ∈ (⊥ : Subgroup (G0 R.Pg D.R.r))
    rw [Subgroup.mem_bot]
    funext PP
    exact hT ⟨PP.1, Finset.mem_union_left _ PP.2⟩ PP.2
  · rintro ⟨⟨⟨⟨hU, hSt⟩, -⟩, -⟩, hT⟩
    refine ⟨⟨⟨⟨hU, hSt⟩, fun i _ => ⟨hSt, hbt _ _⟩⟩, fun i hi => absurd hi (Finset.notMem_empty _)⟩, fun PP hP => ?_⟩
    exact congrFun (Subgroup.mem_bot.1 (show _ ∈ (⊥ : Subgroup (G0 R.Pg D.R.r)) from hT)) ⟨PP.1, hP⟩

/- English proof (translation)
The claim follows from `levS_flat_gen R (R.Q t) hr _ _`.
-/
theorem levS_flat (t : T) (hr : D.R.r ≤ (stY R t 0).V.rank) :
    levS (flat (comR R t) (twR R t) 0 (stY R t 0) hr).V (flat (comR R t) (twR R t) 0 (stY R t 0) hr).β
      (flat (comR R t) (twR R t) 0 (stY R t 0) hr).L = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv) :=
  levS_flat_gen R (R.Q t) hr _ _

end GlobalTheory.ChainTw.LevelYZero

namespace GlobalTheory.ChainTw

open LevelYZero in

/- English proof (translation)
Introduce `hP D G _ _ Pl0 T A Ks _ _ _ R F _hG hch hX t c`. Take `⟨htw, hst, -, -, -⟩` from `hch hX t`. Establish `hm : 0 < D.R.m` using `by have := D.R.two_le_m; omega`. Take `⟨hr, -, hflat⟩` from `hst 0 hm`. Establish `hc : (comR R t).Is` using `htw.com`.

Establish `hS : (comR R t).S = GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t`. Unfold `Com.S GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl comR`. Reduce the equality to equality of the corresponding arguments. Establish `hrk : (Yc D 0).rank = D.R.r` using `le_antisymm Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0)`. Use `set s' := flat (comR R t) (twR R t) 0 (stY R t 0) hr with hs'`.

Establish `hJ' : levS s'.V s'.β s'.L = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv)` using `levS_flat R t hr`. Establish `hχ' : Lev.levChi s'.V s'.β s'.L = Lev.levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv)`. Use function extensionality and compare the values at `fun k => (levChi_flat R t hr k).trans (principalRowLevelCharacter_trivial R k).symm`. Establish `hJ : levS (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv)` using `levS_datYt R t`. Establish `hχ : Lev.levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = Lev.levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv)` using `levChi_datYt R t`.

Take `⟨hval, hHk, hconj⟩` from `GlobalTheory.ConjVal.conj_values_hecke hP D (comR R t) hc 0 (Nat.zero_le _) s' hflat`. Take `⟨-, hlat⟩` from `GlobalTheory.ChainOnto.stabLoc_isParamFun_frameLat D (comR R t) hc 0 (Nat.zero_le _) s' hflat`. Take `⟨hsph, hsph', -⟩` from `GlobalTheory.ChainOntoSph.level_spherical_off_S D (comR R t) hc 0 (Nat.zero_le _) s' hflat`. Establish `hmem : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c, u ∈ partFull (comR R t).θ s'.M (levS s'.V s'.β s'.L) (Lev.levChi s'.V s'.β s'.L) (comR R t).S (fun P d => c P (dualLab d))`. Introduce `u hu`.

Rewrite using `[hJ', hχ', hS]`. Conclude with `(Submodule.mem_inf.1 hu).1`. Establish `hCC : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c, PiTensorProduct.lift u ∈ s'.CC (comR R t)`. Introduce `u hu`. Use `(mem_multT _ _ _ _ _).2 ?_` and prove the remaining obligations.

Use `erw [LinearEquiv.symm_apply_apply]`. Conclude with `((mem_partFull _ _ _ _ _ _ _).1 (hmem u hu)).1`. Establish `hkey : ∀ y : s'.CC (comR R t), PiTensorProduct.lift.symm (y : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) ∈ partFull (comR R t).θ s'.M (levS s'.V s'.β s'.L) (Lev.levChi s'.V s'.β s'.L) (comR R t).S (fun P d => c P (dualLab d)) → ∀ w, (∀ k ∈ levS s'.V s'.β s'.L, ∀ g, (fun g => conj (PiLocaliz …`. Introduce `y hy w`. Take `⟨hcont, ⟨C, hC⟩, hinv, hlev⟩` from `hval y w`.

Establish `hb : PiLocalization₂.val y w ∈ GlobalTheory.FinZeta.bddAut s'.V` using `⟨hcont, hinv, C, hC⟩`. Establish `heig` using `GlobalTheory.T.heckeOperator_inverseCoset_conj_eigenvalue D s'.V _ _ (comR R t).S hsph (PiLocalization₂.val y w) hb hlev c (fun P d Rr hR => val_hecke_of_mem_partFull y _ hy P d Rr hR w)`. Use `⟨fun k hk g => ?_, fun P d Rr hR => ?_, ?_⟩` and prove the remaining obligations. Use `show conj (PiLocalization₂.val y w (g * k)) = _`. Rewrite using `[hlev k hk g, map_mul]`.

Establish `h1` using `heig P d Rr ((hHk P d Rr).2 hR)`. Establish `h2` using `hconj Rr (PiLocalization₂.val y w)`. Rewrite using `[h2, h1]`. Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules.

Use `⟨Complex.continuous_conj.comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩` and prove the remaining obligations. Use `show conj (PiLocalization₂.val y w (γ * g)) = conj (PiLocalization₂.val y w g)`. Rewrite using `[hinv γ hγ g]`. Simplify using `using hC g`. Establish `hiff : ∀ y : s'.CC (comR R t), PiTensorProduct.lift.symm (y : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) ∈ partFull (comR R t).θ s'.M (levS s'.V s'.β s'.L) (Lev.levChi s'.V s'.β s'.L) (comR R t).S (fun P d => c P (dualLab d)) → ∀ w B, PiLocalization₂.val y w ≠ 0 → (ParFun (comR R t) s' (PiL …`.

Introduce `y hy w B h0`. Take `⟨hl, hh, -⟩` from `hkey y hy w`. Establish `hne : (fun g => conj (PiLocalization₂.val y w g)) ≠ 0`. Introduce `h`. Apply `h0` to reduce the goal to its premises.

Use function extensionality and compare the values at `g`. Simplify using `using congrFun h g`. Unfold `ParFun`. Rewrite using `[hlat, ← hS, ← hrk]`. Conclude with `GlobalTheory.LFun.isParamFunV_iff_isSysParamD_of_level hsph' hne hl hh B`.

Establish `hy : ∀ u (hu : u ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c), PiTensorProduct.lift.symm (((⟨PiTensorProduct.lift u, hCC u hu⟩ : s'.CC (comR R t))) : SmT s'.M →ₗ[ℂ] (GA D s'.V → …`. Introduce `u hu`. Use `show PiTensorProduct.lift.symm (PiTensorProduct.lift u) ∈ _`. Rewrite using `[LinearEquiv.symm_apply_apply]`. Conclude with `hmem u hu`.

Use `⟨fun hne => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, hu0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne set y : s'.CC (comR R t) := ⟨PiTensorProduct.lift u, hCC u hu⟩ with hydef`. Establish `hl0 : (y : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) ≠ 0`. Introduce `h`. Conclude with `hu0 (PiTensorProduct.lift.injective (h.trans (map_zero _).symm))`.

Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w, PiLocalization₂.val y w ≠ 0 := by`. Assume the negation of the conclusion as `hh`. Use `push_neg at hh`. Conclude with `hl0 (LinearMap.ext hh)`. Take `⟨hl, hh, hb⟩` from `hkey y (hy u hu) w`.

Establish `hne' : (fun g => conj (PiLocalization₂.val y w g)) ≠ 0`. Introduce `h`. Apply `hw` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Simplify using `using congrFun h g`.

Take `⟨B, hB, -⟩` from `GlobalTheory.FinZeta.ParamBound.exists_param_bounded D s'.V _ _ (comR R t).S hsph' _ hb hne' hl c hh`. Use `⟨B, (hiff y (hy u hu) w B hw).1 ?_⟩` and prove the remaining obligations. Unfold `ParFun`. Rewrite using `[hlat]`. Conclude with `hB`.

Establish `hu' : PiTensorProduct.lift u ∈ (stY R t 0).CC (comR R t)`. Use `(mem_multT _ _ _ _ _).2 ?_` and prove the remaining obligations. Use `erw [LinearEquiv.symm_apply_apply]`. Use `show u ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv)) (Lev.levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv))`. Rewrite using `[hJ, hχ]`.

Conclude with `((mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 hu).1).1`. Use `⟨hu', fun hu0 B hB => ⟨?_, fun w hw => ?_⟩⟩` and prove the remaining obligations. Introduce `h`. Apply `hu0` to reduce the goal to its premises. Establish `h1 : PiTensorProduct.lift u = 0` using `congrArg Subtype.val h`.

Conclude with `PiTensorProduct.lift.injective (h1.trans (map_zero _).symm)`. Conclude with `(hiff ⟨PiTensorProduct.lift u, hCC u hu⟩ (hy u hu) w B hw).2 hB`.
-/
theorem rowPar_of_chain : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → (∀ h : RangeX R, RChain R h) → RangeX R → RowPar R := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F _hG hch hX t c
  obtain ⟨htw, hst, -, -, -⟩ := hch hX t
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨hr, -, hflat⟩ := hst 0 hm
  have hc : (comR R t).Is := htw.com
  have hS : (comR R t).S = GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
    unfold Com.S GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl comR
    congr
  have hrk : (Yc D 0).rank = D.R.r := le_antisymm Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0)
  set s' := flat (comR R t) (twR R t) 0 (stY R t 0) hr with hs'
  have hJ' : levS s'.V s'.β s'.L = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv) := levS_flat R t hr
  have hχ' : Lev.levChi s'.V s'.β s'.L = Lev.levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) :=
    funext fun k => (levChi_flat R t hr k).trans (principalRowLevelCharacter_trivial R k).symm
  have hJ : levS (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv) := levS_datYt R t
  have hχ : Lev.levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = Lev.levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) := levChi_datYt R t
  obtain ⟨hval, hHk, hconj⟩ := GlobalTheory.ConjVal.conj_values_hecke hP D (comR R t) hc 0 (Nat.zero_le _) s' hflat
  obtain ⟨-, hlat⟩ := GlobalTheory.ChainOnto.stabLoc_isParamFun_frameLat D (comR R t) hc 0 (Nat.zero_le _) s' hflat
  obtain ⟨hsph, hsph', -⟩ := GlobalTheory.ChainOntoSph.level_spherical_off_S D (comR R t) hc 0 (Nat.zero_le _) s' hflat
  have hmem : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c,
      u ∈ partFull (comR R t).θ s'.M (levS s'.V s'.β s'.L) (Lev.levChi s'.V s'.β s'.L) (comR R t).S
        (fun P d => c P (dualLab d)) := by
    intro u hu
    rw [hJ', hχ', hS]
    exact (Submodule.mem_inf.1 hu).1
  have hCC : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c,
      PiTensorProduct.lift u ∈ s'.CC (comR R t) := by
    intro u hu
    refine (mem_multT _ _ _ _ _).2 ?_
    erw [LinearEquiv.symm_apply_apply]
    exact ((mem_partFull _ _ _ _ _ _ _).1 (hmem u hu)).1

  have hkey : ∀ y : s'.CC (comR R t), PiTensorProduct.lift.symm (y : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) ∈
      partFull (comR R t).θ s'.M (levS s'.V s'.β s'.L) (Lev.levChi s'.V s'.β s'.L) (comR R t).S
        (fun P d => c P (dualLab d)) → ∀ w,
      (∀ k ∈ levS s'.V s'.β s'.L, ∀ g, (fun g => conj (PiLocalization₂.val y w g)) (g * k) =
        (fun k => conj (Lev.levChi s'.V s'.β s'.L k)) k * (fun g => conj (PiLocalization₂.val y w g)) g) ∧
      (∀ P d Rr, Hecke₂ s'.V (levS s'.V s'.β s'.L) (fun k => conj (Lev.levChi s'.V s'.β s'.L k)) (comR R t).S P d Rr →
        heckeLin s'.V Rr (fun g => conj (PiLocalization₂.val y w g)) = c P d • (fun g => conj (PiLocalization₂.val y w g))) ∧
      (fun g => conj (PiLocalization₂.val y w g)) ∈ GlobalTheory.FinZeta.bddAut s'.V := by
    intro y hy w
    obtain ⟨hcont, ⟨C, hC⟩, hinv, hlev⟩ := hval y w
    have hb : PiLocalization₂.val y w ∈ GlobalTheory.FinZeta.bddAut s'.V := ⟨hcont, hinv, C, hC⟩
    have heig := GlobalTheory.T.heckeOperator_inverseCoset_conj_eigenvalue D s'.V _ _ (comR R t).S hsph (PiLocalization₂.val y w) hb hlev c
      (fun P d Rr hR => val_hecke_of_mem_partFull y _ hy P d Rr hR w)
    refine ⟨fun k hk g => ?_, fun P d Rr hR => ?_, ?_⟩
    · show conj (PiLocalization₂.val y w (g * k)) = _
      rw [hlev k hk g, map_mul]
    · have h1 := heig P d Rr ((hHk P d Rr).2 hR)
      have h2 := hconj Rr (PiLocalization₂.val y w)
      rw [h2, h1]
      funext g
      simp
    · refine ⟨Complex.continuous_conj.comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
      · show conj (PiLocalization₂.val y w (γ * g)) = conj (PiLocalization₂.val y w g)
        rw [hinv γ hγ g]
      · simpa using hC g

  have hiff : ∀ y : s'.CC (comR R t), PiTensorProduct.lift.symm (y : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) ∈
      partFull (comR R t).θ s'.M (levS s'.V s'.β s'.L) (Lev.levChi s'.V s'.β s'.L) (comR R t).S
        (fun P d => c P (dualLab d)) → ∀ w B, PiLocalization₂.val y w ≠ 0 →
      (ParFun (comR R t) s' (PiLocalization₂.val y w) B ↔
        GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B) := by
    intro y hy w B h0
    obtain ⟨hl, hh, -⟩ := hkey y hy w
    have hne : (fun g => conj (PiLocalization₂.val y w g)) ≠ 0 := by
      intro h
      apply h0
      funext g
      simpa using congrFun h g
    unfold ParFun
    rw [hlat, ← hS, ← hrk]
    exact GlobalTheory.LFun.isParamFunV_iff_isSysParamD_of_level hsph' hne hl hh B
  have hy : ∀ u (hu : u ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c),
      PiTensorProduct.lift.symm (((⟨PiTensorProduct.lift u, hCC u hu⟩ : s'.CC (comR R t))) :
        SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) ∈
      partFull (comR R t).θ s'.M (levS s'.V s'.β s'.L) (Lev.levChi s'.V s'.β s'.L) (comR R t).S
        (fun P d => c P (dualLab d)) := by
    intro u hu
    show PiTensorProduct.lift.symm (PiTensorProduct.lift u) ∈ _
    rw [LinearEquiv.symm_apply_apply]
    exact hmem u hu
  refine ⟨fun hne => ?_, fun u hu => ?_⟩
  · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    set y : s'.CC (comR R t) := ⟨PiTensorProduct.lift u, hCC u hu⟩ with hydef
    have hl0 : (y : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) ≠ 0 := by
      intro h
      exact hu0 (PiTensorProduct.lift.injective (h.trans (map_zero _).symm))
    obtain ⟨w, hw⟩ : ∃ w, PiLocalization₂.val y w ≠ 0 := by
      by_contra hh
      push_neg at hh
      exact hl0 (LinearMap.ext hh)
    obtain ⟨hl, hh, hb⟩ := hkey y (hy u hu) w
    have hne' : (fun g => conj (PiLocalization₂.val y w g)) ≠ 0 := by
      intro h
      apply hw
      funext g
      simpa using congrFun h g
    obtain ⟨B, hB, -⟩ := GlobalTheory.FinZeta.ParamBound.exists_param_bounded D s'.V _ _ (comR R t).S hsph' _ hb hne' hl c hh
    refine ⟨B, (hiff y (hy u hu) w B hw).1 ?_⟩
    unfold ParFun
    rw [hlat]
    exact hB
  · have hu' : PiTensorProduct.lift u ∈ (stY R t 0).CC (comR R t) := by
      refine (mem_multT _ _ _ _ _).2 ?_
      erw [LinearEquiv.symm_apply_apply]
      show u ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv))
        (Lev.levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv))
      rw [hJ, hχ]
      exact ((mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 hu).1).1
    refine ⟨hu', fun hu0 B hB => ⟨?_, fun w hw => ?_⟩⟩
    · intro h
      apply hu0
      have h1 : PiTensorProduct.lift u = 0 := congrArg Subtype.val h
      exact PiTensorProduct.lift.injective (h1.trans (map_zero _).symm)
    · exact (hiff ⟨PiTensorProduct.lift u, hCC u hu⟩ (hy u hu) w B hw).2 hB

end GlobalTheory.ChainTw
