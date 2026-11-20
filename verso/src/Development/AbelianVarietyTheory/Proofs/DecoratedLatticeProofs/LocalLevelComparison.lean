import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepBeforeLastEqSSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProofStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelLocalGroupEqOfAgreeOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacesDvdNormIffUnderPrimesDvd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NeConjOfIdemSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelCharacterRepsOnAdelicUnitaryPoints
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLevPrime

section Comp

set_option synthInstance.maxHeartbeats 200000

variable {D : D7}

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero, map_zero, map_zero]`. Consider the case `tmul a e`. Rewrite using `[Algebra.TensorProduct.comm_tmul]`. Simplify using `only [Formalism.UG.prV, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]`.

Both sides reduce to the same expression. Consider the case `add a b ha hb`. Simplify using `only [map_add]`. Conclude with `congrArg₂ (· + ·) ha hb`.
-/
theorem prV_comm (v : GlobalTheory.FinPl.Pl D) (z : Af ↥D.host.F ⊗[↥D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) z) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.comm_tmul]
    simp only [Formalism.UG.prV, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
    rfl
  | add a b ha hb =>
    simp only [map_add]
    exact congrArg₂ (· + ·) ha hb

/- English proof (translation)
Unfold `GlobalTheory.FinPl.compAt at h`. Unfold `toEAf`. Simplify using `only [RingHom.comp_apply] at h ⊢`. Generalize the expression as in `finPart D y = z at h ⊢`. Generalize the expression as in `finPart D y' = z' at h ⊢`.

Use `(prV_comm v z).trans (Eq.trans ?_ (prV_comm v z').symm)` and prove the remaining obligations. Rewrite using `[h]`.
-/
theorem prV_toEAf_congr (v : GlobalTheory.FinPl.Pl D) {y y' : AE D} (h : GlobalTheory.FinPl.compAt D v y = GlobalTheory.FinPl.compAt D v y') :
    Formalism.UG.prV (E := D.host.E) v (toEAf D y) = Formalism.UG.prV (E := D.host.E) v (toEAf D y') := by
  unfold GlobalTheory.FinPl.compAt at h
  unfold toEAf
  simp only [RingHom.comp_apply] at h ⊢
  generalize finPart D y = z at h ⊢
  generalize finPart D y' = z' at h ⊢
  refine (prV_comm v z).trans (Eq.trans ?_ (prV_comm v z').symm)
  rw [h]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `Formalism.UG.prV (E := D.host.E) v (x.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j`. Substitute `hn` using the available equality. Establish `h` using `(GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts V P g).1 hg i j v hv`.

Rewrite `h` using `[Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]`. Establish `e : x.1 i j = toEAf D (Formalism.L2.Theta.mt V g i j)` using `by rw [hx]; rfl`. Rewrite using `[e, prV_toEAf_congr v h]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, map_one]`. Rewrite using `[Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, map_zero]`.
-/
theorem bc_eq_one_of_off (V : HSp D) {n : ℕ} (hn : V.rank = n) {P : GlobalTheory.FinPl.Pl D → Prop} {v : GlobalTheory.FinPl.Pl D} (hv : P v)
    {g : GA D V} (hg : g ∈ GlobalTheory.FinPl.grpOff V P) {x : GL (Fin n) (EF D)} (hx : x.1 = finM V hn g) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  apply Units.ext
  ext i j
  change Formalism.UG.prV (E := D.host.E) v (x.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j
  subst hn
  have h := (GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts V P g).1 hg i j v hv
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  have e : x.1 i j = toEAf D (Formalism.L2.Theta.mt V g i j) := by rw [hx]; rfl
  rw [e, prV_toEAf_congr v h]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, map_zero]

end Comp

section Level

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word}

/- English proof (translation)
Establish `hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u))` using `l.pr.piT_cop u`. Establish `hne : X.piT u ≠ 0`. Introduce `h0`. Rewrite `hcop` using `[h0, map_zero, isCoprime_zero_left]`. Conclude with `not_isUnit_zero hcop`.

Take `⟨w, hw, rfl⟩` from `(GlobalTheory.NormPlaces.places_dvd_iff (I.rec7 l Z) (X.piT u) (B.fields.conjO (X.piT u)) (B.T u) rfl (l.pr.piT_norm u) hne v).1 hv`. Take `⟨e, he⟩` from `hS.1`. Use `⟨e.symm ⟨w, hw⟩, ?_⟩` and prove the remaining obligations. Establish `h` using `he (e.symm ⟨w, hw⟩)`. Rewrite `h` using `[e.apply_symm_apply]`.

Conclude with `(GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under _ h).symm`.
-/
theorem exists_splitPt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k} {β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)}
    {Q : ∀ j, ι → GlobalTheory.LatPair.Pair k (Fin ((I.rec7 l Z).sp.X j).rank)} {L : ∀ j, GlobalTheory.FinPl.Lat ((I.rec7 l Z).sp.X j)}
    (hS : StdT I l Z u p β Q L) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))
    (hv : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) : ∃ i, v = (p i).v := by
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := l.pr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  obtain ⟨w, hw, rfl⟩ := (GlobalTheory.NormPlaces.places_dvd_iff (I.rec7 l Z) (X.piT u) (B.fields.conjO (X.piT u)) (B.T u) rfl
    (l.pr.piT_norm u) hne v).1 hv
  obtain ⟨e, he⟩ := hS.1
  refine ⟨e.symm ⟨w, hw⟩, ?_⟩
  have h := he (e.symm ⟨w, hw⟩)
  rw [e.apply_symm_apply] at h
  exact (GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under _ h).symm

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `h hh`. Take `⟨x, hxU, hxv⟩ : ∃ x ∈ (A.K j hj b).lev.U, Formalism.UG.bc (Formalism.UG.prV (E` from `(I.rec7 l Z).host.E) v) x = h := by`. Use `⟨Formalism.UG.P.afsplitU v h 1, ?_, Formalism.UG.P.afsplit_right1 v h 1⟩` and prove the remaining obligations. Rewrite using `[(A.K j hj b).lev.U_eq]`. Use `⟨Formalism.UG.P.afsplitU_mem v _ _ h 1 ((A.K j hj b).lev.Uloc_le v hh) (one_mem _), fun w => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hw : w = v`. Rewrite using `[hw, Formalism.UG.P.afsplit_right1 v h 1]`. Conclude with `hh`. Establish `hxw : Formalism.UG.bc (Formalism.UG.prV (E` using `(I.rec7 l Z).host.E) w) (Formalism.UG.P.afsplitU v h 1) = 1 := by`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw, Units.val_one, Units.val_one]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Rewrite using `[hxw]`. Conclude with `one_mem _`. Take `⟨g, hgC, hg⟩` from `GlobalTheory.ChartLevRead.exists_finM_GfC _ (rankN (I.rec7 l Z) j hj) ⟨x, (((A.K j hj b).lev.U_eq x).1 hxU).1⟩`.

Establish `hgU : g ∈ A.U j b` using `(hA.U j hj b g).2 ⟨hgC, ⟨x, hxU⟩, hg.symm⟩`. Take `⟨g', hg', κ', hκ', hκe⟩` from `(GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hOk hP l Z u a Ch A hA k ι p β Q L hS J hn hall j hj b).2 g hgU`. Establish `hst` using `(GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hOk hP l Z u a' Ch' A' hA' k ι p β Q L hS J hn hall j hj b').1`. Establish `hprod : (J.map fun i => (β j i).gl (g' i)).prod ∈ A'.U j b'` using `Subgroup.list_prod_mem _ fun y hy => by`. Take `⟨i, -, rfl⟩` from `List.mem_map.1 hy`.

Conclude with `(hst i _ (hg' i)).1`. Take `⟨-, y, hy⟩` from `(hA'.U j hj b' _).1 hprod`. Take `⟨z, hz⟩` from `GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl κ'`. Establish `e : x = y.1 * z.1`. Apply `Units.ext` to reduce the goal to its premises.

Establish `hg2 : finM _ (rankN (I.rec7 l Z) j hj) g = x.1` using `hg`. Rewrite using `[Units.val_mul, hy, hz, ← hg2, hκe]`. Conclude with `GlobalTheory.AdForm.StabMove.finM_mul _ _ _ _`. Establish `hz1` using `bc_eq_one_of_off _ (rankN (I.rec7 l Z) j hj) (v := v) hv hκ' hz`. Rewrite using `[← hxv, e, map_mul, hz1, mul_one]`.

Conclude with `(((A'.K j hj b').lev.U_eq _).1 y.2).2 v`.
-/
theorem uloc_le_of_std (hOk : I.Ok) (hP : TC.Pins B X) {a a' : I.ι} {Ch Ch' : ℕ → Type} {A : TwDat I l Z u a Ch}
    {A' : TwDat I l Z u a' Ch'} (hA : A.Is) (hA' : A'.Is)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k} {β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)}
    {Q : ∀ j, ι → GlobalTheory.LatPair.Pair k (Fin ((I.rec7 l Z).sp.X j).rank)} {L : ∀ j, GlobalTheory.FinPl.Lat ((I.rec7 l Z).sp.X j)}
    (hS : StdT I l Z u p β Q L) (J : List ι) (hn : J.Nodup) (hall : ∀ i, i ∈ J) (j : ℕ) (hj : j ≤ B.R.m) (b : Ch j) (b' : Ch' j)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ∃ i, v = (p i).v) :
    (A.K j hj b).lev.Uloc v ≤ (A'.K j hj b').lev.Uloc v := by
  intro h hh
  obtain ⟨x, hxU, hxv⟩ : ∃ x ∈ (A.K j hj b).lev.U, Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) x = h := by
    refine ⟨Formalism.UG.P.afsplitU v h 1, ?_, Formalism.UG.P.afsplit_right1 v h 1⟩
    rw [(A.K j hj b).lev.U_eq]
    refine ⟨Formalism.UG.P.afsplitU_mem v _ _ h 1 ((A.K j hj b).lev.Uloc_le v hh) (one_mem _), fun w => ?_⟩
    by_cases hw : w = v
    · rw [hw, Formalism.UG.P.afsplit_right1 v h 1]; exact hh
    · have hxw : Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) w) (Formalism.UG.P.afsplitU v h 1) = 1 := by
        apply Units.ext
        rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw,
          Units.val_one, Units.val_one]
        exact Matrix.map_one _ (map_zero _) (map_one _)
      rw [hxw]; exact one_mem _
  obtain ⟨g, hgC, hg⟩ := GlobalTheory.ChartLevRead.exists_finM_GfC _ (rankN (I.rec7 l Z) j hj) ⟨x, (((A.K j hj b).lev.U_eq x).1 hxU).1⟩
  have hgU : g ∈ A.U j b := (hA.U j hj b g).2 ⟨hgC, ⟨x, hxU⟩, hg.symm⟩
  obtain ⟨g', hg', κ', hκ', hκe⟩ := (GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hOk hP l Z u a Ch A hA k ι p β Q L hS J hn hall j hj b).2 g hgU
  have hst := (GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hOk hP l Z u a' Ch' A' hA' k ι p β Q L hS J hn hall j hj b').1
  have hprod : (J.map fun i => (β j i).gl (g' i)).prod ∈ A'.U j b' := Subgroup.list_prod_mem _ fun y hy => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact (hst i _ (hg' i)).1
  obtain ⟨-, y, hy⟩ := (hA'.U j hj b' _).1 hprod
  obtain ⟨z, hz⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl κ'
  have e : x = y.1 * z.1 := by
    apply Units.ext
    have hg2 : finM _ (rankN (I.rec7 l Z) j hj) g = x.1 := hg
    rw [Units.val_mul, hy, hz, ← hg2, hκe]
    exact GlobalTheory.AdForm.StabMove.finM_mul _ _ _ _
  have hz1 := bc_eq_one_of_off _ (rankN (I.rec7 l Z) j hj) (v := v) hv hκ' hz
  rw [← hxv, e, map_mul, hz1, mul_one]
  exact (((A'.K j hj b').lev.U_eq _).1 y.2).2 v

end Level

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' α' v hv`. Use `letI : Field a.k := a.fld`. Use `letI : ValuativeRel a.k := a.val`. Use `letI : TopologicalSpace a.k := a.top`. Use `letI : IsNonarchimedeanLocalField a.k := a.loc`.

Conclude with `uloc_le_of_std hW.tr.ok hW.tr.pins.some hJ.is hJ'.is hTr.std a.o.I ha.shape.pre.nodup ha.shape.pre.all j _ _ _ v (exists_splitPt hTr.std v hv)`.
-/
theorem uloc_le_levelPrime : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) t' (J' : QJ a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' α' v hv
  letI : Field a.k := a.fld
  letI : ValuativeRel a.k := a.val
  letI : TopologicalSpace a.k := a.top
  letI : IsNonarchimedeanLocalField a.k := a.loc
  exact uloc_le_of_std hW.tr.ok hW.tr.pins.some hJ.is hJ'.is hTr.std a.o.I ha.shape.pre.nodup ha.shape.pre.all j _ _ _ v
    (exists_splitPt hTr.std v hv)

end GlobalTheory.PenLevPrime
end
