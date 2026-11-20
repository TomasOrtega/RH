import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationTwist
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel
noncomputable section
namespace GlobalTheory.LevelUnif
open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum GlobalTheory.SplitWeil GlobalTheory.SymChain
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
section Elem
variable {κ : Type} [CommRing κ] {r : ℕ}
end Elem
section Local
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)
  {PP : Pl D.host.E} (h : IsIdemAt q.e PP) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
end Local
section Levels
variable {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ}
end Levels
section Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word}
/- English proof (translation)
Establish `hid : ∀ i, IsIdemAt (G i).q.e (pl i).1` using `fun i => (hR.idem i).1`. Establish `hq : ∀ i, ∃ t : (G i).kˣ, IsUnif t ∧ (t : (G i).k) = ((Formalism.L2.Col.qOf (pl i).1 : ℕ) : (G i).k)` using `fun i => by`. Take `⟨-, hi, hd⟩` from `place_facts (G i).q (hid i)`. Take `⟨t, h1, h2⟩` from `GlobalTheory.WeilCondUnif.isUnif_of (pl i).1 ((G i).q.pr.comp (incA D)) hi hd (norm_notMem_sq (hP.1 _ (pl i).2))`. Conclude with `⟨t, h1, h2.trans (map_natCast _ _)⟩`.

Use `choose t ht htq using hq`. Use `choose α hα using fun i => exists_res (G i).q (hid i) (G i).S.cond (G i).S.unif`. Use `choose β hβ using fun i => exists_res (G i).q (hid i) (G i).S.cond (ht i)`. Take `⟨ψ₀, -, h0, π, hπ, hH, hχ⟩` from `W.Q.charW.base.grp.levels`. Establish `hk` using `D.R.m_add_three_le_k`.

Establish `hm` using `D.R.two_le_m`. Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hrS : D.R.rS = D.R.m / 2 - 1` using `rfl`. Establish `hA : ∀ c, ψ₀ (pl n).1 c = β n c` using `fun c => by`. Set `i : Fin D.R.r` to `⟨0, by omega⟩`.

Set `j : Fin D.R.r` to `⟨1, by omega⟩`. Establish `hij : i ≠ j` using `fun e => zero_ne_one (congrArg Fin.val e)`. Establish `hE : ∀ a : Fin D.R.r, ¬ supEdge a a` using `fun a h => by unfold supEdge at h; omega`. Set `x : G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r` to `Pi.mulSingle (pl n) (elem hij c)`. Establish `hx : x ∈ (P0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ψ₀).H` using `single_mem _ _ (unipCol_le _ 0 0 (elem_mem_unipCol hij zero_lt_one c 0 0 one_ne_zero))`.

Take `⟨hx', e1⟩` from `chi_of_eq h0 x hx`. Establish `e2 : (((P0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ψ₀).chi ⟨x, hx⟩ : ℂˣ) : ℂ) = ∏ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, ψ₀ PP.1 (edgeSum supEdge (x PP))`. Unfold `P0 LevelP.ofLocal`. Rewrite using `[MonoidHom.finsetProd_apply, Units.coe_prod]`. Both sides reduce to the same expression.

Establish `e3` using `W.Q.signs (fun PP => (G (pl.symm PP)).q.e) (fun PP => by`. Use `hid (pl.symm PP)` as an intermediate fact. Rewrite using `[pl.apply_symm_apply] at this) ⟨(_root_.GlobalTheory.Fam.pk_z W).eG.symm x, hx'⟩` and apply the resulting hypothesis. Establish `e4 : (((P0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ψ₀).chi ⟨x, hx⟩ : ℂˣ) : ℂ) = _` using `(congrArg Units.val e1).symm.trans e3`. Rewrite `e4` using `[e2, ← pl.prod_comp, ← pl.prod_comp, prod_single pl (fun m => ψ₀ (pl m).1) supEdge hE hij rfl]`.

Rewrite using `[e4, ← prod_single pl β supEdge hE hij rfl n c]`. Use `Finset.prod_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[pl.symm_apply_apply, psiAt_eq (G m).q (G m).char]`. Express the relevant statement in the definitionally equal form `_ = β m (edgeSum supEdge (x (pl m)))`. Rewrite using `[edgeSum_eq_supSum, ← Function.surjInv_eq Ideal.Quotient.mk_surjective (Formalism.IndefR.Mi.supSum (x (pl m)).val), ← hβ, Units.val_inv_eq_inv_val, htq, MulEquiv.apply_symm_apply]`.

Use `congrArg (fun y => ((G m).S.ψ y : ℂ)) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((G m).q.pr.comp (incA D)) _ = _`. Rewrite using `[map_mul, map_inv₀, map_natCast]`. Both sides reduce to the same expression. Establish `hC : ∀ c, ψ₀ (pl n).1 c = α n c` using `fun c => by`.

Set `i : Fin D.R.r` to `⟨D.R.rS, by omega⟩`. Set `j : Fin D.R.r` to `⟨D.R.rS + 1, by omega⟩`. Establish `hij : i ≠ j` using `fun e => by have := congrArg Fin.val e; simp [i, j] at this`. Establish `hE : ∀ a : Fin D.R.r, ¬ symEdge D.R.rS D.R.k a a` using `fun a h => by unfold symEdge at h; omega`. Establish `hEij : symEdge D.R.rS D.R.k i j` using `Or.inl ⟨rfl, by show D.R.rS + 1 ≠ _; omega, by show D.R.rS + 1 ≠ _; omega⟩`.

Set `y : G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r` to `Pi.mulSingle (pl n) (elem hij c)`. Establish `hy : y ∈ (PsharpSym (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r D.R.rS D.R.k ψ₀).H` using `single_mem _ _ (elem_mem_unipCol hij (Nat.lt_succ_self _) c _ _ (by show D.R.rS + 1 ≠ _; omega))`. Set `g : G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r` to `reord π.symm y`. Establish `hgy : ∀ PP a b, (y PP).val a b = (g PP).val (π a) (π b)` using `fun PP a b => by`. Express the relevant statement in the definitionally equal form `_ = (y PP).val (π.symm (π a)) (π.symm (π b))`.

Rewrite using `[π.symm_apply_apply, π.symm_apply_apply]`. Establish `hre : reord π g = y` using `funext fun PP => Units.ext (Matrix.ext fun a b => (hgy PP a b).symm)`. Establish `hg : g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H` using `(hH g).2 (hre ▸ hy)`. Use `choose x hx using (hR.lev g).1.1 hg`. Establish `e1` using `(hR.lev g).2 hg x hx`.

Establish `e2 : (_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨g, hg⟩ = (PsharpSym (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r D.R.rS D.R.k ψ₀).chi ⟨y, hy⟩` using `(hχ g hg (hre ▸ hy)).trans (congrArg _ (Subtype.ext hre))`. Establish `e3 : (((PsharpSym (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r D.R.rS D.R.k ψ₀).chi ⟨y, hy⟩ : ℂˣ) : ℂ) = ∏ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, ψ₀ PP.1 (edgeSum (symEdge D.R.rS D.R.k) (y PP))`. Unfold `PsharpSym LevelP.ofLocal`. Rewrite using `[MonoidHom.finsetProd_apply, Units.coe_prod]`. Both sides reduce to the same expression.

Rewrite `e3` using `[← e2, e1, ← pl.prod_comp, prod_single pl (fun m => ψ₀ (pl m).1) _ hE hij hEij, Units.coe_prod]`. Rewrite using `[← e3, ← prod_single pl α _ hE hij hEij n c]`. Use `Finset.prod_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `h1` using `(G m).hs`. Establish `h2` using `(G m).S.odd`.

Establish `hρ : D.R.rS = (G m).S.ρ` using `by omega`. Set `e : Fin D.R.k ⊕ Fin ((G m).s + 1) ≃ Fin D.R.r` to `finSumFinEquiv.trans (finCongr (by omega))`. Apply the tactic sequence `have he : ∀ a, (e a).val = framePos _ _ a := by rintro (a | a) <;> simp [e, framePos]`. Use `sym_chr (G m).S (prO (G m).q) e he (hρ ▸ hπ) (g (pl m)) (y (pl m)) (hgy _) (α m) (hα m) (x m) fun a b => hx m a b _ _ (he a) (he b)` as an intermediate fact. Rewrite `this` using `[← hρ]`.

Conclude with `this`. Rewrite using `[← htq]`. Conclude with `near_of_res (G n).q (hid n) (G n).S.cond (G n).S.unif (ht n) fun z => Circle.coe_injective ((hα n z).trans (((hC _).symm.trans (hA _)).trans (hβ n z).symm))`.
-/
theorem valuation_uniformizer_sub_q_lt (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) {v : VCom f.c} {N : ℕ} (G : Fin N → GLoc v) (pl : Fin N ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hR : _root_.GlobalTheory.Fam.LocalGroupReading f G pl)
    (hP : GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg) (n : Fin N) :
    valuation (G n).k ((((G n).S.ϖ : (G n).kˣ) : (G n).k) - ((Formalism.L2.Col.qOf (pl n).1 : ℕ) : (G n).k)) <
      valuation (G n).k (((G n).S.ϖ : (G n).kˣ) : (G n).k) := by
  have hid : ∀ i, IsIdemAt (G i).q.e (pl i).1 := fun i => (hR.idem i).1
  have hq : ∀ i, ∃ t : (G i).kˣ, IsUnif t ∧ (t : (G i).k) = ((Formalism.L2.Col.qOf (pl i).1 : ℕ) : (G i).k) := fun i => by
    obtain ⟨-, hi, hd⟩ := place_facts (G i).q (hid i)
    obtain ⟨t, h1, h2⟩ := GlobalTheory.WeilCondUnif.isUnif_of (pl i).1 ((G i).q.pr.comp (incA D)) hi hd (norm_notMem_sq (hP.1 _ (pl i).2))
    exact ⟨t, h1, h2.trans (map_natCast _ _)⟩
  choose t ht htq using hq
  choose α hα using fun i => exists_res (G i).q (hid i) (G i).S.cond (G i).S.unif
  choose β hβ using fun i => exists_res (G i).q (hid i) (G i).S.cond (ht i)
  obtain ⟨ψ₀, -, h0, π, hπ, hH, hχ⟩ := W.Q.charW.base.grp.levels
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hrS : D.R.rS = D.R.m / 2 - 1 := rfl
  have hA : ∀ c, ψ₀ (pl n).1 c = β n c := fun c => by
    let i : Fin D.R.r := ⟨0, by omega⟩
    let j : Fin D.R.r := ⟨1, by omega⟩
    have hij : i ≠ j := fun e => zero_ne_one (congrArg Fin.val e)
    have hE : ∀ a : Fin D.R.r, ¬ supEdge a a := fun a h => by unfold supEdge at h; omega
    let x : G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r := Pi.mulSingle (pl n) (elem hij c)
    have hx : x ∈ (P0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ψ₀).H :=
      single_mem _ _ (unipCol_le _ 0 0 (elem_mem_unipCol hij zero_lt_one c 0 0 one_ne_zero))
    obtain ⟨hx', e1⟩ := chi_of_eq h0 x hx
    have e2 : (((P0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ψ₀).chi ⟨x, hx⟩ : ℂˣ) : ℂ) = ∏ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, ψ₀ PP.1 (edgeSum supEdge (x PP)) := by
      unfold P0 LevelP.ofLocal
      rw [MonoidHom.finsetProd_apply, Units.coe_prod]
      rfl
    have e3 := W.Q.signs (fun PP => (G (pl.symm PP)).q.e) (fun PP => by
      have := hid (pl.symm PP)
      rwa [pl.apply_symm_apply] at this) ⟨(_root_.GlobalTheory.Fam.pk_z W).eG.symm x, hx'⟩
    have e4 : (((P0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ψ₀).chi ⟨x, hx⟩ : ℂˣ) : ℂ) = _ := (congrArg Units.val e1).symm.trans e3
    rw [e2, ← pl.prod_comp, ← pl.prod_comp, prod_single pl (fun m => ψ₀ (pl m).1) supEdge hE hij rfl] at e4
    rw [e4, ← prod_single pl β supEdge hE hij rfl n c]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [pl.symm_apply_apply, psiAt_eq (G m).q (G m).char]
    change _ = β m (edgeSum supEdge (x (pl m)))
    rw [edgeSum_eq_supSum, ← Function.surjInv_eq Ideal.Quotient.mk_surjective (Formalism.IndefR.Mi.supSum (x (pl m)).val), ← hβ,
      Units.val_inv_eq_inv_val, htq, MulEquiv.apply_symm_apply]
    refine congrArg (fun y => ((G m).S.ψ y : ℂ)) ?_
    change ((G m).q.pr.comp (incA D)) _ = _
    rw [map_mul, map_inv₀, map_natCast]
    rfl
  have hC : ∀ c, ψ₀ (pl n).1 c = α n c := fun c => by
    let i : Fin D.R.r := ⟨D.R.rS, by omega⟩
    let j : Fin D.R.r := ⟨D.R.rS + 1, by omega⟩
    have hij : i ≠ j := fun e => by have := congrArg Fin.val e; simp [i, j] at this
    have hE : ∀ a : Fin D.R.r, ¬ symEdge D.R.rS D.R.k a a := fun a h => by unfold symEdge at h; omega
    have hEij : symEdge D.R.rS D.R.k i j := Or.inl ⟨rfl, by show D.R.rS + 1 ≠ _; omega, by show D.R.rS + 1 ≠ _; omega⟩
    let y : G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r := Pi.mulSingle (pl n) (elem hij c)
    have hy : y ∈ (PsharpSym (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r D.R.rS D.R.k ψ₀).H :=
      single_mem _ _ (elem_mem_unipCol hij (Nat.lt_succ_self _) c _ _ (by show D.R.rS + 1 ≠ _; omega))
    let g : G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r := reord π.symm y
    have hgy : ∀ PP a b, (y PP).val a b = (g PP).val (π a) (π b) := fun PP a b => by
      change _ = (y PP).val (π.symm (π a)) (π.symm (π b))
      rw [π.symm_apply_apply, π.symm_apply_apply]
    have hre : reord π g = y := funext fun PP => Units.ext (Matrix.ext fun a b => (hgy PP a b).symm)
    have hg : g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := (hH g).2 (hre ▸ hy)
    choose x hx using (hR.lev g).1.1 hg
    have e1 := (hR.lev g).2 hg x hx
    have e2 : (_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨g, hg⟩ = (PsharpSym (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r D.R.rS D.R.k ψ₀).chi ⟨y, hy⟩ :=
      (hχ g hg (hre ▸ hy)).trans (congrArg _ (Subtype.ext hre))
    have e3 : (((PsharpSym (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r D.R.rS D.R.k ψ₀).chi ⟨y, hy⟩ : ℂˣ) : ℂ) =
        ∏ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, ψ₀ PP.1 (edgeSum (symEdge D.R.rS D.R.k) (y PP)) := by
      unfold PsharpSym LevelP.ofLocal
      rw [MonoidHom.finsetProd_apply, Units.coe_prod]
      rfl
    rw [← e2, e1, ← pl.prod_comp, prod_single pl (fun m => ψ₀ (pl m).1) _ hE hij hEij, Units.coe_prod] at e3
    rw [← e3, ← prod_single pl α _ hE hij hEij n c]
    refine Finset.prod_congr rfl fun m _ => ?_
    have h1 := (G m).hs
    have h2 := (G m).S.odd
    have hρ : D.R.rS = (G m).S.ρ := by omega
    let e : Fin D.R.k ⊕ Fin ((G m).s + 1) ≃ Fin D.R.r := finSumFinEquiv.trans (finCongr (by omega))
    have he : ∀ a, (e a).val = framePos _ _ a := by rintro (a | a) <;> simp [e, framePos]
    have := sym_chr (G m).S (prO (G m).q) e he (hρ ▸ hπ) (g (pl m)) (y (pl m)) (hgy _) (α m) (hα m) (x m)
      fun a b => hx m a b _ _ (he a) (he b)
    rw [← hρ] at this
    exact this
  rw [← htq]
  exact near_of_res (G n).q (hid n) (G n).S.cond (G n).S.unif (ht n) fun z =>
    Circle.coe_injective ((hα n z).trans (((hC _).symm.trans (hA _)).trans (hβ n z).symm))
end Gen
/- English proof (translation)
Introduce `B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ _ n`. Establish `hR` using `(ha.tie (fun t => (GlobalTheory.Fam.TopLocFac.nonempty_rowCh (D := I.rec7 l Z) _ _ u a.g W.Q.stdChar t).some) fun t => (GlobalTheory.Fam.TopLocFac.nonempty_colCh (D := I.rec7 l Z) u _).some).2`. Establish `h2` using `_root_.GlobalTheory.LevelUnif.valuation_uniformizer_sub_q_lt (D := I.rec7 l Z) _ _ _ hR hW.lev.1 n`. Conclude with `⟨(place_facts (a.G n).q (hR.idem n).1).2.1, h2⟩`.
-/
theorem int_and_unif_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ n : Fin a.n, (∀ x : (I.rec7 l Z).host.E, (ofSplit (a.G n).q).pr x ∈ 𝒪[(a.G n).k] ↔ Formalism.L2.Col.IntAt (a.pl n).1 x) ∧ valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k)) < valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ _ n
  have hR := (ha.tie (fun t => (GlobalTheory.Fam.TopLocFac.nonempty_rowCh (D := I.rec7 l Z) _ _ u a.g W.Q.stdChar t).some)
    fun t => (GlobalTheory.Fam.TopLocFac.nonempty_colCh (D := I.rec7 l Z) u _).some).2
  have h2 := _root_.GlobalTheory.LevelUnif.valuation_uniformizer_sub_q_lt (D := I.rec7 l Z) _ _ _ hR hW.lev.1 n
  exact ⟨(place_facts (a.G n).q (hR.idem n).1).2.1, h2⟩
end GlobalTheory.LevelUnif
end
end
