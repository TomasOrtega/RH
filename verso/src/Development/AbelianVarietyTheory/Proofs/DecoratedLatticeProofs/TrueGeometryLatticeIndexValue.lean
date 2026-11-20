import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLocalGLEmbeddingSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeOpenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd.Supp

section Cut

open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut

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
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `Formalism.UG.prV (E := D.host.E) v (x.1 i j) = Formalism.UG.prV (E := D.host.E) v (y.1 i j)`. Rewrite using `[hx, hy]`. Simplify using `only [GlobalTheory.AdForm.finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]`.

Conclude with `prV_toEAf_congr v (e _ _)`.
-/
theorem bc_congr (V : HSp D) {n : ℕ} (hn : V.rank = n) (v : GlobalTheory.FinPl.Pl D) {g h : GA D V} {x y : GL (Fin n) (EF D)}
    (hx : x.1 = finM V hn g) (hy : y.1 = finM V hn h)
    (e : ∀ i j, GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V g i j) = GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V h i j)) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) y := by
  apply Units.ext
  ext i j
  change Formalism.UG.prV (E := D.host.E) v (x.1 i j) = Formalism.UG.prV (E := D.host.E) v (y.1 i j)
  rw [hx, hy]
  simp only [GlobalTheory.AdForm.finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  exact prV_toEAf_congr v (e _ _)

/- English proof (translation)
Establish `h1 : (1 : GL (Fin n) (EF D)).1 = finM V hn 1`. Substitute `hn` using the available equality. Rewrite using `[GlobalTheory.AdForm.CongAtIdem.finM_rfl, GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Both sides reduce to the same expression. Rewrite using `[bc_congr V hn v hx h1 fun i j => ?_, map_one]`.

Use `((mem_grpAt_iff_parts V P g).1 hg i j).2 v hv` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]`. Rewrite using `[this, GlobalTheory.SplitCut.mt_one]`.
-/
theorem bc_eq_one (V : HSp D) {n : ℕ} (hn : V.rank = n) {P : GlobalTheory.FinPl.Pl D → Prop} {v : GlobalTheory.FinPl.Pl D} (hv : ¬ P v) {g : GA D V}
    (hg : g ∈ grpAt V P) {x : GL (Fin n) (EF D)} (hx : x.1 = finM V hn g) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  have h1 : (1 : GL (Fin n) (EF D)).1 = finM V hn 1 := by
    subst hn
    rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl, GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  rw [bc_congr V hn v hx h1 fun i j => ?_, map_one]
  have := ((mem_grpAt_iff_parts V P g).1 hg i j).2 v hv
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at this
  rw [this, GlobalTheory.SplitCut.mt_one]

abbrev cutAt (V : HSp D) (v : GlobalTheory.FinPl.Pl D) : GA D V →* GA D V := cutG V _ (idemQ_mul_self {v})

/- English proof (translation)
The claim follows from `cutG_mem_Q V {v} g`.
-/
theorem cutAt_mem (V : HSp D) (v : GlobalTheory.FinPl.Pl D) (g : GA D V) : cutAt V v g ∈ grpAt V (· ∈ ({v} : Finset (GlobalTheory.FinPl.Pl D))) :=
  cutG_mem_Q V {v} g

/- English proof (translation)
Rewrite using `[mt_cutG, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, RingHom.map_add, RingHom.map_mul, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, (parts_idemQ {v}).2 v, if_pos (Finset.mem_singleton_self v), sub_self, zero_mul, one_mul, add_zero]`.
-/
theorem compAt_cutAt (V : HSp D) (v : GlobalTheory.FinPl.Pl D) (g : GA D V) (i j) :
    GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V (cutAt V v g) i j) = GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V g i j) := by
  rw [mt_cutG, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, RingHom.map_add, RingHom.map_mul,
    RingHom.map_mul, RingHom.map_sub, RingHom.map_one, (parts_idemQ {v}).2 v, if_pos (Finset.mem_singleton_self v), sub_self,
    zero_mul, one_mul, add_zero]

/- English proof (translation)
Introduce `g hg` and use `(mem_grpAt_iff_parts V Q g).2 fun i j => ⟨((mem_grpAt_iff_parts V P g).1 hg i j).1, fun w hw => ((mem_grpAt_iff_parts V P g).1 hg i j).2 w fun h' => hw (h w h')⟩`.
-/
theorem grpAt_mono (V : HSp D) {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, P v → Q v) : grpAt V P ≤ grpAt V Q := fun g hg =>
  (mem_grpAt_iff_parts V Q g).2 fun i j =>
    ⟨((mem_grpAt_iff_parts V P g).1 hg i j).1, fun w hw => ((mem_grpAt_iff_parts V P g).1 hg i j).2 w fun h' => hw (h w h')⟩

/- English proof (translation)
Establish `h` using `cutG_left V {v} (one_mem _) (grpAt_mono V (Q := (· ∉ ({v} : Finset (GlobalTheory.FinPl.Pl D)))) (fun w hw hm => hv (Finset.mem_singleton.1 hm ▸ hw)) hg)`. Rewrite `h` using `[one_mul]`. Then use the resulting hypothesis.
-/
theorem cutAt_eq_one (V : HSp D) {P : GlobalTheory.FinPl.Pl D → Prop} {v : GlobalTheory.FinPl.Pl D} (hv : ¬ P v) {g : GA D V} (hg : g ∈ grpAt V P) :
    cutAt V v g = 1 := by
  have h := cutG_left V {v} (one_mem _) (grpAt_mono V (Q := (· ∉ ({v} : Finset (GlobalTheory.FinPl.Pl D))))
    (fun w hw hm => hv (Finset.mem_singleton.1 hm ▸ hw)) hg)
  rwa [one_mul] at h

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨ε, hε, hE⟩` from `q.above`. Rewrite `hE` using `[GlobalTheory.SplitCut.eFin_of_placeIdem hε]`. Establish `e : q.e + cA D q.e = eQ D {q.v}`. Rewrite using `[hE]`. Unfold `eQ idemQ indQ`.

Rewrite using `[Finset.sum_singleton]`. Both sides reduce to the same expression. Introduce `i j`. Rewrite using `[e]`. Conclude with `congrFun (congrFun (smul_of_mem_Q V {q.v} (cutAt_mem V q.v g)) i) j`.
-/
theorem suppAt_cutAt (q : SplitPt D k) (V : HSp D) (g : GA D V) : SuppAt q.e V (cutAt V q.v g) := by
  obtain ⟨ε, hε, hE⟩ := q.above
  rw [GlobalTheory.SplitCut.eFin_of_placeIdem hε] at hE
  have e : q.e + cA D q.e = eQ D {q.v} := by
    rw [hE]
    unfold eQ idemQ indQ
    rw [Finset.sum_singleton]
    rfl
  intro i j
  rw [e]
  exact congrFun (congrFun (smul_of_mem_Q V {q.v} (cutAt_mem V q.v g)) i) j

/- English proof (translation)
Establish `h0 : cutG V _ (one_sub_idemQ_mul_self {q.v}) g ∈ grpOff V (· = q.v)` using `grpAt_le_grpOff V _ (· = q.v) (fun p hp e => hp (Finset.mem_singleton.2 e)) (cutG_mem_Qc V {q.v} hg)`. Establish `h2` using `GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q (P := (· = q.v)) rfl h0`. Establish `h3 : GlobalTheory.LevIdx.locHom q V F (cutG V _ (one_sub_idemQ_mul_self {q.v}) g) = 1`. Use `symm`. Rewrite using `[← GlobalTheory.LevIdx.eq_locHom_iff, h2]`.

Simplify using `[F.βγ]`. Use `conv_rhs => rw [← cutG_mul_cutG V {q.v} g, map_mul, h3, mul_one]`.
-/
theorem locHom_cutAt {Y : Type} [Fintype Y] [DecidableEq Y] (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y)
    {g : GA D V} (hg : g ∈ GfC V) : GlobalTheory.LevIdx.locHom q V F (cutAt V q.v g) = GlobalTheory.LevIdx.locHom q V F g := by
  have h0 : cutG V _ (one_sub_idemQ_mul_self {q.v}) g ∈ grpOff V (· = q.v) :=
    grpAt_le_grpOff V _ (· = q.v) (fun p hp e => hp (Finset.mem_singleton.2 e)) (cutG_mem_Qc V {q.v} hg)
  have h2 := GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q (P := (· = q.v)) rfl h0
  have h3 : GlobalTheory.LevIdx.locHom q V F (cutG V _ (one_sub_idemQ_mul_self {q.v}) g) = 1 := by
    symm
    rw [← GlobalTheory.LevIdx.eq_locHom_iff, h2]
    simp [F.βγ]
  conv_rhs => rw [← cutG_mul_cutG V {q.v} g, map_mul, h3, mul_one]

end Cut

section Level

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch : ℕ → Type} {A : TwDat I l Z u a Ch}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `ex` using `GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Take `⟨hC, κ, hκ⟩` from `(hA.U j hj β g).1 hg`. Use `⟨hC, fun v => (hA.U j hj β _).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (cutAt_mem _ v g), ?_⟩⟩` and prove the remaining obligations.

Take `⟨x, hx⟩` from `ex (cutAt _ v g)`. Use `⟨⟨x.1, ((A.K j hj β).lev.U_eq _).2 ⟨x.2, fun w => ?_⟩⟩, hx⟩` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[bc_congr _ _ w hx hκ (compAt_cutAt _ w g)]`.

Conclude with `(((A.K j hj β).lev.U_eq _).1 κ.2).2 w`. Rewrite using `[bc_eq_one _ _ (P := (· ∈ ({v} : Finset _))) (fun h => hw (Finset.mem_singleton.1 h)) (cutAt_mem _ v g) hx]`. Conclude with `one_mem _`. Introduce and unpack `⟨hC, h⟩`. Use `(hA.U j hj β _).2 ⟨hC, ?_⟩` and prove the remaining obligations.

Take `⟨x, hx⟩` from `ex g`. Use `⟨⟨x.1, ((A.K j hj β).lev.U_eq _).2 ⟨x.2, fun w => ?_⟩⟩, hx⟩` and prove the remaining obligations. Take `⟨-, κ, hκ⟩` from `(hA.U j hj β _).1 (h w)`. Rewrite using `[← bc_congr _ _ w hκ hx (compAt_cutAt _ w g)]`. Conclude with `(((A.K j hj β).lev.U_eq _).1 κ.2).2 w`.
-/
theorem mem_U_iff (hA : A.Is) (j : ℕ) (hj : j ≤ B.R.m) (β : Ch j) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :
    g ∈ A.U j β ↔ g ∈ GfC _ ∧ ∀ v, cutAt _ v g ∈ A.U j β := by
  have ex := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl
  constructor
  · intro hg
    obtain ⟨hC, κ, hκ⟩ := (hA.U j hj β g).1 hg
    refine ⟨hC, fun v => (hA.U j hj β _).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (cutAt_mem _ v g), ?_⟩⟩
    obtain ⟨x, hx⟩ := ex (cutAt _ v g)
    refine ⟨⟨x.1, ((A.K j hj β).lev.U_eq _).2 ⟨x.2, fun w => ?_⟩⟩, hx⟩
    by_cases hw : w = v
    · subst hw
      rw [bc_congr _ _ w hx hκ (compAt_cutAt _ w g)]
      exact (((A.K j hj β).lev.U_eq _).1 κ.2).2 w
    · rw [bc_eq_one _ _ (P := (· ∈ ({v} : Finset _))) (fun h => hw (Finset.mem_singleton.1 h)) (cutAt_mem _ v g) hx]
      exact one_mem _
  · rintro ⟨hC, h⟩
    refine (hA.U j hj β _).2 ⟨hC, ?_⟩
    obtain ⟨x, hx⟩ := ex g
    refine ⟨⟨x.1, ((A.K j hj β).lev.U_eq _).2 ⟨x.2, fun w => ?_⟩⟩, hx⟩
    obtain ⟨-, κ, hκ⟩ := (hA.U j hj β _).1 (h w)
    rw [← bc_congr _ _ w hκ hx (compAt_cutAt _ w g)]
    exact (((A.K j hj β).lev.U_eq _).1 κ.2).2 w

end Level

section Std

open Formalism.L2.Col Formalism.L2.Ker Formalism.UG GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

/- English proof (translation)
Establish `e : ∀ i j, p.fr P (Pi.single j 1) i = p'.fr P (Pi.single j 1) i` using `fun i j => (algebraMap E (P.1.adicCompletion E)).injective ((h.fr P i j).symm.trans ((e0 i j).trans (h'.fr P i j)))`. Apply `LinearEquiv.toLinearMap_injective` to reduce the goal to its premises. Use `LinearMap.pi_ext fun j x => ?_` and prove the remaining obligations. Establish `hs : (Pi.single j x : Sp E n) = x • Pi.single j 1`. Rewrite using `[← Pi.single_smul', smul_eq_mul, mul_one]`.

Simplify using `only [LinearEquiv.coe_coe]`. Rewrite using `[hs, map_smul, map_smul]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, e]`.
-/
theorem fr_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g g' : GL (Fin n) (AfE F E)}
    {p p' : DecoF E n ST SG Q} (h : IsPtOf hc g p) (h' : IsPtOf hc g' p') (P : Q)
    (e0 : ∀ i j, adAt F P.1 (g.1 i j) = adAt F P.1 (g'.1 i j)) : p.fr P = p'.fr P := by
  have e : ∀ i j, p.fr P (Pi.single j 1) i = p'.fr P (Pi.single j 1) i := fun i j =>
    (algebraMap E (P.1.adicCompletion E)).injective ((h.fr P i j).symm.trans ((e0 i j).trans (h'.fr P i j)))
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.pi_ext fun j x => ?_
  have hs : (Pi.single j x : Sp E n) = x • Pi.single j 1 := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  simp only [LinearEquiv.coe_coe]
  rw [hs, map_smul, map_smul]
  funext i
  simp only [Pi.smul_apply, e]

/- English proof (translation)
Use `GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat hc ST SG Q g' hg' fun P hP => ?_` and prove the remaining obligations. Set `f` to `p.fr ⟨P, hP⟩`. Use `⟨⟨LinearMap.toMatrix' f.toLinearMap, LinearMap.toMatrix' f.symm.toLinearMap, ?_, ?_⟩, fun r s => ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]`. Rewrite using `[← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]`.

Rewrite using `[e0 P hP, h.fr ⟨P, hP⟩ r s]`. Simplify using `only [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]`. Both sides reduce to the same expression.
-/
theorem exists_pt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g g' : GL (Fin n) (AfE F E)}
    {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (hg' : g' ∈ UAd hc n)
    (e0 : ∀ P ∈ Q, ∀ i j, adAt F P (g'.1 i j) = adAt F P (g.1 i j)) : ∃ p' : DecoF E n ST SG Q, IsPtOf hc g' p' := by
  refine GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat hc ST SG Q g' hg' fun P hP => ?_
  let f := p.fr ⟨P, hP⟩
  refine ⟨⟨LinearMap.toMatrix' f.toLinearMap, LinearMap.toMatrix' f.symm.toLinearMap, ?_, ?_⟩, fun r s => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
  · rw [e0 P hP, h.fr ⟨P, hP⟩ r s]
    simp only [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
    rfl

/- English proof (translation)
Establish `h1 : levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = (I.idx a).levG j (b.get hj)`. Unfold `levGAt`. Rewrite using `[← Idx.some_get b hj]`. Both sides reduce to the same expression. Establish `h2 : ∀ b', (I.idx a).levG j b' = colLevSym I.Ch j`.

Rewrite using `[(hTw a).2]`. Conclude with `fun _ => rfl`. Rewrite using `[h1, h2]`.
-/
theorem levGAt_eq (hTw : I.IsTw) (a : I.ι) (j : ℕ) (hj : j < B.R.m) (b : Idx I.sel (I.tup a) (I.idx a) j) :
    levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = colLevSym I.Ch j := by
  have h1 : levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = (I.idx a).levG j (b.get hj) := by
    unfold levGAt
    rw [← Idx.some_get b hj]
    rfl
  have h2 : ∀ b', (I.idx a).levG j b' = colLevSym I.Ch j := by
    rw [(hTw a).2]
    exact fun _ => rfl
  rw [h1, h2]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Take `⟨c, rfl⟩` from `hR.onto β`. Establish `hy0` using `hR.pt c`. Rewrite `hy0` using `[hβ]`. Establish `hy : IsPtOf B.sp.cm (y c * TC.kStd X u (B.R.N j)) ((I.stp u a j).rep c).1.1` using `IsPtOf.of_extTo (I.Q_subset_SQ a) ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)) hy0`. Establish `hg` using `dia_of_pt hPr u hy`.

Establish `hk : TC.kStd X u (B.R.N j) ∈ UAd B.sp.cm (B.R.N j)` using `(kStd_spec hPr u (B.R.N j)).1.choose_spec.1.uni`. Establish `e0 : ∀ P ∈ I.Q a, ∀ r s, adAt B.host.F P ((y c * x * TC.kStd X u (B.R.N j)).1 r s) = adAt B.host.F P ((y c * TC.kStd X u (B.R.N j)).1 r s)` using `fun P hP r s => by`. Establish `e : x.1.map (adAt B.host.F P) = 1` using `Matrix.ext (h1 P hP)`. Establish `e' : (y c * x * TC.kStd X u (B.R.N j)).1.map (adAt B.host.F P) = (y c * TC.kStd X u (B.R.N j)).1.map (adAt B.host.F P)`. Rewrite using `[Units.val_mul, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, e, Matrix.mul_one]`.

Conclude with `congrFun (congrFun e' r) s`. Take `⟨q, hq⟩` from `exists_pt hy (mul_mem (mul_mem hg.1 hx) hk) e0`. Establish `hfr : ∀ P, q.fr P = ((I.stp u a j).rep c).1.1.fr P` using `fun P => fr_eq hq hy P (e0 P.1 P.2)`. Establish `hxq` using `dia_of_pt hPr u hq`. Establish `hΛ` using `levGAt_eq I hTw a j (by omega) c.1`.

Establish `hcos : ∀ p p' : PtAt B.R I.sel (I.tup a) (I.cst a) u j, cosetIn p = cosetIn p'` using `fun p p' => by`. Establish `key : ∀ p : PtAt B.R I.sel (I.tup a) (I.cst a) u j, p.1.2 = ∅` using `fun p => by`. Use `p.2` as an intermediate fact. Rewrite `this` using `[ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) (by omega)]`. Conclude with `this`.

Use function extensionality and compare the values at `P`. Unfold `cosetIn`. Rewrite using `[key p, key p']`. Use extensionality with `z`. Simplify using the standard rewrite rules.

Rewrite using `[hR.lev c x q (by rw [hβ]; exact hq)]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨κ, h1, h2, -⟩`. Establish `e1 : κ.1 = 1` using `ufGL_inj B.sp.cm (B.R.N j) (h1.trans (map_one _).symm)`. Take `⟨hJ, hr⟩` from `red_of_act B.sp.cm (B.R.N j) (diaT (Pr := B.primes X) u) hg.1 hxq.1 κ.2.1.1 (by`.

Rewrite using `[hg.2, hxq.2, ← h2]`. Use `show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N j) × GLG B.fields.E (B.R.N j) (B.primes X).vGs) • _ = _`. Rewrite using `[e1]`. Use the proof step `rfl)`. Use `(mem_levU _ _ _ _ _).2 ⟨hJ, ?_⟩` and prove the remaining obligations.

Establish `key : ∀ (Λ' : LevFam B.fields.E B.fields.K (B.R.N j) (B.primes X).vGs), Λ' = colLevSym I.Ch j → ∀ g : Λ'.grp, g.1 ∈ (colLevSym I.Ch j).grp`. Introduce and unpack `_ rfl g`. Conclude with `g.2`. Rewrite using `[hr]`. Conclude with `inv_mem (key _ hΛ κ.2.1)`.

Introduce `hxU`. Establish `h2` using `act_of_mem B.sp.cm (B.R.N j) _ (diaT (Pr := B.primes X) u) hg.1 ⟨x, hxU⟩`. Rewrite `h2` using `[hg.2, hxq.2]`. Establish `hm : ((levRed B.sp.cm (B.R.N j) _ _ _ ⟨x, hxU⟩)⁻¹).1 ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j c.1).grp`. Rewrite using `[hΛ]`.

Conclude with `Subtype.property _`. Use `⟨(1, ⟨_, hm⟩, 1), map_one (ufGL B.host.E (B.R.N j)), ?_, hcos _ _⟩` and prove the remaining obligations. Use `Subtype.ext (Prod.ext h2.symm (funext fun P => ?_))` and prove the remaining obligations. Use `show (1 : _ ≃ₗ[B.fields.E] _) * ((I.stp u a j).rep c).1.1.fr P * (1 : _ ≃ₗ[B.fields.E] _) = q.fr P`. Rewrite using `[one_mul, mul_one, hfr]`.
-/
theorem mem_lev_iff (hI : I.Ok) (hTw : I.IsTw) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (j : ℕ) (hj : j + 1 < B.R.m)
    [NeZero (B.R.N j)] {Ch : Type} {chOf : (I.stp u a j).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N j) → B.host.E)} {U : Ch → Subgroup (TC.GA B (B.R.N j))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a j).Cl → TC.GA B (B.R.N j)} {st : ∀ c, (I.stp u a j).Stab c → GL (Fin (B.R.N j)) B.host.E}
    {k : Ch → TC.GA B (B.R.N j)} (hR : I.Reads u a j chOf Lb U chi y st k) (β : Ch) (hβ : k β = TC.kStd X u (B.R.N j))
    (x : TC.GA B (B.R.N j)) (hx : x ∈ UAd B.sp.cm (B.R.N j))
    (h1 : ∀ P ∈ I.Q a, ∀ r s, adAt B.host.F P (x.1 r s) = (1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) _) r s) :
    x ∈ U β ↔ x ∈ levU (F := B.host.F) B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs (colLevSym I.Ch j).grp := by
  obtain ⟨c, rfl⟩ := hR.onto β
  have hy0 := hR.pt c
  rw [hβ] at hy0
  have hy : IsPtOf B.sp.cm (y c * TC.kStd X u (B.R.N j)) ((I.stp u a j).rep c).1.1 :=
    IsPtOf.of_extTo (I.Q_subset_SQ a)
      ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)) hy0
  have hg := dia_of_pt hPr u hy
  have hk : TC.kStd X u (B.R.N j) ∈ UAd B.sp.cm (B.R.N j) := (kStd_spec hPr u (B.R.N j)).1.choose_spec.1.uni
  have e0 : ∀ P ∈ I.Q a, ∀ r s, adAt B.host.F P ((y c * x * TC.kStd X u (B.R.N j)).1 r s) =
      adAt B.host.F P ((y c * TC.kStd X u (B.R.N j)).1 r s) := fun P hP r s => by
    have e : x.1.map (adAt B.host.F P) = 1 := Matrix.ext (h1 P hP)
    have e' : (y c * x * TC.kStd X u (B.R.N j)).1.map (adAt B.host.F P) = (y c * TC.kStd X u (B.R.N j)).1.map (adAt B.host.F P) := by
      rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, e, Matrix.mul_one]
    exact congrFun (congrFun e' r) s
  obtain ⟨q, hq⟩ := exists_pt hy (mul_mem (mul_mem hg.1 hx) hk) e0
  have hfr : ∀ P, q.fr P = ((I.stp u a j).rep c).1.1.fr P := fun P => fr_eq hq hy P (e0 P.1 P.2)
  have hxq := dia_of_pt hPr u hq
  have hΛ := levGAt_eq I hTw a j (by omega) c.1
  have hcos : ∀ p p' : PtAt B.R I.sel (I.tup a) (I.cst a) u j, cosetIn p = cosetIn p' := fun p p' => by
    have key : ∀ p : PtAt B.R I.sel (I.tup a) (I.cst a) u j, p.1.2 = ∅ := fun p => by
      have := p.2
      rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) (by omega)] at this
      exact this
    funext P
    unfold cosetIn
    rw [key p, key p']
    ext z
    simp
  rw [hR.lev c x q (by rw [hβ]; exact hq)]
  constructor
  · rintro ⟨κ, h1, h2, -⟩
    have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N j) (h1.trans (map_one _).symm)
    obtain ⟨hJ, hr⟩ := red_of_act B.sp.cm (B.R.N j) (diaT (Pr := B.primes X) u) hg.1 hxq.1 κ.2.1.1 (by
      rw [hg.2, hxq.2, ← h2]
      show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N j) × GLG B.fields.E (B.R.N j) (B.primes X).vGs) • _ = _
      rw [e1]
      rfl)
    refine (mem_levU _ _ _ _ _).2 ⟨hJ, ?_⟩
    have key : ∀ (Λ' : LevFam B.fields.E B.fields.K (B.R.N j) (B.primes X).vGs), Λ' = colLevSym I.Ch j →
        ∀ g : Λ'.grp, g.1 ∈ (colLevSym I.Ch j).grp := by
      rintro _ rfl g
      exact g.2
    rw [hr]
    exact inv_mem (key _ hΛ κ.2.1)
  · intro hxU
    have h2 := act_of_mem B.sp.cm (B.R.N j) _ (diaT (Pr := B.primes X) u) hg.1 ⟨x, hxU⟩
    rw [hg.2, hxq.2] at h2
    have hm : ((levRed B.sp.cm (B.R.N j) _ _ _ ⟨x, hxU⟩)⁻¹).1 ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j c.1).grp := by
      rw [hΛ]
      exact Subtype.property _
    refine ⟨(1, ⟨_, hm⟩, 1), map_one (ufGL B.host.E (B.R.N j)), ?_, hcos _ _⟩
    refine Subtype.ext (Prod.ext h2.symm (funext fun P => ?_))
    show (1 : _ ≃ₗ[B.fields.E] _) * ((I.stp u a j).rep c).1.1.fr P * (1 : _ ≃ₗ[B.fields.E] _) = q.fr P
    rw [one_mul, mul_one, hfr]

end Std

section Main

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u}

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Establish `hj' : j ≤ B.R.m` using `by omega`. Rewrite using `[← mem_lev_iff I hW.tr.ok hW.tr.tw l.pr u _ j (by omega) (hJ.is.reads j hj') β (hJ.std j (by omega) β) x hxU fun Q hQ r s => ?_]`. Rewrite using `[hJ.is.U j hj']`. Use `⟨fun ⟨_, κ, hκ⟩ => ?_, fun h => ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hg, ⟨x, h⟩, hx⟩⟩` and prove the remaining obligations. Establish `e : x = κ.1` using `Units.ext (hx.trans hκ.symm)`.

Rewrite using `[e]`. Conclude with `κ.2`. Rewrite using `[hx]`. Use `GlobalTheory.FinMComp.adAt_finM_eq_one _ _ _ P g hg Q (fun h => hP _ h ?_) r s` and prove the remaining obligations. Take `⟨i, hi⟩` from `hJ.surj Q ((hW.tq.Q t Q).2 hQ)`.

Conclude with `⟨i, ((GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hTr t J hJ).2 i).trans (congrArg _ hi)⟩`.
-/
theorem mem_U_iff_std (hW : AllTrue W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 2 ≤ B.R.m) [NeZero (B.R.N j)] {t : W.P.T} (J : QJ a t)
    (hJ : J.Reads) (β : J.Ch₀ j) {P : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop} (hP : ∀ v, P v → ¬ twAt J v)
    {g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)} (hg : g ∈ GlobalTheory.FinPl.grpAt _ P) (x : TC.GA B (B.R.N j))
    (hxU : x ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N j)) (hx : x.1 = finM _ (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)) g) :
    g ∈ J.A.U j β ↔ x ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs
      (Formalism.L2.Col.colLevSym I.Ch j).grp := by
  have hj' : j ≤ B.R.m := by omega
  rw [← mem_lev_iff I hW.tr.ok hW.tr.tw l.pr u _ j (by omega) (hJ.is.reads j hj') β (hJ.std j (by omega) β) x hxU fun Q hQ r s => ?_]
  · rw [hJ.is.U j hj']
    refine ⟨fun ⟨_, κ, hκ⟩ => ?_, fun h => ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hg, ⟨x, h⟩, hx⟩⟩
    have e : x = κ.1 := Units.ext (hx.trans hκ.symm)
    rw [e]
    exact κ.2
  · rw [hx]
    refine GlobalTheory.FinMComp.adAt_finM_eq_one _ _ _ P g hg Q (fun h => hP _ h ?_) r s
    obtain ⟨i, hi⟩ := hJ.surj Q ((hW.tq.Q t Q).2 hQ)
    exact ⟨i, ((GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hTr t J hJ).2 i).trans (congrArg _ hi)⟩

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Establish `hj' : j ≤ B.R.m` using `by omega`. Use `haveI : NeZero (B.R.N j) := ⟨(B.R.N_pos j).ne'⟩`. Take `⟨hPins⟩` from `hW.tr.pins`. Establish `hg1 : gramN (I.rec7 l Z) j hj' = 1` using `((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hW.tr.ok hPins l Z).2.2.2 j hj').1`. Establish `eU : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj') (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) = Formalism.L2.Col.UAd B.sp.cm (B.R.N j)` using `by rw [hg1]; rfl`.

Take `⟨x, hx⟩` from `GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj') (gramN (I.rec7 l Z) j hj') rfl g`. Establish `hxU : x.1 ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N j)` using `eU ▸ x.2`. Conclude with `(mem_U_iff_std hW ha hTr j hj J' hJ' β' hP' hg x.1 hxU hx).2 ((mem_U_iff_std hW ha hTr j hj J hJ β hP hg x.1 hxU hx).1 h)`.
-/
theorem transfer (hW : AllTrue W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 2 ≤ B.R.m) {t t' : W.P.T} (J : QJ a t)
    (hJ : J.Reads) (β : J.Ch₀ j) (J' : QJ a t') (hJ' : J'.Reads) (β' : J'.Ch₀ j) {P : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop}
    (hP : ∀ v, P v → ¬ twAt J v) (hP' : ∀ v, P v → ¬ twAt J' v)
    {g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)} (hg : g ∈ GlobalTheory.FinPl.grpAt _ P) (h : g ∈ J.A.U j β) : g ∈ J'.A.U j β' := by
  have hj' : j ≤ B.R.m := by omega
  haveI : NeZero (B.R.N j) := ⟨(B.R.N_pos j).ne'⟩
  obtain ⟨hPins⟩ := hW.tr.pins
  have hg1 : gramN (I.rec7 l Z) j hj' = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hW.tr.ok hPins l Z).2.2.2 j hj').1
  have eU : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj') (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      Formalism.L2.Col.UAd B.sp.cm (B.R.N j) := by rw [hg1]; rfl
  obtain ⟨x, hx⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj') (gramN (I.rec7 l Z) j hj') rfl g
  have hxU : x.1 ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N j) := eU ▸ x.2
  exact (mem_U_iff_std hW ha hTr j hj J' hJ' β' hP' hg x.1 hxU hx).2 ((mem_U_iff_std hW ha hTr j hj J hJ β hP hg x.1 hxU hx).1 h)

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Take `⟨⟨hsup, hgf⟩, hphi⟩` from `Subgroup.mem_inf.1 hg |>.imp_left Subgroup.mem_inf.1`. Distinguish the cases in `hv : twAt J v`. Take `⟨i, rfl⟩` from `hv`. Take `⟨gl, -, h1, h2⟩` from `GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j) (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (Nat.le_succ_of_le (step_index_le_s J i hj)))`. Establish `hy : phi J j hj g i ∈ KO (J.G i).k _` using `(Subgroup.mem_pi _).1 (Subgroup.mem_comap.1 hphi) i (Set.mem_univ _)`.

Rewrite using `[h2 (cutAt _ (J.G i).q.v g) (phi J j hj g i) (suppAt_cutAt _ _ g) ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 (locHom_cutAt _ _ _ hgf).symm)]`. Conclude with `GlobalTheory.T.true_geometry_lattice_open W hW u a ha hTr j hj t' J' hJ' α' t J hJ i hv' gl h1 _ hy`. Establish `hle : J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (twAt J) ≤ (J.A.U j (J.ι j α)).comap (cutAt _ v)`. Use `sup_le (fun x hx => ((mem_U_iff hJ.is j (by omega) _ x).1 hx).2 v) fun x hx => ?_` and prove the remaining obligations. Rewrite using `[Subgroup.mem_comap, cutAt_eq_one _ hv hx]`.

Conclude with `one_mem _`. Conclude with `transfer hW ha hTr j hj J hJ _ J' hJ' _ (P := (· ∈ ({v} : Finset _))) (fun w hw h => hv (Finset.mem_singleton.1 hw ▸ h)) (fun w hw h => hv' (Finset.mem_singleton.1 hw ▸ h)) (cutAt_mem _ v g) (hle hsup)`.
-/
theorem cutAt_mem_U (hW : AllTrue W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 2 ≤ B.R.m) {t t' : W.P.T} (J : QJ a t)
    (hJ : J.Reads) (α : J.Ch j) (J' : QJ a t') (hJ' : J'.Reads) (α' : J'.Ch j)
    {g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)} (hg : g ∈ relax J j hj α) (v : GlobalTheory.FinPl.Pl (I.rec7 l Z)) (hv' : ¬ twAt J' v) :
    cutAt _ v g ∈ J'.A.U j (J'.ι j α') := by
  obtain ⟨⟨hsup, hgf⟩, hphi⟩ := Subgroup.mem_inf.1 hg |>.imp_left Subgroup.mem_inf.1
  by_cases hv : twAt J v
  · obtain ⟨i, rfl⟩ := hv
    obtain ⟨gl, -, h1, h2⟩ := GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j)
      (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (Nat.le_succ_of_le (step_index_le_s J i hj)))
    have hy : phi J j hj g i ∈ KO (J.G i).k _ := (Subgroup.mem_pi _).1 (Subgroup.mem_comap.1 hphi) i (Set.mem_univ _)
    rw [h2 (cutAt _ (J.G i).q.v g) (phi J j hj g i) (suppAt_cutAt _ _ g)
      ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 (locHom_cutAt _ _ _ hgf).symm)]
    exact GlobalTheory.T.true_geometry_lattice_open W hW u a ha hTr j hj t' J' hJ' α' t J hJ i hv' gl h1 _ hy
  · have hle : J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (twAt J) ≤ (J.A.U j (J.ι j α)).comap (cutAt _ v) := by
      refine sup_le (fun x hx => ((mem_U_iff hJ.is j (by omega) _ x).1 hx).2 v) fun x hx => ?_
      rw [Subgroup.mem_comap, cutAt_eq_one _ hv hx]
      exact one_mem _
    exact transfer hW ha hTr j hj J hJ _ J' hJ' _ (P := (· ∈ ({v} : Finset _)))
      (fun w hw h => hv (Finset.mem_singleton.1 hw ▸ h)) (fun w hw h => hv' (Finset.mem_singleton.1 hw ▸ h)) (cutAt_mem _ v g) (hle hsup)

end Main

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' α' g hg`. Establish `hgf : g ∈ GfC _` using `(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2`. Set `Q : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z))` to `Finset.univ.image fun i => (J'.G i).q.v`. Establish `hQ : ∀ v, v ∈ Q ↔ twAt J' v` using `fun v => by`. Simplify using `only [Q, Finset.mem_image, Finset.mem_univ, true_and]`.

Both sides reduce to the same expression. Establish `h1` using `GlobalTheory.FinPl.SetCut.cutG_mem_Q _ Q g`. Establish `h2` using `GlobalTheory.FinPl.SetCut.cutG_mem_Qc _ Q hgf`. Establish `e` using `GlobalTheory.FinPl.SetCut.cutG_mul_cutG _ Q g`. Generalize the expression as in `GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.idemQ_mul_self Q) g = g₁ at h1 e`.

Generalize the expression as in `GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.one_sub_idemQ_mul_self Q) g = g₂ at h2 e`. Establish `h3 : g₂ ∈ J'.A.U j (J'.ι j α')`. Use `(mem_U_iff hJ'.is j (by omega) _ g₂).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ h2, fun v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ Q`. Rewrite using `[cutAt_eq_one _ (P := (· ∉ Q)) (not_not.2 hv) h2]`.

Conclude with `one_mem _`. Establish `h4` using `cutAt_mem_U hW ha hTr j hj J hJ α J' hJ' α' hg v fun h => hv ((hQ v).2 h)`. Rewrite `h4` using `[← e, map_mul, cutAt_eq_one _ (P := (· ∈ Q)) hv h1, one_mul]`. Then use the resulting hypothesis. Rewrite using `[← e]`. Conclude with `mul_mem (Subgroup.mem_sup_right (grpAt_mono _ (fun v hv => (hQ v).1 hv) h1)) (Subgroup.mem_sup_left h3)`.
-/
theorem relax_mem_sup : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) t' (J' : QJ a t'), J'.Reads → ∀ (α' : J'.Ch j), ∀ g ∈ GlobalTheory.LevProd.relax J j hj α, g ∈ J'.A.U j (J'.ι j α') ⊔ GlobalTheory.FinPl.grpAt _ (GlobalTheory.LevProd.twAt J') := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' α' g hg
  have hgf : g ∈ GfC _ := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2
  let Q : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z)) := Finset.univ.image fun i => (J'.G i).q.v
  have hQ : ∀ v, v ∈ Q ↔ twAt J' v := fun v => by
    simp only [Q, Finset.mem_image, Finset.mem_univ, true_and]
    rfl
  have h1 := GlobalTheory.FinPl.SetCut.cutG_mem_Q _ Q g
  have h2 := GlobalTheory.FinPl.SetCut.cutG_mem_Qc _ Q hgf
  have e := GlobalTheory.FinPl.SetCut.cutG_mul_cutG _ Q g
  generalize GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.idemQ_mul_self Q) g = g₁ at h1 e
  generalize GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.one_sub_idemQ_mul_self Q) g = g₂ at h2 e
  have h3 : g₂ ∈ J'.A.U j (J'.ι j α') := by
    refine (mem_U_iff hJ'.is j (by omega) _ g₂).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ h2, fun v => ?_⟩
    by_cases hv : v ∈ Q
    · rw [cutAt_eq_one _ (P := (· ∉ Q)) (not_not.2 hv) h2]
      exact one_mem _
    · have h4 := cutAt_mem_U hW ha hTr j hj J hJ α J' hJ' α' hg v fun h => hv ((hQ v).2 h)
      rwa [← e, map_mul, cutAt_eq_one _ (P := (· ∈ Q)) hv h1, one_mul] at h4
  rw [← e]
  exact mul_mem (Subgroup.mem_sup_right (grpAt_mono _ (fun v hv => (hQ v).1 hv) h1)) (Subgroup.mem_sup_left h3)

end GlobalTheory.LevProd.Supp
end
