import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrXLeKOOfPrCat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLocalGLEmbeddingSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeImagePointOfLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcPrVEqOneOfAdAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd.Bwd

section Dense
open Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.RootEx GlobalTheory.TwBridge ValuativeRel

/- English proof (translation)
Establish `hLev` using `GlobalTheory.TwBridge.Lev.levelAgree X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hat`. Take `⟨e, he, hge⟩` from `hg`. Establish `hcc : cOf R j = c + 1` using `by unfold cOf; have := hat.steps; omega`. Establish `heR : ∀ i : Fin (c + 1), (e (Sum.inr i)).val = R.N j + i.val` using `fun i => he (Sum.inr i)`. Establish `hgφ : g = GlobalTheory.VolBridge.locHom ι e γ` using `Units.ext hge`.

Establish `hreg : (W.T s R).Regular` using `Chain.ofTwist_regular _ _ _ _ _`. Take `⟨hJo, -, -⟩` from `hreg.2.2 j (c + 1) h`. Use `set J := ((W.T s R).lev j (c + 1) h).J with hJdef`. Use `set φ := GlobalTheory.VolBridge.locHom ι e with hφ`. Establish `hcompl` using `hat.compl`.

Establish `hIsGL : ∀ x : AutY X R j, IsGL ι (γ⁻¹ * x * γ) (g⁻¹ * φ x * g)`. Introduce `x`. Use `⟨e, he, ?_⟩` and prove the remaining obligations. Rewrite using `[hgφ, ← map_inv, ← map_mul, ← map_mul]`. Both sides reduce to the same expression.

Establish `hC : ∀ x : AutY X R j, x ∈ Loc.Cbe (Jat (Pr` using `Pr) cst.sharp j P.1) γ ↔ φ x ∈ Cgrp J g := by`. Introduce `x`. Rewrite using `[mem_Cgrp, ← GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι e hcc heR x, (hLev j (c + 1) h _ _ (hIsGL x)).1]`. Simplify using `[Loc.Cbe, Subgroup.mem_comap, MulAut.conj_apply]`. Establish `hN1` using `GlobalTheory.UnipRead.mem_N1_iff_local_hom ι e hcc heR`.

Establish `hdN` using `GlobalTheory.VolBridge.exists_N1_local_hom_mem_open ι hcompl.dense e hcc heR`. Establish `hord : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos (GlobalTheory.VolBridge.eX e hcc heR)` using `fun a => he (Sum.inl a)`. Use `set e' := GlobalTheory.VolBridge.eX e hcc heR with he'`. Use `set φ' := GlobalTheory.VolBridge.locHom ι e' with hφ'`. Establish `hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J}` using `hJo.preimage (by fun_prop)`.

Establish `hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1, z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J}` using `fun z hz => by`. Simplify using `[mem_Cgrp, hz]`. Establish `hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1` using `fun z hz => (mem_Cgrp.1 hz).1`. Establish `hP : ∀ y, y ∈ prCat (Pr` using `Pr) cst.sharp j P.1 γ ↔ φ' y ∈ GlobalTheory.StepData.prX (Cgrp J g) := GlobalTheory.VolBridge.prX_iff_locHom ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC`. Establish `hpo : IsOpen (GlobalTheory.StepData.prX (Cgrp J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k))` using `GlobalTheory.OpenPr.isOpen_prX _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO)`.

Introduce `z hz`. Establish `hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j) k | v⁻¹ * z ∈ ((GlobalTheory.StepData.prX (Cgrp J g) ⊓ K : Subgroup _) : Set _)}` using `(hpo.inter hKo).preimage (by fun_prop)`. Take `⟨y, hy⟩` from `GlobalTheory.denseGL_completion ι hcompl.dense e' z _ hV (by simp [one_mem, hz])`. Establish `hy1 : (φ' y)⁻¹ * z ∈ GlobalTheory.StepData.prX (Cgrp J g)` using `hy.1`. Establish `hy2 : (φ' y)⁻¹ * z ∈ K` using `hy.2`.

Establish `hyC : φ' y ∈ GlobalTheory.StepData.prX (Cgrp J g)`. Use `mul_mem hz (inv_mem hy1)` as an intermediate fact. Simplify using `using this`. Establish `hyK : φ' y ∈ K` using `hle e' hord y ((hP y).2 hyC)`. Use `mul_mem hyK hy2` as an intermediate fact.

Simplify using `using this`.
-/
theorem prX_le_of_prCat (X : Formalism.L2.Col.Fields) (Pr : Formalism.L2.Col.Primes X) (R : Ranks) (Ch : Formalism.L2.Col.Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀)
    (cst : Formalism.L2.Col.LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (hok : cst.Ok) (hat : AtTwist (R := R) sel mu cst σ₀ P ι s W)
    (j c : ℕ) (h : j + (c + 1) = s + 1) (γ : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)
    (hg : IsGL ι γ g) (K : Subgroup (GL (XIx (Fin R.k) (Fin R.t) j) k))
    (hKo : IsOpen (K : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)))
    (hle : ∀ e' : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' →
      ∀ y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ, GlobalTheory.VolBridge.locHom ι e' y ∈ K) :
    GlobalTheory.StepData.prX (Cgrp ((W.T s R).lev j (c + 1) h).J g) ≤ K := by
  have hLev := GlobalTheory.TwBridge.Lev.levelAgree X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hat
  obtain ⟨e, he, hge⟩ := hg
  have hcc : cOf R j = c + 1 := by unfold cOf; have := hat.steps; omega
  have heR : ∀ i : Fin (c + 1), (e (Sum.inr i)).val = R.N j + i.val := fun i => he (Sum.inr i)
  have hgφ : g = GlobalTheory.VolBridge.locHom ι e γ := Units.ext hge
  have hreg : (W.T s R).Regular := Chain.ofTwist_regular _ _ _ _ _
  obtain ⟨hJo, -, -⟩ := hreg.2.2 j (c + 1) h
  set J := ((W.T s R).lev j (c + 1) h).J with hJdef
  set φ := GlobalTheory.VolBridge.locHom ι e with hφ
  have hcompl := hat.compl
  have hIsGL : ∀ x : AutY X R j, IsGL ι (γ⁻¹ * x * γ) (g⁻¹ * φ x * g) := by
    intro x
    refine ⟨e, he, ?_⟩
    rw [hgφ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hC : ∀ x : AutY X R j, x ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ↔ φ x ∈ Cgrp J g := by
    intro x
    rw [mem_Cgrp, ← GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι e hcc heR x, (hLev j (c + 1) h _ _ (hIsGL x)).1]
    simp [Loc.Cbe, Subgroup.mem_comap, MulAut.conj_apply]
  have hN1 := GlobalTheory.UnipRead.mem_N1_iff_local_hom ι e hcc heR
  have hdN := GlobalTheory.VolBridge.exists_N1_local_hom_mem_open ι hcompl.dense e hcc heR
  have hord : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos (GlobalTheory.VolBridge.eX e hcc heR) := fun a => he (Sum.inl a)
  set e' := GlobalTheory.VolBridge.eX e hcc heR with he'
  set φ' := GlobalTheory.VolBridge.locHom ι e' with hφ'
  have hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
    hJo.preimage (by fun_prop)
  have hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1,
      z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J} := fun z hz => by
    simp [mem_Cgrp, hz]
  have hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := fun z hz => (mem_Cgrp.1 hz).1
  have hP : ∀ y, y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ ↔ φ' y ∈ GlobalTheory.StepData.prX (Cgrp J g) :=
    GlobalTheory.VolBridge.prX_iff_locHom ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC
  have hpo : IsOpen (GlobalTheory.StepData.prX (Cgrp J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)) :=
    GlobalTheory.OpenPr.isOpen_prX _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO)
  intro z hz
  have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j) k |
      v⁻¹ * z ∈ ((GlobalTheory.StepData.prX (Cgrp J g) ⊓ K : Subgroup _) : Set _)} :=
    (hpo.inter hKo).preimage (by fun_prop)
  obtain ⟨y, hy⟩ := GlobalTheory.denseGL_completion ι hcompl.dense e' z _ hV (by simp [one_mem, hz])
  have hy1 : (φ' y)⁻¹ * z ∈ GlobalTheory.StepData.prX (Cgrp J g) := hy.1
  have hy2 : (φ' y)⁻¹ * z ∈ K := hy.2
  have hyC : φ' y ∈ GlobalTheory.StepData.prX (Cgrp J g) := by
    have := mul_mem hz (inv_mem hy1); simpa using this
  have hyK : φ' y ∈ K := hle e' hord y ((hP y).2 hyC)
  have := mul_mem hyK hy2; simpa using this

end Dense

/- English proof (translation)
Establish `h1 : q.e * z = q.e * incA D x` using `by rw [← q.sec_pr, ← q.sec_pr, h]`. Establish `h2` using `congrArg (fun w => GlobalTheory.StdFrames.cpt PP (toEAf D w)) h1`. Simplify using `only [RingHom.map_mul, (GlobalTheory.StdFrames.cpt_of_isIdemAt he).1, one_mul] at h2`. Rewrite using `[← GlobalTheory.SplitProj.cpt_eq_adAt, h2]`. Conclude with `(GlobalTheory.SplitProj.cpt_eq_adAt PP _).trans (GlobalTheory.Mem.Col2.adAt_inclE D.host.F PP x)`.
-/
theorem adAt_eq_of_pr {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)) (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (z : Formalism.L2.Theta.AE D) (x : D.host.E) (h : q.pr z = q.pr (incA D x)) :
    adAt D.host.F PP (toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x := by
  have h1 : q.e * z = q.e * incA D x := by rw [← q.sec_pr, ← q.sec_pr, h]
  have h2 := congrArg (fun w => GlobalTheory.StdFrames.cpt PP (toEAf D w)) h1
  simp only [RingHom.map_mul, (GlobalTheory.StdFrames.cpt_of_isIdemAt he).1, one_mul] at h2
  rw [← GlobalTheory.SplitProj.cpt_eq_adAt, h2]
  exact (GlobalTheory.SplitProj.cpt_eq_adAt PP _).trans (GlobalTheory.Mem.Col2.adAt_inclE D.host.F PP x)

section Rat
open Formalism.L2.Col Formalism.UG
attribute [local instance] GlobalTheory.Mem.Col2.starE

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hj' : j ≤ B.R.m` using `by omega`. Establish `hjm : j < B.R.m` using `by omega`. Establish `hL` using `hI.idx_ok a`. Establish `hR` using `hA.reads j hj'`. Take `⟨c, rfl⟩` from `hA.chOf_onto j hj' β`.

Establish `hc` using `(hA.rep j hj' c).1`. Rewrite `hg` using `[← hc]`. Establish `hPQ : P.1 ∈ I.Q a` using `(@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP`. Take `⟨hLev, hdisj, -⟩` from `GlobalTheory.Mem.LevTwist.levOk_twists B X I hI`. Establish `hd : Disjoint (B.primes X).vGs (I.Q a)` using `Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) hdisj`.

Establish `hp` using `IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)`. Take `⟨pk, hpk, -⟩` from `hR.k_std (A.chOf j c)`. Establish `hv : Formalism.L2.Col.IsOver (P.1.under (𝓞 B.host.F)) P.1` using `rfl`. Establish `hgI : g ∈ GLint B.fields.E (B.R.N j) P.1` using `hL.int j _ P hg`. Establish `hT` using `(GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad I hI l u a (P.1.under (𝓞 B.host.F)) ⟨P.1, hPQ, rfl⟩).1`.

Establish `hk1 : bc (prV (E` using `B.host.E) (P.1.under (𝓞 B.host.F))) (A.kb j (A.chOf j c)) = 1 := by`. Rewrite using `[hβ]`. Conclude with `(GlobalTheory.Mem.Col2.MemChart.kStd_spec (X := X) l.pr u (B.R.N j)).2.1 _ hT`. Set `cc : GLQ B.fields.E (B.R.N j) (I.Q a)` to `Pi.mulSingle (⟨P.1, hPQ⟩ : I.Q a) (⟨g, hgI⟩⁻¹ : GLint B.fields.E (B.R.N j) P.1)`. Establish `hccP : cc ⟨P.1, hPQ⟩ = (⟨g, hgI⟩⁻¹ : GLint B.fields.E (B.R.N j) P.1)` using `Pi.mulSingle_eq_same _ _`.

Establish `hccO : ∀ P'' : I.Q a, P''.1 ≠ P.1 → cc P'' = 1` using `fun P'' h => Pi.mulSingle_eq_of_ne (fun e => h (congrArg Subtype.val e)) _`. Establish `hb : c.1 = Idx.of (c.1.get hjm) hjm` using `(Idx.of_get c.1 hjm _).symm`. Establish `hcc : cc ∈ (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) j c.1).grp`. Rewrite using `[hb]`. Introduce `P'' _`.

Distinguish the cases in `h : P''.1 = P.1`. Take `rfl : P'' = ⟨P.1, hPQ⟩` from `Subtype.ext h show cc ⟨P.1, hPQ⟩ ∈ ((I.idx a).levQ j (c.1.get hjm) ⟨P.1, hPQ⟩).H`. Rewrite using `[hccP, hL.grpQ]`. Conclude with `inv_mem (Subgroup.mem_subgroupOf.2 hg)`. Use `show cc P'' ∈ ((I.idx a).levQ j (c.1.get hjm) P'').H`.

Rewrite using `[hccO P'' h]`. Conclude with `one_mem _`. Set `κ : (I.stp u a j).G c.1` to `(1, 1, ⟨cc, hcc⟩)`. Establish `hPu : P.1 ∈ uSG (B.primes X).vGs I.SQ`. Simplify using `only [uSG, Finset.mem_union]`.

Conclude with `Or.inr (ColIn.Q_subset_SQ I a hPQ)`. Establish `key` using `GlobalTheory.Mem.Col2.LevLiftPt.core B.sp.cm hp hx hpk.uni _ P.1 hv hoff g hgI (fun r s => by`. Establish `e : bc (prV (E` using `B.host.E) (P.1.under (𝓞 B.host.F))) ((A.kb j (A.chOf j c))⁻¹ * x * A.kb j (A.chOf j c)) = bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) x := by`. Rewrite using `[map_mul, map_mul, map_inv, hk1, inv_one, one_mul, mul_one]`. Conclude with `(GlobalTheory.Mem.Col2.ChTwRead.adAt_congr_prV P.1 (congrArg (fun m => m.1 r s) e)).trans (hpt r s))`.

Use the proof step `(GlobalTheory.Mem.Col2.LevLiftPt.vT_notOver I hI a P _ hv u) (fun w hw hwv => by`. Establish `hw' : w ∈ uSG (B.primes X).vGs I.SQ`. Simplify using `only [uSG, Finset.mem_union]`. Break down `hw with h | h` into its components or cases. Conclude with `Or.inl h`.

Conclude with `Or.inr (ColIn.Q_subset_SQ I a h)`. Break down `rll_over_cases B.sp.cm hv hwv with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (h ▸ hw') (hLev.split P.1 hPu))`. Use `1 cc (fun h => absurd h hP) (fun w _ y _ => by simp) (fun _ => by rw [hccP, inv_inv])`.

Use the proof step `(fun P'' h => by rw [hccO P'' h, inv_one]; rfl)`. Establish `e` using `GlobalTheory.Mem.Col2.LevLiftPt.mul_conj (G := TC.GA B (B.R.N j)) ((A.K j hj' (A.chOf j c)).y ⟨c, rfl⟩).1 x (A.kb j (A.chOf j c))`. Establish `hq : TC.PtOf ((show TC.GA B (B.R.N j) from ((A.K j hj' (A.chOf j c)).y ⟨c, rfl⟩).1) * x * A.kb j (A.chOf j c)) ((I.stp u a j).act c.1 κ ((I.stp u a j).rep c)).1.1` using `e ▸ key`. Use `(hR.lev c x _ hq).2 ⟨κ, map_one (ufGL B.fields.E (B.R.N j)), rfl, ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ p : PtAt B.R I.sel (I.tup a) (I.cst a) u j, p.1.2 = ∅` using `fun p => by`.

Use `p.2` as an intermediate fact. Rewrite `this` using `[ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) (by omega)]`. Conclude with `this`. Use function extensionality and compare the values at `P'`. Simplify using `only [cosetIn, h0, Set.mem_empty_iff_false, false_and, exists_false]`.
-/
theorem mem_lev_of_rat {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) {Ch : ℕ → Type} (A : TwDat I l Z u a Ch) (hA : A.Is) (j : ℕ) (hj : j + 2 ≤ B.R.m) (β : Ch j)
    (hβ : A.kb j β = TC.kStd X u (B.R.N j)) (P : rowSG (B.primes X) I.sel (I.tup a)) (hP : P.1 ∉ (B.primes X).vGs)
    (x : TC.GA B (B.R.N j)) (hx : x ∈ UAd B.sp.cm (B.R.N j))
    (hoff : ∀ v', v' ≠ P.1.under (𝓞 B.host.F) → bc (prV (E := B.host.E) v') x = 1)
    (g : Sp B.fields.E (B.R.N j) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N j))
    (hg : g ∈ prCat (Pr := B.primes X) (I.cst a).sharp j P.1 ((I.idx a).h j ((A.b0 j β).get (by omega)) P))
    (hpt : ∀ r s, adAt B.host.F P.1 (x.1 r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) (g (Pi.single s 1) r)) :
    x ∈ (A.K j (by omega) β).lev.U := by
  have hj' : j ≤ B.R.m := by omega
  have hjm : j < B.R.m := by omega
  have hL := hI.idx_ok a
  have hR := hA.reads j hj'
  obtain ⟨c, rfl⟩ := hA.chOf_onto j hj' β
  have hc := (hA.rep j hj' c).1
  rw [← hc] at hg
  have hPQ : P.1 ∈ I.Q a := (@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP
  obtain ⟨hLev, hdisj, -⟩ := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hd : Disjoint (B.primes X).vGs (I.Q a) := Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) hdisj
  have hp := IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  obtain ⟨pk, hpk, -⟩ := hR.k_std (A.chOf j c)
  have hv : Formalism.L2.Col.IsOver (P.1.under (𝓞 B.host.F)) P.1 := rfl
  have hgI : g ∈ GLint B.fields.E (B.R.N j) P.1 := hL.int j _ P hg
  have hT := (GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad I hI l u a (P.1.under (𝓞 B.host.F)) ⟨P.1, hPQ, rfl⟩).1
  have hk1 : bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) (A.kb j (A.chOf j c)) = 1 := by
    rw [hβ]; exact (GlobalTheory.Mem.Col2.MemChart.kStd_spec (X := X) l.pr u (B.R.N j)).2.1 _ hT
  let cc : GLQ B.fields.E (B.R.N j) (I.Q a) := Pi.mulSingle (⟨P.1, hPQ⟩ : I.Q a) (⟨g, hgI⟩⁻¹ : GLint B.fields.E (B.R.N j) P.1)
  have hccP : cc ⟨P.1, hPQ⟩ = (⟨g, hgI⟩⁻¹ : GLint B.fields.E (B.R.N j) P.1) := Pi.mulSingle_eq_same _ _
  have hccO : ∀ P'' : I.Q a, P''.1 ≠ P.1 → cc P'' = 1 := fun P'' h => Pi.mulSingle_eq_of_ne (fun e => h (congrArg Subtype.val e)) _
  have hb : c.1 = Idx.of (c.1.get hjm) hjm := (Idx.of_get c.1 hjm _).symm
  have hcc : cc ∈ (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) j c.1).grp := by
    rw [hb]
    intro P'' _
    by_cases h : P''.1 = P.1
    · obtain rfl : P'' = ⟨P.1, hPQ⟩ := Subtype.ext h
      show cc ⟨P.1, hPQ⟩ ∈ ((I.idx a).levQ j (c.1.get hjm) ⟨P.1, hPQ⟩).H
      rw [hccP, hL.grpQ]
      exact inv_mem (Subgroup.mem_subgroupOf.2 hg)
    · show cc P'' ∈ ((I.idx a).levQ j (c.1.get hjm) P'').H
      rw [hccO P'' h]
      exact one_mem _
  let κ : (I.stp u a j).G c.1 := (1, 1, ⟨cc, hcc⟩)
  have hPu : P.1 ∈ uSG (B.primes X).vGs I.SQ := by
    simp only [uSG, Finset.mem_union]
    exact Or.inr (ColIn.Q_subset_SQ I a hPQ)
  have key := GlobalTheory.Mem.Col2.LevLiftPt.core B.sp.cm hp hx hpk.uni _ P.1 hv hoff g hgI (fun r s => by
      have e : bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) ((A.kb j (A.chOf j c))⁻¹ * x * A.kb j (A.chOf j c)) =
          bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) x := by
        rw [map_mul, map_mul, map_inv, hk1, inv_one, one_mul, mul_one]
      exact (GlobalTheory.Mem.Col2.ChTwRead.adAt_congr_prV P.1 (congrArg (fun m => m.1 r s) e)).trans (hpt r s))
    (GlobalTheory.Mem.Col2.LevLiftPt.vT_notOver I hI a P _ hv u) (fun w hw hwv => by
      have hw' : w ∈ uSG (B.primes X).vGs I.SQ := by
        simp only [uSG, Finset.mem_union]
        rcases hw with h | h
        · exact Or.inl h
        · exact Or.inr (ColIn.Q_subset_SQ I a h)
      rcases rll_over_cases B.sp.cm hv hwv with h | h
      · exact h
      · exact absurd (h ▸ hw') (hLev.split P.1 hPu))
    1 cc (fun h => absurd h hP) (fun w _ y _ => by simp) (fun _ => by rw [hccP, inv_inv])
    (fun P'' h => by rw [hccO P'' h, inv_one]; rfl)
  have e := GlobalTheory.Mem.Col2.LevLiftPt.mul_conj (G := TC.GA B (B.R.N j)) ((A.K j hj' (A.chOf j c)).y ⟨c, rfl⟩).1 x (A.kb j (A.chOf j c))
  have hq : TC.PtOf ((show TC.GA B (B.R.N j) from ((A.K j hj' (A.chOf j c)).y ⟨c, rfl⟩).1) * x * A.kb j (A.chOf j c))
      ((I.stp u a j).act c.1 κ ((I.stp u a j).rep c)).1.1 := e ▸ key
  refine (hR.lev c x _ hq).2 ⟨κ, map_one (ufGL B.fields.E (B.R.N j)), rfl, ?_⟩
  have h0 : ∀ p : PtAt B.R I.sel (I.tup a) (I.cst a) u j, p.1.2 = ∅ := fun p => by
    have := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) (by omega)] at this
    exact this
  funext P'
  simp only [cosetIn, h0, Set.mem_empty_iff_false, false_and, exists_false]

end Rat

/- English proof (translation)
Establish `h1 : M * F.β = F.β * g` using `by rw [h, Matrix.mul_assoc, F.γβ, Matrix.mul_one]`. Establish `h2` using `congrFun (congrFun h1 (e a)) b`. Rewrite `h2` using `[he]`. Simplify `h2` using `[Matrix.mul_apply, Matrix.one_apply]`.
-/
theorem entry_of_std {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k N Y) (e : Y ≃ Fin N)
    (he : F.β = (1 : Matrix (Fin N) (Fin N) k).submatrix id e) (M : Matrix (Fin N) (Fin N) k) (g : Matrix Y Y k)
    (h : M = F.β * g * F.γ) (a b : Y) : M (e a) (e b) = g a b := by
  have h1 : M * F.β = F.β * g := by rw [h, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 (e a)) b
  rw [he] at h2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h2

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α i n hn hphi`. Establish `hs` using `GlobalTheory.LevProd.step_index_le_s J i hj`. Establish `hj' : j ≤ B.R.m` using `by omega`. Establish `hjm : j < B.R.m` using `by omega`. Establish `hI` using `hW.tr.ok`.

Establish `hL` using `hI.idx_ok (W.P.I.tup t)`. Establish `hrep` using `hJ.rep i j ((J.G i).s - j) (Nat.add_sub_cancel' hs) hjm (J.ι j α)`. Rewrite `hrep` using `[hJ.sec j (by omega) α i]`. Take `⟨gl, hglc, hgl, hglu⟩` from `GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j) (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (by omega))`. Establish `hAt : ∀ y, gl y ∈ GlobalTheory.FinPl.grpAt _ (· = (J.G i).q.v)` using `fun y => GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ _ _ _ (hgl y).1 _ rfl`.

Establish `hund : (J.G i).q.v = ((J.P i).1).under (𝓞 B.host.F)`. Rewrite using `[hJ.eq i]`. Conclude with `(GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hat t J hJ).2 i`. Establish `hidem : Formalism.L2.NTheta.IsIdemAt (J.G i).q.e (J.P i).1` using `by rw [hJ.eq i]; exact (J.G i).idem`. Establish `hg1 : gramN (I.rec7 l Z) j hj' = 1` using `((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hW.tr.pins.some l Z).2.2.2 j hj').1`.

Establish `eU : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj') (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) = Formalism.L2.Col.UAd B.sp.cm (B.R.N j)` using `by rw [hg1]; rfl`. Take `⟨e, he, heβ⟩` from `(ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 j (by have := hs; exact Nat.le_succ_of_le this)`. Set `K` to `(GlobalTheory.ClassSumLevel.levG ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj') (J.A.K j hj' (J.ι j α)).lev).comap gl`. Establish `hKo : IsOpen (K : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k))` using `(GlobalTheory.ClassSumLevel.isOpen_levG ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj') (J.A.K j hj' (J.ι j α)).lev).preimage hglc`. Establish `hle : GlobalTheory.LevProd.H J j hj α i ≤ K`.

Use `prX_le_of_prCat _ _ _ I.Ch I.sel _ (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i) _ _ _ _ (J.G i).ν (J.G i).unitVol hL.cst_ok (hJ.tw i) j ((J.G i).s - j) (by omega) _ _ hrep K hKo (fun e' he' y hy => ?_)` and prove the remaining obligations. Use `Subgroup.mem_comap.2 ((GlobalTheory.ClassSumLevel.mem_levG_iff _ _ _ _).2 ?_)` and prove the remaining obligations. Use `mem_lev_of_rat I hI l Z u _ J.A hJ.is j hj (J.ι j α) (hJ.std j (by omega) _) (J.P i) (hJ.tw i).nmem _ (eU ▸ GlobalTheory.AdForm.Model.finGL_mem _ (rankN (I.rec7 l Z) j hj') _) (fun v' hv' => ?_) y hy (fun r s => ?_)` and prove the remaining obligations. Use `GlobalTheory.Mem.Col2.AdPlace.bc_prV_eq_one_of_adAt _ _ _ _ _ fun w hw r s => ?_` and prove the remaining obligations. Use `(GlobalTheory.FinMComp.adAt_finM_eq_one (I.rec7 l Z) _ (rankN (I.rec7 l Z) j hj') _ _ (hAt _) w (fun h => hv' (hw.symm.trans (h.trans hund))) r s).trans ?_` and prove the remaining obligations.

Both sides reduce to the same expression. Take `⟨r, rfl⟩` from `e'.surjective r`. Take `⟨s, rfl⟩` from `e'.surjective s`. Establish `ee : ∀ c, (finCongr (rankN (I.rec7 l Z) j hj')).symm (e' c) = e c` using `fun c => Fin.ext ((he' c).trans (he c).symm)`. Establish `h1` using `entry_of_std _ e heβ _ _ (hgl (GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) e' y)).2 r s`.

Use `adAt_eq_of_pr (J.G i).q (J.P i).1 hidem (mt _ (gl (GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) e' y)) ((finCongr (rankN (I.rec7 l Z) j hj')).symm (e' r)) ((finCongr (rankN (I.rec7 l Z) j hj')).symm (e' s))) _ ?_` and prove the remaining obligations. Rewrite using `[ee, ee]`. Conclude with `h1`. Establish `hn' : n = gl (GlobalTheory.LevProd.phi J j hj n i)` using `hglu n _ ((GlobalTheory.LocGl.supp_iff _ _).2 hn) ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl)`. Establish `hK : gl (GlobalTheory.LevProd.phi J j hj n i) ∈ GlobalTheory.ClassSumLevel.levG ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj') (J.A.K j hj' (J.ι j α)).lev` using `hle hphi`.

Rewrite `hK` using `[← hn']`. Conclude with `(hJ.is.U j hj' _ n).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hn, hK⟩`.
-/
theorem onePlace : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) (i : Fin J.r), ∀ n ∈ GlobalTheory.FinPl.grpAt _ (· = (J.G i).q.v), GlobalTheory.LevProd.phi J j hj n i ∈ GlobalTheory.LevProd.H J j hj α i → n ∈ J.A.U j (J.ι j α) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α i n hn hphi
  have hs := GlobalTheory.LevProd.step_index_le_s J i hj
  have hj' : j ≤ B.R.m := by omega
  have hjm : j < B.R.m := by omega
  have hI := hW.tr.ok
  have hL := hI.idx_ok (W.P.I.tup t)
  have hrep := hJ.rep i j ((J.G i).s - j) (Nat.add_sub_cancel' hs) hjm (J.ι j α)
  rw [hJ.sec j (by omega) α i] at hrep
  obtain ⟨gl, hglc, hgl, hglu⟩ := GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j)
    (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (by omega))
  have hAt : ∀ y, gl y ∈ GlobalTheory.FinPl.grpAt _ (· = (J.G i).q.v) := fun y =>
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ _ _ _ (hgl y).1 _ rfl
  have hund : (J.G i).q.v = ((J.P i).1).under (𝓞 B.host.F) := by
    rw [hJ.eq i]; exact (GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hat t J hJ).2 i
  have hidem : Formalism.L2.NTheta.IsIdemAt (J.G i).q.e (J.P i).1 := by rw [hJ.eq i]; exact (J.G i).idem
  have hg1 : gramN (I.rec7 l Z) j hj' = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hW.tr.pins.some l Z).2.2.2 j hj').1
  have eU : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj') (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      Formalism.L2.Col.UAd B.sp.cm (B.R.N j) := by rw [hg1]; rfl
  obtain ⟨e, he, heβ⟩ := (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 j (by have := hs; exact Nat.le_succ_of_le this)
  let K := (GlobalTheory.ClassSumLevel.levG ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj') (J.A.K j hj' (J.ι j α)).lev).comap gl
  have hKo : IsOpen (K : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) :=
    (GlobalTheory.ClassSumLevel.isOpen_levG ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj') (J.A.K j hj' (J.ι j α)).lev).preimage hglc
  have hle : GlobalTheory.LevProd.H J j hj α i ≤ K := by
    refine prX_le_of_prCat _ _ _ I.Ch I.sel _ (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i) _ _ _ _
      (J.G i).ν (J.G i).unitVol hL.cst_ok (hJ.tw i) j ((J.G i).s - j) (by omega) _ _ hrep K hKo (fun e' he' y hy => ?_)
    refine Subgroup.mem_comap.2 ((GlobalTheory.ClassSumLevel.mem_levG_iff _ _ _ _).2 ?_)
    refine mem_lev_of_rat I hI l Z u _ J.A hJ.is j hj (J.ι j α) (hJ.std j (by omega) _) (J.P i) (hJ.tw i).nmem _
      (eU ▸ GlobalTheory.AdForm.Model.finGL_mem _ (rankN (I.rec7 l Z) j hj') _) (fun v' hv' => ?_) y hy (fun r s => ?_)
    · refine GlobalTheory.Mem.Col2.AdPlace.bc_prV_eq_one_of_adAt _ _ _ _ _ fun w hw r s => ?_
      refine (GlobalTheory.FinMComp.adAt_finM_eq_one (I.rec7 l Z) _ (rankN (I.rec7 l Z) j hj') _ _ (hAt _) w
        (fun h => hv' (hw.symm.trans (h.trans hund))) r s).trans ?_
      rfl
    · obtain ⟨r, rfl⟩ := e'.surjective r
      obtain ⟨s, rfl⟩ := e'.surjective s
      have ee : ∀ c, (finCongr (rankN (I.rec7 l Z) j hj')).symm (e' c) = e c := fun c => Fin.ext ((he' c).trans (he c).symm)
      have h1 := entry_of_std _ e heβ _ _ (hgl (GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) e' y)).2 r s
      refine adAt_eq_of_pr (J.G i).q (J.P i).1 hidem
        (mt _ (gl (GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) e' y))
          ((finCongr (rankN (I.rec7 l Z) j hj')).symm (e' r)) ((finCongr (rankN (I.rec7 l Z) j hj')).symm (e' s))) _ ?_
      rw [ee, ee]
      exact h1
  have hn' : n = gl (GlobalTheory.LevProd.phi J j hj n i) :=
    hglu n _ ((GlobalTheory.LocGl.supp_iff _ _).2 hn) ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl)
  have hK : gl (GlobalTheory.LevProd.phi J j hj n i) ∈ GlobalTheory.ClassSumLevel.levG ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj')
    (J.A.K j hj' (J.ι j α)).lev := hle hphi
  rw [← hn'] at hK
  exact (hJ.is.U j hj' _ n).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hn, hK⟩

open GlobalTheory.FinPl in

/- English proof (translation)
Rewrite `hn` using `[GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts]`. Apply `GlobalTheory.FinPlLoc.mt_inj` to reduce the goal to its premises. Rewrite using `[GlobalTheory.FinPlLoc.mt_one]`. Use extensionality with `i j`. Use `GlobalTheory.FinPlLoc.eq_zero_of_comp _ (hn i j).1 (fun w => (hn i j).2 w (hP w))` as an intermediate fact.

Rewrite `this` using `[Matrix.sub_apply, sub_eq_zero]`. Conclude with `this`.
-/
theorem grpAt_empty {D : D7} (V : HSp D) {P : Pl D → Prop} (hP : ∀ w, ¬ P w) (n : GA D V) (hn : n ∈ grpAt V P) : n = 1 := by
  rw [GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts] at hn
  apply GlobalTheory.FinPlLoc.mt_inj
  rw [GlobalTheory.FinPlLoc.mt_one]
  ext i j
  have := GlobalTheory.FinPlLoc.eq_zero_of_comp _ (hn i j).1 (fun w => (hn i j).2 w (hP w))
  rw [Matrix.sub_apply, sub_eq_zero] at this
  exact this

open GlobalTheory.FinPl in

/- English proof (translation)
Establish `h2` using `GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q (P := (· = q.v)) rfl h1`. Use `symm`. Rewrite using `[← GlobalTheory.LevIdx.eq_locHom_iff, h2]`. Simplify using `[F.βγ]`.
-/
theorem locHom_one_of_off {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y)
    {x : GA D S} (h1 : x ∈ grpOff S (· = q.v)) : GlobalTheory.LevIdx.locHom q S F x = 1 := by
  have h2 := GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q (P := (· = q.v)) rfl h1
  symm
  rw [← GlobalTheory.LevIdx.eq_locHom_iff, h2]
  simp [F.βγ]

open GlobalTheory.FinPl in

/- English proof (translation)
Rewrite `hn`, the goal using `[GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts]`. Conclude with `fun i j => ⟨(hn i j).1, fun w hw => (hn i j).2 w (fun hp => hw (h w hp))⟩`.
-/
theorem grpAt_le_of {D : D7} (V : HSp D) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) {n : GA D V} (hn : n ∈ grpAt V P) :
    n ∈ grpAt V P' := by
  rw [GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts] at hn ⊢
  exact fun i j => ⟨(hn i j).1, fun w hw => (hn i j).2 w (fun hp => hw (h w hp))⟩

/- English proof (translation)
Introduce `B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α n hn hphi`. Set `Q : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z))` to `Finset.univ.image (fun i => (J.G i).q.v)`. Establish `key : ∀ S : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z)), S ⊆ Q → ∀ n ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ S), (∀ i, (J.G i).q.v ∈ S → GlobalTheory.LevProd.phi J j hj n i ∈ GlobalTheory.LevProd.H J j hj α i) → n ∈ J.A.U j (J.ι j α)`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`.

Consider the case `empty`. Introduce `_ n hn _`. Rewrite using `[grpAt_empty _ (fun w h => by simp at h) n hn]`. Conclude with `one_mem _`. Consider the case `insert v S hvS ih`.

Introduce `hsub n hn hphi`. Take `⟨i0, -, hi0⟩` from `Finset.mem_image.1 (hsub (Finset.mem_insert_self v S))`. Take `⟨x, hx, y, hy, rfl⟩` from `((GlobalTheory.FinPl.localComponents _ (fun w => w = v)).2 _).1 n`. Establish `hxS : x ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ insert v S)` using `grpAt_le_of _ (fun w hw => by rw [hw]; exact Finset.mem_insert_self v S) hx`. Establish `hyS : y ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ S)`.

Establish `h1 : y ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ insert v S)`. Establish `: y = x⁻¹ * (x * y)` using `by group`. Rewrite using `[this]`. Conclude with `mul_mem (inv_mem hxS) hn`. Rewrite `h1`, the goal using `[GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts]`.

Rewrite `hy` using `[GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts]`. Use `fun a b => ⟨(h1 a b).1, fun w hw => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hwv : w = v`. Conclude with `hy a b w hwv`. Conclude with `(h1 a b).2 w (fun hm => (Finset.mem_insert.1 hm).elim hwv hw)`.

Establish `hyv : GlobalTheory.LevProd.phi J j hj y i0 = 1` using `by show GlobalTheory.LevIdx.locHom (J.G i0).q _ _ y = 1`. Apply `locHom_one_of_off` to reduce the goal to its premises. Rewrite using `[hi0]`. Conclude with `hy`. Establish `hxU : x ∈ J.A.U j (J.ι j α)`.

Use `onePlace W hW u a ha hTr j hj t J hJ α i0 x (by rw [hi0]; exact hx) ?_` and prove the remaining obligations. Use `hphi i0 (by rw [hi0]; exact Finset.mem_insert_self v S)` as an intermediate fact. Rewrite `this` using `[map_mul, Pi.mul_apply, hyv, mul_one]`. Then use the resulting hypothesis. Establish `hyU : y ∈ J.A.U j (J.ι j α)`. Use `ih (fun w hw => hsub (Finset.mem_insert_of_mem hw)) y hyS (fun i hi => ?_)` and prove the remaining obligations.

Establish `hxi : GlobalTheory.LevProd.phi J j hj x i = 1` using `by show GlobalTheory.LevIdx.locHom (J.G i).q _ _ x = 1`. Apply `locHom_one_of_off` to reduce the goal to its premises. Conclude with `GlobalTheory.FinPl.SetCut.grpAt_le_grpOff _ _ _ (fun p hp hp' => hvS (by rw [← hp, hp']; exact hi)) hx`. Use `hphi i (Finset.mem_insert_of_mem hi)` as an intermediate fact. Rewrite `this` using `[map_mul, Pi.mul_apply, hxi, one_mul]`. Then use the resulting hypothesis.

Conclude with `mul_mem hxU hyU`. Use `key Q subset_rfl n (grpAt_le_of _ (fun w hw => ?_) hn) (fun i _ => hphi i)` and prove the remaining obligations. Take `⟨i, hi⟩` from `hw`. Conclude with `Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩`.
-/
theorem mem_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j), ∀ n ∈ GlobalTheory.FinPl.grpAt _ (GlobalTheory.LevProd.twAt J), (∀ i, GlobalTheory.LevProd.phi J j hj n i ∈ GlobalTheory.LevProd.H J j hj α i) → n ∈ J.A.U j (J.ι j α) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α n hn hphi
  classical
  let Q : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z)) := Finset.univ.image (fun i => (J.G i).q.v)
  have key : ∀ S : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z)), S ⊆ Q → ∀ n ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ S),
      (∀ i, (J.G i).q.v ∈ S → GlobalTheory.LevProd.phi J j hj n i ∈ GlobalTheory.LevProd.H J j hj α i) → n ∈ J.A.U j (J.ι j α) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ n hn _
      rw [grpAt_empty _ (fun w h => by simp at h) n hn]
      exact one_mem _
    | insert v S hvS ih =>
      intro hsub n hn hphi
      obtain ⟨i0, -, hi0⟩ := Finset.mem_image.1 (hsub (Finset.mem_insert_self v S))
      obtain ⟨x, hx, y, hy, rfl⟩ := ((GlobalTheory.FinPl.localComponents _ (fun w => w = v)).2 _).1 n
      have hxS : x ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ insert v S) :=
        grpAt_le_of _ (fun w hw => by rw [hw]; exact Finset.mem_insert_self v S) hx
      have hyS : y ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ S) := by
        have h1 : y ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ insert v S) := by
          have : y = x⁻¹ * (x * y) := by group
          rw [this]; exact mul_mem (inv_mem hxS) hn
        rw [GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts] at h1 ⊢
        rw [GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts] at hy
        refine fun a b => ⟨(h1 a b).1, fun w hw => ?_⟩
        by_cases hwv : w = v
        · exact hy a b w hwv
        · exact (h1 a b).2 w (fun hm => (Finset.mem_insert.1 hm).elim hwv hw)
      have hyv : GlobalTheory.LevProd.phi J j hj y i0 = 1 := by
        show GlobalTheory.LevIdx.locHom (J.G i0).q _ _ y = 1
        apply locHom_one_of_off
        rw [hi0]; exact hy
      have hxU : x ∈ J.A.U j (J.ι j α) := by
        refine onePlace W hW u a ha hTr j hj t J hJ α i0 x (by rw [hi0]; exact hx) ?_
        have := hphi i0 (by rw [hi0]; exact Finset.mem_insert_self v S)
        rwa [map_mul, Pi.mul_apply, hyv, mul_one] at this
      have hyU : y ∈ J.A.U j (J.ι j α) := by
        refine ih (fun w hw => hsub (Finset.mem_insert_of_mem hw)) y hyS (fun i hi => ?_)
        have hxi : GlobalTheory.LevProd.phi J j hj x i = 1 := by
          show GlobalTheory.LevIdx.locHom (J.G i).q _ _ x = 1
          apply locHom_one_of_off
          exact GlobalTheory.FinPl.SetCut.grpAt_le_grpOff _ _ _
            (fun p hp hp' => hvS (by rw [← hp, hp']; exact hi)) hx
        have := hphi i (Finset.mem_insert_of_mem hi)
        rwa [map_mul, Pi.mul_apply, hxi, one_mul] at this
      exact mul_mem hxU hyU
  refine key Q subset_rfl n (grpAt_le_of _ (fun w hw => ?_) hn) (fun i _ => hphi i)
  obtain ⟨i, hi⟩ := hw
  exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩

end GlobalTheory.LevProd.Bwd
end
