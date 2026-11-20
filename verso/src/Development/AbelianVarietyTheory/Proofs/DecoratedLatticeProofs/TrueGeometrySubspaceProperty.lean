import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevSph
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.TopVol

/- English proof (translation)
Establish `hT` using `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V`. Use `haveI := hT.1`. Use `haveI := hT.2.1`. Use `haveI := hT.2.2.1`. Use `haveI := hT.2.2.2.1`.

Use `haveI := hT.2.2.2.2.1`. Use `haveI := v.haar`. Use `haveI : (GinfC V).Normal := inferInstanceAs ((finHom V).ker.Normal)`. Set `K : Subgroup (GA D V)` to `GinfC V ⊔ U`. Establish `hKset : (K : Set (GA D V)) = {g | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ}` using `by show ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V)) = _`.

Rewrite using `[Subgroup.normal_mul]`. Use extensionality with `g`. Simplify using `only [Set.mem_mul, SetLike.mem_coe, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, κ, hκ, rfl⟩`.

Conclude with `⟨k, hk, κ, hκ, rfl⟩`. Introduce and unpack `⟨k, hk, κ, hκ, rfl⟩`. Conclude with `⟨k, hk, κ, hκ, rfl⟩`. Establish `hvol : GlobalTheory.SeeSaw.volLev v U = (v.μ K).toReal`. Unfold `GlobalTheory.SeeSaw.volLev`.

Rewrite using `[← hKset]`. Establish `hKc : IsCompact (K : Set (GA D V))` using `by show IsCompact ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V))`. Rewrite using `[Subgroup.normal_mul]`. Conclude with `hK.mul hc`. Establish `hKo : IsOpen (K : Set (GA D V))`.

Establish `ho' : IsOpen (((U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) : Subgroup (GA D V)) : Set (GA D V))` using `ho.preimage (GlobalTheory.AutMult.continuous_toFin V)`. Use `Subgroup.isOpen_mono (fun g hg => ?_) ho'` and prove the remaining obligations. Use `show g ∈ (K : Set (GA D V))`. Rewrite using `[hKset]`. Conclude with `⟨GlobalTheory.AutMult.toInf V g, (GlobalTheory.AutMult.toInf V g).2, GlobalTheory.AutMult.toFin V g, Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hg), (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩`.

Establish `hKfin : v.μ K ≠ ⊤` using `hKc.measure_lt_top.ne`. Establish `hKpos : 0 < v.μ K` using `hKo.measure_pos v.μ ⟨1, K.one_mem⟩`. Rewrite using `[hvol]`. Conclude with `(ENNReal.toReal_pos hKpos.ne' hKfin).ne'`.
-/
theorem volLev_ne_zero_of_isCompact {D : D7} (V : HSp D) (hK : IsCompact (GinfC V : Set (GA D V))) (v : GlobalTheory.Unf.Vol V)
    (U : Subgroup (GA D V)) (hle : U ≤ GfC V) (hc : IsCompact (U : Set (GA D V)))
    (ho : IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V))) : GlobalTheory.SeeSaw.volLev v U ≠ 0 := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := v.haar
  haveI : (GinfC V).Normal := inferInstanceAs ((finHom V).ker.Normal)
  let K : Subgroup (GA D V) := GinfC V ⊔ U
  have hKset : (K : Set (GA D V)) = {g | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ} := by
    show ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V)) = _
    rw [Subgroup.normal_mul]
    ext g
    simp only [Set.mem_mul, SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
  have hvol : GlobalTheory.SeeSaw.volLev v U = (v.μ K).toReal := by
    unfold GlobalTheory.SeeSaw.volLev
    rw [← hKset]
  have hKc : IsCompact (K : Set (GA D V)) := by
    show IsCompact ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V))
    rw [Subgroup.normal_mul]
    exact hK.mul hc
  have hKo : IsOpen (K : Set (GA D V)) := by
    have ho' : IsOpen (((U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) : Subgroup (GA D V)) : Set (GA D V)) :=
      ho.preimage (GlobalTheory.AutMult.continuous_toFin V)
    refine Subgroup.isOpen_mono (fun g hg => ?_) ho'
    show g ∈ (K : Set (GA D V))
    rw [hKset]
    exact ⟨GlobalTheory.AutMult.toInf V g, (GlobalTheory.AutMult.toInf V g).2, GlobalTheory.AutMult.toFin V g,
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hg), (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  have hKfin : v.μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKpos : 0 < v.μ K := hKo.measure_pos v.μ ⟨1, K.one_mem⟩
  rw [hvol]
  exact (ENNReal.toReal_pos hKpos.ne' hKfin).ne'

/- English proof (translation)
Introduce `B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a _ _ U hle hc ho`. Conclude with `volLev_ne_zero_of_isCompact _ (Formalism.IndefR.Eqv.isCompact_GinfC (I.rec7 l Z).sp.X'_sig fun τ => Or.inl ((I.rec7 l Z).X'_posDef τ)) _ U hle hc ho`.
-/
theorem volLev_top_ne_zero : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ U : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), U ≤ GfC _ → IsCompact (U : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) → volLev a.g.volT U ≠ 0 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a _ _ U hle hc ho
  exact volLev_ne_zero_of_isCompact _
    (Formalism.IndefR.Eqv.isCompact_GinfC (I.rec7 l Z).sp.X'_sig fun τ => Or.inl ((I.rec7 l Z).X'_posDef τ)) _ U hle hc ho

end GlobalTheory.TopVol
