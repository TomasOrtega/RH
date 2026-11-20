import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

structure StdKerTie {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop where
  X_eq : t.X = B.fields
  seam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
  Pr : HEq t.Pr (B.primes X)
  Ch : HEq t.Ch I.Ch
  sel : HEq t.sel I.sel
  S : t.S = I.S
  word : HEq t.word fun u : B.Word => u
  tup : HEq t.tup I.tup
  cst : HEq t.cst I.cst
  idx : HEq t.idx I.idx
  m2 : t.m2 = B.R.m - 2
  glob : HEq t.glob I.glob
  amb : HEq t.amb (I.J.amb B t.χ)
  δ : t.δ = I.J.δ
  O : I.StdO l Z Y.Qp t.O

namespace StdKerEmpty

/- English proof (translation)
Use `le_bot_iff.1 (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨A, hA, rfl⟩`. Establish `hA0 : A = 0`. Use extensionality with `i j`. Establish `h1 : (Pi.single j 1 : Fin 2 → D.host.E) ∈ StandardLatticesGL3.stdL D 2` using `fun k _ => by`.

Distinguish the cases in `e : k = j`. Substitute `e` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `Submodule.one_le.1 le_rfl`. Rewrite using `[Pi.single_eq_of_ne e]`.

Conclude with `Submodule.zero_mem _`. Establish `h2` using `congrFun ((Submodule.mem_bot _).1 (hA _ h1)) i`. Simplify `h2` using `[Matrix.mulVec_single]`. Substitute `hA0` using the available equality. Simplify using the standard rewrite rules.
-/
theorem detId_std_bot (D : D7) : TaylorLogMetric.detId D (StandardLatticesGL3.stdL D 2) (⊥ : Submodule (𝓞 D.host.E) (Fin 2 → D.host.E)) = ⊥ := by
  refine le_bot_iff.1 (Submodule.span_le.2 ?_)
  rintro _ ⟨A, hA, rfl⟩
  have hA0 : A = 0 := by
    ext i j
    have h1 : (Pi.single j 1 : Fin 2 → D.host.E) ∈ StandardLatticesGL3.stdL D 2 := fun k _ => by
      by_cases e : k = j
      · subst e
        rw [Pi.single_eq_same]
        exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne e]
        exact Submodule.zero_mem _
    have h2 := congrFun ((Submodule.mem_bot _).1 (hA _ h1)) i
    simpa [Matrix.mulVec_single] using h2
  subst hA0
  simp

/- English proof (translation)
Introduce and unpack `⟨b, -, hb⟩`. Rewrite `hb` using `[Submodule.bot_mul]`. Establish `h1 : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)` using `Submodule.mem_one.2 ⟨1, by simp⟩`. Rewrite `h1` using `[← hb, Submodule.mem_bot]`. Conclude with `one_ne_zero h1`.
-/
theorem not_N1_bot (D : D7) : ¬ TaylorLogMetric.N1 D ⊥ := by
  rintro ⟨b, -, hb⟩
  rw [Submodule.bot_mul] at hb
  have h1 : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := Submodule.mem_one.2 ⟨1, by simp⟩
  rw [← hb, Submodule.mem_bot] at h1
  exact one_ne_zero h1

/- English proof (translation)
Use `Submodule.span_eq_bot.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite `hx` using `[SetLike.mem_coe, Submodule.mem_bot]`. Substitute `hx` using the available equality. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules.
-/
theorem seam_lat_bot {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) : s.lat (⊥ : Submodule (𝓞 X.E) (Sp X.E n)) = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_bot] at hx
  subst hx
  funext i
  simp

/- English proof (translation)
Unfold `TaylorLogMetric.chiRec`. Rewrite using `[dif_neg]`. Conclude with `fun hx => not_N1_bot D ((h.2.1 ⊥).2 hx)`.
-/
theorem chiRec_bot (D : D7) (idl : D.Dt ⧸ D.UO → TaylorLogMetric.IdE D) (h : TaylorLogMetric.RelDetPinned D idl) : TaylorLogMetric.chiRec D idl ⊥ = 0 := by
  unfold TaylorLogMetric.chiRec
  rw [dif_neg]
  exact fun hx => not_N1_bot D ((h.2.1 ⊥).2 hx)

/- English proof (translation)
Introduce `h`. Establish `key : ∀ (X' : Fields) (s : Seam (I.rec7 l Z) X') (hX : X' = B.fields), HEq (ambOf s t.B t.χ t.cD) I.A → False`. Introduce `X' s hX hh`. Substitute `hX` using the available equality. Establish `e` using `congrArg (fun A : Amb B.fields => A.chiF 2 2 ⊥ ⊥) (eq_of_heq hh)`.

Simplify using `only [ambOf] at e`. Establish `hl : Base.chiFac t.χ 2 2 (⊥ : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin 2 → (I.rec7 l Z).host.E)) ⊥ = 0`. Simplify using `[Base.chiFac, t.χ_rec, detId_std_bot, chiRec_bot _ _ t.idl_ok]`. Establish `hr : (I.A).chiF 2 2 ⊥ ⊥ = 1`. Simplify using `only [ColIn.A, AmbIn.amb, Th.chiFac]`.

Establish `hc` using `chiId_ne_zero I.C.chiPsi (Th.detId B.host (Th.stdL B.host 2) ⊥)`. Simplify using `[ColIn.chi, hc]`. Rewrite `e` using `[seam_lat_bot, hl, hr]`. Conclude with `zero_ne_one e`. Conclude with `key t.X t.seam hXe h`.
-/
theorem not_heq_amb {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex)
    (hXe : t.X = B.fields) : ¬ HEq t.amb I.A := by
  intro h
  have key : ∀ (X' : Fields) (s : Seam (I.rec7 l Z) X') (hX : X' = B.fields),
      HEq (ambOf s t.B t.χ t.cD) I.A → False := by
    intro X' s hX hh
    subst hX
    have e := congrArg (fun A : Amb B.fields => A.chiF 2 2 ⊥ ⊥) (eq_of_heq hh)
    simp only [ambOf] at e
    have hl : Base.chiFac t.χ 2 2 (⊥ : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin 2 → (I.rec7 l Z).host.E)) ⊥ = 0 := by
      simp [Base.chiFac, t.χ_rec, detId_std_bot, chiRec_bot _ _ t.idl_ok]
    have hr : (I.A).chiF 2 2 ⊥ ⊥ = 1 := by
      simp only [ColIn.A, AmbIn.amb, Th.chiFac]
      have hc := chiId_ne_zero I.C.chiPsi (Th.detId B.host (Th.stdL B.host 2) ⊥)
      simp [ColIn.chi, hc]
    rw [seam_lat_bot, hl, hr] at e
    exact zero_ne_one e
  exact key t.X t.seam hXe h

end StdKerEmpty

end GlobalTheory.Mem.Col2.TC

end
