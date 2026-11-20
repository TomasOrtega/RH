import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapMemSpanImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandIns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonnegShaOK
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Ex

@[reducible] def reset {B : Base} {C : Cols B} (W : RowsRest B C) (mt ma : B.places.Pl → C.Tup)
    (hmt : ∀ v, mt (B.places.conj v) = mt v) (hma : ∀ v, ma (B.places.conj v) = ma v)
    (hor : ∀ v, ma v = C.mu0 ∨ ma v = mt v) : RowsRest B C :=
  { W with
    muAt := ma
    muAt_conj := hma
    muTw := mt
    muTw_conj := hmt
    muAt_or := hor
    kaBig := GlobalTheory.Mem.DfGen.kaBigB B
    kaSmall := GlobalTheory.Mem.DfGen.kaSmallB B
    shaLen := GaloisStage.shaTrue B.host
    shaLen_nonneg := GaloisStage.shaTrue_nonneg B.host }

/- English proof (translation)
Introduce `V S N G j _ _ τ`. Use `⟨fun i => ?_, fun c => ?_⟩` and prove the remaining obligations. Use `show ((W'.kaBig j τ i : ℤ) : ℚ) = _`. Rewrite using `[hb]`. Conclude with `(GlobalTheory.Mem.DfGen.aPlusB_int B j τ i).choose_spec.symm`.

Use `show ((W'.kaSmall j τ c : ℤ) : ℚ) = _`. Rewrite using `[hs]`. Use `show ((-(GlobalTheory.Mem.DfGen.aMinusB_int B j τ c).choose : ℤ) : ℚ) = -GlobalTheory.Mem.DfGen.aMinusB B j τ c`. Use `push_cast`. Rewrite using `[← (GlobalTheory.Mem.DfGen.aMinusB_int B j τ c).choose_spec]`.
-/
theorem kapDef_of_ka {B : Base} {C : Cols B} (W' : RowsRest B C) (hb : W'.kaBig = GlobalTheory.Mem.DfGen.kaBigB B)
    (hs : W'.kaSmall = GlobalTheory.Mem.DfGen.kaSmallB B) : ∀ V S N G, DV.KapDef (assemble B C W' V S N G) := by
  intro V S N G j _ _ τ
  refine ⟨fun i => ?_, fun c => ?_⟩
  · show ((W'.kaBig j τ i : ℤ) : ℚ) = _
    rw [hb]
    exact (GlobalTheory.Mem.DfGen.aPlusB_int B j τ i).choose_spec.symm
  · show ((W'.kaSmall j τ c : ℤ) : ℚ) = _
    rw [hs]
    show ((-(GlobalTheory.Mem.DfGen.aMinusB_int B j τ c).choose : ℤ) : ℚ) = -GlobalTheory.Mem.DfGen.aMinusB B j τ c
    push_cast
    rw [← (GlobalTheory.Mem.DfGen.aMinusB_int B j τ c).choose_spec]

end GlobalTheory.Mem.R3.Rw.Ex

end

open GlobalTheory.Mem.R3.Rw.Ex in
/- English proof (translation)
Introduce `B f T w hX Wt hWt`. Take `⟨R⟩` from `GlobalTheory.Mem.Df.rowsDef_nonempty w.I w.ok w.pins w.l hX`. Establish `hmem : ∀ v, ∃ a, w.I.xi a = T.xiTw f v` using `fun v => by`. Establish `h : T.xiTw f v ∈ Set.range w.I.xi`. Rewrite using `[w.xi_range]`.

Conclude with `Or.inr ⟨v, rfl⟩`. Conclude with `h`. Establish `hconj : ∀ v, T.xiTw f (B.places.conj v) = T.xiTw f v` using `fun v => by`. Unfold `TwDat.xiTw`. Rewrite using `[GlobalTheory.Mem.Top.TwFin.resChar_conj, (T.conj v).1]`.

Set `mt : B.places.Pl → w.C.Tup` to `fun v => Classical.choose (hmem v)`. Establish `hmt : ∀ v, mt (B.places.conj v) = mt v` using `fun v => by show Classical.choose (hmem (B.places.conj v)) = Classical.choose (hmem v)`. Establish `: ∀ x y (hx : ∃ a, w.I.xi a = x) (hy : ∃ a, w.I.xi a = y), x = y → Classical.choose hx = Classical.choose hy`. Introduce and unpack `x y hx hy rfl`. Both sides reduce to the same expression.

Conclude with `this _ _ _ _ (hconj v)`. Set `ma : B.places.Pl → w.C.Tup` to `fun v => if v ∈ Wt then mt v else w.C.mu0`. Establish `hma : ∀ v, ma (B.places.conj v) = ma v` using `fun v => by`. Simplify using `only [ma, hWt v, hmt v]`. Establish `hor : ∀ v, ma v = w.C.mu0 ∨ ma v = mt v` using `fun v => by`.

Distinguish the cases in `h : v ∈ Wt`. Conclude with `Or.inr (if_pos h)`. Conclude with `Or.inl (if_neg h)`. Use `⟨reset R.W mt ma hmt hma hor, ⟨fun v => Classical.choose_spec (hmem v), fun v h => if_pos h, fun v h => if_neg h⟩, fun W' hb hs => kapDef_of_ka W' hb hs, GlobalTheory.MemN.shaOK_shaTrue B.toPre⟩` and prove the remaining obligations.
-/
theorem GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (hX : B.fields.Ok) (Wt : Set B.places.Pl), (∀ v, B.places.conj v ∈ Wt ↔ v ∈ Wt) → ∃ W₀ : RowsRest B w.C, MuW w Wt W₀ ∧ (∀ W' : RowsRest B w.C, W'.kaBig = W₀.kaBig → W'.kaSmall = W₀.kaSmall → ∀ V S N G, DV.KapDef (assemble B w.C W' V S N G)) ∧ GlobalTheory.MemN.ShaOK B.toPre W₀.shaLen := by
  intro B f T w hX Wt hWt
  classical
  obtain ⟨R⟩ := GlobalTheory.Mem.Df.rowsDef_nonempty w.I w.ok w.pins w.l hX
  have hmem : ∀ v, ∃ a, w.I.xi a = T.xiTw f v := fun v => by
    have h : T.xiTw f v ∈ Set.range w.I.xi := by
      rw [w.xi_range]; exact Or.inr ⟨v, rfl⟩
    exact h
  have hconj : ∀ v, T.xiTw f (B.places.conj v) = T.xiTw f v := fun v => by
    unfold TwDat.xiTw
    rw [GlobalTheory.Mem.Top.TwFin.resChar_conj, (T.conj v).1]
  let mt : B.places.Pl → w.C.Tup := fun v => Classical.choose (hmem v)
  have hmt : ∀ v, mt (B.places.conj v) = mt v := fun v => by
    show Classical.choose (hmem (B.places.conj v)) = Classical.choose (hmem v)
    have : ∀ x y (hx : ∃ a, w.I.xi a = x) (hy : ∃ a, w.I.xi a = y), x = y →
        Classical.choose hx = Classical.choose hy := by
      rintro x y hx hy rfl; rfl
    exact this _ _ _ _ (hconj v)
  let ma : B.places.Pl → w.C.Tup := fun v => if v ∈ Wt then mt v else w.C.mu0
  have hma : ∀ v, ma (B.places.conj v) = ma v := fun v => by
    simp only [ma, hWt v, hmt v]
  have hor : ∀ v, ma v = w.C.mu0 ∨ ma v = mt v := fun v => by
    by_cases h : v ∈ Wt
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  refine ⟨reset R.W mt ma hmt hma hor, ⟨fun v => Classical.choose_spec (hmem v), fun v h => if_pos h, fun v h => if_neg h⟩,
    fun W' hb hs => kapDef_of_ka W' hb hs, GlobalTheory.MemN.shaOK_shaTrue B.toPre⟩
