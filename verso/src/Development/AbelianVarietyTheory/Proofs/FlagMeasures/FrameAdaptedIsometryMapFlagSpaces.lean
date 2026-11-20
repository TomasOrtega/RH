import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Establish `hmono : ∀ (H : LFlag (VS D) D.R.rS T) {a b : ℕ}, a ≤ b → Xflag H a ≤ Xflag H b`. Introduce `H a b hab`. Conclude with `Submodule.span_mono (Set.image_mono fun i (hi : i.1 < a) => (lt_of_lt_of_le hi hab : i.1 < b))`. Establish `hmem : ∀ (H : LFlag (VS D) D.R.rS T) (i : Fin D.R.rS) {j : ℕ}, i.1 < j → H.fl.e i ∈ Xflag H j`. Introduce `H i j hij`.

Conclude with `Submodule.subset_span ⟨i, hij, rfl⟩`. Establish `hX : ∀ H : LFlag (VS D) D.R.rS T, Xsp H = Xflag H D.R.rS`. Introduce `H`. Use `show Submodule.span _ (Set.range H.fl.e) = Submodule.span _ (H.fl.e '' {i | i.1 < D.R.rS})`. Use `congr 1`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `hstep : ∀ i : Fin D.R.rS, g (F.fl.e i) - G.fl.e i ∈ Xflag G i.1`. Introduce `i`. Use `hg.2 i.castSucc` as an intermediate fact.

Simplify `this` using `[frame, Formalism.MainNotions.S.FlagG.fvec]`. Establish `hle : ∀ j, (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag G j`. Introduce `j`. Rewrite using `[Submodule.map_le_iff_le_comap]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, hi, rfl⟩`. Use `show g (F.fl.e i) ∈ Xflag G j`. Establish `h1` using `hmono G (le_of_lt hi) (hstep i)`. Establish `h2` using `hmem G i hi`. Simplify using `using add_mem h1 h2`.

Establish `hge : ∀ j, Xflag G j ≤ (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, hi, rfl⟩`. Conclude with `absurd hi (Nat.not_lt_zero _)`. Consider the case `succ j ih`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`.

Establish `hi' : i.1 ≤ j` using `Nat.lt_succ_iff.mp hi`. Establish `hmap : (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V)` using `Submodule.map_mono (hmono F (Nat.le_succ j))`. Establish `h1 : g (F.fl.e i) - G.fl.e i ∈ (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V)` using `hmap (ih (hmono G hi' (hstep i)))`. Establish `h2 : (g : (VS D).V →ₗ[D.host.E] (VS D).V) (F.fl.e i) ∈ (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V)` using `Submodule.mem_map_of_mem (hmem F i hi)`. Establish `h3` using `sub_mem h2 h1`.

Simplify using `only [LinearEquiv.coe_coe, sub_sub_cancel] at h3`. Conclude with `h3`. Use `⟨fun j => le_antisymm (hle j) (hge j), ?_⟩` and prove the remaining obligations. Rewrite using `[hX F, hX G]`. Conclude with `le_antisymm (hle _) (hge _)`.
-/
theorem adapt_map_flag (D : D7) (T : D.host.E) (F G : LFlag (VS D) D.R.rS T) (g : GV D) (hg : Adapt g F G) :
    (∀ j : ℕ, (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag G j) ∧
      (Xsp F).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G := by
  have hmono : ∀ (H : LFlag (VS D) D.R.rS T) {a b : ℕ}, a ≤ b → Xflag H a ≤ Xflag H b := by
    intro H a b hab
    exact Submodule.span_mono (Set.image_mono fun i (hi : i.1 < a) => (lt_of_lt_of_le hi hab : i.1 < b))
  have hmem : ∀ (H : LFlag (VS D) D.R.rS T) (i : Fin D.R.rS) {j : ℕ}, i.1 < j → H.fl.e i ∈ Xflag H j := by
    intro H i j hij
    exact Submodule.subset_span ⟨i, hij, rfl⟩
  have hX : ∀ H : LFlag (VS D) D.R.rS T, Xsp H = Xflag H D.R.rS := by
    intro H
    show Submodule.span _ (Set.range H.fl.e) = Submodule.span _ (H.fl.e '' {i | i.1 < D.R.rS})
    congr 1
    ext x
    simp
  have hstep : ∀ i : Fin D.R.rS, g (F.fl.e i) - G.fl.e i ∈ Xflag G i.1 := by
    intro i
    have := hg.2 i.castSucc
    simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using this
  have hle : ∀ j, (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag G j := by
    intro j
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    show g (F.fl.e i) ∈ Xflag G j
    have h1 := hmono G (le_of_lt hi) (hstep i)
    have h2 := hmem G i hi
    simpa using add_mem h1 h2
  have hge : ∀ j, Xflag G j ≤ (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    intro j
    induction j with
    | zero =>
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      exact absurd hi (Nat.not_lt_zero _)
    | succ j ih =>
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i.1 ≤ j := Nat.lt_succ_iff.mp hi
      have hmap : (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤
          (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) :=
        Submodule.map_mono (hmono F (Nat.le_succ j))
      have h1 : g (F.fl.e i) - G.fl.e i ∈ (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) :=
        hmap (ih (hmono G hi' (hstep i)))
      have h2 : (g : (VS D).V →ₗ[D.host.E] (VS D).V) (F.fl.e i) ∈
          (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) :=
        Submodule.mem_map_of_mem (hmem F i hi)
      have h3 := sub_mem h2 h1
      simp only [LinearEquiv.coe_coe, sub_sub_cancel] at h3
      exact h3
  refine ⟨fun j => le_antisymm (hle j) (hge j), ?_⟩
  rw [hX F, hX G]
  exact le_antisymm (hle _) (hge _)

end GlobalTheory
