import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[Formalism.L2.DIV.mem_blockTri]`. Introduce `i j hij`. Establish `hi : Formalism.L2.DIV.blk2 r i = 0`. Unfold `Formalism.L2.DIV.blk2`. Conclude with `if_pos (lt_of_lt_of_le i.isLt h)`.

Establish `hj : Formalism.L2.DIV.blk2 r j = 0`. Unfold `Formalism.L2.DIV.blk2`. Conclude with `if_pos (lt_of_lt_of_le j.isLt h)`. Rewrite `hij` using `[hi, hj]`. Conclude with `absurd hij (lt_irrefl 0)`.
-/
theorem mem_blockTriangular_singleBlock_of_le {κ : Type} [CommRing κ] {n r : ℕ} (h : n ≤ r) (g : GL (Fin n) κ) :
    g ∈ Formalism.L2.DIV.blockTri (κ := κ) (n := n) (Formalism.L2.DIV.blk2 r) := by
  rw [Formalism.L2.DIV.mem_blockTri]
  intro i j hij
  have hi : Formalism.L2.DIV.blk2 r i = 0 := by
    unfold Formalism.L2.DIV.blk2; exact if_pos (lt_of_lt_of_le i.isLt h)
  have hj : Formalism.L2.DIV.blk2 r j = 0 := by
    unfold Formalism.L2.DIV.blk2; exact if_pos (lt_of_lt_of_le j.isLt h)
  rw [hi, hj] at hij
  exact absurd hij (lt_irrefl 0)

/- English proof (translation)
Establish `hm` using `mem_blockTriangular_singleBlock_of_le (κ := κ) h g`. Use `haveI : IsEmpty {a : Fin n // Formalism.L2.DIV.blk2 r a = 1} := by`. Use `⟨fun a => ?_⟩` and prove the remaining obligations. Establish `h1` using `a.2`. Establish `h2` using `a.1.isLt`.

Unfold `Formalism.L2.DIV.blk2 at h1`. Apply the tactic sequence `split_ifs at h1 with hlt <;> omega`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Formalism.L2.DIV.diag_block_det_val 1 hm, Units.val_one]`. Conclude with `Matrix.det_isEmpty`.
-/
theorem blockDet_singleBlock_second_eq_one_of_le {κ : Type} [CommRing κ] {n r : ℕ} (h : n ≤ r) (g : GL (Fin n) κ) :
    Formalism.L2.DIV.dBlk (κ := κ) (n := n) (Formalism.L2.DIV.blk2 r) 1 g = 1 := by
  have hm := mem_blockTriangular_singleBlock_of_le (κ := κ) h g
  haveI : IsEmpty {a : Fin n // Formalism.L2.DIV.blk2 r a = 1} := by
    refine ⟨fun a => ?_⟩
    have h1 := a.2
    have h2 := a.1.isLt
    unfold Formalism.L2.DIV.blk2 at h1
    split_ifs at h1 with hlt <;> omega
  apply Units.ext
  rw [Formalism.L2.DIV.diag_block_det_val 1 hm, Units.val_one]
  exact Matrix.det_isEmpty

/- English proof (translation)
Introduce `D V β r t hr hrk Pg Q P χ ξ`. Substitute `hrk` using the available equality. Establish `hlev : Formalism.L2.DIV.lev D.sp.cm V.gram β (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B) = Formalism.L2.DIV.lev D.sp.cm V.gram β (datY V.rank V.rank t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B)`. Use extensionality with `x`. Simplify using `only [Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2, h3, _⟩, h5⟩`. Use `⟨⟨h1, h2, h3, fun PP hPP => ?_⟩, h5⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `PP ∈ (∅ : Finset (Formalism.L2.DIV.Pl D.host.E)) at hPP`. Simplify using `at hPP`.

Introduce and unpack `⟨⟨h1, h2, h3, _⟩, h5⟩`. Conclude with `⟨⟨h1, h2, h3, fun PP _ => mem_blockTriangular_singleBlock_of_le (r := V.rank) le_rfl _⟩, h5⟩`. Establish `hfn : ∀ y, Formalism.L2.DIV.levFn β (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B) y = Formalism.L2.DIV.levFn β (datY V.rank V.rank t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) y`. Introduce `y`. Unfold `Formalism.L2.DIV.levFn`.

Establish `hq : ∏ PP ∈ (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).Q, (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).xq PP (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).r) 1 (Formalism.L2.DIV.redFn β PP y)) = 1`. Use `Finset.prod_eq_one fun PP _ => ?_` and prove the remaining obligations. Establish `h2` using `blockDet_singleBlock_second_eq_one_of_le (r := V.rank) (le_refl V.rank) (Formalism.L2.DIV.redFn β PP y)`. Conclude with `(congrArg (⇑((datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).xq PP)) h2).trans (map_one _)`. Rewrite using `[hq]`.

Express the relevant statement in the definitionally equal form `_ = _ * ∏ PP ∈ (∅ : Finset (Formalism.L2.DIV.Pl D.host.E)), _`. Rewrite using `[Finset.prod_empty]`. Both sides reduce to the same expression. Use `⟨?_, fun k _ => ?_⟩` and prove the remaining obligations. Unfold `levG`.

Rewrite using `[hlev]`. Unfold `levChi`. Rewrite using `[hfn]`.
-/
theorem levG_twist_trivial_of_rank_eq :
    ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t : ℕ) (hr : r ≤ V.rank), V.rank = r → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), levG V β (datY V.rank r t 0 hr Pg Q P χ ξ Frm.B) = levG V β (datY V.rank r t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) ∧ ∀ k ∈ levG V β (datY V.rank r t 0 hr Pg Q P χ ξ Frm.B), levChi V β (datY V.rank r t 0 hr Pg Q P χ ξ Frm.B) k = levChi V β (datY V.rank r t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) k := by
  intro D V β r t hr hrk Pg Q P χ ξ
  subst hrk
  have hlev : Formalism.L2.DIV.lev D.sp.cm V.gram β (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B) =
      Formalism.L2.DIV.lev D.sp.cm V.gram β (datY V.rank V.rank t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) := by
    ext x
    simp only [Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev]
    constructor
    · rintro ⟨⟨h1, h2, h3, _⟩, h5⟩
      refine ⟨⟨h1, h2, h3, fun PP hPP => ?_⟩, h5⟩
      change PP ∈ (∅ : Finset (Formalism.L2.DIV.Pl D.host.E)) at hPP
      simp at hPP
    · rintro ⟨⟨h1, h2, h3, _⟩, h5⟩
      exact ⟨⟨h1, h2, h3, fun PP _ => mem_blockTriangular_singleBlock_of_le (r := V.rank) le_rfl _⟩, h5⟩
  have hfn : ∀ y, Formalism.L2.DIV.levFn β (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B) y =
      Formalism.L2.DIV.levFn β (datY V.rank V.rank t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) y := by
    intro y
    unfold Formalism.L2.DIV.levFn
    have hq : ∏ PP ∈ (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).Q,
        (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).xq PP
          (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).r) 1
            (Formalism.L2.DIV.redFn β PP y)) = 1 := by
      refine Finset.prod_eq_one fun PP _ => ?_
      have h2 := blockDet_singleBlock_second_eq_one_of_le (r := V.rank) (le_refl V.rank) (Formalism.L2.DIV.redFn β PP y)
      exact (congrArg (⇑((datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).xq PP)) h2).trans (map_one _)
    rw [hq]
    change _ = _ * ∏ PP ∈ (∅ : Finset (Formalism.L2.DIV.Pl D.host.E)), _
    rw [Finset.prod_empty]
    rfl
  refine ⟨?_, fun k _ => ?_⟩
  · unfold levG
    rw [hlev]
  · unfold levChi
    rw [hfn]

end GlobalTheory
