import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieLatFin
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CompFintype

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp

variable {D : D7}

/- English proof (translation)
Establish `hW` using `Formalism.MainNotions.G.Joints.weylSandwich_of_model D (Formalism.L2.G.Model.modelSandwichG_of_ties D Gt)`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `Z ⟨F, hF, rfl⟩`. Use `⟨F, fun v => ?_, rfl⟩` and prove the remaining obligations. Use `(Submodule.span_mono ?_ : HtenW (D.gat u w hg).O _ _ ≤ Hten (D.gat u w hg).O _ _) (hF v)` and prove the remaining obligations.

Introduce and unpack `Y ⟨F', hF', rfl⟩`. Conclude with `⟨F', fun s => (hW u w hg _ _ _).2 (hF' s), rfl⟩`.
-/
theorem htupW_le_htupJ (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : Fills (D.gat u w hg)) (j : ℕ) (L : (Fl.Pj j).Tup) :
    (Fl.Pj j).HtupW L ≤ (Fl.Pj j).Htup L := by
  have hW := Formalism.MainNotions.G.Joints.weylSandwich_of_model D (Formalism.L2.G.Model.modelSandwichG_of_ties D Gt)
  refine Submodule.span_mono ?_
  rintro Z ⟨F, hF, rfl⟩
  refine ⟨F, fun v => ?_, rfl⟩
  refine (Submodule.span_mono ?_ : HtenW (D.gat u w hg).O _ _ ≤ Hten (D.gat u w hg).O _ _) (hF v)
  rintro Y ⟨F', hF', rfl⟩
  exact ⟨F', fun s => (hW u w hg _ _ _).2 (hF' s), rfl⟩

/- English proof (translation)
Use `Formalism.MainNotions.FormalGroupSystem.Pf.m_finite (gatJ Lv j) h ?_` and prove the remaining obligations. Introduce `F hF`. Establish `h1` using `(mem_funMod_iff (gatJ Lv j) (gatJ Lv j).P.HtupW F).1 hF`. Use `(mem_funMod_iff (gatJ Lv j) (gatJ Lv j).P.Htup F).2 fun i => ?_` and prove the remaining obligations. Conclude with `⟨fun L hL => htupW_le_htupJ Gt u w hg Fl j L ((h1 i).1 L hL), (h1 i).2⟩`.
-/
theorem mfin_of (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w hg)} (Lv : Levels Fl) (j : ℕ)
    (h : (gatJ Lv j).FinClasses) : Module.Finite (D.gat u w hg).O (gatJ Lv j).M := by
  refine Formalism.MainNotions.FormalGroupSystem.Pf.m_finite (gatJ Lv j) h ?_
  intro F hF
  have h1 := (mem_funMod_iff (gatJ Lv j) (gatJ Lv j).P.HtupW F).1 hF
  refine (mem_funMod_iff (gatJ Lv j) (gatJ Lv j).P.Htup F).2 fun i => ?_
  exact ⟨fun L hL => htupW_le_htupJ Gt u w hg Fl j L ((h1 i).1 L hL), (h1 i).2⟩

end Formalism.MainNotions.G.CmpJ

end
