import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev

/- English proof (translation)
Establish `hm : z - z' ∈ wSub D w0 r`. Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Simplify `hz` using `[sub_eq_zero]`. Use `h.1 z' (z - z')` as an intermediate fact. Rewrite `this` using `[add_sub_cancel, h.2.2.1 _ hm, _root_.mul_one]`.

Conclude with `this`.
-/
theorem isEtLevOver_eq_of_mkQ_eq {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ} {T : Over S}
    {l : D.La → (T ⟶ o.A)} (h : IsEtLevOver o w0 r l) {z z' : D.La}
    (hz : (wSub D w0 r).mkQ z = (wSub D w0 r).mkQ z') : l z = l z' := by
  have hm : z - z' ∈ wSub D w0 r := by
    rw [← Submodule.Quotient.mk_eq_zero]; simpa [sub_eq_zero] using hz
  have := h.1 z' (z - z')
  rw [add_sub_cancel, h.2.2.1 _ hm, _root_.mul_one] at this
  exact this

/- English proof (translation)
Establish `hq` using `fun {z z' : D.La} (hz : (wSub D w0 r).mkQ z = (wSub D w0 r).mkQ z') => isEtLevOver_eq_of_mkQ_eq h hz`. Use `⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x => ⟨fun y hy => ?_, fun gg hgg => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← h.1]`. Apply `hq` to reduce the goal to its premises. Simplify using `only [mkQ_levAct, map_add]`.

Rewrite using `[← h.2.1]`. Apply `hq` to reduce the goal to its premises. Simplify using `only [mkQ_levAct, map_smul]`. Establish `: levAct g x ∈ wSub D w0 r`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, mkQ_levAct, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hx, map_zero]`.

Conclude with `h.2.2.1 _ this`. Establish `h1` using `(h.2.2.2 k x).1 _ hy`. Rewrite `h1` using `[← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, mkQ_levAct]`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]`. Conclude with `(LinearEquiv.map_eq_zero_iff g).1 h1`.

Take `⟨y, hy⟩` from `(h.2.2.2 k x).2 gg hgg`. Use `⟨levAct g.symm y, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy]`. Use `congr 1`. Apply `hq` to reduce the goal to its premises.

Simplify using `only [mkQ_levAct, LinearEquiv.apply_symm_apply]`.
-/
theorem isEtLevOver_levAct (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T : Over S)
    (l : D.La → (T ⟶ o.A)) (g : LevGrp D w0 r) (h : IsEtLevOver o w0 r l) :
    IsEtLevOver o w0 r (fun y => l (levAct g y)) := by
  have hq := fun {z z' : D.La} (hz : (wSub D w0 r).mkQ z = (wSub D w0 r).mkQ z') =>
    isEtLevOver_eq_of_mkQ_eq h hz
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x => ⟨fun y hy => ?_, fun gg hgg => ?_⟩⟩
  · rw [← h.1]; apply hq
    simp only [mkQ_levAct, map_add]
  · rw [← h.2.1]; apply hq
    simp only [mkQ_levAct, map_smul]
  · have : levAct g x ∈ wSub D w0 r := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, mkQ_levAct,
        Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hx, map_zero]
    exact h.2.2.1 _ this
  · have h1 := (h.2.2.2 k x).1 _ hy
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, mkQ_levAct] at h1
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    exact (LinearEquiv.map_eq_zero_iff g).1 h1
  · obtain ⟨y, hy⟩ := (h.2.2.2 k x).2 gg hgg
    refine ⟨levAct g.symm y, ?_⟩
    rw [← hy]; congr 1; apply hq
    simp only [mkQ_levAct, LinearEquiv.apply_symm_apply]

end GlobalTheory.UPel.HT.EtLev
