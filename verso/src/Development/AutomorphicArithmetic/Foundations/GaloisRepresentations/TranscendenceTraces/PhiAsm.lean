import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiExact
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `Q Z S p _`. Use `⟨phi p (ZMod Q), inferInstance, fun G => phiE p G, ⟨fun f A a => ?_, fun G J t => hU Q p G J t⟩, fun T hT => hE _ p T hT⟩` and prove the remaining obligations. Rewrite using `[phiE_app, phiE_app, phiSec_map, DS.map_inc, map_res]`.
-/
theorem phiEx_of_parts (hU : PhiUniv) (hE : PhiExact) : PhiEx := by
  intro Q Z S p _
  refine ⟨phi p (ZMod Q), inferInstance, fun G => phiE p G, ⟨fun f A a => ?_, fun G J t => hU Q p G J t⟩,
    fun T hT => hE _ p T hT⟩
  rw [phiE_app, phiE_app, phiSec_map, DS.map_inc, map_res]

/- English proof (translation)
Introduce `Q Z S p _ F G t`. Take `⟨Φ, _, e, hr, hex⟩` from `hP Q p`. Take `⟨ε, hq, hε⟩` from `hQ _ Φ hex F`. Take `⟨h1, h2⟩` from `hX _ (Φ.obj F) G _ ε`. Take `⟨k1, k2⟩` from `hH Q p Φ e hr (res _ F) (res _ G)`.

Take `⟨a0, ha0, -⟩` from `hr.univ F G t`. Establish `key : ∀ (m : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res _ F) ⟶ res _ G) (A : Sq p) (a : Sec F A.V), Sec.map (sglι (Φ.obj F) ≫ ε.f 0 ≫ m.f 0) ((e F).app A a) = Sec.map (F` using `Φ.obj ((res _ F).X 0)) (m.f 0) ((e _).app A (Sec.map (resι _ F) a)) := by`. Introduce `m A a`. Rewrite using `[← hr.nat, ← hε]`. Both sides reduce to the same expression.

Use `⟨?_, fun τ τ' hτ hτ' A m n k hm hn a ha => ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `h1 a0`. Take `⟨τ, hτ⟩` from `k1 m`. Use `⟨τ, fun A a => ?_⟩` and prove the remaining obligations. Rewrite using `[hτ, ← key, hm, ← ha0]`.

Both sides reduce to the same expression. Take `⟨u, hu⟩` from `k2 τ`. Take `⟨u', hu'⟩` from `k2 τ'`. Set `t' : Fam0 p F ((res _ G).X 0)` to `{ app := fun A => ((resι _ G).hom.app (op A.U)).hom.toAddMonoidHom.comp (t.app A) nat := fun s a => (map_res (resι _ G) s.g _).symm.trans (congrArg _ (t.nat s a)) }`. Establish `e0 : sglι (Φ.obj F) ≫ ε.f 0 ≫ u.f 0 = sglι (Φ.obj F) ≫ ε.f 0 ≫ u'.f 0` using `(hr.univ F _ t').unique (fun A a => by rw [key, ← hu]; exact hτ A a) (fun A a => by rw [key, ← hu']; exact hτ' A a)`.

Establish `hy : Sec.map (((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res _ F)).d n k) ((e _).app A a) = 0`. Use `(hr.nat ((res _ F).d n k) A a).trans ?_` and prove the remaining obligations. Rewrite using `[ha]`. Conclude with `map_zero _`. Take `⟨c, hc⟩` from `h2 u u' e0 A.U m n k hm hn _ hy`.

Conclude with `⟨c, by rw [hu, hu']; exact hc⟩`.
-/
theorem fL_of_parts (hQ : PhiQis) (hX : ExtRes) (hH : FamHom) (hP : PhiEx) : FL := by
  intro Q Z S p _ F G t
  obtain ⟨Φ, _, e, hr, hex⟩ := hP Q p
  obtain ⟨ε, hq, hε⟩ := hQ _ Φ hex F
  obtain ⟨h1, h2⟩ := hX _ (Φ.obj F) G _ ε
  obtain ⟨k1, k2⟩ := hH Q p Φ e hr (res _ F) (res _ G)
  obtain ⟨a0, ha0, -⟩ := hr.univ F G t
  have key : ∀ (m : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res _ F) ⟶ res _ G) (A : Sq p) (a : Sec F A.V),
      Sec.map (sglι (Φ.obj F) ≫ ε.f 0 ≫ m.f 0) ((e F).app A a) =
        Sec.map (F := Φ.obj ((res _ F).X 0)) (m.f 0) ((e _).app A (Sec.map (resι _ F) a)) := by
    intro m A a
    rw [← hr.nat, ← hε]
    rfl
  refine ⟨?_, fun τ τ' hτ hτ' A m n k hm hn a ha => ?_⟩
  · obtain ⟨m, hm⟩ := h1 a0
    obtain ⟨τ, hτ⟩ := k1 m
    refine ⟨τ, fun A a => ?_⟩
    rw [hτ, ← key, hm, ← ha0]
    rfl
  · obtain ⟨u, hu⟩ := k2 τ
    obtain ⟨u', hu'⟩ := k2 τ'
    let t' : Fam0 p F ((res _ G).X 0) :=
      { app := fun A => ((resι _ G).hom.app (op A.U)).hom.toAddMonoidHom.comp (t.app A)
        nat := fun s a => (map_res (resι _ G) s.g _).symm.trans (congrArg _ (t.nat s a)) }
    have e0 : sglι (Φ.obj F) ≫ ε.f 0 ≫ u.f 0 = sglι (Φ.obj F) ≫ ε.f 0 ≫ u'.f 0 :=
      (hr.univ F _ t').unique (fun A a => by rw [key, ← hu]; exact hτ A a) (fun A a => by rw [key, ← hu']; exact hτ' A a)
    have hy : Sec.map (((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res _ F)).d n k) ((e _).app A a) = 0 := by
      refine (hr.nat ((res _ F).d n k) A a).trans ?_
      rw [ha]
      exact map_zero _
    obtain ⟨c, hc⟩ := h2 u u' e0 A.U m n k hm hn _ hy
    exact ⟨c, by rw [hu, hu']; exact hc⟩

end UpperTheory.Gal.TranscendenceTraces
