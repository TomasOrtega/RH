import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.MVPf

def MVSpc : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ n : ℤ, (∀ c : H R (pullback f g) F n, ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) →
  ∀ x : H R E F (n + 1), pull R f F _ x = 0 → pull R g F _ x = 0 → x = 0

def StdCover : Prop := ∀ (R : Type) [CommRing R] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  Cover2 R (spMap (algebraMap S (Localization.Away f))) (spMap (algebraMap S (Localization.Away g)))

def StdPB : Prop := ∀ (S : Type) [CommRing S] (f g : S),
  ∃ e : sp (Localization.Away (f * g)) ⟶
      pullback (spMap (algebraMap S (Localization.Away f))) (spMap (algebraMap S (Localization.Away g))),
    IsIso e ∧ e ≫ pullback.fst _ _ = spMap (LateralTheory.E.t_E1Cut.rL f g) ∧ e ≫ pullback.snd _ _ = spMap (LateralTheory.E.t_E1Cut.rR f g)

/- English proof (translation)
Introduce `x y h`. Establish `hx : pull R (inv e) F n (pull R e F n x) = x`. Rewrite using `[← pull_comp, IsIso.inv_hom_id, pull_id]`. Establish `hy : pull R (inv e) F n (pull R e F n y) = y`. Rewrite using `[← pull_comp, IsIso.inv_hom_id, pull_id]`.

Rewrite using `[← hx, ← hy, h]`.
-/
theorem pull_inj_of_iso (R : Type) [CommRing R] {E E' : Spc} (e : E ⟶ E') [IsIso e] (F : Shv R) (n : ℤ) :
    Function.Injective (pull R e F n) := by
  intro x y h
  have hx : pull R (inv e) F n (pull R e F n x) = x := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have hy : pull R (inv e) F n (pull R e F n y) = y := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  rw [← hx, ← hy, h]

end LateralTheory.E.MVPf

open LateralTheory.E.MVPf in
/- English proof (translation)
Introduce `hA1 R _ F S _ f g hfg n hc x hxf hxg`. Use `h1 hA1 R F _ _ (h2 R S f g hfg) n ?_ x hxf hxg` and prove the remaining obligations. Introduce `c`. Take `⟨e, he, hfst, hsnd⟩` from `h3 S f g`. Take `⟨a, b, hab⟩` from `hc (pull R e F n c)`.

Use `⟨a, b, pull_inj_of_iso R e F n ?_⟩` and prove the remaining obligations. Rewrite using `[hab, map_sub, ← pull_comp, ← pull_comp, hfst, hsnd]`.
-/
theorem LateralTheory.E.t_E1Cut.MV_of (h1 : MVSpc) (h2 : StdCover) (h3 : StdPB) : LateralTheory.E.t_E1Cut.MV := by
  intro hA1 R _ F S _ f g hfg n hc x hxf hxg
  refine h1 hA1 R F _ _ (h2 R S f g hfg) n ?_ x hxf hxg
  intro c
  obtain ⟨e, he, hfst, hsnd⟩ := h3 S f g
  obtain ⟨a, b, hab⟩ := hc (pull R e F n c)
  refine ⟨a, b, pull_inj_of_iso R e F n ?_⟩
  rw [hab, map_sub, ← pull_comp, ← pull_comp, hfst, hsnd]
