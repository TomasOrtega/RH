import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SHTensorPf

def LocTensor : Prop := ∀ {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z), IsPushout x b u v →
  SH A → SH X → IsLocalHom x.hom → b.hom.IsIntegral → IsLocalRing B → IsLocalRing Z

def SepTensor : Prop := ∀ {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z), IsPushout x b u v →
  SH A → SH X → IsLocalHom x.hom → b.hom.IsIntegral → IsLocalRing B → ∀ (_ : IsLocalRing Z),
  IsSepClosed (IsLocalRing.ResidueField Z)

/- English proof (translation)
Establish `h : (RingHom.toMorphismProperty fun f => f.IsIntegral).IsStableUnderCobaseChange` using `RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.isIntegral_isStableUnderBaseChange`. Conclude with `h.of_isPushout hp hb`.
-/
theorem intPush {A X B Z : CommRingCat.{0}} {x : A ⟶ X} {b : A ⟶ B} {u : X ⟶ Z} {v : B ⟶ Z}
    (hp : IsPushout x b u v) (hb : b.hom.IsIntegral) : u.hom.IsIntegral := by
  have h : (RingHom.toMorphismProperty fun f => f.IsIntegral).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.isIntegral_isStableUnderBaseChange
  exact h.of_isPushout hp hb

/- English proof (translation)
Establish `h0 : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, he.eq, sub_self]`. Break down `IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h` into its components or cases. Use `right`. Conclude with `(sub_eq_zero.mp ((h.mul_right_eq_zero).mp h0)).symm`. Use `left`.

Conclude with `(h.mul_left_eq_zero).mp h0`.
-/
theorem idem_local (R : Type) [CommRing R] [IsLocalRing R] (e : R) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · right; exact (sub_eq_zero.mp ((h.mul_right_eq_zero).mp h0)).symm
  · left; exact (h.mul_left_eq_zero).mp h0

/- English proof (translation)
Introduce `A X B Z x b u v hp hA hX hx hb hB`. Establish `hZ : IsLocalRing Z` using `hL x b u v hp hA hX hx hb hB`. Establish `hsep` using `hS x b u v hp hA hX hx hb hB hZ`. Take `⟨hXh, _⟩` from `hX`. Take `⟨hZh⟩` from `hH X Z u.hom (intPush hp hb) (idem_local Z)`.

Conclude with `⟨hZh, hsep⟩`.
-/
theorem SHTensor_of (hH : LateralTheory.E.t_E3Cut.HensInt) (hL : LocTensor) (hS : SepTensor) : LateralTheory.E.t_E3Cut.SHTensor := by
  intro A X B Z x b u v hp hA hX hx hb hB
  have hZ : IsLocalRing Z := hL x b u v hp hA hX hx hb hB
  have hsep := hS x b u v hp hA hX hx hb hB hZ
  obtain ⟨hXh, _⟩ := hX
  obtain ⟨hZh⟩ := hH X Z u.hom (intPush hp hb) (idem_local Z)
  exact ⟨hZh, hsep⟩

end LateralTheory.E.SHTensorPf
