import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.SHExistsPf

def SHLoc : Prop := ∀ (A : CommRingCat.{0}) [IsLocalRing A],
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O), IE f ∧ SH O ∧ IsLocalHom f.hom

def LocAt : Prop := ∀ (A : CommRingCat.{0}) (r : Ideal A) [r.IsPrime],
  IE (CommRingCat.ofHom (algebraMap A (Localization.AtPrime r)))

def Comp : Prop := ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), IE f → IE g → IE (f ≫ g)

/- English proof (translation)
Introduce `A r hr`. Set `L : CommRingCat.{0}` to `CommRingCat.of (Localization.AtPrime r)`. Set `g : A ⟶ L` to `CommRingCat.ofHom (algebraMap A (Localization.AtPrime r))`. Use `haveI : IsLocalRing L := inferInstanceAs (IsLocalRing (Localization.AtPrime r))`. Take `⟨O, h, hIE, hSH, hloc⟩` from `hL L`.

Use `⟨O, g ≫ h, hC g h (hA A r) hIE, hSH, fun a => ?_⟩` and prove the remaining obligations. Establish `key : IsUnit (algebraMap A (Localization.AtPrime r) a) ↔ a ∈ r.primeCompl` using `IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime r) r a`. Establish `e : (g ≫ h).hom a = h.hom (algebraMap A (Localization.AtPrime r) a)` using `rfl`. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion.

Introduce `ha hu`. Use `(key.1 (isUnit_of_map_unit h.hom _ hu))` as an intermediate fact. Conclude with `this ha`. Introduce `hn`. Assume the negation of the conclusion as `ha`.

Conclude with `hn ((key.2 ha).map h.hom)`.
-/
theorem SHExists_of (hL : SHLoc) (hA : LocAt) (hC : Comp) : t_E3Cut.SHExists := by
  intro A r hr
  let L : CommRingCat.{0} := CommRingCat.of (Localization.AtPrime r)
  let g : A ⟶ L := CommRingCat.ofHom (algebraMap A (Localization.AtPrime r))
  haveI : IsLocalRing L := inferInstanceAs (IsLocalRing (Localization.AtPrime r))
  obtain ⟨O, h, hIE, hSH, hloc⟩ := hL L
  refine ⟨O, g ≫ h, hC g h (hA A r) hIE, hSH, fun a => ?_⟩
  have key : IsUnit (algebraMap A (Localization.AtPrime r) a) ↔ a ∈ r.primeCompl :=
    IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime r) r a
  have e : (g ≫ h).hom a = h.hom (algebraMap A (Localization.AtPrime r) a) := rfl
  rw [e]
  constructor
  · intro ha hu
    have := (key.1 (isUnit_of_map_unit h.hom _ hu))
    exact this ha
  · intro hn
    by_contra ha
    exact hn ((key.2 ha).map h.hom)

end LateralTheory.E.SHExistsPf
