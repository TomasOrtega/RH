import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Substitute `hA` using the available equality. Substitute `hB` using the available equality. Simplify `h` using `only [eqToHom_refl, Category.id_comp, Category.comp_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]`.
-/
theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.of_eq {A A' B B' : Scheme.{u}} {π : A ⟶ B} {J : B.IdealSheafData}
    (h : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π J) (hA : A = A') (hB : B = B') :
    FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf (eqToHom hA.symm ≫ π ≫ eqToHom hB) (J.comap (eqToHom hB.symm)) := by
  subst hA
  subst hB
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id] using h

namespace BlowupSequenceData

variable {X : Scheme.{u}}

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[eqToHom_refl, Category.id_comp]`.
-/
theorem projectionToBase_congr (d : BlowupSequenceData X) {n n' : ℕ} (h : n = n') :
    projectionToBase d n = eqToHom (congrArg d.obj h) ≫ projectionToBase d n' := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

variable (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))

def appendSchemeAt (i : ℕ) : Scheme.{u} :=
  if i ≤ s.length then s.obj i else t.obj (i - s.length)

/- English proof (translation)
The claim follows from `if_pos h`.
-/
theorem appendSchemeAt_of_le_length {i : ℕ} (h : i ≤ s.length) : appendSchemeAt s t i = s.obj i := if_pos h

/- English proof (translation)
The claim follows from `if_neg (not_le.2 h)`.
-/
theorem appendSchemeAt_of_length_lt {i : ℕ} (h : s.length < i) :
    appendSchemeAt s t i = t.obj (i - s.length) := if_neg (not_le.2 h)

/- English proof (translation)
The claim follows from `appendSchemeAt_of_le_length s t (Nat.zero_le _)`.
-/
theorem appendSchemeAt_zero : appendSchemeAt s t 0 = s.obj 0 := appendSchemeAt_of_le_length s t (Nat.zero_le _)

/- English proof (translation)
The claim follows from `appendSchemeAt_of_le_length s t (by omega)`.
-/
theorem appendSchemeAt_succ_of_lt_length {i : ℕ} (h : i < s.length) :
    appendSchemeAt s t (i + 1) = s.obj (i + 1) :=
  appendSchemeAt_of_le_length s t (by omega)

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `appendSchemeAt_of_le_length s t le_rfl`.
-/
theorem appendSchemeAt_of_eq_length {i : ℕ} (h : i = s.length) : appendSchemeAt s t i = s.obj s.length := by
  subst h
  exact appendSchemeAt_of_le_length s t le_rfl

/- English proof (translation)
Substitute `h` using the available equality. Establish `h2 : s.length + 1 - s.length = 1` using `by omega`. Rewrite using `[appendSchemeAt_of_length_lt s t (by omega), h2]`.
-/
theorem appendSchemeAt_succ_of_eq_length {i : ℕ} (h : i = s.length) :
    appendSchemeAt s t (i + 1) = t.obj 1 := by
  subst h
  have h2 : s.length + 1 - s.length = 1 := by omega
  rw [appendSchemeAt_of_length_lt s t (by omega), h2]

/- English proof (translation)
Establish `h2 : i + 1 - s.length = i - s.length + 1` using `by omega`. Rewrite using `[appendSchemeAt_of_length_lt s t (by omega), h2]`.
-/
theorem appendSchemeAt_succ_of_length_lt {i : ℕ} (h : s.length < i) :
    appendSchemeAt s t (i + 1) = t.obj (i - s.length + 1) := by
  have h2 : i + 1 - s.length = i - s.length + 1 := by omega
  rw [appendSchemeAt_of_length_lt s t (by omega), h2]

def appendBlowupMorphism (i : ℕ) : appendSchemeAt s t (i + 1) ⟶ appendSchemeAt s t i :=
  if h : i < s.length then
    eqToHom (appendSchemeAt_succ_of_lt_length s t h) ≫ s.map i ≫ eqToHom (appendSchemeAt_of_le_length s t (le_of_lt h)).symm
  else if h2 : s.length < i then
    eqToHom (appendSchemeAt_succ_of_length_lt s t h2) ≫ t.map (i - s.length) ≫
      eqToHom (appendSchemeAt_of_length_lt s t h2).symm
  else
    eqToHom (appendSchemeAt_succ_of_eq_length s t (by omega)) ≫ t.map 0 ≫ t.isoZero.hom ≫
      eqToHom (appendSchemeAt_of_eq_length s t (by omega)).symm

def appendCenter (i : ℕ) : (appendSchemeAt s t i).IdealSheafData :=
  if h : i < s.length then (s.center i).comap (eqToHom (appendSchemeAt_of_le_length s t (le_of_lt h)))
  else if h2 : s.length < i then (t.center (i - s.length)).comap (eqToHom (appendSchemeAt_of_length_lt s t h2))
  else ((t.center 0).comap t.isoZero.inv).comap (eqToHom (appendSchemeAt_of_eq_length s t (by omega)))

/- English proof (translation)
Break down `lt_trichotomy i s.length with h | h | h` into its components or cases. Establish `hmap : appendBlowupMorphism s t i = eqToHom (appendSchemeAt_succ_of_lt_length s t h) ≫ s.map i ≫ eqToHom (appendSchemeAt_of_le_length s t (le_of_lt h)).symm` using `dif_pos h`. Establish `hcen : appendCenter s t i = (s.center i).comap (eqToHom (appendSchemeAt_of_le_length s t (le_of_lt h)))` using `dif_pos h`. Rewrite using `[hmap, hcen]`. Conclude with `Blowup.IsBlowupAlongIdealSheaf.of_eq (s.isBlowup i h) (appendSchemeAt_succ_of_lt_length s t h).symm (appendSchemeAt_of_le_length s t (le_of_lt h)).symm`.

Substitute `h` using the available equality. Establish `ht : 0 < t.length` using `by omega`. Establish `hmap : appendBlowupMorphism s t s.length = eqToHom (appendSchemeAt_succ_of_eq_length s t (rfl : s.length = s.length)) ≫ t.map 0 ≫ t.isoZero.hom ≫ eqToHom (appendSchemeAt_of_eq_length s t (rfl : s.length = s.length)).symm` using `(dif_neg (lt_irrefl s.length)).trans (dif_neg (lt_irrefl s.length))`. Establish `hcen : appendCenter s t s.length = ((t.center 0).comap t.isoZero.inv).comap (eqToHom (appendSchemeAt_of_eq_length s t (rfl : s.length = s.length)))` using `(dif_neg (lt_irrefl s.length)).trans (dif_neg (lt_irrefl s.length))`. Rewrite using `[hmap, hcen, ← Category.assoc (t.map 0) t.isoZero.hom]`.

Conclude with `Blowup.IsBlowupAlongIdealSheaf.of_eq (Blowup.IsBlowupAlongIdealSheaf.comp_iso_hom (t.isBlowup 0 ht) t.isoZero) (appendSchemeAt_succ_of_eq_length s t (rfl : s.length = s.length)).symm (appendSchemeAt_of_eq_length s t (rfl : s.length = s.length)).symm`. Establish `hlt : i - s.length < t.length` using `by omega`. Establish `hmap : appendBlowupMorphism s t i = eqToHom (appendSchemeAt_succ_of_length_lt s t h) ≫ t.map (i - s.length) ≫ eqToHom (appendSchemeAt_of_length_lt s t h).symm` using `(dif_neg (not_lt.2 (le_of_lt h))).trans (dif_pos h)`. Establish `hcen : appendCenter s t i = (t.center (i - s.length)).comap (eqToHom (appendSchemeAt_of_length_lt s t h))` using `(dif_neg (not_lt.2 (le_of_lt h))).trans (dif_pos h)`. Rewrite using `[hmap, hcen]`.

Conclude with `Blowup.IsBlowupAlongIdealSheaf.of_eq (t.isBlowup (i - s.length) hlt) (appendSchemeAt_succ_of_length_lt s t h).symm (appendSchemeAt_of_length_lt s t h).symm`.
-/
theorem isBlowupAlongIdealSheaf_appendBlowupMorphism (i : ℕ) (hi : i < s.length + t.length) :
    Blowup.IsBlowupAlongIdealSheaf (appendBlowupMorphism s t i) (appendCenter s t i) := by
  rcases lt_trichotomy i s.length with h | h | h
  · have hmap : appendBlowupMorphism s t i =
        eqToHom (appendSchemeAt_succ_of_lt_length s t h) ≫ s.map i ≫
          eqToHom (appendSchemeAt_of_le_length s t (le_of_lt h)).symm := dif_pos h
    have hcen : appendCenter s t i =
        (s.center i).comap (eqToHom (appendSchemeAt_of_le_length s t (le_of_lt h))) := dif_pos h
    rw [hmap, hcen]
    exact Blowup.IsBlowupAlongIdealSheaf.of_eq (s.isBlowup i h) (appendSchemeAt_succ_of_lt_length s t h).symm
      (appendSchemeAt_of_le_length s t (le_of_lt h)).symm
  · subst h
    have ht : 0 < t.length := by omega
    have hmap : appendBlowupMorphism s t s.length =
        eqToHom (appendSchemeAt_succ_of_eq_length s t (rfl : s.length = s.length)) ≫ t.map 0 ≫
          t.isoZero.hom ≫
            eqToHom (appendSchemeAt_of_eq_length s t (rfl : s.length = s.length)).symm :=
      (dif_neg (lt_irrefl s.length)).trans (dif_neg (lt_irrefl s.length))
    have hcen : appendCenter s t s.length =
        ((t.center 0).comap t.isoZero.inv).comap
          (eqToHom (appendSchemeAt_of_eq_length s t (rfl : s.length = s.length))) :=
      (dif_neg (lt_irrefl s.length)).trans (dif_neg (lt_irrefl s.length))
    rw [hmap, hcen, ← Category.assoc (t.map 0) t.isoZero.hom]
    exact Blowup.IsBlowupAlongIdealSheaf.of_eq (Blowup.IsBlowupAlongIdealSheaf.comp_iso_hom (t.isBlowup 0 ht) t.isoZero)
      (appendSchemeAt_succ_of_eq_length s t (rfl : s.length = s.length)).symm
      (appendSchemeAt_of_eq_length s t (rfl : s.length = s.length)).symm
  · have hlt : i - s.length < t.length := by omega
    have hmap : appendBlowupMorphism s t i =
        eqToHom (appendSchemeAt_succ_of_length_lt s t h) ≫ t.map (i - s.length) ≫
          eqToHom (appendSchemeAt_of_length_lt s t h).symm :=
      (dif_neg (not_lt.2 (le_of_lt h))).trans (dif_pos h)
    have hcen : appendCenter s t i =
        (t.center (i - s.length)).comap (eqToHom (appendSchemeAt_of_length_lt s t h)) :=
      (dif_neg (not_lt.2 (le_of_lt h))).trans (dif_pos h)
    rw [hmap, hcen]
    exact Blowup.IsBlowupAlongIdealSheaf.of_eq (t.isBlowup (i - s.length) hlt)
      (appendSchemeAt_succ_of_length_lt s t h).symm (appendSchemeAt_of_length_lt s t h).symm

def append : BlowupSequenceData X where
  length := s.length + t.length
  obj := appendSchemeAt s t
  map := appendBlowupMorphism s t
  isoZero := eqToIso (appendSchemeAt_zero s t) ≪≫ s.isoZero
  center := appendCenter s t
  isBlowup := fun i hi => isBlowupAlongIdealSheaf_appendBlowupMorphism s t i hi

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem append_length : (s.append t).length = s.length + t.length := rfl

/- English proof (translation)
The claim follows from `appendSchemeAt_of_le_length s t h`.
-/
theorem append_schemeAt_of_le_length {i : ℕ} (h : i ≤ s.length) : (s.append t).obj i = s.obj i :=
  appendSchemeAt_of_le_length s t h

/- English proof (translation)
The claim follows from `appendSchemeAt_of_length_lt s t h`.
-/
theorem append_schemeAt_of_length_lt {i : ℕ} (h : s.length < i) :
    (s.append t).obj i = t.obj (i - s.length) :=
  appendSchemeAt_of_length_lt s t h

/- English proof (translation)
The claim follows from `appendSchemeAt_zero s t`.
-/
theorem append_schemeAt_zero : (s.append t).obj 0 = s.obj 0 := appendSchemeAt_zero s t

/- English proof (translation)
The claim follows from `appendSchemeAt_succ_of_lt_length s t h`.
-/
theorem append_schemeAt_succ_of_lt_length {i : ℕ} (h : i < s.length) :
    (s.append t).obj (i + 1) = s.obj (i + 1) :=
  appendSchemeAt_succ_of_lt_length s t h

/- English proof (translation)
The claim follows from `appendSchemeAt_succ_of_length_lt s t h`.
-/
theorem append_schemeAt_succ_of_length_lt {i : ℕ} (h : s.length < i) :
    (s.append t).obj (i + 1) = t.obj (i - s.length + 1) :=
  appendSchemeAt_succ_of_length_lt s t h

/- English proof (translation)
The claim follows from `appendSchemeAt_succ_of_eq_length s t rfl`.
-/
theorem append_schemeAt_length_succ : (s.append t).obj (s.length + 1) = t.obj 1 :=
  appendSchemeAt_succ_of_eq_length s t rfl

/- English proof (translation)
Establish `h2 : s.length + t.length - s.length = t.length` using `by omega`. Use `show appendSchemeAt s t (s.length + t.length) = t.obj t.length`. Rewrite using `[appendSchemeAt_of_length_lt s t (by omega), h2]`.
-/
theorem append_schemeAt_length_add_length (h : 0 < t.length) :
    (s.append t).obj (s.length + t.length) = t.obj t.length := by
  have h2 : s.length + t.length - s.length = t.length := by omega
  show appendSchemeAt s t (s.length + t.length) = t.obj t.length
  rw [appendSchemeAt_of_length_lt s t (by omega), h2]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem append_isoObjZero_hom :
    (s.append t).isoZero.hom = eqToHom (append_schemeAt_zero s t) ≫ s.isoZero.hom := rfl

/- English proof (translation)
Conclude with `dif_pos h`.
-/
theorem append_blowupMorphism_of_lt_length {i : ℕ} (h : i < s.length) :
    (s.append t).map i =
      eqToHom (append_schemeAt_succ_of_lt_length s t h) ≫ s.map i ≫
        eqToHom (append_schemeAt_of_le_length s t (le_of_lt h)).symm := by
  exact dif_pos h

/- English proof (translation)
Conclude with `(dif_neg (not_lt.2 (le_of_lt h))).trans (dif_pos h)`.
-/
theorem append_blowupMorphism_of_length_lt {i : ℕ} (h : s.length < i) :
    (s.append t).map i =
      eqToHom (append_schemeAt_succ_of_length_lt s t h) ≫ t.map (i - s.length) ≫
        eqToHom (append_schemeAt_of_length_lt s t h).symm := by
  exact (dif_neg (not_lt.2 (le_of_lt h))).trans (dif_pos h)

/- English proof (translation)
Conclude with `(dif_neg (lt_irrefl s.length)).trans (dif_neg (lt_irrefl s.length))`.
-/
theorem append_blowupMorphism_length :
    (s.append t).map s.length =
      eqToHom (append_schemeAt_length_succ s t) ≫ t.map 0 ≫ t.isoZero.hom ≫
        eqToHom (append_schemeAt_of_le_length s t (le_refl s.length)).symm := by
  exact (dif_neg (lt_irrefl s.length)).trans (dif_neg (lt_irrefl s.length))

/- English proof (translation)
Conclude with `dif_pos h`.
-/
theorem append_center_of_lt_length {i : ℕ} (h : i < s.length) :
    (s.append t).center i = (s.center i).comap (eqToHom (append_schemeAt_of_le_length s t (le_of_lt h))) := by
  exact dif_pos h

/- English proof (translation)
Conclude with `(dif_neg (not_lt.2 (le_of_lt h))).trans (dif_pos h)`.
-/
theorem append_center_of_length_lt {i : ℕ} (h : s.length < i) :
    (s.append t).center i =
      (t.center (i - s.length)).comap (eqToHom (append_schemeAt_of_length_lt s t h)) := by
  exact (dif_neg (not_lt.2 (le_of_lt h))).trans (dif_pos h)

/- English proof (translation)
Conclude with `(dif_neg (lt_irrefl s.length)).trans (dif_neg (lt_irrefl s.length))`.
-/
theorem append_center_length :
    (s.append t).center s.length =
      ((t.center 0).comap t.isoZero.inv).comap
        (eqToHom (append_schemeAt_of_le_length s t (le_refl s.length))) := by
  exact (dif_neg (lt_irrefl s.length)).trans (dif_neg (lt_irrefl s.length))

/- English proof (translation)
Use `revert h`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_`. Both sides reduce to the same expression.

Consider the case `succ n ih`. Introduce `h`. Establish `hn : n < s.length` using `h`. Rewrite using `[projectionToBase_succ, ih (le_of_lt hn), append_blowupMorphism_of_lt_length s t hn, projectionToBase_succ]`. Simplify using the standard rewrite rules.
-/
theorem projectionToBase_append_of_le_length {i : ℕ} (h : i ≤ s.length) :
    projectionToBase (s.append t) i = eqToHom (append_schemeAt_of_le_length s t h) ≫ projectionToBase s i := by
  revert h
  induction i with
  | zero =>
    intro _
    rfl
  | succ n ih =>
    intro h
    have hn : n < s.length := h
    rw [projectionToBase_succ, ih (le_of_lt hn), append_blowupMorphism_of_lt_length s t hn, projectionToBase_succ]
    simp

/- English proof (translation)
Substitute `h` using the available equality. Simplify using the standard rewrite rules.
-/
private theorem blowupMorphism_eq_eqToHom_comp_of_eq {Y : Scheme.{u}} (d : BlowupSequenceData Y) {n n' : ℕ} (h : n = n')
    (e1 : d.obj (n + 1) = d.obj (n' + 1)) (e2 : d.obj n' = d.obj n) :
    d.map n = eqToHom e1 ≫ d.map n' ≫ eqToHom e2 := by
  subst h
  simp

/- English proof (translation)
Substitute `h` using the available equality. Establish `hgt : a.length < a.length + j + 1` using `by omega`. Establish `hsub : a.length + j + 1 - a.length = j + 1` using `by omega`. Rewrite using `[append_schemeAt_of_length_lt a b hgt, hsub]`.
-/
private theorem append_schemeAt_of_eq_length_add_succ {Y : Scheme.{u}} (a : BlowupSequenceData Y)
    (b : BlowupSequenceData (a.obj a.length)) (i j : ℕ) (h : i = a.length + j + 1) :
    (a.append b).obj i = b.obj (j + 1) := by
  subst h
  have hgt : a.length < a.length + j + 1 := by omega
  have hsub : a.length + j + 1 - a.length = j + 1 := by omega
  rw [append_schemeAt_of_length_lt a b hgt, hsub]

/- English proof (translation)
Substitute `h` using the available equality. Establish `hgt : a.length < a.length + j + 1` using `by omega`. Establish `hsub : a.length + j + 1 - a.length = j + 1` using `by omega`. Rewrite using `[append_blowupMorphism_of_length_lt a b hgt, blowupMorphism_eq_eqToHom_comp_of_eq b hsub (by rw [hsub]) (by rw [hsub])]`. Simplify using the standard rewrite rules.
-/
private theorem append_blowupMorphism_of_eq_length_add_succ {Y : Scheme.{u}} (a : BlowupSequenceData Y)
    (b : BlowupSequenceData (a.obj a.length)) (i j : ℕ) (h : i = a.length + j + 1)
    (e1 : (a.append b).obj (i + 1) = b.obj (j + 1 + 1))
    (e2 : b.obj (j + 1) = (a.append b).obj i) :
    (a.append b).map i = eqToHom e1 ≫ b.map (j + 1) ≫ eqToHom e2 := by
  subst h
  have hgt : a.length < a.length + j + 1 := by omega
  have hsub : a.length + j + 1 - a.length = j + 1 := by omega
  rw [append_blowupMorphism_of_length_lt a b hgt, blowupMorphism_eq_eqToHom_comp_of_eq b hsub (by rw [hsub]) (by rw [hsub])]
  simp

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `i hi e`. Establish `hi' : i = a.length + 1` using `by omega`.

Substitute `hi'` using the available equality. Rewrite using `[projectionToBase_succ (a.append b) a.length, append_blowupMorphism_length a b, projectionToBase_append_of_le_length a b le_rfl, projectionToBase_succ b 0, projectionToBase_zero b]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `i hi e`.

Establish `hi' : i = a.length + n + 1 + 1` using `by omega`. Substitute `hi'` using the available equality. Rewrite using `[projectionToBase_succ (a.append b) (a.length + n + 1), append_blowupMorphism_of_eq_length_add_succ a b (a.length + n + 1) n rfl (append_schemeAt_of_eq_length_add_succ a b (a.length + n + 1 + 1) (n + 1) (by omega)) (append_schemeAt_of_eq_length_add_succ a b (a.length + n + 1) n r …`. Simplify using the standard rewrite rules.
-/
private theorem projectionToBase_append_of_eq_length_add_succ {Y : Scheme.{u}} (a : BlowupSequenceData Y)
    (b : BlowupSequenceData (a.obj a.length)) :
    ∀ (j i : ℕ), i = a.length + j + 1 → ∀ (e : (a.append b).obj i = b.obj (j + 1)),
      projectionToBase (a.append b) i = eqToHom e ≫ projectionToBase b (j + 1) ≫ projectionToBase a a.length := by
  intro j
  induction j with
  | zero =>
      intro i hi e
      have hi' : i = a.length + 1 := by omega
      subst hi'
      rw [projectionToBase_succ (a.append b) a.length, append_blowupMorphism_length a b,
        projectionToBase_append_of_le_length a b le_rfl, projectionToBase_succ b 0, projectionToBase_zero b]
      simp
  | succ n ih =>
      intro i hi e
      have hi' : i = a.length + n + 1 + 1 := by omega
      subst hi'
      rw [projectionToBase_succ (a.append b) (a.length + n + 1),
        append_blowupMorphism_of_eq_length_add_succ a b (a.length + n + 1) n rfl
          (append_schemeAt_of_eq_length_add_succ a b (a.length + n + 1 + 1) (n + 1) (by omega))
          (append_schemeAt_of_eq_length_add_succ a b (a.length + n + 1) n rfl).symm,
        ih (a.length + n + 1) rfl (append_schemeAt_of_eq_length_add_succ a b (a.length + n + 1) n rfl),
        projectionToBase_succ b (n + 1)]
      simp

/- English proof (translation)
Take `⟨j, rfl⟩ : ∃ j, i = s.length + j + 1` from `⟨i - s.length - 1, by omega⟩`. Establish `hsub : s.length + j + 1 - s.length = j + 1` using `by omega`. Rewrite using `[projectionToBase_congr t hsub, projectionToBase_append_of_eq_length_add_succ s t j (s.length + j + 1) rfl (append_schemeAt_of_eq_length_add_succ s t (s.length + j + 1) j rfl)]`. Simplify using the standard rewrite rules.
-/
theorem projectionToBase_append_of_length_lt {i : ℕ} (h : s.length < i) :
    projectionToBase (s.append t) i =
      eqToHom (append_schemeAt_of_length_lt s t h) ≫ projectionToBase t (i - s.length) ≫ projectionToBase s s.length := by
  obtain ⟨j, rfl⟩ : ∃ j, i = s.length + j + 1 := ⟨i - s.length - 1, by omega⟩
  have hsub : s.length + j + 1 - s.length = j + 1 := by omega
  rw [projectionToBase_congr t hsub,
    projectionToBase_append_of_eq_length_add_succ s t j (s.length + j + 1) rfl
      (append_schemeAt_of_eq_length_add_succ s t (s.length + j + 1) j rfl)]
  simp

end BlowupSequenceData

structure ComapIsoInvariance : Prop where
  coSupport_comap : ∀ {X Y : Scheme.{u}} (e : X ≅ Y) (J : Y.IdealSheafData) (n : ℕ),
    orderAtLeastLocus (J.comap e.hom) n = ⇑e.hom.base ⁻¹' orderAtLeastLocus J n
  hasSNCWith_comap : ∀ {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) (Z : Y.IdealSheafData)
    (F : List Y.IdealSheafData), HasStrictNormalCrossingsWith q Z F →
      HasStrictNormalCrossingsWith (e.hom ≫ q) (Z.comap e.hom) (F.map (fun D => D.comap e.hom))
  smooth_comap : ∀ {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) (Z : Y.IdealSheafData),
    AlgebraicGeometry.Smooth (Z.subschemeι ≫ q) →
      AlgebraicGeometry.Smooth ((Z.comap e.hom).subschemeι ≫ e.hom ≫ q)
  strictTransform_comap : ∀ {X X₁ Y : Scheme.{u}} (π : X₁ ⟶ X) (e : X ≅ Y)
    (Z D : Y.IdealSheafData),
    Blowup.strictTransform (π ≫ e.hom) Z D = Blowup.strictTransform π (Z.comap e.hom) (D.comap e.hom)

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

variable (s : MarkedBlowupSequenceData p I m E)
  (t : MarkedBlowupSequenceData (s.proj s.toBlowupSequenceData.length ≫ p) (s.ideal s.toBlowupSequenceData.length) m
    (s.boundary s.toBlowupSequenceData.length))

def appendToBlowupSequenceData : BlowupSequenceData X := s.toBlowupSequenceData.append t.toBlowupSequenceData

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem appendToBlowupSequenceData_length :
    (s.appendToBlowupSequenceData t).length = s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := rfl

/- English proof (translation)
The claim follows from `BlowupSequenceData.append_schemeAt_of_le_length s.toBlowupSequenceData t.toBlowupSequenceData h`.
-/
theorem appendToBlowupSequenceData_schemeAt_of_le_length {i : ℕ} (h : i ≤ s.toBlowupSequenceData.length) :
    (s.appendToBlowupSequenceData t).obj i = s.toBlowupSequenceData.obj i :=
  BlowupSequenceData.append_schemeAt_of_le_length s.toBlowupSequenceData t.toBlowupSequenceData h

/- English proof (translation)
The claim follows from `BlowupSequenceData.append_schemeAt_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h`.
-/
theorem appendToBlowupSequenceData_schemeAt_of_length_lt {i : ℕ} (h : s.toBlowupSequenceData.length < i) :
    (s.appendToBlowupSequenceData t).obj i = t.toBlowupSequenceData.obj (i - s.toBlowupSequenceData.length) :=
  BlowupSequenceData.append_schemeAt_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h

/- English proof (translation)
The claim follows from `BlowupSequenceData.append_schemeAt_zero s.toBlowupSequenceData t.toBlowupSequenceData`.
-/
theorem appendToBlowupSequenceData_schemeAt_zero : (s.appendToBlowupSequenceData t).obj 0 = s.toBlowupSequenceData.obj 0 :=
  BlowupSequenceData.append_schemeAt_zero s.toBlowupSequenceData t.toBlowupSequenceData

/- English proof (translation)
The claim follows from `BlowupSequenceData.append_schemeAt_succ_of_lt_length s.toBlowupSequenceData t.toBlowupSequenceData h`.
-/
theorem appendToBlowupSequenceData_schemeAt_succ_of_lt_length {i : ℕ} (h : i < s.toBlowupSequenceData.length) :
    (s.appendToBlowupSequenceData t).obj (i + 1) = s.toBlowupSequenceData.obj (i + 1) :=
  BlowupSequenceData.append_schemeAt_succ_of_lt_length s.toBlowupSequenceData t.toBlowupSequenceData h

/- English proof (translation)
The claim follows from `BlowupSequenceData.append_schemeAt_succ_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h`.
-/
theorem appendToBlowupSequenceData_schemeAt_succ_of_length_lt {i : ℕ} (h : s.toBlowupSequenceData.length < i) :
    (s.appendToBlowupSequenceData t).obj (i + 1) =
      t.toBlowupSequenceData.obj (i - s.toBlowupSequenceData.length + 1) :=
  BlowupSequenceData.append_schemeAt_succ_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h

/- English proof (translation)
The claim follows from `BlowupSequenceData.append_schemeAt_length_succ s.toBlowupSequenceData t.toBlowupSequenceData`.
-/
theorem appendToBlowupSequenceData_schemeAt_length_succ :
    (s.appendToBlowupSequenceData t).obj (s.toBlowupSequenceData.length + 1) = t.toBlowupSequenceData.obj 1 :=
  BlowupSequenceData.append_schemeAt_length_succ s.toBlowupSequenceData t.toBlowupSequenceData

/- English proof (translation)
The claim follows from `BlowupSequenceData.append_schemeAt_length_add_length s.toBlowupSequenceData t.toBlowupSequenceData h`.
-/
theorem appendToBlowupSequenceData_schemeAt_length_add_length (h : 0 < t.toBlowupSequenceData.length) :
    (s.appendToBlowupSequenceData t).obj (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      t.toBlowupSequenceData.obj t.toBlowupSequenceData.length :=
  BlowupSequenceData.append_schemeAt_length_add_length s.toBlowupSequenceData t.toBlowupSequenceData h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem appendToBlowupSequenceData_isoObjZero_hom :
    (s.appendToBlowupSequenceData t).isoZero.hom =
      eqToHom (appendToBlowupSequenceData_schemeAt_zero s t) ≫ s.toBlowupSequenceData.isoZero.hom := rfl

/- English proof (translation)
The claim follows from `BlowupSequenceData.append_blowupMorphism_of_lt_length s.toBlowupSequenceData t.toBlowupSequenceData h`.
-/
theorem appendToBlowupSequenceData_blowupMorphism_of_lt_length {i : ℕ} (h : i < s.toBlowupSequenceData.length) :
    (s.appendToBlowupSequenceData t).map i =
      eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_lt_length s t h) ≫ s.toBlowupSequenceData.map i ≫
        eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)).symm :=
  BlowupSequenceData.append_blowupMorphism_of_lt_length s.toBlowupSequenceData t.toBlowupSequenceData h

/- English proof (translation)
The claim follows from `BlowupSequenceData.append_blowupMorphism_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h`.
-/
theorem appendToBlowupSequenceData_blowupMorphism_of_length_lt {i : ℕ} (h : s.toBlowupSequenceData.length < i) :
    (s.appendToBlowupSequenceData t).map i =
      eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h) ≫
        t.toBlowupSequenceData.map (i - s.toBlowupSequenceData.length) ≫
        eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h).symm :=
  BlowupSequenceData.append_blowupMorphism_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h

/- English proof (translation)
The claim follows from `BlowupSequenceData.append_blowupMorphism_length s.toBlowupSequenceData t.toBlowupSequenceData`.
-/
theorem appendToBlowupSequenceData_blowupMorphism_length :
    (s.appendToBlowupSequenceData t).map s.toBlowupSequenceData.length =
      eqToHom (appendToBlowupSequenceData_schemeAt_length_succ s t) ≫ t.toBlowupSequenceData.map 0 ≫
        t.toBlowupSequenceData.isoZero.hom ≫
        eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length)).symm :=
  BlowupSequenceData.append_blowupMorphism_length s.toBlowupSequenceData t.toBlowupSequenceData

/- English proof (translation)
The claim follows from `BlowupSequenceData.append_center_of_lt_length s.toBlowupSequenceData t.toBlowupSequenceData h`.
-/
theorem appendToBlowupSequenceData_center_of_lt_length {i : ℕ} (h : i < s.toBlowupSequenceData.length) :
    (s.appendToBlowupSequenceData t).center i =
      (s.toBlowupSequenceData.center i).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h))) :=
  BlowupSequenceData.append_center_of_lt_length s.toBlowupSequenceData t.toBlowupSequenceData h

/- English proof (translation)
The claim follows from `BlowupSequenceData.append_center_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h`.
-/
theorem appendToBlowupSequenceData_center_of_length_lt {i : ℕ} (h : s.toBlowupSequenceData.length < i) :
    (s.appendToBlowupSequenceData t).center i =
      (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length)).comap
        (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)) :=
  BlowupSequenceData.append_center_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h

/- English proof (translation)
The claim follows from `BlowupSequenceData.append_center_length s.toBlowupSequenceData t.toBlowupSequenceData`.
-/
theorem appendToBlowupSequenceData_center_length :
    (s.appendToBlowupSequenceData t).center s.toBlowupSequenceData.length =
      ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv).comap
        (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))) :=
  BlowupSequenceData.append_center_length s.toBlowupSequenceData t.toBlowupSequenceData

def appendProjectionToBase (i : ℕ) : (s.appendToBlowupSequenceData t).obj i ⟶ X :=
  if h : i ≤ s.toBlowupSequenceData.length then
    eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t h) ≫ s.proj i
  else
    eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t (not_le.1 h)) ≫ t.proj (i - s.toBlowupSequenceData.length) ≫
      s.proj s.toBlowupSequenceData.length

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
theorem appendProjectionToBase_of_le_length {i : ℕ} (h : i ≤ s.toBlowupSequenceData.length) :
    s.appendProjectionToBase t i = eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t h) ≫ s.proj i :=
  dif_pos h

/- English proof (translation)
The claim follows from `dif_neg (not_le.2 h)`.
-/
theorem appendProjectionToBase_of_length_lt {i : ℕ} (h : s.toBlowupSequenceData.length < i) :
    s.appendProjectionToBase t i =
      eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h) ≫ t.proj (i - s.toBlowupSequenceData.length) ≫
        s.proj s.toBlowupSequenceData.length :=
  dif_neg (not_le.2 h)

def appendIdeal (i : ℕ) : ((s.appendToBlowupSequenceData t).obj i).IdealSheafData :=
  if h : i ≤ s.toBlowupSequenceData.length then
    (s.ideal i).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t h))
  else
    (t.ideal (i - s.toBlowupSequenceData.length)).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t (not_le.1 h)))

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
theorem appendIdeal_of_le_length {i : ℕ} (h : i ≤ s.toBlowupSequenceData.length) :
    s.appendIdeal t i = (s.ideal i).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t h)) :=
  dif_pos h

/- English proof (translation)
The claim follows from `dif_neg (not_le.2 h)`.
-/
theorem appendIdeal_of_length_lt {i : ℕ} (h : s.toBlowupSequenceData.length < i) :
    s.appendIdeal t i =
      (t.ideal (i - s.toBlowupSequenceData.length)).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)) :=
  dif_neg (not_le.2 h)

/- English proof (translation)
Substitute `hij` using the available equality. Both sides reduce to the same expression.
-/
private theorem comap_eqToHom_congr {A : Scheme.{u}} (F : ℕ → Scheme.{u})
    (G : ∀ n : ℕ, (F n).IdealSheafData) {i j : ℕ} (hij : i = j)
    (hi : A = F i) (hj : A = F j) :
    (G i).comap (eqToHom hi) = (G j).comap (eqToHom hj) := by
  subst hij
  rfl

/- English proof (translation)
Establish `hlt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + 1` using `Nat.lt_succ_self _`. Use `(appendIdeal_of_length_lt s t hlt).trans ?_` and prove the remaining obligations. Conclude with `comap_eqToHom_congr (fun n => t.toBlowupSequenceData.obj n) (fun n => t.ideal n) (by omega) (appendToBlowupSequenceData_schemeAt_of_length_lt s t hlt) (appendToBlowupSequenceData_schemeAt_length_succ s t)`.
-/
theorem appendIdeal_length_succ :
    s.appendIdeal t (s.toBlowupSequenceData.length + 1) =
      (t.ideal 1).comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_succ s t)) := by
  have hlt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + 1 := Nat.lt_succ_self _
  refine (appendIdeal_of_length_lt s t hlt).trans ?_
  exact comap_eqToHom_congr (fun n => t.toBlowupSequenceData.obj n)
    (fun n => t.ideal n) (by omega) (appendToBlowupSequenceData_schemeAt_of_length_lt s t hlt)
    (appendToBlowupSequenceData_schemeAt_length_succ s t)

def appendBoundary (i : ℕ) : List ((s.appendToBlowupSequenceData t).obj i).IdealSheafData :=
  if h : i ≤ s.toBlowupSequenceData.length then
    (s.boundary i).map (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t h)))
  else
    (t.boundary (i - s.toBlowupSequenceData.length)).map
      (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t (not_le.1 h))))

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
theorem appendBoundary_of_le_length {i : ℕ} (h : i ≤ s.toBlowupSequenceData.length) :
    s.appendBoundary t i =
      (s.boundary i).map (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t h))) :=
  dif_pos h

/- English proof (translation)
The claim follows from `dif_neg (not_le.2 h)`.
-/
theorem appendBoundary_of_length_lt {i : ℕ} (h : s.toBlowupSequenceData.length < i) :
    s.appendBoundary t i =
      (t.boundary (i - s.toBlowupSequenceData.length)).map
        (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h))) :=
  dif_neg (not_le.2 h)

/- English proof (translation)
Substitute `hij` using the available equality. Both sides reduce to the same expression.
-/
private theorem map_comap_eqToHom_congr {A : Scheme.{u}}
    {F : ℕ → Scheme.{u}} (B : ∀ n : ℕ, List (F n).IdealSheafData) (i j : ℕ) (hij : i = j)
    (e : A = F i) (e' : A = F j) :
    (B i).map (fun D => D.comap (eqToHom e)) = (B j).map (fun D => D.comap (eqToHom e')) := by
  subst hij
  rfl

/- English proof (translation)
Establish `hlt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + 1` using `Nat.lt_succ_self _`. Use `(appendBoundary_of_length_lt s t hlt).trans ?_` and prove the remaining obligations. Conclude with `map_comap_eqToHom_congr (A := (s.appendToBlowupSequenceData t).obj (s.toBlowupSequenceData.length + 1)) (F := fun n => t.toBlowupSequenceData.obj n) (fun n => t.boundary n) (s.toBlowupSequenceData.length + 1 - s.toBlowupSequenceData.length) 1 (by omega) (appendToBlowupSequenceDat …`.
-/
theorem appendBoundary_length_succ :
    s.appendBoundary t (s.toBlowupSequenceData.length + 1) =
      (t.boundary 1).map (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_succ s t))) := by
  have hlt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + 1 := Nat.lt_succ_self _
  refine (appendBoundary_of_length_lt s t hlt).trans ?_
  exact map_comap_eqToHom_congr
    (A := (s.appendToBlowupSequenceData t).obj (s.toBlowupSequenceData.length + 1))
    (F := fun n => t.toBlowupSequenceData.obj n) (fun n => t.boundary n)
    (s.toBlowupSequenceData.length + 1 - s.toBlowupSequenceData.length) 1 (by omega)
    (appendToBlowupSequenceData_schemeAt_of_length_lt s t hlt) (appendToBlowupSequenceData_schemeAt_length_succ s t)

/- English proof (translation)
Rewrite using `[appendProjectionToBase_of_le_length s t (Nat.zero_le _), appendToBlowupSequenceData_isoObjZero_hom, s.proj_zero]`.
-/
theorem appendProjectionToBase_zero : s.appendProjectionToBase t 0 = (s.appendToBlowupSequenceData t).isoZero.hom := by
  rw [appendProjectionToBase_of_le_length s t (Nat.zero_le _), appendToBlowupSequenceData_isoObjZero_hom, s.proj_zero]

/- English proof (translation)
Substitute `h` using the available equality. Simplify using the standard rewrite rules.
-/
private theorem projectionToBase_congr (d : MarkedBlowupSequenceData p I m E) {i j : ℕ} (h : i = j) :
    d.proj i = eqToHom (congrArg d.toBlowupSequenceData.obj h) ≫ d.proj j := by
  subst h
  simp

/- English proof (translation)
Break down `lt_trichotomy i s.toBlowupSequenceData.length with h | h | h` into its components or cases. Establish `h1 : i + 1 ≤ s.toBlowupSequenceData.length` using `by omega`. Rewrite using `[appendProjectionToBase_of_le_length s t h1, appendToBlowupSequenceData_blowupMorphism_of_lt_length s t h, appendProjectionToBase_of_le_length s t (le_of_lt h), s.proj_succ i]`. Simplify using the standard rewrite rules. Substitute `h` using the available equality.

Establish `hlt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + 1` using `by omega`. Establish `hsub : s.toBlowupSequenceData.length + 1 - s.toBlowupSequenceData.length = 1` using `by omega`. Establish `hp1 : t.proj 1 = t.toBlowupSequenceData.map 0 ≫ t.proj 0` using `t.proj_succ 0`. Rewrite using `[appendProjectionToBase_of_length_lt s t hlt, appendToBlowupSequenceData_blowupMorphism_length s t, appendProjectionToBase_of_le_length s t (le_refl s.toBlowupSequenceData.length), projectionToBase_congr t hsub, hp1, t.proj_zero]`. Simplify using the standard rewrite rules.

Establish `h1 : s.toBlowupSequenceData.length < i + 1` using `by omega`. Establish `hsub : i + 1 - s.toBlowupSequenceData.length = (i - s.toBlowupSequenceData.length) + 1` using `by omega`. Establish `hp1 : t.proj (i - s.toBlowupSequenceData.length + 1) = t.toBlowupSequenceData.map (i - s.toBlowupSequenceData.length) ≫ t.proj (i - s.toBlowupSequenceData.length)` using `t.proj_succ _`. Rewrite using `[appendProjectionToBase_of_length_lt s t h1, appendToBlowupSequenceData_blowupMorphism_of_length_lt s t h, appendProjectionToBase_of_length_lt s t h, projectionToBase_congr t hsub, hp1]`. Simplify using the standard rewrite rules.
-/
theorem appendProjectionToBase_succ (i : ℕ) :
    s.appendProjectionToBase t (i + 1) = (s.appendToBlowupSequenceData t).map i ≫ s.appendProjectionToBase t i := by
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  · have h1 : i + 1 ≤ s.toBlowupSequenceData.length := by omega
    rw [appendProjectionToBase_of_le_length s t h1, appendToBlowupSequenceData_blowupMorphism_of_lt_length s t h, appendProjectionToBase_of_le_length s t (le_of_lt h),
      s.proj_succ i]
    simp
  · subst h
    have hlt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + 1 := by omega
    have hsub : s.toBlowupSequenceData.length + 1 - s.toBlowupSequenceData.length = 1 := by omega
    have hp1 : t.proj 1 = t.toBlowupSequenceData.map 0 ≫ t.proj 0 := t.proj_succ 0
    rw [appendProjectionToBase_of_length_lt s t hlt, appendToBlowupSequenceData_blowupMorphism_length s t,
      appendProjectionToBase_of_le_length s t (le_refl s.toBlowupSequenceData.length),
      projectionToBase_congr t hsub, hp1, t.proj_zero]
    simp
  · have h1 : s.toBlowupSequenceData.length < i + 1 := by omega
    have hsub : i + 1 - s.toBlowupSequenceData.length = (i - s.toBlowupSequenceData.length) + 1 := by omega
    have hp1 : t.proj (i - s.toBlowupSequenceData.length + 1) =
        t.toBlowupSequenceData.map (i - s.toBlowupSequenceData.length) ≫ t.proj (i - s.toBlowupSequenceData.length) :=
      t.proj_succ _
    rw [appendProjectionToBase_of_length_lt s t h1, appendToBlowupSequenceData_blowupMorphism_of_length_lt s t h, appendProjectionToBase_of_length_lt s t h,
      projectionToBase_congr t hsub, hp1]
    simp

/- English proof (translation)
Rewrite using `[appendIdeal_of_le_length s t (Nat.zero_le _), s.ideal_zero, appendToBlowupSequenceData_isoObjZero_hom]`. Conclude with `(AlgebraicGeometry.Scheme.IdealSheafData.comap_comp ..).symm`.
-/
theorem appendIdeal_zero : s.appendIdeal t 0 = I.comap (s.appendToBlowupSequenceData t).isoZero.hom := by
  rw [appendIdeal_of_le_length s t (Nat.zero_le _), s.ideal_zero, appendToBlowupSequenceData_isoObjZero_hom]
  exact (AlgebraicGeometry.Scheme.IdealSheafData.comap_comp ..).symm

/- English proof (translation)
Substitute `h` using the available equality. Simplify using `[AlgebraicGeometry.Scheme.IdealSheafData.comap_id]`.
-/
private theorem map_comap_eqToHom_comp {A B C : Scheme.{u}} (h : A = B) (g : B ⟶ C)
    (L : List C.IdealSheafData) :
    (L.map (fun D => D.comap g)).map (fun D => D.comap (eqToHom h)) =
      L.map (fun D => D.comap (eqToHom h ≫ g)) := by
  subst h
  simp [AlgebraicGeometry.Scheme.IdealSheafData.comap_id]

/- English proof (translation)
Rewrite using `[appendBoundary_of_le_length s t (Nat.zero_le _), appendToBlowupSequenceData_isoObjZero_hom, s.boundary_zero]`. Conclude with `map_comap_eqToHom_comp (appendToBlowupSequenceData_schemeAt_of_le_length s t (Nat.zero_le _)) s.toBlowupSequenceData.isoZero.hom E`.
-/
theorem appendBoundary_zero :
    s.appendBoundary t 0 = E.map (fun D => D.comap (s.appendToBlowupSequenceData t).isoZero.hom) := by
  rw [appendBoundary_of_le_length s t (Nat.zero_le _), appendToBlowupSequenceData_isoObjZero_hom, s.boundary_zero]
  exact map_comap_eqToHom_comp (appendToBlowupSequenceData_schemeAt_of_le_length s t (Nat.zero_le _))
    s.toBlowupSequenceData.isoZero.hom E

/- English proof (translation)
Establish `hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length` using `hi`. Establish `hcomp : ∀ (V W T : Scheme.{u}) (f : V ⟶ W) (g : W ⟶ T) (J : T.IdealSheafData), J.comap (f ≫ g) = (J.comap g).comap f`. Introduce `V W T f g J`. Simplify using `only [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp]`. Establish `key : ∀ (A B : Scheme.{u}) (hAB : A = B) (C K : B.IdealSheafData), ((C.support : Set ↥B) ⊆ orderAtLeastLocus K m) → (((C.comap (eqToHom hAB)).support : Set ↥A) ⊆ orderAtLeastLocus (K.comap (eqToHom hAB)) m)`.

Introduce `A B hAB C K h`. Substitute `hAB` using the available equality. Simplify `h` using `only [eqToHom_refl, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]`. Establish `keyIso : ∀ (A B : Scheme.{u}) (e : A ≅ B) (C : A.IdealSheafData) (K : B.IdealSheafData), ((C.support : Set ↥A) ⊆ orderAtLeastLocus (K.comap e.hom) m) → (((C.comap e.inv).support : Set ↥B) ⊆ orderAtLeastLocus K m)`. Introduce `A B e C K h`.

Establish `hK : (K.comap e.hom).comap e.inv = K`. Rewrite using `[← hcomp, e.inv_hom_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]`. Establish `h2 : orderAtLeastLocus ((K.comap e.hom).comap e.inv) m = ⇑e.inv.base ⁻¹' orderAtLeastLocus (K.comap e.hom) m` using `hinv.coSupport_comap e.symm (K.comap e.hom) m`. Rewrite `h2` using `[hK]`. Establish `hsupp : ((C.comap e.inv).support : Set ↥B) = ⇑e.inv.base ⁻¹' (C.support : Set ↥A)`.

Simplify using `[AlgebraicGeometry.Scheme.IdealSheafData.support_comap]`. Rewrite using `[hsupp, h2]`. Conclude with `Set.preimage_mono h`. Break down `lt_trichotomy i s.toBlowupSequenceData.length with h | h | h` into its components or cases. Rewrite using `[appendToBlowupSequenceData_center_of_lt_length s t h, appendIdeal_of_le_length s t (le_of_lt h)]`.

Conclude with `key _ _ (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)) (s.toBlowupSequenceData.center i) (s.ideal i) (s.center_order i h)`. Substitute `h` using the available equality. Establish `ht0 : 0 < t.toBlowupSequenceData.length` using `by omega`. Establish `hb` using `t.center_order 0 ht0`. Rewrite `hb` using `[t.ideal_zero]`.

Establish `hbase` using `keyIso _ _ t.toBlowupSequenceData.isoZero (t.toBlowupSequenceData.center 0) (s.ideal s.toBlowupSequenceData.length) hb`. Rewrite using `[appendToBlowupSequenceData_center_length s t, appendIdeal_of_le_length s t (le_refl s.toBlowupSequenceData.length)]`. Conclude with `key _ _ (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length)) ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv) (s.ideal s.toBlowupSequenceData.length) hbase`. Establish `hsub : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length` using `by omega`. Rewrite using `[appendToBlowupSequenceData_center_of_length_lt s t h, appendIdeal_of_length_lt s t h]`.

Conclude with `key _ _ (appendToBlowupSequenceData_schemeAt_of_length_lt s t h) (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length)) (t.ideal (i - s.toBlowupSequenceData.length)) (t.center_order (i - s.toBlowupSequenceData.length) hsub)`.
-/
theorem center_support_subset_orderAtLeastLocus_appendIdeal (hinv : ComapIsoInvariance.{u}) (i : ℕ)
    (hi : i < (s.appendToBlowupSequenceData t).length) :
    (((s.appendToBlowupSequenceData t).center i).support : Set ↥((s.appendToBlowupSequenceData t).obj i)) ⊆
      orderAtLeastLocus (s.appendIdeal t i) m := by
  have hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  have hcomp : ∀ (V W T : Scheme.{u}) (f : V ⟶ W) (g : W ⟶ T) (J : T.IdealSheafData),
      J.comap (f ≫ g) = (J.comap g).comap f := by
    intro V W T f g J
    simp only [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp]
  have key : ∀ (A B : Scheme.{u}) (hAB : A = B) (C K : B.IdealSheafData),
      ((C.support : Set ↥B) ⊆ orderAtLeastLocus K m) →
      (((C.comap (eqToHom hAB)).support : Set ↥A) ⊆ orderAtLeastLocus (K.comap (eqToHom hAB)) m) := by
    intro A B hAB C K h
    subst hAB
    simpa only [eqToHom_refl, AlgebraicGeometry.Scheme.IdealSheafData.comap_id] using h
  have keyIso : ∀ (A B : Scheme.{u}) (e : A ≅ B) (C : A.IdealSheafData) (K : B.IdealSheafData),
      ((C.support : Set ↥A) ⊆ orderAtLeastLocus (K.comap e.hom) m) →
      (((C.comap e.inv).support : Set ↥B) ⊆ orderAtLeastLocus K m) := by
    intro A B e C K h
    have hK : (K.comap e.hom).comap e.inv = K := by
      rw [← hcomp, e.inv_hom_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]
    have h2 : orderAtLeastLocus ((K.comap e.hom).comap e.inv) m
        = ⇑e.inv.base ⁻¹' orderAtLeastLocus (K.comap e.hom) m :=
      hinv.coSupport_comap e.symm (K.comap e.hom) m
    rw [hK] at h2
    have hsupp : ((C.comap e.inv).support : Set ↥B) = ⇑e.inv.base ⁻¹' (C.support : Set ↥A) := by
      simp [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    rw [hsupp, h2]
    exact Set.preimage_mono h
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  · rw [appendToBlowupSequenceData_center_of_lt_length s t h, appendIdeal_of_le_length s t (le_of_lt h)]
    exact key _ _ (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)) (s.toBlowupSequenceData.center i) (s.ideal i)
      (s.center_order i h)
  · subst h
    have ht0 : 0 < t.toBlowupSequenceData.length := by omega
    have hb := t.center_order 0 ht0
    rw [t.ideal_zero] at hb
    have hbase := keyIso _ _ t.toBlowupSequenceData.isoZero (t.toBlowupSequenceData.center 0)
      (s.ideal s.toBlowupSequenceData.length) hb
    rw [appendToBlowupSequenceData_center_length s t,
      appendIdeal_of_le_length s t (le_refl s.toBlowupSequenceData.length)]
    exact key _ _ (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))
      ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv)
      (s.ideal s.toBlowupSequenceData.length) hbase
  · have hsub : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length := by omega
    rw [appendToBlowupSequenceData_center_of_length_lt s t h, appendIdeal_of_length_lt s t h]
    exact key _ _ (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)
      (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length))
      (t.ideal (i - s.toBlowupSequenceData.length))
      (t.center_order (i - s.toBlowupSequenceData.length) hsub)

/- English proof (translation)
Establish `hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length` using `hi`. Break down `lt_trichotomy i s.toBlowupSequenceData.length with h | h | h` into its components or cases. Rewrite using `[appendProjectionToBase_of_le_length s t (le_of_lt h), appendToBlowupSequenceData_center_of_lt_length s t h]`. Establish `hA` using `hinv.smooth_comap (s.proj i ≫ p) (eqToIso (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h))) (s.toBlowupSequenceData.center i) (s.center_smooth i h)`. Simplify `hA` using `only [eqToIso.hom, Category.assoc]`.

Substitute `h` using the available equality. Establish `ht0 : 0 < t.toBlowupSequenceData.length` using `by omega`. Establish `hsm` using `t.center_smooth 0 ht0`. Rewrite `hsm` using `[t.proj_zero]`. Establish `hT` using `hinv.smooth_comap (t.toBlowupSequenceData.isoZero.hom ≫ s.proj s.toBlowupSequenceData.length ≫ p) t.toBlowupSequenceData.isoZero.symm (t.toBlowupSequenceData.center 0) hsm`.

Simplify using `only [Iso.symm_hom, Iso.inv_hom_id_assoc] at hT`. Rewrite using `[appendProjectionToBase_of_le_length s t (le_refl s.toBlowupSequenceData.length), appendToBlowupSequenceData_center_length s t]`. Establish `hB` using `hinv.smooth_comap (s.proj s.toBlowupSequenceData.length ≫ p) (eqToIso (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))) ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv) hT`. Simplify `hB` using `only [eqToIso.hom, Category.assoc]`. Rewrite using `[appendProjectionToBase_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h]`.

Establish `hC` using `hinv.smooth_comap (t.proj (i - s.toBlowupSequenceData.length) ≫ s.proj s.toBlowupSequenceData.length ≫ p) (eqToIso (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)) (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length)) (t.center_smooth (i - s.toBlowupSequenc …`. Simplify `hC` using `only [eqToIso.hom, Category.assoc]`.
-/
private theorem smooth_center_comp_appendProjectionToBase (hinv : ComapIsoInvariance.{u}) (i : ℕ)
    (hi : i < (s.appendToBlowupSequenceData t).length) :
    AlgebraicGeometry.Smooth
      (((s.appendToBlowupSequenceData t).center i).subschemeι ≫ s.appendProjectionToBase t i ≫ p) := by
  have hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  · rw [appendProjectionToBase_of_le_length s t (le_of_lt h), appendToBlowupSequenceData_center_of_lt_length s t h]
    have hA := hinv.smooth_comap (s.proj i ≫ p)
      (eqToIso (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h))) (s.toBlowupSequenceData.center i)
      (s.center_smooth i h)
    simpa only [eqToIso.hom, Category.assoc] using hA
  · subst h
    have ht0 : 0 < t.toBlowupSequenceData.length := by omega
    have hsm := t.center_smooth 0 ht0
    rw [t.proj_zero] at hsm
    have hT := hinv.smooth_comap
      (t.toBlowupSequenceData.isoZero.hom ≫ s.proj s.toBlowupSequenceData.length ≫ p)
      t.toBlowupSequenceData.isoZero.symm (t.toBlowupSequenceData.center 0) hsm
    simp only [Iso.symm_hom, Iso.inv_hom_id_assoc] at hT
    rw [appendProjectionToBase_of_le_length s t (le_refl s.toBlowupSequenceData.length), appendToBlowupSequenceData_center_length s t]
    have hB := hinv.smooth_comap (s.proj s.toBlowupSequenceData.length ≫ p)
      (eqToIso (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length)))
      ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv) hT
    simpa only [eqToIso.hom, Category.assoc] using hB
  · rw [appendProjectionToBase_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h]
    have hC := hinv.smooth_comap
      (t.proj (i - s.toBlowupSequenceData.length) ≫ s.proj s.toBlowupSequenceData.length ≫ p)
      (eqToIso (appendToBlowupSequenceData_schemeAt_of_length_lt s t h))
      (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length))
      (t.center_smooth (i - s.toBlowupSequenceData.length) (by omega))
    simpa only [eqToIso.hom, Category.assoc] using hC

/- English proof (translation)
Rewrite using `[← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, e.inv_hom_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]`.
-/
private theorem comap_comap_hom_inv {A B : Scheme.{u}} (e : A ≅ B)
    (D : B.IdealSheafData) : (D.comap e.hom).comap e.inv = D := by
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, e.inv_hom_id,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id]

/- English proof (translation)
Proceed by induction on `F with`. Consider the case `nil => rfl`. Consider the case `cons D L ih => simp only [List.map_cons, ih, comap_comap_hom_inv]`.
-/
private theorem map_comap_hom_map_comap_inv {A B : Scheme.{u}} (e : A ≅ B)
    (F : List B.IdealSheafData) :
    ((F.map fun D => D.comap e.hom).map fun D => D.comap e.inv) = F := by
  induction F with
  | nil => rfl
  | cons D L ih => simp only [List.map_cons, ih, comap_comap_hom_inv]

/- English proof (translation)
Substitute `h` using the available equality. Simplify `hZ` using `[AlgebraicGeometry.Scheme.IdealSheafData.comap_id]`.
-/
private theorem hasStrictNormalCrossingsWith_comap_eqToHom {K : Type u} [Field K] {A B : Scheme.{u}}
    (h : A = B) (q : B ⟶ Spec (CommRingCat.of K)) (Z : B.IdealSheafData)
    (F : List B.IdealSheafData) (hZ : HasStrictNormalCrossingsWith q Z F) :
    HasStrictNormalCrossingsWith (eqToHom h ≫ q) (Z.comap (eqToHom h))
      (F.map fun D => D.comap (eqToHom h)) := by
  subst h
  simpa [AlgebraicGeometry.Scheme.IdealSheafData.comap_id] using hZ

/- English proof (translation)
Establish `h2` using `hinv.hasSNCWith_comap (e.hom ≫ q) e.symm Z (F.map fun D => D.comap e.hom) hZ`. Rewrite `h2` using `[Iso.symm_hom, Iso.inv_hom_id_assoc, map_comap_hom_map_comap_inv e F]`. Conclude with `h2`.
-/
private theorem hasStrictNormalCrossingsWith_comap_iso_inv {K : Type u} [Field K] {A B : Scheme.{u}}
    (hinv : ComapIsoInvariance.{u}) (e : A ≅ B) (q : B ⟶ Spec (CommRingCat.of K))
    (Z : A.IdealSheafData) (F : List B.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith (e.hom ≫ q) Z (F.map fun D => D.comap e.hom)) :
    HasStrictNormalCrossingsWith q (Z.comap e.inv) F := by
  have h2 := hinv.hasSNCWith_comap (e.hom ≫ q) e.symm Z (F.map fun D => D.comap e.hom) hZ
  rw [Iso.symm_hom, Iso.inv_hom_id_assoc, map_comap_hom_map_comap_inv e F] at h2
  exact h2

/- English proof (translation)
Establish `hlen : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length` using `hi`. Break down `lt_trichotomy i s.toBlowupSequenceData.length with h | h | h` into its components or cases. Rewrite using `[appendProjectionToBase_of_le_length s t (le_of_lt h), appendToBlowupSequenceData_center_of_lt_length s t h, appendBoundary_of_le_length s t (le_of_lt h)]`. Simplify using `only [Category.assoc]`. Conclude with `hasStrictNormalCrossingsWith_comap_eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)) (s.proj i ≫ p) (s.toBlowupSequenceData.center i) (s.boundary i) (s.center_snc i h)`.

Substitute `h` using the available equality. Establish `ht : 0 < t.toBlowupSequenceData.length` using `by omega`. Establish `H0` using `t.center_snc 0 ht`. Rewrite `H0` using `[t.proj_zero, t.boundary_zero]`. Establish `H1` using `hasStrictNormalCrossingsWith_comap_iso_inv hinv t.toBlowupSequenceData.isoZero (s.proj s.toBlowupSequenceData.length ≫ p) (t.toBlowupSequenceData.center 0) (s.boundary s.toBlowupSequenceData.length) H0`.

Rewrite using `[appendProjectionToBase_of_le_length s t (le_refl s.toBlowupSequenceData.length), appendToBlowupSequenceData_center_length s t, appendBoundary_of_le_length s t (le_refl s.toBlowupSequenceData.length)]`. Simplify using `only [Category.assoc]`. Conclude with `hasStrictNormalCrossingsWith_comap_eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length)) (s.proj s.toBlowupSequenceData.length ≫ p) ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv) (s.boundary s.toBlowup …`. Establish `hsub : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length` using `by omega`. Rewrite using `[appendProjectionToBase_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h, appendBoundary_of_length_lt s t h]`.

Simplify using `only [Category.assoc]`. Conclude with `hasStrictNormalCrossingsWith_comap_eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h) (t.proj (i - s.toBlowupSequenceData.length) ≫ s.proj s.toBlowupSequenceData.length ≫ p) (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length)) (t.boundary (i - s.toBlo …`.
-/
private theorem hasStrictNormalCrossingsWith_appendBoundary (hinv : ComapIsoInvariance.{u}) (i : ℕ)
    (hi : i < (s.appendToBlowupSequenceData t).length) :
    HasStrictNormalCrossingsWith (s.appendProjectionToBase t i ≫ p) ((s.appendToBlowupSequenceData t).center i)
      (s.appendBoundary t i) := by
  have hlen : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  · rw [appendProjectionToBase_of_le_length s t (le_of_lt h), appendToBlowupSequenceData_center_of_lt_length s t h,
      appendBoundary_of_le_length s t (le_of_lt h)]
    simp only [Category.assoc]
    exact hasStrictNormalCrossingsWith_comap_eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)) (s.proj i ≫ p)
      (s.toBlowupSequenceData.center i) (s.boundary i) (s.center_snc i h)
  · subst h
    have ht : 0 < t.toBlowupSequenceData.length := by omega
    have H0 := t.center_snc 0 ht
    rw [t.proj_zero, t.boundary_zero] at H0
    have H1 := hasStrictNormalCrossingsWith_comap_iso_inv hinv t.toBlowupSequenceData.isoZero
      (s.proj s.toBlowupSequenceData.length ≫ p) (t.toBlowupSequenceData.center 0)
      (s.boundary s.toBlowupSequenceData.length) H0
    rw [appendProjectionToBase_of_le_length s t (le_refl s.toBlowupSequenceData.length), appendToBlowupSequenceData_center_length s t,
      appendBoundary_of_le_length s t (le_refl s.toBlowupSequenceData.length)]
    simp only [Category.assoc]
    exact hasStrictNormalCrossingsWith_comap_eqToHom
      (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))
      (s.proj s.toBlowupSequenceData.length ≫ p)
      ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv)
      (s.boundary s.toBlowupSequenceData.length) H1
  · have hsub : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length := by omega
    rw [appendProjectionToBase_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h, appendBoundary_of_length_lt s t h]
    simp only [Category.assoc]
    exact hasStrictNormalCrossingsWith_comap_eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)
      (t.proj (i - s.toBlowupSequenceData.length) ≫ s.proj s.toBlowupSequenceData.length ≫ p)
      (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length))
      (t.boundary (i - s.toBlowupSequenceData.length))
      (t.center_snc (i - s.toBlowupSequenceData.length) hsub)

/- English proof (translation)
Rewrite using `[← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, e.hom_inv_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]`.
-/
private theorem comap_comap_inv_hom {A B : Scheme.{u}} (e : A ≅ B) (D : A.IdealSheafData) :
    (D.comap e.inv).comap e.hom = D := by
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, e.hom_inv_id,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id]

/- English proof (translation)
Substitute `eA` using the available equality. Substitute `eB` using the available equality. Simplify using `only [eqToHom_refl, Category.id_comp, Category.comp_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]`. Conclude with `h`.
-/
private theorem exceptionalIdeal_pow_mul_comap_eqToHom {A A' B B' : Scheme.{u}} (eA : A = A')
    (eB : B = B') (g : A' ⟶ B') (Z J : B'.IdealSheafData) (J' : A'.IdealSheafData) (n : ℕ)
    (h : Blowup.exceptionalIdeal g Z ^ n * J' = J.comap g) :
    Blowup.exceptionalIdeal (eqToHom eA ≫ g ≫ eqToHom eB.symm) (Z.comap (eqToHom eB)) ^ n *
        J'.comap (eqToHom eA) =
      (J.comap (eqToHom eB)).comap (eqToHom eA ≫ g ≫ eqToHom eB.symm) := by
  subst eA
  subst eB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id]
  exact h

/- English proof (translation)
Establish `hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length` using `hi`. Break down `lt_trichotomy i s.toBlowupSequenceData.length with h | h | h` into its components or cases. Establish `h1 : i + 1 ≤ s.toBlowupSequenceData.length` using `h`. Rewrite using `[appendToBlowupSequenceData_blowupMorphism_of_lt_length s t h, appendToBlowupSequenceData_center_of_lt_length s t h, appendIdeal_of_le_length s t h1, appendIdeal_of_le_length s t (le_of_lt h)]`. Conclude with `exceptionalIdeal_pow_mul_comap_eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_lt_length s t h) (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)) (s.toBlowupSequenceData.map i) (s.toBlowupSequenceData.center i) (s.ideal i) (s.ideal (i + 1)) m (s.ideal_succ …`.

Substitute `h` using the available equality. Establish `ht0 : 0 < t.toBlowupSequenceData.length` using `by omega`. Establish `hExceptional : Blowup.exceptionalIdeal (t.toBlowupSequenceData.map 0 ≫ t.toBlowupSequenceData.isoZero.hom) ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv) ^ m * t.ideal 1 = (s.ideal s.toBlowupSequenceData.length).comap (t.toBlowupSequenceData.map 0 ≫ …`. Rewrite using `[Blowup.exceptionalIdeal_eq_comap, AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, comap_comap_inv_hom t.toBlowupSequenceData.isoZero (t.toBlowupSequenceData.center 0), ← t.ideal_zero]`. Simplify `t.ideal_succ 0 ht0` using `only [Blowup.exceptionalIdeal_eq_comap, zero_add]`.

Rewrite using `[appendToBlowupSequenceData_blowupMorphism_length s t, appendToBlowupSequenceData_center_length s t, appendIdeal_length_succ s t, appendIdeal_of_le_length s t (le_refl s.toBlowupSequenceData.length), ← Category.assoc (t.toBlowupSequenceData.map 0) t.toBlowupSequenceData.isoZero.h …`. Conclude with `exceptionalIdeal_pow_mul_comap_eqToHom (appendToBlowupSequenceData_schemeAt_length_succ s t) (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length)) (t.toBlowupSequenceData.map 0 ≫ t.toBlowupSequenceData.isoZero.hom) ((t.toBlowupSequenceData …`. Establish `h1 : s.toBlowupSequenceData.length < i + 1` using `by omega`. Establish `hsub : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length` using `by omega`. Establish `hidx : s.appendIdeal t (i + 1) = (t.ideal (i - s.toBlowupSequenceData.length + 1)).comap (eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h))`.

Rewrite using `[appendIdeal_of_length_lt s t h1]`. Conclude with `comap_eqToHom_congr (fun n => t.toBlowupSequenceData.obj n) (fun n => t.ideal n) (by omega) (appendToBlowupSequenceData_schemeAt_of_length_lt s t h1) (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h)`. Rewrite using `[appendToBlowupSequenceData_blowupMorphism_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h, hidx, appendIdeal_of_length_lt s t h]`. Conclude with `exceptionalIdeal_pow_mul_comap_eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h) (appendToBlowupSequenceData_schemeAt_of_length_lt s t h) (t.toBlowupSequenceData.map (i - s.toBlowupSequenceData.length)) (t.toBlowupSequenceData.center (i - s.toBlowupSequenceDat …`.
-/
theorem exceptionalIdeal_pow_mul_appendIdeal_succ (_hinv : ComapIsoInvariance.{u}) (i : ℕ)
    (hi : i < (s.appendToBlowupSequenceData t).length) :
    Blowup.exceptionalIdeal ((s.appendToBlowupSequenceData t).map i) ((s.appendToBlowupSequenceData t).center i) ^ m *
        s.appendIdeal t (i + 1) =
      (s.appendIdeal t i).comap ((s.appendToBlowupSequenceData t).map i) := by
  have hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  · have h1 : i + 1 ≤ s.toBlowupSequenceData.length := h
    rw [appendToBlowupSequenceData_blowupMorphism_of_lt_length s t h, appendToBlowupSequenceData_center_of_lt_length s t h, appendIdeal_of_le_length s t h1,
      appendIdeal_of_le_length s t (le_of_lt h)]
    exact exceptionalIdeal_pow_mul_comap_eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_lt_length s t h)
      (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)) (s.toBlowupSequenceData.map i) (s.toBlowupSequenceData.center i)
      (s.ideal i) (s.ideal (i + 1)) m (s.ideal_succ i h)
  · subst h
    have ht0 : 0 < t.toBlowupSequenceData.length := by omega
    have hExceptional : Blowup.exceptionalIdeal (t.toBlowupSequenceData.map 0 ≫ t.toBlowupSequenceData.isoZero.hom)
        ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv) ^ m * t.ideal 1 =
        (s.ideal s.toBlowupSequenceData.length).comap
          (t.toBlowupSequenceData.map 0 ≫ t.toBlowupSequenceData.isoZero.hom) := by
      rw [Blowup.exceptionalIdeal_eq_comap,
        AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
        AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
        comap_comap_inv_hom t.toBlowupSequenceData.isoZero (t.toBlowupSequenceData.center 0),
        ← t.ideal_zero]
      simpa only [Blowup.exceptionalIdeal_eq_comap, zero_add] using t.ideal_succ 0 ht0
    rw [appendToBlowupSequenceData_blowupMorphism_length s t, appendToBlowupSequenceData_center_length s t,
      appendIdeal_length_succ s t, appendIdeal_of_le_length s t (le_refl s.toBlowupSequenceData.length),
      ← Category.assoc (t.toBlowupSequenceData.map 0) t.toBlowupSequenceData.isoZero.hom]
    exact exceptionalIdeal_pow_mul_comap_eqToHom (appendToBlowupSequenceData_schemeAt_length_succ s t)
      (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))
      (t.toBlowupSequenceData.map 0 ≫ t.toBlowupSequenceData.isoZero.hom)
      ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv)
      (s.ideal s.toBlowupSequenceData.length) (t.ideal 1) m hExceptional
  · have h1 : s.toBlowupSequenceData.length < i + 1 := by omega
    have hsub : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length := by omega
    have hidx : s.appendIdeal t (i + 1) =
        (t.ideal (i - s.toBlowupSequenceData.length + 1)).comap
          (eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h)) := by
      rw [appendIdeal_of_length_lt s t h1]
      exact comap_eqToHom_congr (fun n => t.toBlowupSequenceData.obj n)
        (fun n => t.ideal n) (by omega) (appendToBlowupSequenceData_schemeAt_of_length_lt s t h1)
        (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h)
    rw [appendToBlowupSequenceData_blowupMorphism_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h, hidx, appendIdeal_of_length_lt s t h]
    exact exceptionalIdeal_pow_mul_comap_eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h)
      (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)
      (t.toBlowupSequenceData.map (i - s.toBlowupSequenceData.length))
      (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length))
      (t.ideal (i - s.toBlowupSequenceData.length))
      (t.ideal (i - s.toBlowupSequenceData.length + 1)) m
      (t.ideal_succ (i - s.toBlowupSequenceData.length) hsub)

/- English proof (translation)
Substitute `hA` using the available equality. Substitute `hB` using the available equality. Substitute `hL` using the available equality. Simplify using `[AlgebraicGeometry.Scheme.IdealSheafData.comap_id]`.
-/
private theorem map_strictTransform_comap_eqToHom {A A' B B' : Scheme.{u}}
    (hA : A = A') (hB : B = B') (f : A' ⟶ B') (Z : B'.IdealSheafData)
    (Lst : List B'.IdealSheafData) (Lst1 : List A'.IdealSheafData)
    (hL : Lst1 = Lst.map (Blowup.strictTransform f Z) ++ [Blowup.exceptionalIdeal f Z]) :
    Lst1.map (fun D => D.comap (eqToHom hA)) =
      (Lst.map (fun D => D.comap (eqToHom hB))).map
          (Blowup.strictTransform (eqToHom hA ≫ f ≫ eqToHom hB.symm) (Z.comap (eqToHom hB))) ++
        [Blowup.exceptionalIdeal (eqToHom hA ≫ f ≫ eqToHom hB.symm) (Z.comap (eqToHom hB))] := by
  subst hA
  subst hB
  subst hL
  simp [AlgebraicGeometry.Scheme.IdealSheafData.comap_id]

/- English proof (translation)
Establish `hZ : (Z.comap e.inv).comap e.hom = Z`. Rewrite using `[← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, e.hom_inv_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]`. Establish `hfun : (Blowup.strictTransform f Z) ∘ (fun D : C.IdealSheafData => D.comap e.hom) = Blowup.strictTransform (f ≫ e.hom) (Z.comap e.inv)`. Use function extensionality and compare the values at `D`. Use `show Blowup.strictTransform f Z (D.comap e.hom) = Blowup.strictTransform (f ≫ e.hom) (Z.comap e.inv) D`.

Rewrite using `[hinv.strictTransform_comap f e (Z.comap e.inv) D, hZ]`. Establish `hexc : Blowup.exceptionalIdeal (f ≫ e.hom) (Z.comap e.inv) = Blowup.exceptionalIdeal f Z`. Rewrite using `[Blowup.exceptionalIdeal_eq_comap, Blowup.exceptionalIdeal_eq_comap, AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hZ]`. Rewrite using `[hL1, List.map_map, hfun, hexc]`.
-/
private theorem map_strictTransform_comp_iso_hom (hinv : ComapIsoInvariance.{u}) {A B C : Scheme.{u}}
    (f : A ⟶ B) (e : B ≅ C) (Z : B.IdealSheafData) (Lst : List C.IdealSheafData)
    (Lst1 : List A.IdealSheafData)
    (hL1 : Lst1 = (Lst.map (fun D => D.comap e.hom)).map (Blowup.strictTransform f Z) ++
      [Blowup.exceptionalIdeal f Z]) :
    Lst1 = Lst.map (Blowup.strictTransform (f ≫ e.hom) (Z.comap e.inv)) ++
      [Blowup.exceptionalIdeal (f ≫ e.hom) (Z.comap e.inv)] := by
  have hZ : (Z.comap e.inv).comap e.hom = Z := by
    rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, e.hom_inv_id,
      AlgebraicGeometry.Scheme.IdealSheafData.comap_id]
  have hfun : (Blowup.strictTransform f Z) ∘ (fun D : C.IdealSheafData => D.comap e.hom) =
      Blowup.strictTransform (f ≫ e.hom) (Z.comap e.inv) := by
    funext D
    show Blowup.strictTransform f Z (D.comap e.hom) =
      Blowup.strictTransform (f ≫ e.hom) (Z.comap e.inv) D
    rw [hinv.strictTransform_comap f e (Z.comap e.inv) D, hZ]
  have hexc : Blowup.exceptionalIdeal (f ≫ e.hom) (Z.comap e.inv) = Blowup.exceptionalIdeal f Z := by
    rw [Blowup.exceptionalIdeal_eq_comap, Blowup.exceptionalIdeal_eq_comap,
      AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hZ]
  rw [hL1, List.map_map, hfun, hexc]

/- English proof (translation)
Establish `hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length` using `hi`. Break down `lt_trichotomy i s.toBlowupSequenceData.length with h | h | h` into its components or cases. Establish `h1 : i + 1 ≤ s.toBlowupSequenceData.length` using `by omega`. Rewrite using `[appendBoundary_of_le_length s t h1, appendBoundary_of_le_length s t (le_of_lt h), appendToBlowupSequenceData_blowupMorphism_of_lt_length s t h, appendToBlowupSequenceData_center_of_lt_length s t h]`. Conclude with `map_strictTransform_comap_eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_lt_length s t h) (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)) (s.toBlowupSequenceData.map i) (s.toBlowupSequenceData.center i) (s.boundary i) (s.boundary (i + 1)) (s.boundary_suc …`.

Substitute `h` using the available equality. Establish `ht0 : 0 < t.toBlowupSequenceData.length` using `by omega`. Establish `hbs : t.boundary 1 = (t.boundary 0).map (Blowup.strictTransform (t.toBlowupSequenceData.map 0) (t.toBlowupSequenceData.center 0)) ++ [Blowup.exceptionalIdeal (t.toBlowupSequenceData.map 0) (t.toBlowupSequenceData.center 0)]` using `t.boundary_succ 0 ht0`. Establish `hL1 : t.boundary 1 = ((s.boundary s.toBlowupSequenceData.length).map (fun D => D.comap t.toBlowupSequenceData.isoZero.hom)).map (Blowup.strictTransform (t.toBlowupSequenceData.map 0) (t.toBlowupSequenceData.center 0)) ++ [Blowup.exceptionalIdeal (t.toBlowupSequenceData.map 0) (t. …`. Rewrite using `[hbs, t.boundary_zero]`.

Establish `hb1` using `map_strictTransform_comp_iso_hom hinv (t.toBlowupSequenceData.map 0) t.toBlowupSequenceData.isoZero (t.toBlowupSequenceData.center 0) (s.boundary s.toBlowupSequenceData.length) (t.boundary 1) hL1`. Rewrite using `[appendBoundary_length_succ s t, appendBoundary_of_le_length s t (le_refl s.toBlowupSequenceData.length), appendToBlowupSequenceData_blowupMorphism_length s t, appendToBlowupSequenceData_center_length s t, ← Category.assoc (t.toBlowupSequenceData.map 0) t.toBlowupSequenceData.iso …`. Conclude with `map_strictTransform_comap_eqToHom (appendToBlowupSequenceData_schemeAt_length_succ s t) (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length)) (t.toBlowupSequenceData.map 0 ≫ t.toBlowupSequenceData.isoZero.hom) ((t.toBlowupSequenceData.cent …`. Establish `hlt : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length` using `by omega`. Establish `hsucc : s.toBlowupSequenceData.length < i + 1` using `by omega`.

Establish `hidx : i + 1 - s.toBlowupSequenceData.length = i - s.toBlowupSequenceData.length + 1` using `by omega`. Rewrite using `[appendBoundary_of_length_lt s t hsucc, appendBoundary_of_length_lt s t h, appendToBlowupSequenceData_blowupMorphism_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h, map_comap_eqToHom_congr (A := (s.appendToBlowupSequenceData t).obj (i + 1)) (F := t.toBlo …`. Conclude with `map_strictTransform_comap_eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h) (appendToBlowupSequenceData_schemeAt_of_length_lt s t h) (t.toBlowupSequenceData.map (i - s.toBlowupSequenceData.length)) (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.len …`.
-/
private theorem appendBoundary_succ (hinv : ComapIsoInvariance.{u}) (i : ℕ)
    (hi : i < (s.appendToBlowupSequenceData t).length) :
    s.appendBoundary t (i + 1) =
      (s.appendBoundary t i).map
          (Blowup.strictTransform ((s.appendToBlowupSequenceData t).map i) ((s.appendToBlowupSequenceData t).center i)) ++
        [Blowup.exceptionalIdeal ((s.appendToBlowupSequenceData t).map i) ((s.appendToBlowupSequenceData t).center i)] := by
  have hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  · have h1 : i + 1 ≤ s.toBlowupSequenceData.length := by omega
    rw [appendBoundary_of_le_length s t h1, appendBoundary_of_le_length s t (le_of_lt h),
      appendToBlowupSequenceData_blowupMorphism_of_lt_length s t h, appendToBlowupSequenceData_center_of_lt_length s t h]
    exact map_strictTransform_comap_eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_lt_length s t h)
      (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)) (s.toBlowupSequenceData.map i) (s.toBlowupSequenceData.center i)
      (s.boundary i) (s.boundary (i + 1)) (s.boundary_succ i h)
  · subst h
    have ht0 : 0 < t.toBlowupSequenceData.length := by omega
    have hbs : t.boundary 1 =
        (t.boundary 0).map
            (Blowup.strictTransform (t.toBlowupSequenceData.map 0) (t.toBlowupSequenceData.center 0)) ++
          [Blowup.exceptionalIdeal (t.toBlowupSequenceData.map 0) (t.toBlowupSequenceData.center 0)] :=
      t.boundary_succ 0 ht0
    have hL1 : t.boundary 1 =
        ((s.boundary s.toBlowupSequenceData.length).map
            (fun D => D.comap t.toBlowupSequenceData.isoZero.hom)).map
            (Blowup.strictTransform (t.toBlowupSequenceData.map 0) (t.toBlowupSequenceData.center 0)) ++
          [Blowup.exceptionalIdeal (t.toBlowupSequenceData.map 0) (t.toBlowupSequenceData.center 0)] := by
      rw [hbs, t.boundary_zero]
    have hb1 := map_strictTransform_comp_iso_hom hinv (t.toBlowupSequenceData.map 0) t.toBlowupSequenceData.isoZero
      (t.toBlowupSequenceData.center 0) (s.boundary s.toBlowupSequenceData.length) (t.boundary 1) hL1
    rw [appendBoundary_length_succ s t,
      appendBoundary_of_le_length s t (le_refl s.toBlowupSequenceData.length),
      appendToBlowupSequenceData_blowupMorphism_length s t, appendToBlowupSequenceData_center_length s t,
      ← Category.assoc (t.toBlowupSequenceData.map 0) t.toBlowupSequenceData.isoZero.hom]
    exact map_strictTransform_comap_eqToHom (appendToBlowupSequenceData_schemeAt_length_succ s t)
      (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))
      (t.toBlowupSequenceData.map 0 ≫ t.toBlowupSequenceData.isoZero.hom)
      ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv)
      (s.boundary s.toBlowupSequenceData.length) (t.boundary 1) hb1
  · have hlt : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length := by omega
    have hsucc : s.toBlowupSequenceData.length < i + 1 := by omega
    have hidx : i + 1 - s.toBlowupSequenceData.length = i - s.toBlowupSequenceData.length + 1 := by omega
    rw [appendBoundary_of_length_lt s t hsucc, appendBoundary_of_length_lt s t h,
      appendToBlowupSequenceData_blowupMorphism_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h,
      map_comap_eqToHom_congr (A := (s.appendToBlowupSequenceData t).obj (i + 1))
        (F := t.toBlowupSequenceData.obj) t.boundary
        (i + 1 - s.toBlowupSequenceData.length) (i - s.toBlowupSequenceData.length + 1) hidx
        (appendToBlowupSequenceData_schemeAt_of_length_lt s t hsucc) (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h)]
    exact map_strictTransform_comap_eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h)
      (appendToBlowupSequenceData_schemeAt_of_length_lt s t h) (t.toBlowupSequenceData.map (i - s.toBlowupSequenceData.length))
      (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length))
      (t.boundary (i - s.toBlowupSequenceData.length))
      (t.boundary (i - s.toBlowupSequenceData.length + 1))
      (t.boundary_succ (i - s.toBlowupSequenceData.length) hlt)

def append (hinv : ComapIsoInvariance.{u}) : MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := s.appendToBlowupSequenceData t
  proj := s.appendProjectionToBase t
  proj_zero := appendProjectionToBase_zero s t
  proj_succ := appendProjectionToBase_succ s t
  ideal := s.appendIdeal t
  boundary := s.appendBoundary t
  ideal_zero := appendIdeal_zero s t
  boundary_zero := appendBoundary_zero s t
  center_order := fun i hi => center_support_subset_orderAtLeastLocus_appendIdeal s t hinv i hi
  center_smooth := fun i hi => smooth_center_comp_appendProjectionToBase s t hinv i hi
  center_snc := fun i hi => hasStrictNormalCrossingsWith_appendBoundary s t hinv i hi
  ideal_succ := fun i hi => exceptionalIdeal_pow_mul_appendIdeal_succ s t hinv i hi
  boundary_succ := fun i hi => appendBoundary_succ s t hinv i hi

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem append_toBlowupSequenceData (hinv : ComapIsoInvariance.{u}) :
    (s.append t hinv).toBlowupSequenceData = s.appendToBlowupSequenceData t := rfl

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem append_length (hinv : ComapIsoInvariance.{u}) :
    (s.append t hinv).toBlowupSequenceData.length =
      s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem append_toMarkedSequence_length (hinv : ComapIsoInvariance.{u}) :
    (s.append t hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups.length =
      s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem append_projectionToBase (hinv : ComapIsoInvariance.{u}) (i : ℕ) :
    (s.append t hinv).proj i = s.appendProjectionToBase t i := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem append_ideal (hinv : ComapIsoInvariance.{u}) (i : ℕ) :
    (s.append t hinv).ideal i = s.appendIdeal t i := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem append_boundary (hinv : ComapIsoInvariance.{u}) (i : ℕ) :
    (s.append t hinv).boundary i = s.appendBoundary t i := rfl

/- English proof (translation)
The claim follows from `appendToBlowupSequenceData_schemeAt_of_le_length s t h`.
-/
theorem append_schemeAt_of_le_length (hinv : ComapIsoInvariance.{u}) {i : ℕ} (h : i ≤ s.toBlowupSequenceData.length) :
    (s.append t hinv).toBlowupSequenceData.obj i = s.toBlowupSequenceData.obj i :=
  appendToBlowupSequenceData_schemeAt_of_le_length s t h

/- English proof (translation)
The claim follows from `appendToBlowupSequenceData_schemeAt_of_length_lt s t h`.
-/
theorem append_schemeAt_of_length_lt (hinv : ComapIsoInvariance.{u}) {i : ℕ} (h : s.toBlowupSequenceData.length < i) :
    (s.append t hinv).toBlowupSequenceData.obj i =
      t.toBlowupSequenceData.obj (i - s.toBlowupSequenceData.length) :=
  appendToBlowupSequenceData_schemeAt_of_length_lt s t h

/- English proof (translation)
Establish `hgt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length` using `by omega`. Establish `key : s.appendIdeal t (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) = (t.ideal t.toBlowupSequenceData.length).comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_add_length s t h))`. Rewrite using `[appendIdeal_of_length_lt s t hgt]`. Conclude with `comap_eqToHom_congr (fun n => t.toBlowupSequenceData.obj n) (fun n => t.ideal n) (by omega) (appendToBlowupSequenceData_schemeAt_of_length_lt s t hgt) (appendToBlowupSequenceData_schemeAt_length_add_length s t h)`. Conclude with `key`.
-/
theorem append_ideal_length_add_length (hinv : ComapIsoInvariance.{u}) (h : 0 < t.toBlowupSequenceData.length) :
    (s.append t hinv).ideal (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      (t.ideal t.toBlowupSequenceData.length).comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_add_length s t h)) := by
  have hgt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := by omega
  have key : s.appendIdeal t (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      (t.ideal t.toBlowupSequenceData.length).comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_add_length s t h)) := by
    rw [appendIdeal_of_length_lt s t hgt]
    exact comap_eqToHom_congr (fun n => t.toBlowupSequenceData.obj n)
      (fun n => t.ideal n) (by omega) (appendToBlowupSequenceData_schemeAt_of_length_lt s t hgt)
      (appendToBlowupSequenceData_schemeAt_length_add_length s t h)
  exact key

/- English proof (translation)
Establish `hgt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length` using `by omega`. Use `show s.appendBoundary t (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) = (t.boundary t.toBlowupSequenceData.length).map (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_add_length s t h)))`. Use `(appendBoundary_of_length_lt s t hgt).trans ?_` and prove the remaining obligations. Conclude with `map_comap_eqToHom_congr (A := (s.appendToBlowupSequenceData t).obj (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length)) (F := fun n => t.toBlowupSequenceData.obj n) (fun n => t.boundary n) (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length - s.toBlowupSequ …`.
-/
theorem append_boundary_length_add_length (hinv : ComapIsoInvariance.{u}) (h : 0 < t.toBlowupSequenceData.length) :
    (s.append t hinv).boundary (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      (t.boundary t.toBlowupSequenceData.length).map
        (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_add_length s t h))) := by
  have hgt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := by omega
  show s.appendBoundary t (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      (t.boundary t.toBlowupSequenceData.length).map
        (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_add_length s t h)))
  refine (appendBoundary_of_length_lt s t hgt).trans ?_
  exact map_comap_eqToHom_congr
    (A := (s.appendToBlowupSequenceData t).obj (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length))
    (F := fun n => t.toBlowupSequenceData.obj n) (fun n => t.boundary n)
    (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length - s.toBlowupSequenceData.length)
    t.toBlowupSequenceData.length (by omega)
    (appendToBlowupSequenceData_schemeAt_of_length_lt s t hgt) (appendToBlowupSequenceData_schemeAt_length_add_length s t h)

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution

end
