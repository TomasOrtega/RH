import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace SequenceOfBlowupsPullback

variable {X X' : Scheme.{u}}

def prependIndex (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | (n + 1) => f n + 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem prependIndex_zero (f : ℕ → ℕ) : prependIndex f 0 = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem prependIndex_succ (f : ℕ → ℕ) (n : ℕ) : prependIndex f (n + 1) = f n + 1 := rfl

def succIndex (f : ℕ → ℕ) : ℕ → ℕ := fun j => f j + 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem succIndex_apply (f : ℕ → ℕ) (j : ℕ) : succIndex f j = f j + 1 := rfl

/- English proof (translation)
The claim follows from `(BlowupSequenceData.toSequenceOfBlowups_schemeAt (BlowupSequenceData.prepend Z hZ d) 0).trans (BlowupSequenceData.prepend_schemeAt_zero Z hZ d)`.
-/
private theorem prepend_schemeAt_zero (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z)
    (d : BlowupSequenceData X) : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt 0 = X :=
  (BlowupSequenceData.toSequenceOfBlowups_schemeAt (BlowupSequenceData.prepend Z hZ d) 0).trans
    (BlowupSequenceData.prepend_schemeAt_zero Z hZ d)

/- English proof (translation)
The claim follows from `(BlowupSequenceData.toSequenceOfBlowups_schemeAt (BlowupSequenceData.prepend Z hZ d) (n + 1)).trans ((BlowupSequenceData.prepend_schemeAt_succ Z hZ d n).trans (BlowupSequenceData.toSequenceOfBlowups_schemeAt d n).symm)`.
-/
private theorem prepend_schemeAt_succ (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z)
    (d : BlowupSequenceData X) (n : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt (n + 1) = d.toSequenceOfBlowups.schemeAt n :=
  (BlowupSequenceData.toSequenceOfBlowups_schemeAt (BlowupSequenceData.prepend Z hZ d) (n + 1)).trans
    ((BlowupSequenceData.prepend_schemeAt_succ Z hZ d n).trans (BlowupSequenceData.toSequenceOfBlowups_schemeAt d n).symm)

/- English proof (translation)
Rewrite using `[BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.prepend_length, BlowupSequenceData.toSequenceOfBlowups_length]`.
-/
private theorem prepend_length (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z)
    (d : BlowupSequenceData X) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length = d.toSequenceOfBlowups.length + 1 := by
  rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.prepend_length, BlowupSequenceData.toSequenceOfBlowups_length]

/- English proof (translation)
Rewrite `h` using `[prepend_length]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem le_length_of_succ_le_prepend_length (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z)
    (d : BlowupSequenceData X) (n : ℕ)
    (h : n + 1 ≤ (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length) : n ≤ d.toSequenceOfBlowups.length := by
  rw [prepend_length] at h
  omega

private def prependMapOfLELength {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) :
    ∀ j : ℕ, j ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length →
      ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.schemeAt j ⟶
        (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt (prependIndex c.idx j))
  | 0, _ =>
      eqToHom (prepend_schemeAt_zero (Z.comap φ) hZ' d') ≫ φ ≫
        eqToHom (prepend_schemeAt_zero Z hZ d).symm
  | (n + 1), h =>
      eqToHom (prepend_schemeAt_succ (Z.comap φ) hZ' d' n) ≫
        c.map n (le_length_of_succ_le_prepend_length (Z.comap φ) hZ' d' n h) ≫
        eqToHom (prepend_schemeAt_succ Z hZ d (c.idx n)).symm

/- English proof (translation)
Rewrite using `[prepend_length, prepend_length, prependIndex_succ, c.idx_length]`.
-/
private theorem prependIndex_length_eq_prepend_length {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) :
    prependIndex c.idx (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length =
      (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length := by
  rw [prepend_length, prepend_length, prependIndex_succ, c.idx_length]

/- English proof (translation)
Establish `hlen'` using `prepend_length (Z.comap φ) hZ' d'`. Establish `hlen` using `prepend_length Z hZ d`. Rewrite `hj` using `[hlen']`. Rewrite using `[hlen]`. Consider the cases of `j with`.

Consider the case `zero`. Simplify using `only [prependIndex_zero]`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n`. Establish `hn : n < d'.toSequenceOfBlowups.length` using `by omega`.

Establish `hc` using `c.idx_lt n hn`. Simplify using `only [prependIndex_succ]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem prependIndex_lt_prepend_length {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (j : ℕ)
    (hj : j < (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    prependIndex c.idx j < (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length := by
  have hlen' := prepend_length (Z.comap φ) hZ' d'
  have hlen := prepend_length Z hZ d
  rw [hlen'] at hj
  rw [hlen]
  cases j with
  | zero =>
      simp only [prependIndex_zero]
      omega
  | succ n =>
      have hn : n < d'.toSequenceOfBlowups.length := by omega
      have hc := c.idx_lt n hn
      simp only [prependIndex_succ]
      omega

/- English proof (translation)
Consider the cases of `j with`. Consider the case `zero`. Simplify using `only [prependIndex_zero, prependIndex_succ]`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n`.

Establish `hn : n < d'.toSequenceOfBlowups.length`. Rewrite `hj` using `[prepend_length]`. Use linear arithmetic over natural numbers and integers. Establish `hstep : c.idx n < c.idx (n + 1)` using `c.idx_strictMono n hn`. Simplify using `only [prependIndex_succ]`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem prependIndex_lt_prependIndex_succ {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (_hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (j : ℕ)
    (hj : j < (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    prependIndex c.idx j < prependIndex c.idx (j + 1) := by
  cases j with
  | zero =>
      simp only [prependIndex_zero, prependIndex_succ]
      omega
  | succ n =>
      have hn : n < d'.toSequenceOfBlowups.length := by
        rw [prepend_length] at hj
        omega
      have hstep : c.idx n < c.idx (n + 1) := c.idx_strictMono n hn
      simp only [prependIndex_succ]
      omega

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) 0, BlowupSequenceData.prepend_blowupMorphism_zero Z hZ d, BlowupSequenceData.projectionToBase_zero (BlowupSequenceData.prepend Z hZ d)]`. Conclude with `(Category.comp_id _).trans (BlowupSequenceData.projectionToBase_zero d).symm`. Consider the case `succ m ih`.

Rewrite using `[BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) (m + 1), BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d m, ih]`. Conclude with `(BlowupSequenceData.projectionToBase_succ d m).symm`.
-/
private theorem prepend_projectionToBase_succ {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y) (n : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).projectionToBase (n + 1) = d.projectionToBase n := by
  induction n with
  | zero =>
      rw [BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) 0,
        BlowupSequenceData.prepend_blowupMorphism_zero Z hZ d,
        BlowupSequenceData.projectionToBase_zero (BlowupSequenceData.prepend Z hZ d)]
      exact (Category.comp_id _).trans (BlowupSequenceData.projectionToBase_zero d).symm
  | succ m ih =>
      rw [BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) (m + 1),
        BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d m, ih]
      exact (BlowupSequenceData.projectionToBase_succ d m).symm

/- English proof (translation)
The claim follows from `(BlowupSequenceData.toSequenceOfBlowups_projectionToBase (BlowupSequenceData.prepend Z hZ d) 0).trans ((BlowupSequenceData.projectionToBase_zero (BlowupSequenceData.prepend Z hZ d)).trans rfl)`.
-/
private theorem prepend_toSequenceOfBlowups_projectionToBase_zero {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase 0 = 𝟙 Y :=
  (BlowupSequenceData.toSequenceOfBlowups_projectionToBase (BlowupSequenceData.prepend Z hZ d) 0).trans
    ((BlowupSequenceData.projectionToBase_zero (BlowupSequenceData.prepend Z hZ d)).trans rfl)

/- English proof (translation)
The claim follows from `(BlowupSequenceData.toSequenceOfBlowups_projectionToBase (BlowupSequenceData.prepend Z hZ d) (n + 1)).trans ((prepend_projectionToBase_succ Z hZ d n).trans (BlowupSequenceData.toSequenceOfBlowups_projectionToBase d n).symm)`.
-/
private theorem prepend_toSequenceOfBlowups_projectionToBase_succ {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y) (n : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (n + 1) = d.toSequenceOfBlowups.projectionToBase n :=
  (BlowupSequenceData.toSequenceOfBlowups_projectionToBase (BlowupSequenceData.prepend Z hZ d) (n + 1)).trans
    ((prepend_projectionToBase_succ Z hZ d n).trans (BlowupSequenceData.toSequenceOfBlowups_projectionToBase d n).symm)

/- English proof (translation)
Rewrite using `[eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]`.
-/
private theorem eqToHom_comp_comp_eqToHom_refl {A B : Scheme.{u}} (f : A ⟶ B) (h1 : A = A)
    (h2 : B = B) : eqToHom h1 ≫ f ≫ eqToHom h2 = f := by
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/- English proof (translation)
Use `show 𝟙 X' ≫ φ ≫ 𝟙 X = φ`. Simplify using the standard rewrite rules.
-/
private theorem prependComparisonMap_zero {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ))
    (hj : 0 ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    prependMapOfLELength c Z hZ hZ' 0 hj = φ := by
  show 𝟙 X' ≫ φ ≫ 𝟙 X = φ
  simp

/- English proof (translation)
Use `show eqToHom (prepend_schemeAt_succ (Z.comap φ) hZ' d' n) ≫ c.map n (le_length_of_succ_le_prepend_length (Z.comap φ) hZ' d' n h) ≫ eqToHom (prepend_schemeAt_succ Z hZ d (c.idx n)).symm = c.map n hn`. Conclude with `eqToHom_comp_comp_eqToHom_refl (c.map n hn) (prepend_schemeAt_succ (Z.comap φ) hZ' d' n) (prepend_schemeAt_succ Z hZ d (c.idx n)).symm`.
-/
private theorem prependComparisonMap_succ {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (n : ℕ)
    (h : n + 1 ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length)
    (hn : n ≤ d'.toSequenceOfBlowups.length) :
    prependMapOfLELength c Z hZ hZ' (n + 1) h = c.map n hn := by
  show eqToHom (prepend_schemeAt_succ (Z.comap φ) hZ' d' n) ≫
      c.map n (le_length_of_succ_le_prepend_length (Z.comap φ) hZ' d' n h) ≫
      eqToHom (prepend_schemeAt_succ Z hZ d (c.idx n)).symm = c.map n hn
  exact eqToHom_comp_comp_eqToHom_refl (c.map n hn) (prepend_schemeAt_succ (Z.comap φ) hZ' d' n)
    (prepend_schemeAt_succ Z hZ d (c.idx n)).symm

/- English proof (translation)
Establish `key : IsPullback φ (𝟙 X') (𝟙 X) φ` using `(IsPullback.of_horiz_isIso ⟨by simp⟩).flip`. Establish `h1 : prependMapOfLELength c Z hZ hZ' 0 hj = φ` using `prependComparisonMap_zero c Z hZ hZ' hj`. Establish `h2 : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.projectionToBase 0 = 𝟙 X'` using `prepend_toSequenceOfBlowups_projectionToBase_zero (Z.comap φ) hZ' d'`. Establish `h3 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (prependIndex c.idx 0) = 𝟙 X` using `prepend_toSequenceOfBlowups_projectionToBase_zero Z hZ d`. Rewrite using `[h1, h2, h3]`.

Conclude with `key`.
-/
private theorem isPullback_prependComparisonMap_zero {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ))
    (hj : 0 ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    IsPullback (prependMapOfLELength c Z hZ hZ' 0 hj)
      ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.projectionToBase 0)
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (prependIndex c.idx 0)) φ := by
  have key : IsPullback φ (𝟙 X') (𝟙 X) φ := (IsPullback.of_horiz_isIso ⟨by simp⟩).flip
  have h1 : prependMapOfLELength c Z hZ hZ' 0 hj = φ := prependComparisonMap_zero c Z hZ hZ' hj
  have h2 : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.projectionToBase 0 = 𝟙 X' :=
    prepend_toSequenceOfBlowups_projectionToBase_zero (Z.comap φ) hZ' d'
  have h3 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (prependIndex c.idx 0) = 𝟙 X :=
    prepend_toSequenceOfBlowups_projectionToBase_zero Z hZ d
  rw [h1, h2, h3]
  exact key

/- English proof (translation)
Establish `h1 : prependMapOfLELength c Z hZ hZ' (n + 1) hj = c.map n (le_length_of_succ_le_prepend_length (Z.comap φ) hZ' d' n hj)` using `prependComparisonMap_succ c Z hZ hZ' n hj (le_length_of_succ_le_prepend_length (Z.comap φ) hZ' d' n hj)`. Establish `h2 : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.projectionToBase (n + 1) = d'.toSequenceOfBlowups.projectionToBase n` using `prepend_toSequenceOfBlowups_projectionToBase_succ (Z.comap φ) hZ' d' n`. Establish `h3 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (prependIndex c.idx (n + 1)) = d.toSequenceOfBlowups.projectionToBase (c.idx n)` using `prepend_toSequenceOfBlowups_projectionToBase_succ Z hZ d (c.idx n)`. Rewrite using `[h1, h2, h3]`. Conclude with `c.isPullback n (le_length_of_succ_le_prepend_length (Z.comap φ) hZ' d' n hj)`.
-/
private theorem isPullback_prependComparisonMap_succ {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (n : ℕ)
    (hj : n + 1 ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    IsPullback (prependMapOfLELength c Z hZ hZ' (n + 1) hj)
      ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.projectionToBase (n + 1))
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (prependIndex c.idx (n + 1))) φ := by
  have h1 : prependMapOfLELength c Z hZ hZ' (n + 1) hj =
      c.map n (le_length_of_succ_le_prepend_length (Z.comap φ) hZ' d' n hj) :=
    prependComparisonMap_succ c Z hZ hZ' n hj (le_length_of_succ_le_prepend_length (Z.comap φ) hZ' d' n hj)
  have h2 : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.projectionToBase (n + 1) =
      d'.toSequenceOfBlowups.projectionToBase n := prepend_toSequenceOfBlowups_projectionToBase_succ (Z.comap φ) hZ' d' n
  have h3 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (prependIndex c.idx (n + 1)) =
      d.toSequenceOfBlowups.projectionToBase (c.idx n) := prepend_toSequenceOfBlowups_projectionToBase_succ Z hZ d (c.idx n)
  rw [h1, h2, h3]
  exact c.isPullback n (le_length_of_succ_le_prepend_length (Z.comap φ) hZ' d' n hj)

/- English proof (translation)
Consider the cases of `j with`. Consider the case `zero => exact isPullback_prependComparisonMap_zero c Z hZ hZ' _`. Consider the case `succ n => exact isPullback_prependComparisonMap_succ c Z hZ hZ' n _`.
-/
private theorem isPullback_prependComparisonMap {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (j : ℕ)
    (hj : j ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    IsPullback (prependMapOfLELength c Z hZ hZ' j hj)
      ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.projectionToBase j)
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (prependIndex c.idx j)) φ := by
  cases j with
  | zero => exact isPullback_prependComparisonMap_zero c Z hZ hZ' _
  | succ n => exact isPullback_prependComparisonMap_succ c Z hZ hZ' n _

/- English proof (translation)
Substitute `e0'` using the available equality. Substitute `e1'` using the available equality. Substitute `e0` using the available equality. Substitute `e1` using the available equality. Establish `h1 : L1 = s'` using `eq_of_heq hL1`.

Establish `h2 : L2 = ψ` using `eq_of_heq hL2`. Establish `h3 : R1 = m` using `eq_of_heq hR1`. Establish `h4 : R2 = s` using `eq_of_heq hR2`. Rewrite using `[h1, h2, h3, h4, hw]`.
-/
private theorem comp_eq_comp_of_heq {A' B' A B Y' Y V' V : Scheme.{u}}
    (e0' : A' = Y') (e1' : B' = V') (e0 : A = Y) (e1 : B = V)
    {s' : V' ⟶ Y'} {ψ : Y' ⟶ Y} {m : V' ⟶ V} {s : V ⟶ Y}
    (hw : m ≫ s = s' ≫ ψ)
    {L1 : B' ⟶ A'} {L2 : A' ⟶ A} {R1 : B' ⟶ B} {R2 : B ⟶ A}
    (hL1 : HEq L1 s') (hL2 : HEq L2 ψ) (hR1 : HEq R1 m) (hR2 : HEq R2 s) :
    L1 ≫ L2 = R1 ≫ R2 := by
  subst e0'
  subst e1'
  subst e0
  subst e1
  have h1 : L1 = s' := eq_of_heq hL1
  have h2 : L2 = ψ := eq_of_heq hL2
  have h3 : R1 = m := eq_of_heq hR1
  have h4 : R2 = s := eq_of_heq hR2
  rw [h1, h2, h3, h4, hw]

/- English proof (translation)
Rewrite using `[BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.prepend_blowupMorphism_succ]`.
-/
private theorem prepend_blowupMorphism_succ {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y) (n : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMapSucc (n + 1) = d.toSequenceOfBlowups.transitionMapSucc n := by
  rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.prepend_blowupMorphism_succ]

/- English proof (translation)
Rewrite using `[BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.prepend_blowupMorphism_zero, SequenceOfBlowups.projectionToBase_zero, BlowupSequenceData.toSequenceOfBlowups_isoObjZero]`.
-/
private theorem prepend_blowupMorphism_zero_eq_projectionToBase {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMapSucc 0 = d.toSequenceOfBlowups.projectionToBase 0 := by
  rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.prepend_blowupMorphism_zero, SequenceOfBlowups.projectionToBase_zero,
    BlowupSequenceData.toSequenceOfBlowups_isoObjZero]

/- English proof (translation)
Rewrite using `[SequenceOfBlowups.projectionToBase_def, BlowupSequenceData.toSequenceOfBlowups_isoObjZero, BlowupSequenceData.prepend_isoObjZero, Iso.refl_hom]`. Conclude with `(Category.comp_id _).symm`.
-/
private theorem prepend_transitionMap_zero {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y) (m : ℕ) (h : 0 ≤ m) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap h =
      (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase m := by
  rw [SequenceOfBlowups.projectionToBase_def, BlowupSequenceData.toSequenceOfBlowups_isoObjZero, BlowupSequenceData.prepend_isoObjZero,
    Iso.refl_hom]
  exact (Category.comp_id _).symm

/- English proof (translation)
The claim follows from `((SequenceOfBlowups.blowupMorphism_eq_transitionMap (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups (n + 1)).symm.trans (prepend_blowupMorphism_succ Z hZ d n)).trans (SequenceOfBlowups.blowupMorphism_eq_transitionMap d.toSequenceOfBlowups n)`.
-/
private theorem prepend_transitionMap_succ_self {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y) (n : ℕ) (h : n + 1 ≤ n + 1 + 1)
    (h' : n ≤ n + 1) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap h = d.toSequenceOfBlowups.transitionMap h' :=
  ((SequenceOfBlowups.blowupMorphism_eq_transitionMap (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups (n + 1)).symm.trans
      (prepend_blowupMorphism_succ Z hZ d n)).trans
    (SequenceOfBlowups.blowupMorphism_eq_transitionMap d.toSequenceOfBlowups n)

/- English proof (translation)
Use `revert h`. Proceed by induction on `b, hab using Nat.le_induction with`. Consider the case `base`. Introduce `h`. Conclude with `(SequenceOfBlowups.transitionMap_self (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups h).trans (SequenceOfBlowups.transitionMap_self d.toSequenceOfBlowups (le_refl a)).symm`.

Consider the case `succ m hm ih`. Introduce `h`. Establish `e1 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap (Nat.add_le_add_right hm 1) = d.toSequenceOfBlowups.transitionMap hm` using `ih (Nat.add_le_add_right hm 1)`. Establish `e2 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap (Nat.le_succ (m + 1)) = d.toSequenceOfBlowups.transitionMap (Nat.le_succ m)` using `prepend_transitionMap_succ_self Z hZ d m (Nat.le_succ (m + 1)) (Nat.le_succ m)`. Establish `e3 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap h = (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap (Nat.le_succ (m + 1)) ≫ (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap (Nat.add_le_add_right hm 1)` using `(SequenceOfBlowups.transitionMap_trans (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups (Nat.add_le_add_right hm 1) (Nat.le_succ (m + 1))).symm`.

Rewrite using `[e3, e1, e2]`. Conclude with `SequenceOfBlowups.transitionMap_trans d.toSequenceOfBlowups hm (Nat.le_succ m)`.
-/
private theorem prepend_transitionMap_succ_succ {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y) {a b : ℕ} (hab : a ≤ b)
    (h : a + 1 ≤ b + 1) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap h = d.toSequenceOfBlowups.transitionMap hab := by
  revert h
  induction b, hab using Nat.le_induction with
  | base =>
      intro h
      exact (SequenceOfBlowups.transitionMap_self (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups h).trans
        (SequenceOfBlowups.transitionMap_self d.toSequenceOfBlowups (le_refl a)).symm
  | succ m hm ih =>
      intro h
      have e1 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap (Nat.add_le_add_right hm 1) =
          d.toSequenceOfBlowups.transitionMap hm := ih (Nat.add_le_add_right hm 1)
      have e2 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap (Nat.le_succ (m + 1)) =
          d.toSequenceOfBlowups.transitionMap (Nat.le_succ m) :=
        prepend_transitionMap_succ_self Z hZ d m (Nat.le_succ (m + 1)) (Nat.le_succ m)
      have e3 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap h =
          (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap (Nat.le_succ (m + 1)) ≫
            (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap (Nat.add_le_add_right hm 1) :=
        (SequenceOfBlowups.transitionMap_trans (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups
          (Nat.add_le_add_right hm 1) (Nat.le_succ (m + 1))).symm
      rw [e3, e1, e2]
      exact SequenceOfBlowups.transitionMap_trans d.toSequenceOfBlowups hm (Nat.le_succ m)

/- English proof (translation)
Consider the cases of `j with`. Consider the case `zero`. Establish `hlen : 0 ≤ d'.toSequenceOfBlowups.length` using `Nat.zero_le _`. Use `comp_eq_comp_of_heq (prepend_schemeAt_zero (Z.comap φ) hZ' d') (prepend_schemeAt_succ (Z.comap φ) hZ' d' 0) (prepend_schemeAt_zero Z hZ d) (prepend_schemeAt_succ Z hZ d (c.idx 0)) ((c.isPullback 0 hlen).w) ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `heq_of_eq (prepend_blowupMorphism_zero_eq_projectionToBase (Z.comap φ) hZ' d')`.

Conclude with `heq_of_eq (prependComparisonMap_zero c Z hZ hZ' (le_of_lt hj))`. Conclude with `heq_of_eq (prependComparisonMap_succ c Z hZ hZ' 0 hj hlen)`. Conclude with `heq_of_eq ((prepend_transitionMap_zero Z hZ d (c.idx 0 + 1) (Nat.zero_le _)).trans (prepend_toSequenceOfBlowups_projectionToBase_succ Z hZ d (c.idx 0)))`. Consider the case `succ n`. Establish `hn : n < d'.toSequenceOfBlowups.length`.

Establish `hlen` using `prepend_length (Z.comap φ) hZ' d'`. Use linear arithmetic over natural numbers and integers. Use `comp_eq_comp_of_heq (prepend_schemeAt_succ (Z.comap φ) hZ' d' n) (prepend_schemeAt_succ (Z.comap φ) hZ' d' (n + 1)) (prepend_schemeAt_succ Z hZ d (c.idx n)) (prepend_schemeAt_succ Z hZ d (c.idx (n + 1))) ((c.step n hn).symm) ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `heq_of_eq (prepend_blowupMorphism_succ (Z.comap φ) hZ' d' n)`. Conclude with `heq_of_eq (prependComparisonMap_succ c Z hZ hZ' n (le_of_lt hj) (le_of_lt hn))`.

Conclude with `heq_of_eq (prependComparisonMap_succ c Z hZ hZ' (n + 1) hj hn)`. Conclude with `heq_of_eq (prepend_transitionMap_succ_succ Z hZ d (le_of_lt (c.idx_strictMono n hn)) (Nat.add_le_add_right (le_of_lt (c.idx_strictMono n hn)) 1))`.
-/
private theorem blowupMorphism_comp_prependComparisonMap {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (j : ℕ)
    (hj : j < (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.transitionMapSucc j ≫
        prependMapOfLELength c Z hZ hZ' j (le_of_lt hj) =
      prependMapOfLELength c Z hZ hZ' (j + 1) hj ≫
        (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap
          (le_of_lt (prependIndex_lt_prependIndex_succ c Z hZ hZ' j hj)) := by
  cases j with
  | zero =>
      have hlen : 0 ≤ d'.toSequenceOfBlowups.length := Nat.zero_le _
      refine comp_eq_comp_of_heq (prepend_schemeAt_zero (Z.comap φ) hZ' d')
        (prepend_schemeAt_succ (Z.comap φ) hZ' d' 0)
        (prepend_schemeAt_zero Z hZ d)
        (prepend_schemeAt_succ Z hZ d (c.idx 0))
        ((c.isPullback 0 hlen).w) ?_ ?_ ?_ ?_
      · exact heq_of_eq (prepend_blowupMorphism_zero_eq_projectionToBase (Z.comap φ) hZ' d')
      · exact heq_of_eq (prependComparisonMap_zero c Z hZ hZ' (le_of_lt hj))
      · exact heq_of_eq (prependComparisonMap_succ c Z hZ hZ' 0 hj hlen)
      · exact heq_of_eq ((prepend_transitionMap_zero Z hZ d (c.idx 0 + 1) (Nat.zero_le _)).trans
          (prepend_toSequenceOfBlowups_projectionToBase_succ Z hZ d (c.idx 0)))
  | succ n =>
      have hn : n < d'.toSequenceOfBlowups.length := by
        have hlen := prepend_length (Z.comap φ) hZ' d'
        omega
      refine comp_eq_comp_of_heq (prepend_schemeAt_succ (Z.comap φ) hZ' d' n)
        (prepend_schemeAt_succ (Z.comap φ) hZ' d' (n + 1))
        (prepend_schemeAt_succ Z hZ d (c.idx n))
        (prepend_schemeAt_succ Z hZ d (c.idx (n + 1)))
        ((c.step n hn).symm) ?_ ?_ ?_ ?_
      · exact heq_of_eq (prepend_blowupMorphism_succ (Z.comap φ) hZ' d' n)
      · exact heq_of_eq (prependComparisonMap_succ c Z hZ hZ' n (le_of_lt hj) (le_of_lt hn))
      · exact heq_of_eq (prependComparisonMap_succ c Z hZ hZ' (n + 1) hj hn)
      · exact heq_of_eq (prepend_transitionMap_succ_succ Z hZ d (le_of_lt (c.idx_strictMono n hn))
          (Nat.add_le_add_right (le_of_lt (c.idx_strictMono n hn)) 1))

/- English proof (translation)
Substitute `hA` using the available equality. Substitute `hB` using the available equality. Establish `e1 : Jb = J` using `eq_of_heq hJb`. Establish `e2 : J' = K` using `eq_of_heq hJ'`. Rewrite using `[e1, e2, hK]`.

Simplify using the standard rewrite rules.
-/
private theorem comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq {A A' B B' : Scheme.{u}} (hA : A' = A) (hB : B = B')
    (g : A ⟶ B) (J : B.IdealSheafData) (K : A.IdealSheafData) (hK : K = J.comap g)
    (J' : A'.IdealSheafData) (Jb : B'.IdealSheafData)
    (hJb : HEq Jb J) (hJ' : HEq J' K) :
    J' = Jb.comap (eqToHom hA ≫ g ≫ eqToHom hB) := by
  subst hA
  subst hB
  have e1 : Jb = J := eq_of_heq hJb
  have e2 : J' = K := eq_of_heq hJ'
  rw [e1, e2, hK]
  simp

/- English proof (translation)
Consider the cases of `j with`. Consider the case `zero`. Use `comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq (prepend_schemeAt_zero (Z.comap φ) hZ' d') (prepend_schemeAt_zero Z hZ d).symm φ Z (Z.comap φ) rfl ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center 0) ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowu …` and prove the remaining obligations. Conclude with `heq_of_eq ((BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) 0).trans (BlowupSequenceData.prepend_center_zero Z hZ d))`. Conclude with `heq_of_eq ((BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend (Z.comap φ) hZ' d') 0).trans (BlowupSequenceData.prepend_center_zero (Z.comap φ) hZ' d'))`.

Consider the case `succ n`. Establish `hlen : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length = d'.toSequenceOfBlowups.length + 1` using `prepend_length (Z.comap φ) hZ' d'`. Establish `hn' : n < d'.toSequenceOfBlowups.length` using `by omega`. Use `comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq (prepend_schemeAt_succ (Z.comap φ) hZ' d' n) (prepend_schemeAt_succ Z hZ d (c.idx n)).symm (c.map n (le_of_lt hn')) (d.toSequenceOfBlowups.center (c.idx n)) (d'.toSequenceOfBlowups.center n) (c.center_comap n hn') ((BlowupSequenceDa …` and prove the remaining obligations. Conclude with `heq_of_eq ((BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) (c.idx n + 1)).trans ((BlowupSequenceData.prepend_center_succ Z hZ d (c.idx n)).trans (BlowupSequenceData.toSequenceOfBlowups_center d (c.idx n)).symm))`.

Conclude with `heq_of_eq ((BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend (Z.comap φ) hZ' d') (n + 1)).trans ((BlowupSequenceData.prepend_center_succ (Z.comap φ) hZ' d' n).trans (BlowupSequenceData.toSequenceOfBlowups_center d' n).symm))`.
-/
private theorem prepend_center_eq_comap_prependIndex {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (j : ℕ)
    (hj : j < (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center j =
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (prependIndex c.idx j)).comap
        (prependMapOfLELength c Z hZ hZ' j (le_of_lt hj)) := by
  cases j with
  | zero =>
      refine comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq (prepend_schemeAt_zero (Z.comap φ) hZ' d')
        (prepend_schemeAt_zero Z hZ d).symm φ Z (Z.comap φ) rfl
        ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center 0)
        ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center 0) ?_ ?_
      · exact heq_of_eq ((BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) 0).trans
          (BlowupSequenceData.prepend_center_zero Z hZ d))
      · exact heq_of_eq
          ((BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend (Z.comap φ) hZ' d') 0).trans
            (BlowupSequenceData.prepend_center_zero (Z.comap φ) hZ' d'))
  | succ n =>
      have hlen : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length
          = d'.toSequenceOfBlowups.length + 1 := prepend_length (Z.comap φ) hZ' d'
      have hn' : n < d'.toSequenceOfBlowups.length := by omega
      refine comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq (prepend_schemeAt_succ (Z.comap φ) hZ' d' n)
        (prepend_schemeAt_succ Z hZ d (c.idx n)).symm (c.map n (le_of_lt hn'))
        (d.toSequenceOfBlowups.center (c.idx n)) (d'.toSequenceOfBlowups.center n) (c.center_comap n hn')
        ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center (n + 1))
        ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (c.idx n + 1)) ?_ ?_
      · exact heq_of_eq
          ((BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) (c.idx n + 1)).trans
            ((BlowupSequenceData.prepend_center_succ Z hZ d (c.idx n)).trans
              (BlowupSequenceData.toSequenceOfBlowups_center d (c.idx n)).symm))
      · exact heq_of_eq
          ((BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend (Z.comap φ) hZ' d') (n + 1)).trans
            ((BlowupSequenceData.prepend_center_succ (Z.comap φ) hZ' d' n).trans
              (BlowupSequenceData.toSequenceOfBlowups_center d' n).symm))

/- English proof (translation)
Establish `hlen : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length = d'.toSequenceOfBlowups.length + 1` using `prepend_length (Z.comap φ) hZ' d'`. Consider the cases of `j with`. Consider the case `zero`. Establish `h0 : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center 0 = Z.comap φ` using `(BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend (Z.comap φ) hZ' d') 0).trans (BlowupSequenceData.prepend_center_zero (Z.comap φ) hZ' d')`. Introduce `htop`.

Conclude with `hne (h0.symm.trans htop)`. Consider the case `succ n`. Establish `hn : n < d'.toSequenceOfBlowups.length` using `by omega`. Establish `h1 : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center (n + 1) = d'.toSequenceOfBlowups.center n` using `(BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend (Z.comap φ) hZ' d') (n + 1)).trans ((BlowupSequenceData.prepend_center_succ (Z.comap φ) hZ' d' n).trans (BlowupSequenceData.toSequenceOfBlowups_center d' n).symm)`. Introduce `htop`.

Conclude with `c.center_ne_top n hn (h1.symm.trans htop)`.
-/
private theorem prepend_center_ne_top {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (_hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (hne : Z.comap φ ≠ ⊤) (j : ℕ)
    (hj : j < (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center j ≠ ⊤ := by
  have hlen : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length = d'.toSequenceOfBlowups.length + 1 :=
    prepend_length (Z.comap φ) hZ' d'
  cases j with
  | zero =>
      have h0 : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center 0 = Z.comap φ :=
        (BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend (Z.comap φ) hZ' d') 0).trans
          (BlowupSequenceData.prepend_center_zero (Z.comap φ) hZ' d')
      intro htop
      exact hne (h0.symm.trans htop)
  | succ n =>
      have hn : n < d'.toSequenceOfBlowups.length := by omega
      have h1 : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center (n + 1) =
          d'.toSequenceOfBlowups.center n :=
        (BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend (Z.comap φ) hZ' d') (n + 1)).trans
          ((BlowupSequenceData.prepend_center_succ (Z.comap φ) hZ' d' n).trans
            (BlowupSequenceData.toSequenceOfBlowups_center d' n).symm)
      intro htop
      exact c.center_ne_top n hn (h1.symm.trans htop)

/- English proof (translation)
The claim follows from `(BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) (n + 1)).trans ((BlowupSequenceData.prepend_center_succ Z hZ d n).trans (BlowupSequenceData.toSequenceOfBlowups_center d n).symm)`.
-/
private theorem prepend_center_succ {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y) (n : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (n + 1) = d.toSequenceOfBlowups.center n :=
  (BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) (n + 1)).trans
    ((BlowupSequenceData.prepend_center_succ Z hZ d n).trans (BlowupSequenceData.toSequenceOfBlowups_center d n).symm)

/- English proof (translation)
Establish `hlen' : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length = d'.toSequenceOfBlowups.length + 1` using `prepend_length (Z.comap φ) hZ' d'`. Establish `hlen : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length = d.toSequenceOfBlowups.length + 1` using `prepend_length Z hZ d`. Establish `h0 : prependIndex c.idx 0 ≠ i` using `hmiss 0 (by omega)`. Rewrite `h0` using `[prependIndex_zero]`. Take `⟨n, rfl⟩ : ∃ n : ℕ, i = n + 1` from `⟨i - 1, by omega⟩`.

Establish `hn : n < d.toSequenceOfBlowups.length` using `by omega`. Establish `hmiss' : ∀ m : ℕ, m < d'.toSequenceOfBlowups.length → c.idx m ≠ n`. Introduce `m hm hmn`. Conclude with `hmiss (m + 1) (by omega) (by rw [prependIndex_succ, hmn])`. Establish `hzc : z ∈ (d.toSequenceOfBlowups.center n).support`.

Establish `hz2` using `hz`. Rewrite `hz2` using `[prepend_center_succ Z hZ d n]`. Conclude with `hz2`. Introduce `heq`. Use `c.omitted n hn hmiss' z hzc x' ?_` and prove the remaining obligations.

Rewrite using `[← prepend_toSequenceOfBlowups_projectionToBase_succ Z hZ d n]`. Conclude with `heq`.
-/
private theorem ne_projectionToBase_of_forall_prependIndex_ne {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (i : ℕ)
    (hi : i < (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length)
    (hmiss : ∀ j : ℕ, j < (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length →
      prependIndex c.idx j ≠ i)
    (z : ↥((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt i))
    (hz : z ∈ ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center i).support) (x' : ↥X') :
    φ.base x' ≠ ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase i).base z := by
  have hlen' : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length = d'.toSequenceOfBlowups.length + 1 :=
    prepend_length (Z.comap φ) hZ' d'
  have hlen : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length = d.toSequenceOfBlowups.length + 1 :=
    prepend_length Z hZ d
  have h0 : prependIndex c.idx 0 ≠ i := hmiss 0 (by omega)
  rw [prependIndex_zero] at h0
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = n + 1 := ⟨i - 1, by omega⟩
  have hn : n < d.toSequenceOfBlowups.length := by omega
  have hmiss' : ∀ m : ℕ, m < d'.toSequenceOfBlowups.length → c.idx m ≠ n := by
    intro m hm hmn
    exact hmiss (m + 1) (by omega) (by rw [prependIndex_succ, hmn])
  have hzc : z ∈ (d.toSequenceOfBlowups.center n).support := by
    have hz2 := hz
    rw [prepend_center_succ Z hZ d n] at hz2
    exact hz2
  intro heq
  refine c.omitted n hn hmiss' z hzc x' ?_
  rw [← prepend_toSequenceOfBlowups_projectionToBase_succ Z hZ d n]
  exact heq

def prepend {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (hne : Z.comap φ ≠ ⊤) :
    SequenceOfBlowupsPullback φ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups
      (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups where
  idx := prependIndex c.idx
  map := prependMapOfLELength c Z hZ hZ'
  idx_length := prependIndex_length_eq_prepend_length c Z hZ hZ'
  idx_lt := prependIndex_lt_prepend_length c Z hZ hZ'
  idx_strictMono := prependIndex_lt_prependIndex_succ c Z hZ hZ'
  isPullback := isPullback_prependComparisonMap c Z hZ hZ'
  step := blowupMorphism_comp_prependComparisonMap c Z hZ hZ'
  center_comap := prepend_center_eq_comap_prependIndex c Z hZ hZ'
  center_ne_top := prepend_center_ne_top c Z hZ hZ' hne
  omitted := ne_projectionToBase_of_forall_prependIndex_ne c Z hZ hZ'

private def mapToPrependSuccIndex {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (j : ℕ) (hj : j ≤ d'.toSequenceOfBlowups.length) :
    d'.toSequenceOfBlowups.schemeAt j ⟶ (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt (succIndex c.idx j) :=
  c.map j hj ≫ eqToHom (prepend_schemeAt_succ Z hZ d (c.idx j)).symm

/- English proof (translation)
Rewrite using `[succIndex_apply, prepend_length, c.idx_length]`.
-/
private theorem succIndex_length_eq_prepend_length {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) :
    succIndex c.idx d'.toSequenceOfBlowups.length = (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length := by
  rw [succIndex_apply, prepend_length, c.idx_length]

/- English proof (translation)
Establish `hlen : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length = d.toSequenceOfBlowups.length + 1` using `prepend_length Z hZ d`. Establish `hc : c.idx j < d.toSequenceOfBlowups.length` using `c.idx_lt j hj`. Rewrite using `[hlen, succIndex_apply]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem succIndex_lt_prepend_length {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (j : ℕ) (hj : j < d'.toSequenceOfBlowups.length) :
    succIndex c.idx j < (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length := by
  have hlen : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length = d.toSequenceOfBlowups.length + 1 :=
    prepend_length Z hZ d
  have hc : c.idx j < d.toSequenceOfBlowups.length := c.idx_lt j hj
  rw [hlen, succIndex_apply]
  omega

/- English proof (translation)
Establish `h : c.idx j < c.idx (j + 1)` using `c.idx_strictMono j hj`. Simplify using `only [succIndex_apply]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem succIndex_lt_succIndex_succ {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (_hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (j : ℕ) (hj : j < d'.toSequenceOfBlowups.length) :
    succIndex c.idx j < succIndex c.idx (j + 1) := by
  have h : c.idx j < c.idx (j + 1) := c.idx_strictMono j hj
  simp only [succIndex_apply]
  omega

/- English proof (translation)
Establish `h1 : mapToPrependSuccIndex c Z hZ j hj = c.map j hj` using `by show c.map j hj ≫ 𝟙 (d.toSequenceOfBlowups.schemeAt (c.idx j)) = c.map j hj`. Simplify using the standard rewrite rules. Establish `h2 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (succIndex c.idx j) = d.toSequenceOfBlowups.projectionToBase (c.idx j)` using `prepend_toSequenceOfBlowups_projectionToBase_succ Z hZ d (c.idx j)`. Rewrite using `[h1, h2]`. Conclude with `c.isPullback j hj`.
-/
private theorem isPullback_comparisonMapOfComapEqTop {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (j : ℕ) (hj : j ≤ d'.toSequenceOfBlowups.length) :
    IsPullback (mapToPrependSuccIndex c Z hZ j hj) (d'.toSequenceOfBlowups.projectionToBase j)
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (succIndex c.idx j)) φ := by
  have h1 : mapToPrependSuccIndex c Z hZ j hj = c.map j hj := by
    show c.map j hj ≫ 𝟙 (d.toSequenceOfBlowups.schemeAt (c.idx j)) = c.map j hj
    simp
  have h2 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (succIndex c.idx j) =
      d.toSequenceOfBlowups.projectionToBase (c.idx j) := prepend_toSequenceOfBlowups_projectionToBase_succ Z hZ d (c.idx j)
  rw [h1, h2]
  exact c.isPullback j hj

/- English proof (translation)
Rewrite using `[eqToHom_refl, Category.comp_id]`.
-/
private theorem comp_eqToHom_refl {A B : Scheme.{u}} (f : A ⟶ B) (h : B = B) :
    f ≫ eqToHom h = f := by
  rw [eqToHom_refl, Category.comp_id]

/- English proof (translation)
The claim follows from `comp_eqToHom_refl (c.map j hj) (prepend_schemeAt_succ Z hZ d (c.idx j)).symm`.
-/
private theorem comparisonMapOfComapEqTop_eq_map {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (j : ℕ) (hj : j ≤ d'.toSequenceOfBlowups.length) :
    mapToPrependSuccIndex c Z hZ j hj = c.map j hj :=
  comp_eqToHom_refl (c.map j hj) (prepend_schemeAt_succ Z hZ d (c.idx j)).symm

/- English proof (translation)
Establish `h1 : mapToPrependSuccIndex c Z hZ j (le_of_lt hj) = c.map j (le_of_lt hj)` using `comparisonMapOfComapEqTop_eq_map c Z hZ j (le_of_lt hj)`. Establish `h2 : mapToPrependSuccIndex c Z hZ (j + 1) hj = c.map (j + 1) hj` using `comparisonMapOfComapEqTop_eq_map c Z hZ (j + 1) hj`. Establish `hdown : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap (le_of_lt (succIndex_lt_succIndex_succ c Z hZ j hj)) = d.toSequenceOfBlowups.transitionMap (le_of_lt (c.idx_strictMono j hj))` using `prepend_transitionMap_succ_succ Z hZ d (le_of_lt (c.idx_strictMono j hj)) (le_of_lt (succIndex_lt_succIndex_succ c Z hZ j hj))`. Rewrite using `[h1, h2, hdown]`. Conclude with `c.step j hj`.
-/
private theorem blowupMorphism_comp_comparisonMapOfComapEqTop {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (j : ℕ) (hj : j < d'.toSequenceOfBlowups.length) :
    d'.toSequenceOfBlowups.transitionMapSucc j ≫ mapToPrependSuccIndex c Z hZ j (le_of_lt hj) =
      mapToPrependSuccIndex c Z hZ (j + 1) hj ≫
        (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap
          (le_of_lt (succIndex_lt_succIndex_succ c Z hZ j hj)) := by
  have h1 : mapToPrependSuccIndex c Z hZ j (le_of_lt hj) = c.map j (le_of_lt hj) :=
    comparisonMapOfComapEqTop_eq_map c Z hZ j (le_of_lt hj)
  have h2 : mapToPrependSuccIndex c Z hZ (j + 1) hj = c.map (j + 1) hj :=
    comparisonMapOfComapEqTop_eq_map c Z hZ (j + 1) hj
  have hdown : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap
        (le_of_lt (succIndex_lt_succIndex_succ c Z hZ j hj)) =
      d.toSequenceOfBlowups.transitionMap (le_of_lt (c.idx_strictMono j hj)) :=
    prepend_transitionMap_succ_succ Z hZ d (le_of_lt (c.idx_strictMono j hj))
      (le_of_lt (succIndex_lt_succIndex_succ c Z hZ j hj))
  rw [h1, h2, hdown]
  exact c.step j hj

/- English proof (translation)
Substitute `hB` using the available equality. Establish `h1 : J' = J` using `eq_of_heq hJ`. Substitute `h1` using the available equality. Rewrite using `[hK]`. Simplify using the standard rewrite rules.
-/
private theorem comap_eq_comap_comp_eqToHom_of_heq {A B B' : Scheme.{u}} (hB : B = B') (g : A ⟶ B)
    (J : B.IdealSheafData) (J' : B'.IdealSheafData) (K : A.IdealSheafData)
    (hK : K = J.comap g) (hJ : HEq J' J) :
    K = J'.comap (g ≫ eqToHom hB) := by
  subst hB
  have h1 : J' = J := eq_of_heq hJ
  subst h1
  rw [hK]
  simp

/- English proof (translation)
Establish `hc : d'.toSequenceOfBlowups.center j = (d.toSequenceOfBlowups.center (c.idx j)).comap (c.map j (le_of_lt hj))` using `c.center_comap j hj`. Establish `hJ : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (c.idx j + 1) = d.toSequenceOfBlowups.center (c.idx j)` using `(BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) (c.idx j + 1)).trans ((BlowupSequenceData.prepend_center_succ Z hZ d (c.idx j)).trans (BlowupSequenceData.toSequenceOfBlowups_center d (c.idx j)).symm)`. Use `show d'.toSequenceOfBlowups.center j = ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (c.idx j + 1)).comap (c.map j (le_of_lt hj) ≫ eqToHom (prepend_schemeAt_succ Z hZ d (c.idx j)).symm)`. Conclude with `comap_eq_comap_comp_eqToHom_of_heq (prepend_schemeAt_succ Z hZ d (c.idx j)).symm (c.map j (le_of_lt hj)) (d.toSequenceOfBlowups.center (c.idx j)) ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (c.idx j + 1)) (d'.toSequenceOfBlowups.center j) hc (heq_of_eq hJ)`.
-/
private theorem center_eq_comap_prepend_center_succIndex {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (j : ℕ) (hj : j < d'.toSequenceOfBlowups.length) :
    d'.toSequenceOfBlowups.center j =
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (succIndex c.idx j)).comap
        (mapToPrependSuccIndex c Z hZ j (le_of_lt hj)) := by
  have hc : d'.toSequenceOfBlowups.center j =
      (d.toSequenceOfBlowups.center (c.idx j)).comap (c.map j (le_of_lt hj)) := c.center_comap j hj
  have hJ : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (c.idx j + 1) =
      d.toSequenceOfBlowups.center (c.idx j) :=
    (BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) (c.idx j + 1)).trans
      ((BlowupSequenceData.prepend_center_succ Z hZ d (c.idx j)).trans
        (BlowupSequenceData.toSequenceOfBlowups_center d (c.idx j)).symm)
  show d'.toSequenceOfBlowups.center j =
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (c.idx j + 1)).comap
        (c.map j (le_of_lt hj) ≫ eqToHom (prepend_schemeAt_succ Z hZ d (c.idx j)).symm)
  exact comap_eq_comap_comp_eqToHom_of_heq (prepend_schemeAt_succ Z hZ d (c.idx j)).symm
    (c.map j (le_of_lt hj)) (d.toSequenceOfBlowups.center (c.idx j))
    ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (c.idx j + 1))
    (d'.toSequenceOfBlowups.center j) hc (heq_of_eq hJ)

/- English proof (translation)
The claim follows from `c.center_ne_top j hj`.
-/
private theorem center_ne_top_of_prepend_comap_eq_top {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (_Z : X.IdealSheafData)
    (_hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) _Z) (j : ℕ) (hj : j < d'.toSequenceOfBlowups.length) :
    d'.toSequenceOfBlowups.center j ≠ ⊤ := c.center_ne_top j hj

/- English proof (translation)
Establish `hlen : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length = d.toSequenceOfBlowups.length + 1` using `prepend_length Z hZ d`. Consider the cases of `i with`. Consider the case `zero`. Introduce `heq`. Establish `hc0 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center 0 = Z` using `(BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) 0).trans (BlowupSequenceData.prepend_center_zero Z hZ d)`.

Establish `hzZ : z ∈ Z.support`. Rewrite `hz` using `[hc0]`. Conclude with `hz`. Establish `hst : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase 0 = 𝟙 X` using `prepend_toSequenceOfBlowups_projectionToBase_zero Z hZ d`. Establish `hb : φ.base x' ∈ Z.support`.

Rewrite using `[heq, hst]`. Conclude with `hzZ`. Establish `hmem : x' ∈ (Z.comap φ).support` using `AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.mpr hb`. Conclude with `AlgebraicGeometry.Scheme.IdealSheafData.ne_top_of_mem_support (Z.comap φ) x' hmem htop`. Consider the case `succ n`.

Establish `hn : n < d.toSequenceOfBlowups.length` using `by omega`. Establish `hmiss' : ∀ m : ℕ, m < d'.toSequenceOfBlowups.length → c.idx m ≠ n`. Introduce `m hm hmn`. Conclude with `hmiss m hm (by rw [succIndex_apply, hmn])`. Establish `hzc : z ∈ (d.toSequenceOfBlowups.center n).support`.

Establish `hz2` using `hz`. Rewrite `hz2` using `[prepend_center_succ Z hZ d n]`. Conclude with `hz2`. Introduce `heq`. Use `c.omitted n hn hmiss' z hzc x' ?_` and prove the remaining obligations.

Rewrite using `[← prepend_toSequenceOfBlowups_projectionToBase_succ Z hZ d n]`. Conclude with `heq`.
-/
private theorem ne_projectionToBase_of_forall_succIndex_ne {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (htop : Z.comap φ = ⊤) (i : ℕ)
    (hi : i < (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length)
    (hmiss : ∀ j : ℕ, j < d'.toSequenceOfBlowups.length → succIndex c.idx j ≠ i)
    (z : ↥((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt i))
    (hz : z ∈ ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center i).support) (x' : ↥X') :
    φ.base x' ≠ ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase i).base z := by
  have hlen : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length = d.toSequenceOfBlowups.length + 1 :=
    prepend_length Z hZ d
  cases i with
  | zero =>
      intro heq
      have hc0 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center 0 = Z :=
        (BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) 0).trans
          (BlowupSequenceData.prepend_center_zero Z hZ d)
      have hzZ : z ∈ Z.support := by
        rw [hc0] at hz
        exact hz
      have hst : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase 0 = 𝟙 X :=
        prepend_toSequenceOfBlowups_projectionToBase_zero Z hZ d
      have hb : φ.base x' ∈ Z.support := by
        rw [heq, hst]
        exact hzZ
      have hmem : x' ∈ (Z.comap φ).support :=
        AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.mpr hb
      exact AlgebraicGeometry.Scheme.IdealSheafData.ne_top_of_mem_support
        (Z.comap φ) x' hmem htop
  | succ n =>
      have hn : n < d.toSequenceOfBlowups.length := by omega
      have hmiss' : ∀ m : ℕ, m < d'.toSequenceOfBlowups.length → c.idx m ≠ n := by
        intro m hm hmn
        exact hmiss m hm (by rw [succIndex_apply, hmn])
      have hzc : z ∈ (d.toSequenceOfBlowups.center n).support := by
        have hz2 := hz
        rw [prepend_center_succ Z hZ d n] at hz2
        exact hz2
      intro heq
      refine c.omitted n hn hmiss' z hzc x' ?_
      rw [← prepend_toSequenceOfBlowups_projectionToBase_succ Z hZ d n]
      exact heq

def prependOfComapEqTop {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (htop : Z.comap φ = ⊤) :
    SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups where
  idx := succIndex c.idx
  map := mapToPrependSuccIndex c Z hZ
  idx_length := succIndex_length_eq_prepend_length c Z hZ
  idx_lt := succIndex_lt_prepend_length c Z hZ
  idx_strictMono := succIndex_lt_succIndex_succ c Z hZ
  isPullback := isPullback_comparisonMapOfComapEqTop c Z hZ
  step := blowupMorphism_comp_comparisonMapOfComapEqTop c Z hZ
  center_comap := center_eq_comap_prepend_center_succIndex c Z hZ
  center_ne_top := center_ne_top_of_prepend_comap_eq_top c Z hZ
  omitted := ne_projectionToBase_of_forall_succIndex_ne c Z hZ htop

end SequenceOfBlowupsPullback

/- English proof (translation)
Take `⟨c⟩` from `h.nonempty_sequenceOfBlowupsPullback`. Conclude with `(c.prepend Z hZ hZ' hne).isPullbackSequenceOfBlowups`.
-/
theorem IsPullbackBlowupSequence.prepend_of_comap_ne_top {X X' : Scheme.{u}} {φ : X' ⟶ X} {d' : BlowupSequenceData X'}
    {d : BlowupSequenceData X} (h : IsPullbackBlowupSequence φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (hne : Z.comap φ ≠ ⊤) :
    IsPullbackBlowupSequence φ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups
      (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups := by
  obtain ⟨c⟩ := h.nonempty_sequenceOfBlowupsPullback
  exact (c.prepend Z hZ hZ' hne).isPullbackSequenceOfBlowups

/- English proof (translation)
Take `⟨c⟩` from `h.nonempty_sequenceOfBlowupsPullback`. Conclude with `(c.prependOfComapEqTop Z hZ htop).isPullbackSequenceOfBlowups`.
-/
theorem IsPullbackBlowupSequence.prepend_of_comap_eq_top {X X' : Scheme.{u}} {φ : X' ⟶ X} {d' : BlowupSequenceData X'}
    {d : BlowupSequenceData X} (h : IsPullbackBlowupSequence φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (htop : Z.comap φ = ⊤) :
    IsPullbackBlowupSequence φ d'.toSequenceOfBlowups (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups := by
  obtain ⟨c⟩ := h.nonempty_sequenceOfBlowupsPullback
  exact (c.prependOfComapEqTop Z hZ htop).isPullbackSequenceOfBlowups

private def prependMapOfLevelwise {X X' : Scheme.{u}} (φ : X' ⟶ X) {d' : BlowupSequenceData X'}
    {d : BlowupSequenceData X} (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z)
    (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ))
    (σ : ∀ i : ℕ, i ≤ d'.toSequenceOfBlowups.length → (d'.toSequenceOfBlowups.schemeAt i ⟶ d.toSequenceOfBlowups.schemeAt i)) :
    ∀ i : ℕ, i ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length →
      ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.schemeAt i ⟶
        (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt i)
  | 0, _ =>
      eqToHom (SequenceOfBlowupsPullback.prepend_schemeAt_zero (Z.comap φ) hZ' d') ≫ φ ≫
        eqToHom (SequenceOfBlowupsPullback.prepend_schemeAt_zero Z hZ d).symm
  | (n + 1), h =>
      eqToHom (SequenceOfBlowupsPullback.prepend_schemeAt_succ (Z.comap φ) hZ' d' n) ≫
        σ n (SequenceOfBlowupsPullback.le_length_of_succ_le_prepend_length (Z.comap φ) hZ' d' n h) ≫
        eqToHom (SequenceOfBlowupsPullback.prepend_schemeAt_succ Z hZ d n).symm

/- English proof (translation)
Use `show 𝟙 X' ≫ φ ≫ 𝟙 X = φ`. Simplify using the standard rewrite rules.
-/
private theorem strictPrependComparisonMap_zero {X X' : Scheme.{u}} (φ : X' ⟶ X) {d' : BlowupSequenceData X'}
    {d : BlowupSequenceData X} (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z)
    (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ))
    (σ : ∀ i : ℕ, i ≤ d'.toSequenceOfBlowups.length → (d'.toSequenceOfBlowups.schemeAt i ⟶ d.toSequenceOfBlowups.schemeAt i))
    (h : 0 ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    prependMapOfLevelwise φ Z hZ hZ' σ 0 h = φ := by
  show 𝟙 X' ≫ φ ≫ 𝟙 X = φ
  simp

/- English proof (translation)
Use `show 𝟙 (d'.toSequenceOfBlowups.schemeAt n) ≫ σ n hn ≫ 𝟙 (d.toSequenceOfBlowups.schemeAt n) = σ n hn`. Simplify using the standard rewrite rules.
-/
private theorem strictPrependComparisonMap_succ {X X' : Scheme.{u}} (φ : X' ⟶ X) {d' : BlowupSequenceData X'}
    {d : BlowupSequenceData X} (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z)
    (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ))
    (σ : ∀ i : ℕ, i ≤ d'.toSequenceOfBlowups.length → (d'.toSequenceOfBlowups.schemeAt i ⟶ d.toSequenceOfBlowups.schemeAt i)) (n : ℕ)
    (h : n + 1 ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length)
    (hn : n ≤ d'.toSequenceOfBlowups.length) :
    prependMapOfLevelwise φ Z hZ hZ' σ (n + 1) h = σ n hn := by
  show 𝟙 (d'.toSequenceOfBlowups.schemeAt n) ≫ σ n hn ≫ 𝟙 (d.toSequenceOfBlowups.schemeAt n) = σ n hn
  simp

/- English proof (translation)
Rewrite using `[BlowupSequenceData.toSequenceOfBlowups_isoObjZero, BlowupSequenceData.prepend_isoObjZero, Iso.refl_hom]`.
-/
private theorem prepend_isoObjZero_hom {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.isoZero.hom = 𝟙 Y := by
  rw [BlowupSequenceData.toSequenceOfBlowups_isoObjZero, BlowupSequenceData.prepend_isoObjZero, Iso.refl_hom]

/- English proof (translation)
Substitute `eP` using the available equality. Substitute `eQ` using the available equality. Establish `h1` using `eq_of_heq hI`. Establish `h2` using `eq_of_heq hJ`. Rewrite using `[h1, h2]`.

Simplify using the standard rewrite rules.
-/
private theorem eqToHom_conj_comp_eq_comp_of_heq_id {A B P Q : Scheme.{u}} (eP : P = A) (eQ : Q = B)
    (ψ : A ⟶ B) (I : Q ⟶ B) (J : P ⟶ A) (hI : HEq I (𝟙 B)) (hJ : HEq J (𝟙 A)) :
    (eqToHom eP ≫ ψ ≫ eqToHom eQ.symm) ≫ I = J ≫ ψ := by
  subst eP
  subst eQ
  have h1 := eq_of_heq hI
  have h2 := eq_of_heq hJ
  rw [h1, h2]
  simp

/- English proof (translation)
Rewrite using `[BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.prepend_blowupMorphism_zero, BlowupSequenceData.toSequenceOfBlowups_isoObjZero]`.
-/
private theorem prepend_blowupMorphism_zero {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMapSucc 0 = d.toSequenceOfBlowups.isoZero.hom := by
  rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.prepend_blowupMorphism_zero, BlowupSequenceData.toSequenceOfBlowups_isoObjZero]

/- English proof (translation)
The claim follows from `(BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) 0).trans (BlowupSequenceData.prepend_center_zero Z hZ d)`.
-/
private theorem prepend_center_zero {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center 0 = Z :=
  (BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) 0).trans
    (BlowupSequenceData.prepend_center_zero Z hZ d)

/- English proof (translation)
Rewrite using `[hf, hg, hh, hk]`. Conclude with `H`.
-/
private theorem isPullback_congr {P Q R S : Scheme.{u}} {f f' : P ⟶ Q} {g g' : P ⟶ R}
    {h h' : Q ⟶ S} {k k' : R ⟶ S} (hf : f = f') (hg : g = g') (hh : h = h') (hk : k = k')
    (H : IsPullback f' g' h' k') : IsPullback f g h k := by
  rw [hf, hg, hh, hk]
  exact H

/- English proof (translation)
Take `⟨hlen, σ, h0, hpb, hcen⟩` from `h`. Use `⟨?_, prependMapOfLevelwise φ Z hZ hZ' σ, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SequenceOfBlowupsPullback.prepend_length (Z.comap φ) hZ' d', SequenceOfBlowupsPullback.prepend_length Z hZ d, hlen]`. Conclude with `eqToHom_conj_comp_eq_comp_of_heq_id (SequenceOfBlowupsPullback.prepend_schemeAt_zero (Z.comap φ) hZ' d') (SequenceOfBlowupsPullback.prepend_schemeAt_zero Z hZ d) φ ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.isoZero.hom) ((BlowupSequenceData.prepend (Z.comap φ) hZ' d …`. Introduce `i hi`.

Consider the cases of `i with`. Consider the case `zero`. Establish `hz : (0 : ℕ) ≤ d'.toSequenceOfBlowups.length` using `Nat.zero_le _`. Establish `hsq : IsPullback (σ 0 hz) d'.toSequenceOfBlowups.isoZero.hom d.toSequenceOfBlowups.isoZero.hom φ` using `(IsPullback.of_horiz_isIso ⟨h0.symm⟩).flip`. Conclude with `isPullback_congr (strictPrependComparisonMap_succ φ Z hZ hZ' σ 0 hi hz) (prepend_blowupMorphism_zero (Z.comap φ) hZ' d') (prepend_blowupMorphism_zero Z hZ d) (strictPrependComparisonMap_zero φ Z hZ hZ' σ hi.le) hsq`.

Consider the case `succ n`. Establish `hlen' : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length = d'.toSequenceOfBlowups.length + 1` using `SequenceOfBlowupsPullback.prepend_length (Z.comap φ) hZ' d'`. Establish `hn : n < d'.toSequenceOfBlowups.length` using `by omega`. Conclude with `isPullback_congr (strictPrependComparisonMap_succ φ Z hZ hZ' σ (n + 1) hi hn) (SequenceOfBlowupsPullback.prepend_blowupMorphism_succ (Z.comap φ) hZ' d' n) (SequenceOfBlowupsPullback.prepend_blowupMorphism_succ Z hZ d n) (strictPrependComparisonMap_succ φ Z hZ hZ' σ n hi.le hn.le) …`. Introduce `i hi`.

Consider the cases of `i with`. Consider the case `zero`. Conclude with `SequenceOfBlowupsPullback.comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq (SequenceOfBlowupsPullback.prepend_schemeAt_zero (Z.comap φ) hZ' d') (SequenceOfBlowupsPullback.prepend_schemeAt_zero Z hZ d).symm φ Z (Z.comap φ) rfl ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequ …`. Consider the case `succ n`. Establish `hlen' : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length = d'.toSequenceOfBlowups.length + 1` using `SequenceOfBlowupsPullback.prepend_length (Z.comap φ) hZ' d'`.

Establish `hn : n < d'.toSequenceOfBlowups.length` using `by omega`. Conclude with `SequenceOfBlowupsPullback.comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq (SequenceOfBlowupsPullback.prepend_schemeAt_succ (Z.comap φ) hZ' d' n) (SequenceOfBlowupsPullback.prepend_schemeAt_succ Z hZ d n).symm (σ n hn.le) (d.toSequenceOfBlowups.center n) (d'.toSequenceOfBlowups.ce …`.
-/
theorem IsStrictPullbackBlowupSeq.prepend {X X' : Scheme.{u}} {φ : X' ⟶ X} {d' : BlowupSequenceData X'}
    {d : BlowupSequenceData X} (h : IsStrictPullbackBlowupSeq φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) :
    IsStrictPullbackBlowupSeq φ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups
      (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups := by
  obtain ⟨hlen, σ, h0, hpb, hcen⟩ := h
  refine ⟨?_, prependMapOfLevelwise φ Z hZ hZ' σ, ?_, ?_, ?_⟩
  · rw [SequenceOfBlowupsPullback.prepend_length (Z.comap φ) hZ' d',
      SequenceOfBlowupsPullback.prepend_length Z hZ d, hlen]
  · exact eqToHom_conj_comp_eq_comp_of_heq_id
      (SequenceOfBlowupsPullback.prepend_schemeAt_zero (Z.comap φ) hZ' d')
      (SequenceOfBlowupsPullback.prepend_schemeAt_zero Z hZ d) φ
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.isoZero.hom)
      ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.isoZero.hom)
      (heq_of_eq (prepend_isoObjZero_hom Z hZ d))
      (heq_of_eq (prepend_isoObjZero_hom (Z.comap φ) hZ' d'))
  · intro i hi
    cases i with
    | zero =>
        have hz : (0 : ℕ) ≤ d'.toSequenceOfBlowups.length := Nat.zero_le _
        have hsq : IsPullback (σ 0 hz) d'.toSequenceOfBlowups.isoZero.hom d.toSequenceOfBlowups.isoZero.hom φ :=
          (IsPullback.of_horiz_isIso ⟨h0.symm⟩).flip
        exact isPullback_congr (strictPrependComparisonMap_succ φ Z hZ hZ' σ 0 hi hz)
          (prepend_blowupMorphism_zero (Z.comap φ) hZ' d') (prepend_blowupMorphism_zero Z hZ d)
          (strictPrependComparisonMap_zero φ Z hZ hZ' σ hi.le) hsq
    | succ n =>
        have hlen' : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length
            = d'.toSequenceOfBlowups.length + 1 := SequenceOfBlowupsPullback.prepend_length (Z.comap φ) hZ' d'
        have hn : n < d'.toSequenceOfBlowups.length := by omega
        exact isPullback_congr (strictPrependComparisonMap_succ φ Z hZ hZ' σ (n + 1) hi hn)
          (SequenceOfBlowupsPullback.prepend_blowupMorphism_succ (Z.comap φ) hZ' d' n)
          (SequenceOfBlowupsPullback.prepend_blowupMorphism_succ Z hZ d n)
          (strictPrependComparisonMap_succ φ Z hZ hZ' σ n hi.le hn.le) (hpb n hn)
  · intro i hi
    cases i with
    | zero =>
        exact SequenceOfBlowupsPullback.comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq
          (SequenceOfBlowupsPullback.prepend_schemeAt_zero (Z.comap φ) hZ' d')
          (SequenceOfBlowupsPullback.prepend_schemeAt_zero Z hZ d).symm φ Z (Z.comap φ) rfl
          ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center 0)
          ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center 0)
          (heq_of_eq (prepend_center_zero Z hZ d))
          (heq_of_eq (prepend_center_zero (Z.comap φ) hZ' d'))
    | succ n =>
        have hlen' : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length
            = d'.toSequenceOfBlowups.length + 1 := SequenceOfBlowupsPullback.prepend_length (Z.comap φ) hZ' d'
        have hn : n < d'.toSequenceOfBlowups.length := by omega
        exact SequenceOfBlowupsPullback.comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq
          (SequenceOfBlowupsPullback.prepend_schemeAt_succ (Z.comap φ) hZ' d' n)
          (SequenceOfBlowupsPullback.prepend_schemeAt_succ Z hZ d n).symm (σ n hn.le)
          (d.toSequenceOfBlowups.center n) (d'.toSequenceOfBlowups.center n) (hcen n hn)
          ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center (n + 1))
          ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (n + 1))
          (heq_of_eq (SequenceOfBlowupsPullback.prepend_center_succ Z hZ d n))
          (heq_of_eq (SequenceOfBlowupsPullback.prepend_center_succ (Z.comap φ) hZ' d' n))

end FunctorialResolution.EmbeddedResolution

end
