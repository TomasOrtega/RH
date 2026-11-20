import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.SmoothDivisorOperations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace TransportedDivisor

def iteratedComap {X : Scheme.{u}} (d : BlowupSequenceData X) (B : (d.obj 0).IdealSheafData) (t : ℕ) :
    (d.obj t).IdealSheafData :=
  Nat.rec (motive := fun n => (d.obj n).IdealSheafData) B
    (fun n ih => ih.comap (d.map n)) t

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem iteratedComap_zero {X : Scheme.{u}} (d : BlowupSequenceData X) (B : (d.obj 0).IdealSheafData) :
    iteratedComap d B 0 = B := rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iteratedComap_succ {X : Scheme.{u}} (d : BlowupSequenceData X) (B : (d.obj 0).IdealSheafData)
    (t : ℕ) : iteratedComap d B (t + 1) = (iteratedComap d B t).comap (d.map t) := rfl

/- English proof (translation)
Establish `hpre : (((D.comap π).support : Closeds Y') : Set Y') = ⇑π.base ⁻¹' (D.support : Set Y)`. Rewrite using `[Scheme.IdealSheafData.support_comap]`. Both sides reduce to the same expression. Establish `hclosed : IsClosed (((D.comap π).support : Closeds Y') : Set Y')` using `(D.comap π).support.2`. Rewrite using `[support_strictTransform_eq_closure_sdiff π Z D, ← hpre]`.

Conclude with `closure_minimal Set.sdiff_subset hclosed`.
-/
theorem support_strictTransform_subset_preimage {Y Y' : Scheme.{u}} [IsLocallyNoetherian Y']
    (π : Y' ⟶ Y) (Z D : Y.IdealSheafData) :
    ((Blowup.strictTransform π Z D).support : Set Y') ⊆ ⇑π.base ⁻¹' (D.support : Set Y) := by
  have hpre : (((D.comap π).support : Closeds Y') : Set Y') =
      ⇑π.base ⁻¹' (D.support : Set Y) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hclosed : IsClosed (((D.comap π).support : Closeds Y') : Set Y') :=
    (D.comap π).support.2
  rw [support_strictTransform_eq_closure_sdiff π Z D, ← hpre]
  exact closure_minimal Set.sdiff_subset hclosed

/- English proof (translation)
Introduce `t`. Proceed by induction on `t with`. Consider the case `zero`. Introduce `_`. Conclude with `hB₀`.

Consider the case `succ n ih`. Introduce `hn`. Establish `hlt : n < L` using `Nat.lt_of_succ_le hn`. Establish `hle : n ≤ L` using `le_of_lt hlt`. Establish `hs1 : AlgebraicGeometry.Smooth (BlowupSequenceData.projectionToBase d n ≫ p)` using `hsm n hle`.

Establish `heq : BlowupSequenceData.projectionToBase d (n + 1) ≫ p = d.map n ≫ BlowupSequenceData.projectionToBase d n ≫ p`. Rewrite using `[BlowupSequenceData.projectionToBase_succ, Category.assoc]`. Establish `hs2 : AlgebraicGeometry.Smooth (d.map n ≫ BlowupSequenceData.projectionToBase d n ≫ p)`. Rewrite using `[← heq]`. Conclude with `hsm (n + 1) hn`.

Establish `hblow : Blowup.IsBlowupAlongIdealSheaf (d.map n) (d.center n)` using `d.isBlowup n (lt_of_lt_of_le hlt hL)`. Establish `key` using `isSmoothDivisor_comap_of_isBlowupAlongIdealSheaf (BlowupSequenceData.projectionToBase d n ≫ p) (d.map n) (d.center n) (iteratedComap d B₀ n) hblow (ih hle) (hcent n hlt)`. Rewrite using `[iteratedComap_succ, heq]`. Conclude with `key`.
-/
theorem isSmoothDivisor_iteratedComap {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (d : BlowupSequenceData X) (L : ℕ) (hL : L ≤ d.length)
    (hsm : ∀ t, t ≤ L → AlgebraicGeometry.Smooth (BlowupSequenceData.projectionToBase d t ≫ p))
    (B₀ : (d.obj 0).IdealSheafData)
    (hB₀ : IsSmoothDivisor (BlowupSequenceData.projectionToBase d 0 ≫ p) B₀)
    (hcent : ∀ t, t < L →
      Disjoint (((d.center t).support : Set (d.obj t)))
        ((iteratedComap d B₀ t).support : Set (d.obj t))) :
    ∀ t, t ≤ L → IsSmoothDivisor (BlowupSequenceData.projectionToBase d t ≫ p) (iteratedComap d B₀ t) := by
  intro t
  induction t with
  | zero =>
    intro _
    exact hB₀
  | succ n ih =>
    intro hn
    have hlt : n < L := Nat.lt_of_succ_le hn
    have hle : n ≤ L := le_of_lt hlt
    have hs1 : AlgebraicGeometry.Smooth (BlowupSequenceData.projectionToBase d n ≫ p) := hsm n hle
    have heq : BlowupSequenceData.projectionToBase d (n + 1) ≫ p = d.map n ≫ BlowupSequenceData.projectionToBase d n ≫ p := by
      rw [BlowupSequenceData.projectionToBase_succ, Category.assoc]
    have hs2 : AlgebraicGeometry.Smooth (d.map n ≫ BlowupSequenceData.projectionToBase d n ≫ p) := by
      rw [← heq]
      exact hsm (n + 1) hn
    have hblow : Blowup.IsBlowupAlongIdealSheaf (d.map n) (d.center n) := d.isBlowup n (lt_of_lt_of_le hlt hL)
    have key := isSmoothDivisor_comap_of_isBlowupAlongIdealSheaf (BlowupSequenceData.projectionToBase d n ≫ p) (d.map n)
      (d.center n) (iteratedComap d B₀ n) hblow (ih hle) (hcent n hlt)
    rw [iteratedComap_succ, heq]
    exact key

/- English proof (translation)
Introduce `t`. Proceed by induction on `t with`. Consider the case `zero`. Introduce `_`. Conclude with `⟨hK0, hdisj0⟩`.

Consider the case `succ n ih`. Introduce `hn`. Establish `hlt : n < L` using `Nat.lt_of_succ_le hn`. Establish `hle : n ≤ L` using `le_of_lt hlt`. Take `⟨hKn, hdn⟩` from `ih hle`.

Establish `hnoe : IsLocallyNoetherian (d.obj (n + 1))` using `hnoeth (n + 1) hn`. Establish `hmul : K (n + 1) = A (n + 1) * iteratedComap d B₀ (n + 1)`. Rewrite using `[hKsucc n hlt, hKn, strictTransform_mul_of_disjoint_support (d.map n) (d.center n) (A n) (iteratedComap d B₀ n) (hcent n hlt).symm, hAsucc n hlt, iteratedComap_succ]`. Use `⟨hmul, ?_⟩` and prove the remaining obligations. Establish `hsub : ((A (n + 1)).support : Set (d.obj (n + 1))) ⊆ ⇑(d.map n).base ⁻¹' ((A n).support : Set (d.obj n))`.

Rewrite using `[hAsucc n hlt]`. Conclude with `support_strictTransform_subset_preimage (d.map n) (d.center n) (A n)`. Establish `hpre : ((((iteratedComap d B₀ n).comap (d.map n)).support : Closeds (d.obj (n + 1))) : Set (d.obj (n + 1))) = ⇑(d.map n).base ⁻¹' ((iteratedComap d B₀ n).support : Set (d.obj n))`. Rewrite using `[Scheme.IdealSheafData.support_comap]`. Both sides reduce to the same expression.

Rewrite using `[iteratedComap_succ, hpre]`. Rewrite `hdn`, the goal using `[Set.disjoint_left]`. Introduce `x hx hx'`. Conclude with `hdn (hsub hx) hx'`.
-/
theorem strictTransform_eq_mul_iteratedComap {X : Scheme.{u}} (d : BlowupSequenceData X) (L : ℕ)
    (hnoeth : ∀ t, t ≤ L → IsLocallyNoetherian (d.obj t))
    (K A : ∀ t : ℕ, (d.obj t).IdealSheafData) (B₀ : (d.obj 0).IdealSheafData)
    (hK0 : K 0 = A 0 * B₀)
    (hdisj0 : Disjoint ((A 0).support : Set (d.obj 0)) ((B₀).support : Set (d.obj 0)))
    (hKsucc : ∀ t, t < L → K (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (K t))
    (hAsucc : ∀ t, t < L → A (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (A t))
    (hcent : ∀ t, t < L →
      Disjoint (((d.center t).support : Set (d.obj t)))
        ((iteratedComap d B₀ t).support : Set (d.obj t))) :
    ∀ t, t ≤ L →
      K t = A t * iteratedComap d B₀ t ∧
        Disjoint ((A t).support : Set (d.obj t))
          ((iteratedComap d B₀ t).support : Set (d.obj t)) := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨hK0, hdisj0⟩
  | succ n ih =>
    intro hn
    have hlt : n < L := Nat.lt_of_succ_le hn
    have hle : n ≤ L := le_of_lt hlt
    obtain ⟨hKn, hdn⟩ := ih hle
    have hnoe : IsLocallyNoetherian (d.obj (n + 1)) := hnoeth (n + 1) hn
    have hmul : K (n + 1) = A (n + 1) * iteratedComap d B₀ (n + 1) := by
      rw [hKsucc n hlt, hKn, strictTransform_mul_of_disjoint_support (d.map n) (d.center n)
        (A n) (iteratedComap d B₀ n) (hcent n hlt).symm, hAsucc n hlt, iteratedComap_succ]
    refine ⟨hmul, ?_⟩
    have hsub : ((A (n + 1)).support : Set (d.obj (n + 1))) ⊆
        ⇑(d.map n).base ⁻¹' ((A n).support : Set (d.obj n)) := by
      rw [hAsucc n hlt]
      exact support_strictTransform_subset_preimage (d.map n) (d.center n) (A n)
    have hpre : ((((iteratedComap d B₀ n).comap (d.map n)).support : Closeds (d.obj (n + 1))) :
          Set (d.obj (n + 1))) =
        ⇑(d.map n).base ⁻¹' ((iteratedComap d B₀ n).support : Set (d.obj n)) := by
      rw [Scheme.IdealSheafData.support_comap]; rfl
    rw [iteratedComap_succ, hpre]
    rw [Set.disjoint_left] at hdn ⊢
    intro x hx hx'
    exact hdn (hsub hx) hx'

/- English proof (translation)
Introduce `t ht`. Establish `hst : AlgebraicGeometry.Smooth (BlowupSequenceData.projectionToBase d t ≫ p)` using `hsm t ht`. Establish `hfac` using `strictTransform_eq_mul_iteratedComap d L hnoeth K A B₀ hK0 hdisj0 hKsucc hAsucc hcent t ht`. Establish `hB` using `isSmoothDivisor_iteratedComap p d L hL hsm B₀ hB₀ hcent t ht`. Rewrite using `[hfac.1]`.

Conclude with `isSmoothDivisor_mul_of_disjoint_support (BlowupSequenceData.projectionToBase d t ≫ p) (A t) (iteratedComap d B₀ t) (hA t ht) hB hfac.2`.
-/
theorem isSmoothDivisor_strictTransform_of_disjoint_center {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (d : BlowupSequenceData X) (L : ℕ) (hL : L ≤ d.length)
    (hnoeth : ∀ t, t ≤ L → IsLocallyNoetherian (d.obj t))
    (hsm : ∀ t, t ≤ L → AlgebraicGeometry.Smooth (BlowupSequenceData.projectionToBase d t ≫ p))
    (K A : ∀ t : ℕ, (d.obj t).IdealSheafData) (B₀ : (d.obj 0).IdealSheafData)
    (hK0 : K 0 = A 0 * B₀)
    (hdisj0 : Disjoint ((A 0).support : Set (d.obj 0)) ((B₀).support : Set (d.obj 0)))
    (hKsucc : ∀ t, t < L → K (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (K t))
    (hAsucc : ∀ t, t < L → A (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (A t))
    (hB₀ : IsSmoothDivisor (BlowupSequenceData.projectionToBase d 0 ≫ p) B₀)
    (hA : ∀ t, t ≤ L → IsSmoothDivisor (BlowupSequenceData.projectionToBase d t ≫ p) (A t))
    (hcent : ∀ t, t < L →
      Disjoint (((d.center t).support : Set (d.obj t)))
        ((iteratedComap d B₀ t).support : Set (d.obj t))) :
    ∀ t, t ≤ L → IsSmoothDivisor (BlowupSequenceData.projectionToBase d t ≫ p) (K t) := by
  intro t ht
  have hst : AlgebraicGeometry.Smooth (BlowupSequenceData.projectionToBase d t ≫ p) := hsm t ht
  have hfac := strictTransform_eq_mul_iteratedComap d L hnoeth K A B₀ hK0 hdisj0 hKsucc hAsucc hcent t ht
  have hB := isSmoothDivisor_iteratedComap p d L hL hsm B₀ hB₀ hcent t ht
  rw [hfac.1]
  exact isSmoothDivisor_mul_of_disjoint_support (BlowupSequenceData.projectionToBase d t ≫ p) (A t)
    (iteratedComap d B₀ t) (hA t ht) hB hfac.2

end TransportedDivisor

end FunctorialResolution.EmbeddedResolution

end
