import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def withBotSuccToNat : WithBot ℕ∞ → ℕ
  | ⊥ => 0
  | (n : ℕ∞) => n.toNat + 1

/- English proof (authored)
The successor conversion assigns zero to the bottom element.
-/
theorem withBotSuccToNat_bot : withBotSuccToNat ⊥ = 0 := rfl

/- English proof (authored)
On an extended natural number viewed in the larger ordered set, the conversion takes its natural-number value and adds one.
-/
theorem withBotSuccToNat_coe (n : ℕ∞) : withBotSuccToNat (n : WithBot ℕ∞) = n.toNat + 1 := rfl

def krullDimSucc (X : Scheme.{u}) : ℕ := withBotSuccToNat (topologicalKrullDim ↥X)

/- English proof (authored)
The dimension index is defined by applying the successor conversion to the topological Krull dimension of the underlying space.
-/
theorem krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim (X : Scheme.{u}) : krullDimSucc X = withBotSuccToNat (topologicalKrullDim ↥X) := rfl

/- English proof (authored)
If the first dimension is bottom, its successor index is zero. Otherwise both dimensions are non-bottom because the first is at most the second. The upper dimension is below top, so both are embedded finite natural numbers. Their natural-number values have the same order, and adding one to both preserves the inequality.
-/
theorem krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le (X Y : Scheme.{u})
    (h : topologicalKrullDim ↥X ≤ topologicalKrullDim ↥Y)
    (hY : topologicalKrullDim ↥Y < ⊤) :
    krullDimSucc X ≤ krullDimSucc Y := by
  rcases eq_or_ne (topologicalKrullDim ↥X) ⊥ with hX | hX
  · simp [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, hX, withBotSuccToNat_bot]
  · obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hX
    have hYne : topologicalKrullDim ↥Y ≠ ⊥ := by
      intro hb0
      rw [hb0, le_bot_iff] at h
      exact hX h
    obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hYne
    have hab : a ≤ b := by
      rw [← ha, ← hb] at h
      exact_mod_cast h
    have hbtop : b ≠ ⊤ := by
      intro hbt
      rw [← hb, hbt] at hY
      exact lt_irrefl _ hY
    have hatop : a ≠ ⊤ := by
      intro hat
      rw [hat, top_le_iff] at hab
      exact hbtop hab
    have hle : a.toNat ≤ b.toNat := by
      lift a to ℕ using hatop
      lift b to ℕ using hbtop
      simpa using hab
    rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim X, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim Y, ← ha, ← hb, withBotSuccToNat_coe, withBotSuccToNat_coe]
    omega

structure MarkedIdealWithBoundary : Type (u + 1) where
  base : Type u
  [instField : Field base]
  scheme : Scheme.{u}
  structMap : scheme ⟶ Spec (CommRingCat.of base)
  ideal : scheme.IdealSheafData
  mult : ℕ
  boundary : List scheme.IdealSheafData

attribute [instance] MarkedIdealWithBoundary.instField

/- English proof (authored)
The two marked ideals already have the same field, ambient and marking. Substituting the equal structure maps, ideals and boundaries makes every component agree, so the data are equal.
-/
theorem MarkedIdealWithBoundary.mk_eq_mk {k : Type u} [instk : Field k] (X : Scheme.{u}) (m : ℕ)
    {p p' : X ⟶ Spec (CommRingCat.of k)} {I I' : X.IdealSheafData}
    {E E' : List X.IdealSheafData} (hp : p = p') (hI : I = I') (hE : E = E') :
    @MarkedIdealWithBoundary.mk k instk X p I m E = @MarkedIdealWithBoundary.mk k instk X p' I' m E' := by
  subst hp
  subst hI
  subst hE
  rfl

abbrev MarkedIdealWithBoundary.krullDimSucc (T : MarkedIdealWithBoundary.{u}) : ℕ := EmbeddedResolution.krullDimSucc T.scheme

/- English proof (authored)
The dimension index of the marked ideal is defined to be the dimension index of its ambient scheme.
-/
theorem MarkedIdealWithBoundary.krullDimSucc_eq_krullDimSucc_scheme (T : MarkedIdealWithBoundary.{u}) : T.krullDimSucc = EmbeddedResolution.krullDimSucc T.scheme := rfl

structure MarkedIdealWithBoundary.IsAdmissible (T : MarkedIdealWithBoundary.{u}) : Prop where
  charZero : CharZero T.base
  locallyOfFiniteType : AlgebraicGeometry.LocallyOfFiniteType T.structMap
  nonzeroOnComponents : NonzeroOnComponents T.ideal
  one_le_mult : 1 ≤ T.mult
  quasiCompact : AlgebraicGeometry.QuasiCompact T.structMap
  smooth : AlgebraicGeometry.Smooth T.structMap
  snc : InStrictNormalCrossingPosition T.structMap T.boundary

structure MarkedSequenceOfBlowups {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) extends SequenceOfBlowups X where
  ideal : ∀ i : ℕ, (toSequenceOfBlowups.schemeAt i).IdealSheafData
  boundary : ∀ i : ℕ, List (toSequenceOfBlowups.schemeAt i).IdealSheafData
  ideal_zero : ideal 0 = I.comap toSequenceOfBlowups.isoZero.hom
  boundary_zero : boundary 0 = E.map (fun D => D.comap toSequenceOfBlowups.isoZero.hom)
  center_smooth : ∀ i, i < toSequenceOfBlowups.length →
    AlgebraicGeometry.Smooth
      ((toSequenceOfBlowups.center i).subschemeι ≫ toSequenceOfBlowups.projectionToBase i ≫ p)
  center_snc : ∀ i, i < toSequenceOfBlowups.length →
    HasStrictNormalCrossingsWith (toSequenceOfBlowups.projectionToBase i ≫ p) (toSequenceOfBlowups.center i) (boundary i)
  center_order : ∀ i, i < toSequenceOfBlowups.length →
    ((toSequenceOfBlowups.center i).support : Set ↥(toSequenceOfBlowups.schemeAt i)) ⊆ orderAtLeastLocus (ideal i) m
  ideal_succ : ∀ i, i < toSequenceOfBlowups.length →
    Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i) ^ m * ideal (i + 1) =
      (ideal i).comap (toSequenceOfBlowups.transitionMapSucc i)
  boundary_succ : ∀ i, i < toSequenceOfBlowups.length →
    boundary (i + 1) =
      (boundary i).map (Blowup.strictTransform (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)) ++
        [Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)]

namespace MarkedSequenceOfBlowups

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def projectionToSpec (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    s.toSequenceOfBlowups.schemeAt i ⟶ Spec (CommRingCat.of k) :=
  s.toSequenceOfBlowups.projectionToBase i ≫ p

/- English proof (authored)
The projection from the stage to the field is defined by composing its projection to the base with the original structural map.
-/
theorem projectionToSpec_eq (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    s.projectionToSpec i = s.toSequenceOfBlowups.projectionToBase i ≫ p := rfl

def exceptionalDivisor (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (s.toSequenceOfBlowups.schemeAt (i + 1)).IdealSheafData :=
  Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)

/- English proof (authored)
The exceptional ideal of the stage is the center ideal pulled back along that stage's blowup transition.
-/
theorem exceptionalDivisor_eq (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    s.exceptionalDivisor i = (s.toSequenceOfBlowups.center i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := rfl

def lastIdeal (s : MarkedSequenceOfBlowups p I m E) :
    (s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length).IdealSheafData :=
  s.ideal s.toSequenceOfBlowups.length

/- English proof (authored)
The last ideal is the ideal at the index given by the sequence's length.
-/
theorem lastIdeal_eq (s : MarkedSequenceOfBlowups p I m E) :
    s.lastIdeal = s.ideal s.toSequenceOfBlowups.length := rfl

def lastBoundary (s : MarkedSequenceOfBlowups p I m E) :
    List (s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length).IdealSheafData :=
  s.boundary s.toSequenceOfBlowups.length

/- English proof (authored)
The last boundary is the boundary list at the final index, which is the length of the underlying sequence.
-/
theorem lastBoundary_eq (s : MarkedSequenceOfBlowups p I m E) :
    s.lastBoundary = s.boundary s.toSequenceOfBlowups.length := rfl

def IsResolution (s : MarkedSequenceOfBlowups p I m E) : Prop :=
  orderAtLeastLocus s.lastIdeal m = ∅

/- English proof (authored)
The sequence is a resolution precisely when the final ideal's locus of order at least the marking is empty. This is its defining resolution condition.
-/
theorem isResolution_iff (s : MarkedSequenceOfBlowups p I m E) :
    s.IsResolution ↔ orderAtLeastLocus s.lastIdeal m = ∅ := Iff.rfl

end MarkedSequenceOfBlowups

def emptySequenceOfBlowups (X : Scheme.{u}) : SequenceOfBlowups X where
  length := 0
  tower := (CategoryTheory.Functor.const ℕᵒᵖ).obj X
  isoZero := Iso.refl X
  center := fun _ => ⊥
  isBlowup := fun i hi => absurd hi (Nat.not_lt_zero i)

/- English proof (authored)
The empty sequence is defined with length zero.
-/
theorem emptySequenceOfBlowups_length (X : Scheme.{u}) : (emptySequenceOfBlowups X).length = 0 := rfl

def emptyMarkedSequenceOfBlowups {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) : MarkedSequenceOfBlowups p I m E where
  toSequenceOfBlowups := emptySequenceOfBlowups X
  ideal := fun _ => I.comap (emptySequenceOfBlowups X).isoZero.hom
  boundary := fun _ => E.map (fun D => D.comap (emptySequenceOfBlowups X).isoZero.hom)
  ideal_zero := rfl
  boundary_zero := rfl
  center_smooth := fun i hi => absurd hi (Nat.not_lt_zero i)
  center_snc := fun i hi => absurd hi (Nat.not_lt_zero i)
  center_order := fun i hi => absurd hi (Nat.not_lt_zero i)
  ideal_succ := fun i hi => absurd hi (Nat.not_lt_zero i)
  boundary_succ := fun i hi => absurd hi (Nat.not_lt_zero i)

/- English proof (authored)
The empty marked sequence uses the empty ordinary sequence as its underlying sequence, so its length is zero.
-/
theorem emptyMarkedSequenceOfBlowups_length {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    (emptyMarkedSequenceOfBlowups p I m E).toSequenceOfBlowups.length = 0 := rfl

abbrev MarkedIdealWithBoundary.SequenceOfBlowups (T : MarkedIdealWithBoundary.{u}) : Type (u + 1) :=
  MarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

def PrincipalizationAssignment : Type (u + 1) := ∀ T : MarkedIdealWithBoundary.{u}, T.SequenceOfBlowups

/- English proof (authored)
Identify the two marked ideals using the given equality. The assignment is then applied to the same input on both sides, so the underlying blowup sequences are equal under that identification.
-/
theorem PrincipalizationAssignment.toSequenceOfBlowups_heq_of_eq (L : PrincipalizationAssignment.{u})
    {T T' : MarkedIdealWithBoundary.{u}} (h : T = T') :
    HEq (L T).toSequenceOfBlowups (L T').toSequenceOfBlowups := by
  subst h
  rfl

def trivialPrincipalizationAssignment : PrincipalizationAssignment.{u} :=
  fun (T : MarkedIdealWithBoundary.{u}) => emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

structure OrderReductionData : Type (u + 1) where
  maxOrderRed : PrincipalizationAssignment.{u}
  orderRed : PrincipalizationAssignment.{u}

def trivialOrderReductionData : OrderReductionData.{u} where
  maxOrderRed := trivialPrincipalizationAssignment
  orderRed := trivialPrincipalizationAssignment

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def HasReducedCenters (s : MarkedSequenceOfBlowups p I m E) : Prop :=
  ∀ i, i < s.toSequenceOfBlowups.length → ∀ J : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData,
    ((s.toSequenceOfBlowups.center i).support : Set ↥(s.toSequenceOfBlowups.schemeAt i)) ⊆
        (J.support : Set ↥(s.toSequenceOfBlowups.schemeAt i)) →
      J ≤ s.toSequenceOfBlowups.center i

/- English proof (authored)
The stage-zero ideal is pulled back along its chosen isomorphism to the base. This isomorphism is the projection at stage zero, giving the claimed formula.
-/
theorem markedSequenceOfBlowups_ideal_zero (s : MarkedSequenceOfBlowups p I m E) :
    s.ideal 0 = I.comap (s.toSequenceOfBlowups.projectionToBase 0) := by
  rw [s.ideal_zero, s.toSequenceOfBlowups.projectionToBase_zero]

/- English proof (authored)
The initial boundary is the pullback of the input list along the stage-zero isomorphism. Since the projection at zero is that same isomorphism, the displayed formula follows.
-/
theorem markedSequenceOfBlowups_boundary_zero (s : MarkedSequenceOfBlowups p I m E) :
    s.boundary 0 = E.map (fun D => D.comap (s.toSequenceOfBlowups.projectionToBase 0)) := by
  rw [s.boundary_zero, s.toSequenceOfBlowups.projectionToBase_zero]

/- English proof (authored)
Apply the controlled-transform identity at the given valid stage. The marking is one, so the first power of the exceptional ideal is the ideal itself.
-/
theorem markedSequenceOfBlowups_exceptionalIdeal_mul_ideal_succ (s : MarkedSequenceOfBlowups p I 1 E) (i : ℕ)
    (h : i < s.toSequenceOfBlowups.length) :
    Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i) * s.ideal (i + 1) =
      (s.ideal i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := by
  have hs := s.ideal_succ i h
  rwa [pow_one] at hs

/- English proof (authored)
The center support is in the locus where the stage ideal has order at least one. This locus is the ideal's support. The reduced-center condition turns that containment of supports into containment of the stage ideal in the center ideal, which means it vanishes along the center.
-/
theorem markedSequenceOfBlowups_ideal_vanishesAlong_center (s : MarkedSequenceOfBlowups p I 1 E)
    (hmax : HasReducedCenters s) (i : ℕ) (h : i < s.toSequenceOfBlowups.length) :
    VanishesAlong (s.ideal i) (s.toSequenceOfBlowups.center i) := by
  rw [vanishesAlong_iff_le]
  refine hmax i h (s.ideal i) ?_
  intro x hx
  have hx' := s.center_order i h hx
  rw [mem_orderAtLeastLocus_one_iff] at hx'
  exact hx'

def MarkedSequenceOfBlowups.toIdealBlowupSequence (s : MarkedSequenceOfBlowups p I 1 E) (hmax : HasReducedCenters s) :
    IdealBlowupSequence p I E where
  toSequenceOfBlowups := s.toSequenceOfBlowups
  ideal := s.ideal
  boundary := s.boundary
  ideal_zero := markedSequenceOfBlowups_ideal_zero s
  boundary_zero := markedSequenceOfBlowups_boundary_zero s
  center_smooth := s.center_smooth
  center_snc := s.center_snc
  ideal_vanishes := fun i h => markedSequenceOfBlowups_ideal_vanishesAlong_center s hmax i h
  ideal_succ := fun i h => markedSequenceOfBlowups_exceptionalIdeal_mul_ideal_succ s i h
  boundary_succ := s.boundary_succ

@[simp]
/- English proof (authored)
The conversion to an ideal blowup sequence adds the properties of the ideal transforms but retains the same underlying sequence of schemes and blowup maps.
-/
theorem MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups (s : MarkedSequenceOfBlowups p I 1 E)
    (hmax : HasReducedCenters s) :
    (s.toIdealBlowupSequence hmax).toSequenceOfBlowups = s.toSequenceOfBlowups := rfl

@[simp]
/- English proof (authored)
The conversion retains the underlying sequence and the ideal at every stage. Evaluating the same ideals at the same final index gives equal last ideals.
-/
theorem MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal (s : MarkedSequenceOfBlowups p I 1 E)
    (hmax : HasReducedCenters s) :
    (s.toIdealBlowupSequence hmax).lastIdeal = s.lastIdeal := rfl

end

end FunctorialResolution.EmbeddedResolution
