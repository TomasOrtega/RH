import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MaxOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CoordinateSubspaceIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplitting
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SmoothComponentsDisjoint
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {N : X.IdealSheafData} {μ : ℕ} {E : List X.IdealSheafData}

def MarkedSequenceOfBlowups.monomialFactor (s : MarkedSequenceOfBlowups p N μ E) (M : X.IdealSheafData) (m : ℕ) :
    ∀ i : ℕ, (s.schemeAt i).IdealSheafData
  | 0 => M.comap s.isoZero.hom
  | i + 1 =>
      (MarkedSequenceOfBlowups.monomialFactor s M m i).comap (s.transitionMapSucc i) * s.exceptionalDivisor i ^ (μ - m)

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem MarkedSequenceOfBlowups.monomialFactor_zero (s : MarkedSequenceOfBlowups p N μ E) (M : X.IdealSheafData)
    (m : ℕ) : MarkedSequenceOfBlowups.monomialFactor s M m 0 = M.comap s.isoZero.hom :=
  rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem MarkedSequenceOfBlowups.monomialFactor_succ (s : MarkedSequenceOfBlowups p N μ E) (M : X.IdealSheafData)
    (m i : ℕ) :
    MarkedSequenceOfBlowups.monomialFactor s M m (i + 1) =
      (MarkedSequenceOfBlowups.monomialFactor s M m i).comap (s.transitionMapSucc i) * s.exceptionalDivisor i ^ (μ - m) :=
  rfl

def MarkedSequenceOfBlowups.controlledTransform (s : MarkedSequenceOfBlowups p N μ E) (I : X.IdealSheafData) (m : ℕ) :
    ∀ i : ℕ, (s.schemeAt i).IdealSheafData
  | 0 => I.comap s.isoZero.hom
  | i + 1 =>
      residualByPow ((MarkedSequenceOfBlowups.controlledTransform s I m i).comap (s.transitionMapSucc i)) (s.exceptionalDivisor i) m

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem MarkedSequenceOfBlowups.controlledTransform_zero (s : MarkedSequenceOfBlowups p N μ E) (I : X.IdealSheafData)
    (m : ℕ) : MarkedSequenceOfBlowups.controlledTransform s I m 0 = I.comap s.isoZero.hom :=
  rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem MarkedSequenceOfBlowups.controlledTransform_succ (s : MarkedSequenceOfBlowups p N μ E) (I : X.IdealSheafData)
    (m i : ℕ) :
    MarkedSequenceOfBlowups.controlledTransform s I m (i + 1) =
      residualByPow ((MarkedSequenceOfBlowups.controlledTransform s I m i).comap (s.transitionMapSucc i)) (s.exceptionalDivisor i) m :=
  rfl

end

section

variable {A B : Scheme.{u}}

/- English proof (translation)
Rewrite using `[AlgebraicGeometry.Scheme.IdealSheafData.support_comap]`. Both sides reduce to the same expression.
-/
private theorem support_comap_coe {A' B' : Scheme.{u}} (f : A' ⟶ B') (I : B'.IdealSheafData) :
    (↑(I.comap f).support : Set ↥A') = ⇑f.base ⁻¹' (↑I.support : Set ↥B') := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem comap_one {A' B' : Scheme.{u}} (f : A' ⟶ B') :
    (1 : B'.IdealSheafData).comap f = 1 := by
  simp

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.support_mul]`. Conclude with `Set.Subset.rfl`.
-/
private theorem support_mul_subset {Y : Scheme.{u}} (P Q : Y.IdealSheafData) :
    (↑(P * Q).support : Set ↥Y) ⊆ (↑P.support : Set ↥Y) ∪ (↑Q.support : Set ↥Y) := by
  rw [Scheme.IdealSheafData.support_mul]
  exact Set.Subset.rfl

/- English proof (translation)
Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Introduce `x hx`. Establish `h1 : stalkIdeal (P ^ 0) x = ⊤`. Rewrite using `[stalkIdeal_pow, pow_zero, ← Ideal.one_eq_top]`. Conclude with `absurd h1 ((mem_support_iff_stalkIdeal_ne_top (P ^ 0) x).1 hx)`.

Rewrite using `[Scheme.IdealSheafData.support_pow]`. Conclude with `hn`.
-/
private theorem support_pow_subset {Y : Scheme.{u}} (P : Y.IdealSheafData) (n : ℕ) :
    (↑(P ^ n).support : Set ↥Y) ⊆ (↑P.support : Set ↥Y) := by
  rcases eq_or_ne n 0 with rfl | hn
  · intro x hx
    have h1 : stalkIdeal (P ^ 0) x = ⊤ := by
      rw [stalkIdeal_pow, pow_zero, ← Ideal.one_eq_top]
    exact absurd h1 ((mem_support_iff_stalkIdeal_ne_top (P ^ 0) x).1 hx)
  · rw [Scheme.IdealSheafData.support_pow]
    exact hn

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.support_mul]`. Conclude with `Set.subset_union_right`.
-/
private theorem support_subset_support_mul_right {Y : Scheme.{u}} (P Q : Y.IdealSheafData) :
    (↑Q.support : Set ↥Y) ⊆ (↑(P * Q).support : Set ↥Y) := by
  rw [Scheme.IdealSheafData.support_mul]
  exact Set.subset_union_right

/- English proof (translation)
Unfold `IsIrreducibleComponentOf`. Conclude with `⟨h1, h2, fun C' hC' hCle hC'S => Set.Subset.antisymm (h3 C' hC' hC'S hCle) hCle⟩`.
-/
private theorem isIrreducibleComponentOf_of_maximal {Y : Scheme.{u}} {C S : Set ↥Y} (h1 : IsIrreducible C)
    (h2 : C ⊆ S) (h3 : ∀ C', IsIrreducible C' → C' ⊆ S → C ⊆ C' → C' ⊆ C) :
    IsIrreducibleComponentOf C S := by
  unfold IsIrreducibleComponentOf
  exact ⟨h1, h2, fun C' hC' hCle hC'S => Set.Subset.antisymm (h3 C' hC' hC'S hCle) hCle⟩

/- English proof (translation)
Unfold `IsIrreducibleComponentOf at h`. Conclude with `⟨h.1, h.2.1, fun C' hC' hC'S hCle => (h.2.2 C' hC' hCle hC'S).subset⟩`.
-/
private theorem isIrreducible_subset_maximal_of_isIrreducibleComponentOf {Y : Scheme.{u}} {C S : Set ↥Y} (h : IsIrreducibleComponentOf C S) :
    IsIrreducible C ∧ C ⊆ S ∧ ∀ C', IsIrreducible C' → C' ⊆ S → C ⊆ C' → C' ⊆ C := by
  unfold IsIrreducibleComponentOf at h
  exact ⟨h.1, h.2.1, fun C' hC' hC'S hCle => (h.2.2 C' hC' hCle hC'S).subset⟩

/- English proof (translation)
Rewrite using `[← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]`.
-/
private theorem comap_homOfLE {Y : Scheme.{u}} {U V : Y.Opens} (h : U ≤ V)
    (D : Y.IdealSheafData) : (D.comap V.ι).comap (Y.homOfLE h) = D.comap U.ι := by
  rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]

/- English proof (translation)
Introduce `y hy`. Proceed by induction on `hy using Submonoid.closure_induction with`. Consider the case `mem D hD`. Take `⟨D₀, hD₀, rfl⟩` from `hD`. Rewrite using `[comap_homOfLE]`.

Conclude with `Submonoid.subset_closure ⟨D₀, hD₀, rfl⟩`. Consider the case `one`. Rewrite using `[comap_one]`. Conclude with `one_mem _`. Consider the case `mul a b _ _ iha ihb`.

Rewrite using `[Scheme.IdealSheafData.comap_mul]`. Conclude with `mul_mem iha ihb`.
-/
private theorem comap_homOfLE_mem_closure_comap {Y : Scheme.{u}} {E : List Y.IdealSheafData}
    {U V : Y.Opens} (h : U ≤ V) :
    ∀ y ∈ Submonoid.closure ((fun D : Y.IdealSheafData => D.comap V.ι) '' {D | D ∈ E}),
      y.comap (Y.homOfLE h) ∈
        Submonoid.closure ((fun D : Y.IdealSheafData => D.comap U.ι) '' {D | D ∈ E}) := by
  intro y hy
  induction hy using Submonoid.closure_induction with
  | mem D hD =>
      obtain ⟨D₀, hD₀, rfl⟩ := hD
      rw [comap_homOfLE]
      exact Submonoid.subset_closure ⟨D₀, hD₀, rfl⟩
  | one =>
      rw [comap_one]
      exact one_mem _
  | mul a b _ _ iha ihb =>
      rw [Scheme.IdealSheafData.comap_mul]
      exact mul_mem iha ihb

/- English proof (translation)
Rewrite using `[isMonomialIn_iff_forall_exists_mem_closure]`. Introduce `x`. Use `⟨⊤, trivial, ?_⟩` and prove the remaining obligations. Conclude with `Submonoid.subset_closure ⟨D, hD, rfl⟩`.
-/
private theorem isMonomialIn_of_mem {Y : Scheme.{u}} {E : List Y.IdealSheafData}
    {D : Y.IdealSheafData} (hD : D ∈ E) : IsMonomialIn E D := by
  rw [isMonomialIn_iff_forall_exists_mem_closure]
  intro x
  refine ⟨⊤, trivial, ?_⟩
  exact Submonoid.subset_closure ⟨D, hD, rfl⟩

/- English proof (translation)
Rewrite `hP`, `hQ`, the goal using `[isMonomialIn_iff_forall_exists_mem_closure]`. Introduce `x`. Take `⟨U1, hx1, h1⟩` from `hP x`. Take `⟨U2, hx2, h2⟩` from `hQ x`. Use `⟨U1 ⊓ U2, ⟨hx1, hx2⟩, ?_⟩` and prove the remaining obligations.

Establish `k1` using `comap_homOfLE_mem_closure_comap (E := E) (inf_le_left : U1 ⊓ U2 ≤ U1) _ h1`. Establish `k2` using `comap_homOfLE_mem_closure_comap (E := E) (inf_le_right : U1 ⊓ U2 ≤ U2) _ h2`. Rewrite `k1`, `k2` using `[comap_homOfLE]`. Rewrite using `[Scheme.IdealSheafData.comap_mul]`. Conclude with `mul_mem k1 k2`.
-/
private theorem isMonomialIn_mul {Y : Scheme.{u}} (E : List Y.IdealSheafData)
    {P Q : Y.IdealSheafData} (hP : IsMonomialIn E P) (hQ : IsMonomialIn E Q) :
    IsMonomialIn E (P * Q) := by
  rw [isMonomialIn_iff_forall_exists_mem_closure] at hP hQ ⊢
  intro x
  obtain ⟨U1, hx1, h1⟩ := hP x
  obtain ⟨U2, hx2, h2⟩ := hQ x
  refine ⟨U1 ⊓ U2, ⟨hx1, hx2⟩, ?_⟩
  have k1 := comap_homOfLE_mem_closure_comap (E := E) (inf_le_left : U1 ⊓ U2 ≤ U1) _ h1
  have k2 := comap_homOfLE_mem_closure_comap (E := E) (inf_le_right : U1 ⊓ U2 ≤ U2) _ h2
  rw [comap_homOfLE] at k1 k2
  rw [Scheme.IdealSheafData.comap_mul]
  exact mul_mem k1 k2

/- English proof (translation)
Rewrite `hP`, the goal using `[isMonomialIn_iff_forall_exists_mem_closure]`. Introduce `x`. Take `⟨U, hxU, h⟩` from `hP x`. Use `⟨U, hxU, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.IdealSheafData.comap_pow]`.

Conclude with `pow_mem h n`.
-/
private theorem isMonomialIn_pow {Y : Scheme.{u}} (E : List Y.IdealSheafData)
    {P : Y.IdealSheafData} (hP : IsMonomialIn E P) (n : ℕ) : IsMonomialIn E (P ^ n) := by
  rw [isMonomialIn_iff_forall_exists_mem_closure] at hP ⊢
  intro x
  obtain ⟨U, hxU, h⟩ := hP x
  refine ⟨U, hxU, ?_⟩
  rw [Scheme.IdealSheafData.comap_pow]
  exact pow_mem h n

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `_ x`. Use `⟨⊤, trivial, ?_⟩` and prove the remaining obligations.

Introduce `D hD`. Conclude with `absurd hD (by simp)`. Consider the case `cons D0 L ih`. Introduce `hall x`. Take `⟨Vleft, hxVleft, hV1⟩` from `ih (fun D hD => hall D (by simp [hD])) x`.

Take `⟨Vright, hxVright, hV2⟩` from `(isMonomialIn_iff_forall_exists_mem_closure L2 D0).1 (hall D0 (by simp)) x`. Use `⟨Vleft ⊓ Vright, ⟨hxVleft, hxVright⟩, ?_⟩` and prove the remaining obligations. Introduce `D hD`. Break down `List.mem_cons.1 hD with rfl | hD'` into its components or cases. Establish `hk` using `comap_homOfLE_mem_closure_comap (E := L2) (inf_le_right : Vleft ⊓ Vright ≤ Vright) _ hV2`.

Rewrite `hk` using `[comap_homOfLE]`. Then use the resulting hypothesis. Establish `hk` using `comap_homOfLE_mem_closure_comap (E := L2) (inf_le_left : Vleft ⊓ Vright ≤ Vleft) _ (hV1 D hD')`. Rewrite `hk` using `[comap_homOfLE]`. Then use the resulting hypothesis.
-/
private theorem exists_opens_forall_comap_mem_closure {Y : Scheme.{u}} (L2 : List Y.IdealSheafData) :
    ∀ (L : List Y.IdealSheafData), (∀ D ∈ L, IsMonomialIn L2 D) → ∀ x : ↥Y,
      ∃ V : Y.Opens, x ∈ V ∧ ∀ D ∈ L, D.comap V.ι ∈
        Submonoid.closure ((fun D' : Y.IdealSheafData => D'.comap V.ι) '' {D' | D' ∈ L2}) := by
  intro L
  induction L with
  | nil =>
      intro _ x
      refine ⟨⊤, trivial, ?_⟩
      intro D hD
      exact absurd hD (by simp)
  | cons D0 L ih =>
      intro hall x
      obtain ⟨Vleft, hxVleft, hV1⟩ := ih (fun D hD => hall D (by simp [hD])) x
      obtain ⟨Vright, hxVright, hV2⟩ :=
        (isMonomialIn_iff_forall_exists_mem_closure L2 D0).1 (hall D0 (by simp)) x
      refine ⟨Vleft ⊓ Vright, ⟨hxVleft, hxVright⟩, ?_⟩
      intro D hD
      rcases List.mem_cons.1 hD with rfl | hD'
      · have hk := comap_homOfLE_mem_closure_comap (E := L2) (inf_le_right : Vleft ⊓ Vright ≤ Vright) _ hV2
        rwa [comap_homOfLE] at hk
      · have hk := comap_homOfLE_mem_closure_comap (E := L2) (inf_le_left : Vleft ⊓ Vright ≤ Vleft) _ (hV1 D hD')
        rwa [comap_homOfLE] at hk

/- English proof (translation)
Rewrite `hP`, the goal using `[isMonomialIn_iff_forall_exists_mem_closure]`. Introduce `x`. Take `⟨U, hxU, hU⟩` from `hP x`. Take `⟨Vinter, hxW, hW⟩` from `exists_opens_forall_comap_mem_closure L2 L1 h x`. Use `⟨U ⊓ Vinter, ⟨hxU, hxW⟩, ?_⟩` and prove the remaining obligations.

Establish `h1` using `comap_homOfLE_mem_closure_comap (E := L1) (inf_le_left : U ⊓ Vinter ≤ U) _ hU`. Rewrite `h1` using `[comap_homOfLE]`. Use `Submonoid.closure_le.2 ?_ h1` and prove the remaining obligations. Introduce and unpack `y ⟨D, hD, rfl⟩`. Establish `h2` using `comap_homOfLE_mem_closure_comap (E := L2) (inf_le_right : U ⊓ Vinter ≤ Vinter) _ (hW D hD)`.

Rewrite `h2` using `[comap_homOfLE]`. Then use the resulting hypothesis.
-/
private theorem isMonomialIn_of_forall_mem {Y : Scheme.{u}} {L1 L2 : List Y.IdealSheafData}
    (h : ∀ D ∈ L1, IsMonomialIn L2 D) {P : Y.IdealSheafData} (hP : IsMonomialIn L1 P) :
    IsMonomialIn L2 P := by
  rw [isMonomialIn_iff_forall_exists_mem_closure] at hP ⊢
  intro x
  obtain ⟨U, hxU, hU⟩ := hP x
  obtain ⟨Vinter, hxW, hW⟩ := exists_opens_forall_comap_mem_closure L2 L1 h x
  refine ⟨U ⊓ Vinter, ⟨hxU, hxW⟩, ?_⟩
  have h1 := comap_homOfLE_mem_closure_comap (E := L1) (inf_le_left : U ⊓ Vinter ≤ U) _ hU
  rw [comap_homOfLE] at h1
  refine Submonoid.closure_le.2 ?_ h1
  rintro y ⟨D, hD, rfl⟩
  have h2 := comap_homOfLE_mem_closure_comap (E := L2) (inf_le_right : U ⊓ Vinter ≤ Vinter) _ (hW D hD)
  rwa [comap_homOfLE] at h2

/- English proof (translation)
Introduce `x hx`. Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[Set.mem_union, not_or]`. Take `⟨hA, hB⟩` from `hcon`. Take `⟨U, ε, hxU, heq⟩` from `h x`.

Establish `hA0 : orderAt A' x = 0` using `(orderAt_eq_zero_iff_not_mem_support A' x).2 hA`. Establish `hB0 : orderAt B' x = 0` using `(orderAt_eq_zero_iff_not_mem_support B' x).2 hB`. Establish `hAy : orderAt (A'.comap U.ι) (⟨x, hxU⟩ : ↥U) = 0`. Rewrite using `[orderAt_comap_of_isOpenImmersion U.ι A' (⟨x, hxU⟩ : ↥U)]`. Conclude with `hA0`.

Establish `hBy : orderAt (B'.comap U.ι) (⟨x, hxU⟩ : ↥U) = 0`. Rewrite using `[orderAt_comap_of_isOpenImmersion U.ι B' (⟨x, hxU⟩ : ↥U)]`. Conclude with `hB0`. Establish `hnA` using `(orderAt_eq_zero_iff_not_mem_support (A'.comap U.ι) (⟨x, hxU⟩ : ↥U)).1 hAy`. Establish `hnB` using `(orderAt_eq_zero_iff_not_mem_support (B'.comap U.ι) (⟨x, hxU⟩ : ↥U)).1 hBy`.

Establish `hDy : orderAt (D'.comap U.ι) (⟨x, hxU⟩ : ↥U) = 0`. Use `(orderAt_eq_zero_iff_not_mem_support (D'.comap U.ι) (⟨x, hxU⟩ : ↥U)).2 ?_` and prove the remaining obligations. Rewrite using `[heq]`. Introduce `hmem`. Break down `support_mul_subset (A'.comap U.ι) (B'.comap U.ι ^ ε) hmem with h1 | h2` into its components or cases.

Conclude with `hnA h1`. Conclude with `hnB (support_pow_subset (B'.comap U.ι) ε h2)`. Rewrite `hDy` using `[orderAt_comap_of_isOpenImmersion U.ι D' (⟨x, hxU⟩ : ↥U)]`. Conclude with `(orderAt_eq_zero_iff_not_mem_support D' x).1 hDy hx`.
-/
private theorem support_subset_union_of_locally_eq_mul_pow {Y : Scheme.{u}} (D' A' B' : Y.IdealSheafData)
    (h : ∀ x : ↥Y, ∃ (U : Y.Opens) (ε : ℕ), x ∈ U ∧
      D'.comap U.ι = A'.comap U.ι * B'.comap U.ι ^ ε) :
    (↑D'.support : Set ↥Y) ⊆ (↑A'.support : Set ↥Y) ∪ (↑B'.support : Set ↥Y) := by
  intro x hx
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  obtain ⟨U, ε, hxU, heq⟩ := h x
  have hA0 : orderAt A' x = 0 := (orderAt_eq_zero_iff_not_mem_support A' x).2 hA
  have hB0 : orderAt B' x = 0 := (orderAt_eq_zero_iff_not_mem_support B' x).2 hB
  have hAy : orderAt (A'.comap U.ι) (⟨x, hxU⟩ : ↥U) = 0 := by
    rw [orderAt_comap_of_isOpenImmersion U.ι A' (⟨x, hxU⟩ : ↥U)]
    exact hA0
  have hBy : orderAt (B'.comap U.ι) (⟨x, hxU⟩ : ↥U) = 0 := by
    rw [orderAt_comap_of_isOpenImmersion U.ι B' (⟨x, hxU⟩ : ↥U)]
    exact hB0
  have hnA := (orderAt_eq_zero_iff_not_mem_support (A'.comap U.ι) (⟨x, hxU⟩ : ↥U)).1 hAy
  have hnB := (orderAt_eq_zero_iff_not_mem_support (B'.comap U.ι) (⟨x, hxU⟩ : ↥U)).1 hBy
  have hDy : orderAt (D'.comap U.ι) (⟨x, hxU⟩ : ↥U) = 0 := by
    refine (orderAt_eq_zero_iff_not_mem_support (D'.comap U.ι) (⟨x, hxU⟩ : ↥U)).2 ?_
    rw [heq]
    intro hmem
    rcases support_mul_subset (A'.comap U.ι) (B'.comap U.ι ^ ε) hmem with h1 | h2
    · exact hnA h1
    · exact hnB (support_pow_subset (B'.comap U.ι) ε h2)
  rw [orderAt_comap_of_isOpenImmersion U.ι D' (⟨x, hxU⟩ : ↥U)] at hDy
  exact (orderAt_eq_zero_iff_not_mem_support D' x).1 hDy hx

/- English proof (translation)
Rewrite using `[isMonomialIn_iff_forall_exists_mem_closure]`. Introduce `x`. Take `⟨U, ε, hxU, heq⟩` from `h x`. Use `⟨U, hxU, ?_⟩` and prove the remaining obligations. Establish `hA2 : A'.comap U.ι ∈ Submonoid.closure ((fun D0 : Y.IdealSheafData => D0.comap U.ι) '' {D0 | D0 ∈ L})` using `Submonoid.subset_closure ⟨A', hA, rfl⟩`.

Establish `hB2 : B'.comap U.ι ∈ Submonoid.closure ((fun D0 : Y.IdealSheafData => D0.comap U.ι) '' {D0 | D0 ∈ L})` using `Submonoid.subset_closure ⟨B', hB, rfl⟩`. Rewrite using `[heq]`. Conclude with `mul_mem hA2 (pow_mem hB2 ε)`.
-/
private theorem isMonomialIn_of_locally_eq_mul_pow {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (D' A' B' : Y.IdealSheafData) (hA : A' ∈ L) (hB : B' ∈ L)
    (h : ∀ x : ↥Y, ∃ (U : Y.Opens) (ε : ℕ), x ∈ U ∧
      D'.comap U.ι = A'.comap U.ι * B'.comap U.ι ^ ε) :
    IsMonomialIn L D' := by
  rw [isMonomialIn_iff_forall_exists_mem_closure]
  intro x
  obtain ⟨U, ε, hxU, heq⟩ := h x
  refine ⟨U, hxU, ?_⟩
  have hA2 : A'.comap U.ι ∈
      Submonoid.closure ((fun D0 : Y.IdealSheafData => D0.comap U.ι) '' {D0 | D0 ∈ L}) :=
    Submonoid.subset_closure ⟨A', hA, rfl⟩
  have hB2 : B'.comap U.ι ∈
      Submonoid.closure ((fun D0 : Y.IdealSheafData => D0.comap U.ι) '' {D0 | D0 ∈ L}) :=
    Submonoid.subset_closure ⟨B', hB, rfl⟩
  rw [heq]
  exact mul_mem hA2 (pow_mem hB2 ε)

/- English proof (translation)
Rewrite `h`, the goal using `[isMonomialIn_iff_forall_exists_mem_closure]`. Introduce `x`. Take `⟨U, hxU, hmem⟩` from `h (f.base x)`. Use `⟨f ⁻¹ᵁ U, hxU, ?_⟩` and prove the remaining obligations. Establish `hcomp : f.resLE U (f ⁻¹ᵁ U) le_rfl ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f` using `Scheme.Hom.resLE_comp_ι f le_rfl`.

Establish `key : ∀ J : B.IdealSheafData, (J.comap f).comap (f ⁻¹ᵁ U).ι = (J.comap U.ι).comap (f.resLE U (f ⁻¹ᵁ U) le_rfl)`. Introduce `J`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomp]`. Establish `main : ∀ y ∈ Submonoid.closure ((fun D : B.IdealSheafData => D.comap U.ι) '' {D | D ∈ E}), y.comap (f.resLE U (f ⁻¹ᵁ U) le_rfl) ∈ Submonoid.closure ((fun D : A.IdealSheafData => D.comap (f ⁻¹ᵁ U).ι) '' {D | D ∈ List.map (fun D : B.IdealSheafData => D.comap f) E})`. Introduce `y hy`.

Proceed by induction on `hy using Submonoid.closure_induction with`. Consider the case `mem D hD`. Take `⟨D₀, hD₀, rfl⟩` from `hD`. Rewrite using `[← key D₀]`. Conclude with `Submonoid.subset_closure ⟨D₀.comap f, List.mem_map.2 ⟨D₀, hD₀, rfl⟩, rfl⟩`.

Consider the case `one`. Rewrite using `[comap_one]`. Conclude with `one_mem _`. Consider the case `mul a b _ _ iha ihb`. Rewrite using `[Scheme.IdealSheafData.comap_mul]`.

Conclude with `mul_mem iha ihb`. Rewrite using `[key M]`. Conclude with `main _ hmem`.
-/
theorem IsMonomialIn.comap (f : A ⟶ B) {E : List B.IdealSheafData} {M : B.IdealSheafData}
    (h : IsMonomialIn E M) :
    IsMonomialIn (List.map (fun D : B.IdealSheafData => D.comap f) E) (M.comap f) := by
  rw [isMonomialIn_iff_forall_exists_mem_closure] at h ⊢
  intro x
  obtain ⟨U, hxU, hmem⟩ := h (f.base x)
  refine ⟨f ⁻¹ᵁ U, hxU, ?_⟩
  have hcomp : f.resLE U (f ⁻¹ᵁ U) le_rfl ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f :=
    Scheme.Hom.resLE_comp_ι f le_rfl
  have key : ∀ J : B.IdealSheafData,
      (J.comap f).comap (f ⁻¹ᵁ U).ι = (J.comap U.ι).comap (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    intro J
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomp]
  have main : ∀ y ∈ Submonoid.closure ((fun D : B.IdealSheafData => D.comap U.ι) '' {D | D ∈ E}),
      y.comap (f.resLE U (f ⁻¹ᵁ U) le_rfl) ∈
        Submonoid.closure ((fun D : A.IdealSheafData => D.comap (f ⁻¹ᵁ U).ι) ''
          {D | D ∈ List.map (fun D : B.IdealSheafData => D.comap f) E}) := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem D hD =>
        obtain ⟨D₀, hD₀, rfl⟩ := hD
        rw [← key D₀]
        exact Submonoid.subset_closure ⟨D₀.comap f, List.mem_map.2 ⟨D₀, hD₀, rfl⟩, rfl⟩
    | one =>
        rw [comap_one]
        exact one_mem _
    | mul a b _ _ iha ihb =>
        rw [Scheme.IdealSheafData.comap_mul]
        exact mul_mem iha ihb
  rw [key M]
  exact main _ hmem

/- English proof (translation)
Establish `hAB : ∀ x : ↥A, (e.inv).base ((e.hom).base x) = x`. Introduce `x`. Simplify using the standard rewrite rules. Establish `hhomInv : ∀ y : ↥B, (e.hom).base ((e.inv).base y) = y`. Introduce `y`.

Simplify using the standard rewrite rules. Establish `hcont : Continuous (⇑e.hom.base)` using `(Scheme.homeoOfIso e).continuous`. Establish `hcont' : Continuous (⇑e.inv.base)` using `(Scheme.homeoOfIso e).symm.continuous`. Use `⟨?_, ?_, h.monomial.comap e.hom, ?_⟩` and prove the remaining obligations. Rewrite using `[h.eq_mul, Scheme.IdealSheafData.comap_mul]`.

Introduce `x hx`. Rewrite `hx` using `[support_comap_coe]`. Take `⟨D, hD, hxD⟩` from `Set.mem_iUnion₂.1 (h.monomial_support hx)`. Use `Set.mem_iUnion₂.2 ⟨D.comap e.hom, List.mem_map.2 ⟨D, hD, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[support_comap_coe]`.

Conclude with `hxD`. Introduce and unpack `D hD C hCirr hCsubD hCmax hCN`. Take `⟨D₀, hD₀, rfl⟩` from `List.mem_map.1 hD`. Rewrite `hCsubD` using `[support_comap_coe]`. Rewrite `hCN` using `[support_comap_coe]`.

Use `h.transversal D₀ hD₀ (⇑e.hom.base '' C) (hCirr.image _ hcont.continuousOn) (Set.image_subset_iff.2 hCsubD) ?_ (Set.image_subset_iff.2 hCN)` and prove the remaining obligations. Introduce `C' hC'irr hC'D hCle`. Establish `hsub : ⇑e.inv.base '' C' ⊆ (↑((D₀.comap e.hom)).support : Set ↥A)`. Rewrite using `[support_comap_coe]`. Introduce and unpack `x ⟨y, hy, rfl⟩`.

Simplify using `only [Set.mem_preimage, hhomInv]`. Conclude with `hC'D hy`. Establish `hCsub : C ⊆ ⇑e.inv.base '' C'`. Introduce `x hx`. Conclude with `⟨(e.hom).base x, hCle ⟨x, hx, rfl⟩, hAB x⟩`.

Establish `hfin` using `hCmax (⇑e.inv.base '' C') (hC'irr.image _ hcont'.continuousOn) hsub hCsub`. Introduce `y hy`. Conclude with `⟨(e.inv).base y, hfin ⟨y, hy, rfl⟩, hhomInv y⟩`.
-/
theorem IsMonomialSplitting.comap_iso (e : A ≅ B) {E : List B.IdealSheafData}
    {I M N : B.IdealSheafData} (h : IsMonomialSplitting E I M N) :
    IsMonomialSplitting (List.map (fun D : B.IdealSheafData => D.comap e.hom) E) (I.comap e.hom)
      (M.comap e.hom) (N.comap e.hom) := by
  have hAB : ∀ x : ↥A, (e.inv).base ((e.hom).base x) = x := by
    intro x
    simp
  have hhomInv : ∀ y : ↥B, (e.hom).base ((e.inv).base y) = y := by
    intro y
    simp
  have hcont : Continuous (⇑e.hom.base) := (Scheme.homeoOfIso e).continuous
  have hcont' : Continuous (⇑e.inv.base) := (Scheme.homeoOfIso e).symm.continuous
  refine ⟨?_, ?_, h.monomial.comap e.hom, ?_⟩
  · rw [h.eq_mul, Scheme.IdealSheafData.comap_mul]
  · intro x hx
    rw [support_comap_coe] at hx
    obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 (h.monomial_support hx)
    refine Set.mem_iUnion₂.2 ⟨D.comap e.hom, List.mem_map.2 ⟨D, hD, rfl⟩, ?_⟩
    rw [support_comap_coe]
    exact hxD
  · rintro D hD C hCirr hCsubD hCmax hCN
    obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD
    rw [support_comap_coe] at hCsubD
    rw [support_comap_coe] at hCN
    refine h.transversal D₀ hD₀ (⇑e.hom.base '' C) (hCirr.image _ hcont.continuousOn)
      (Set.image_subset_iff.2 hCsubD) ?_ (Set.image_subset_iff.2 hCN)
    intro C' hC'irr hC'D hCle
    have hsub : ⇑e.inv.base '' C' ⊆ (↑((D₀.comap e.hom)).support : Set ↥A) := by
      rw [support_comap_coe]
      rintro x ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage, hhomInv]
      exact hC'D hy
    have hCsub : C ⊆ ⇑e.inv.base '' C' := by
      intro x hx
      exact ⟨(e.hom).base x, hCle ⟨x, hx, rfl⟩, hAB x⟩
    have hfin := hCmax (⇑e.inv.base '' C') (hC'irr.image _ hcont'.continuousOn) hsub hCsub
    intro y hy
    exact ⟨(e.inv).base y, hfin ⟨y, hy, rfl⟩, hhomInv y⟩

end

section

def MarkedIdealWithBoundary.withIdealAndMult (T : MarkedIdealWithBoundary.{u}) (N : T.scheme.IdealSheafData) (μ : ℕ) :
    MarkedIdealWithBoundary.{u} :=
  { base := T.base
    instField := T.instField
    scheme := T.scheme
    structMap := T.structMap
    ideal := N
    mult := μ
    boundary := T.boundary }

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem MarkedIdealWithBoundary.withIdealAndMult_baseField (T : MarkedIdealWithBoundary.{u}) (N : T.scheme.IdealSheafData)
    (μ : ℕ) : (T.withIdealAndMult N μ).base = T.base :=
  rfl

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem MarkedIdealWithBoundary.withIdealAndMult_scheme (T : MarkedIdealWithBoundary.{u}) (N : T.scheme.IdealSheafData)
    (μ : ℕ) : (T.withIdealAndMult N μ).scheme = T.scheme :=
  rfl

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem MarkedIdealWithBoundary.withIdealAndMult_structureMorphism (T : MarkedIdealWithBoundary.{u}) (N : T.scheme.IdealSheafData)
    (μ : ℕ) : (T.withIdealAndMult N μ).structMap = T.structMap :=
  rfl

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem MarkedIdealWithBoundary.withIdealAndMult_ideal (T : MarkedIdealWithBoundary.{u}) (N : T.scheme.IdealSheafData)
    (μ : ℕ) : (T.withIdealAndMult N μ).ideal = N :=
  rfl

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem MarkedIdealWithBoundary.withIdealAndMult_mult (T : MarkedIdealWithBoundary.{u}) (N : T.scheme.IdealSheafData)
    (μ : ℕ) : (T.withIdealAndMult N μ).mult = μ :=
  rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem MarkedIdealWithBoundary.withIdealAndMult_boundary (T : MarkedIdealWithBoundary.{u}) (N : T.scheme.IdealSheafData)
    (μ : ℕ) : (T.withIdealAndMult N μ).boundary = T.boundary :=
  rfl

/- English proof (translation)
The claim follows from `{ charZero := hT.charZero locallyOfFiniteType := hT.locallyOfFiniteType nonzeroOnComponents := hsplit.nonzeroOnComponents_nonMonomial hT.nonzeroOnComponents one_le_mult := le_trans hT.one_le_mult hμ quasiCompact := hT.quasiCompact smooth := hT.smooth snc := hT.snc }`.
-/
theorem MarkedIdealWithBoundary.IsAdmissible.withIdealAndMult {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    {M N : T.scheme.IdealSheafData} (hsplit : IsMonomialSplitting T.boundary T.ideal M N)
    {μ : ℕ} (hμ : T.mult ≤ μ) :
    (T.withIdealAndMult N μ).IsAdmissible :=
  { charZero := hT.charZero
    locallyOfFiniteType := hT.locallyOfFiniteType
    nonzeroOnComponents := hsplit.nonzeroOnComponents_nonMonomial hT.nonzeroOnComponents
    one_le_mult := le_trans hT.one_le_mult hμ
    quasiCompact := hT.quasiCompact
    smooth := hT.smooth
    snc := hT.snc }

end

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {N : X.IdealSheafData} {μ : ℕ} {E : List X.IdealSheafData}

/- English proof (translation)
Rewrite using `[MarkedSequenceOfBlowups.exceptionalDivisor_eq, Blowup.exceptionalIdeal_eq_comap]`.
-/
private theorem exceptionalDivisor_eq_exceptionalIdeal (s : MarkedSequenceOfBlowups p N μ E) (i : ℕ) :
    s.exceptionalDivisor i = Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) := by
  rw [MarkedSequenceOfBlowups.exceptionalDivisor_eq, Blowup.exceptionalIdeal_eq_comap]

/- English proof (translation)
Rewrite using `[exceptionalDivisor_eq_exceptionalIdeal]`. Conclude with `isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal (s.isBlowupAlongIdealSheaf_blowupMorphism i hi)`.
-/
private theorem isLocallyGeneratedByNonZeroDivisor_exceptionalDivisor (s : MarkedSequenceOfBlowups p N μ E) (i : ℕ)
    (hi : i < s.length) : Blowup.IsLocallyGeneratedByNonZeroDivisor (s.exceptionalDivisor i) := by
  rw [exceptionalDivisor_eq_exceptionalIdeal]
  exact isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal (s.isBlowupAlongIdealSheaf_blowupMorphism i hi)

/- English proof (translation)
Introduce `x hx`. Establish `h1 : (m : ℕ∞) ≤ orderAt Ni x` using `(mem_orderAtLeastLocus_iff _ _ _).1 (hS hx)`. Establish `h2` using `add_orderAt_le_orderAt_mul Mi Ni x`. Rewrite `h2` using `[← h]`. Conclude with `(mem_orderAtLeastLocus_iff _ _ _).2 (le_trans h1 (le_trans le_add_self h2))`.
-/
private theorem subset_orderAtLeastLocus_of_eq_mul {Y : Scheme.{u}} (Mi Ni Ci : Y.IdealSheafData)
    (h : Ci = Mi * Ni) (m : ℕ) (S : Set ↥Y) (hS : S ⊆ orderAtLeastLocus Ni m) :
    S ⊆ orderAtLeastLocus Ci m := by
  intro x hx
  have h1 : (m : ℕ∞) ≤ orderAt Ni x := (mem_orderAtLeastLocus_iff _ _ _).1 (hS hx)
  have h2 := add_orderAt_le_orderAt_mul Mi Ni x
  rw [← h] at h2
  exact (mem_orderAtLeastLocus_iff _ _ _).2 (le_trans h1 (le_trans le_add_self h2))

/- English proof (translation)
Establish `hid : s.exceptionalDivisor i ^ μ * s.ideal (i + 1) = (s.ideal i).comap (s.transitionMapSucc i)`. Rewrite using `[exceptionalDivisor_eq_exceptionalIdeal]`. Conclude with `s.ideal_succ i hi`. Establish `hF : s.exceptionalDivisor i ^ m * s.exceptionalDivisor i ^ (μ - m) = s.exceptionalDivisor i ^ μ`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hm]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc, mul_comm, mul_left_comm]`. Use `_ = Mi.comap (s.transitionMapSucc i) * ((s.ideal i).comap (s.transitionMapSucc i)) := by rw [hF, hid]`. Use `_ = Ci.comap (s.transitionMapSucc i) := by rw [h, Scheme.IdealSheafData.comap_mul]`.
-/
private theorem exceptionalDivisor_pow_mul_comap_mul_eq_comap (s : MarkedSequenceOfBlowups p N μ E) (m : ℕ) (hm : m ≤ μ)
    (i : ℕ) (hi : i < s.length) (Ci Mi : (s.schemeAt i).IdealSheafData)
    (h : Ci = Mi * s.ideal i) :
    s.exceptionalDivisor i ^ m *
        (Mi.comap (s.transitionMapSucc i) * s.exceptionalDivisor i ^ (μ - m) * s.ideal (i + 1))
      = Ci.comap (s.transitionMapSucc i) := by
  have hid : s.exceptionalDivisor i ^ μ * s.ideal (i + 1) = (s.ideal i).comap (s.transitionMapSucc i) := by
    rw [exceptionalDivisor_eq_exceptionalIdeal]
    exact s.ideal_succ i hi
  have hF : s.exceptionalDivisor i ^ m * s.exceptionalDivisor i ^ (μ - m) = s.exceptionalDivisor i ^ μ := by
    rw [← pow_add, Nat.add_sub_cancel' hm]
  calc s.exceptionalDivisor i ^ m *
          (Mi.comap (s.transitionMapSucc i) * s.exceptionalDivisor i ^ (μ - m) * s.ideal (i + 1))
      = Mi.comap (s.transitionMapSucc i) *
          ((s.exceptionalDivisor i ^ m * s.exceptionalDivisor i ^ (μ - m)) * s.ideal (i + 1)) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]
    _ = Mi.comap (s.transitionMapSucc i) * ((s.ideal i).comap (s.transitionMapSucc i)) := by rw [hF, hid]
    _ = Ci.comap (s.transitionMapSucc i) := by rw [h, Scheme.IdealSheafData.comap_mul]

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero`. Conclude with `(BlowupSequenceData.controlledTransform_zero ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData) I m).symm`. Consider the case `succ n ih`. Establish `h2` using `BlowupSequenceData.controlledTransform_succ ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData) I m n`.

Use `Eq.trans ?_ h2.symm` and prove the remaining obligations. Conclude with `congrArg (fun J : (s.schemeAt n).IdealSheafData => residualByPow (J.comap (s.transitionMapSucc n)) (s.exceptionalDivisor n) m) ih`.
-/
private theorem controlledTransform_eq_sequenceData (s : MarkedSequenceOfBlowups p N μ E)
    (I : X.IdealSheafData) (m i : ℕ) :
    MarkedSequenceOfBlowups.controlledTransform s I m i
      = ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData).controlledTransform I m i := by
  induction i with
  | zero =>
      exact (BlowupSequenceData.controlledTransform_zero ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData) I m).symm
  | succ n ih =>
      have h2 := BlowupSequenceData.controlledTransform_succ ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData) I m n
      refine Eq.trans ?_ h2.symm
      exact congrArg
        (fun J : (s.schemeAt n).IdealSheafData =>
          residualByPow (J.comap (s.transitionMapSucc n)) (s.exceptionalDivisor n) m) ih

/- English proof (translation)
The claim follows from `congrArg (fun J : (s.schemeAt i).IdealSheafData => J.comap (s.transitionMapSucc i)) (controlledTransform_eq_sequenceData s I m i)`.
-/
private theorem comap_controlledTransform_eq_comap_sequenceData (s : MarkedSequenceOfBlowups p N μ E)
    (I : X.IdealSheafData) (m i : ℕ) :
    (MarkedSequenceOfBlowups.controlledTransform s I m i).comap (s.transitionMapSucc i)
      = (((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData).controlledTransform I m i).comap
          (((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData).map i) :=
  congrArg (fun J : (s.schemeAt i).IdealSheafData => J.comap (s.transitionMapSucc i))
    (controlledTransform_eq_sequenceData s I m i)

/- English proof (translation)
Take `⟨Bd, hBd⟩` from `h`. Establish `hd` using `BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData) I m i ⟨Bd, hBd.trans (comap_controlledTransform_eq_comap_sequenceData s I m i)⟩`. Conclude with `(congrArg (fun J : (s.schemeAt (i + 1)).IdealSheafData => s.exceptionalDivisor i ^ m * J) (controlledTransform_eq_sequenceData s I m (i + 1))).trans (hd.trans (comap_controlledTransform_eq_comap_sequenceData s I m i).symm)`.
-/
private theorem exceptionalDivisor_pow_mul_controlledTransform_succ (s : MarkedSequenceOfBlowups p N μ E)
    (I : X.IdealSheafData) (m i : ℕ)
    (h : ∃ Bd, s.exceptionalDivisor i ^ m * Bd
        = (MarkedSequenceOfBlowups.controlledTransform s I m i).comap (s.transitionMapSucc i)) :
    s.exceptionalDivisor i ^ m * MarkedSequenceOfBlowups.controlledTransform s I m (i + 1)
      = (MarkedSequenceOfBlowups.controlledTransform s I m i).comap (s.transitionMapSucc i) := by
  obtain ⟨Bd, hBd⟩ := h
  have hd := BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData)
    I m i ⟨Bd, hBd.trans (comap_controlledTransform_eq_comap_sequenceData s I m i)⟩
  exact (congrArg (fun J : (s.schemeAt (i + 1)).IdealSheafData => s.exceptionalDivisor i ^ m * J)
      (controlledTransform_eq_sequenceData s I m (i + 1))).trans
    (hd.trans (comap_controlledTransform_eq_comap_sequenceData s I m i).symm)

/- English proof (translation)
The claim follows from `le_antisymm (hord i (le_of_lt hi) x) ((mem_orderAtLeastLocus_iff _ _ _).1 (s.center_order i hi hx))`.
-/
private theorem orderAt_eq_of_mem_center_support (s : MarkedSequenceOfBlowups p N μ E)
    (hord : ∀ i ≤ s.length, ∀ x : ↥(s.schemeAt i), orderAt (s.ideal i) x ≤ (μ : ℕ∞))
    (i : ℕ) (hi : i < s.length) (x : ↥(s.schemeAt i)) (hx : x ∈ (s.center i).support) :
    orderAt (s.ideal i) x = (μ : ℕ∞) :=
  le_antisymm (hord i (le_of_lt hi) x) ((mem_orderAtLeastLocus_iff _ _ _).1 (s.center_order i hi hx))

end

section

/- English proof (translation)
Establish `hECNC : EffectiveCartierSupportContainsNoComponent.{u}` using `effectiveCartierSupportContainsNoComponent`. Establish `hadm : (T.withIdealAndMult N μ).IsAdmissible` using `hT.withIdealAndMult hsplit hμ`. Establish `hsplit_all : ∀ j, j ≤ s.length → IsMonomialSplitting (s.boundary j) (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult j) (MarkedSequenceOfBlowups.monomialFactor s M T.mult j) (s.ideal j)`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero`. Introduce `_`. Rewrite using `[s.boundary_zero, s.ideal_zero]`. Conclude with `hsplit.comap_iso s.isoZero`. Consider the case `succ n ih`.

Introduce `hn`. Establish `hn' : n < s.length` using `hn`. Establish `hsp` using `ih (le_of_lt hn')`. Establish `hdiv : s.exceptionalDivisor n ^ T.mult * ((MarkedSequenceOfBlowups.monomialFactor s M T.mult n).comap (s.transitionMapSucc n) * s.exceptionalDivisor n ^ (μ - T.mult) * s.ideal (n + 1)) = (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult n).comap (s.transitionMapSucc n …` using `exceptionalDivisor_pow_mul_comap_mul_eq_comap s T.mult hμ n hn' _ _ hsp.eq_mul`. Establish `htw` using `exceptionalDivisor_pow_mul_controlledTransform_succ s T.ideal T.mult n ⟨_, hdiv⟩`.

Establish `heq : MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult (n + 1) = MarkedSequenceOfBlowups.monomialFactor s M T.mult (n + 1) * s.ideal (n + 1)`. Use `eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul (isLocallyGeneratedByNonZeroDivisor_exceptionalDivisor s n hn') T.mult ?_` and prove the remaining obligations. Rewrite using `[htw, ← hdiv]`. Simplify using `only [MarkedSequenceOfBlowups.monomialFactor_succ, mul_comm, mul_left_comm]`. Establish `hTn` using `MarkedIdealWithBoundary.IsAdmissible.transformAt hECNC hadm s n (le_of_lt hn')`.

Establish `hsm : AlgebraicGeometry.Smooth ((s.center n).subschemeι ≫ s.projectionToSpec n)`. Rewrite using `[MarkedSequenceOfBlowups.projectionToSpec_eq]`. Conclude with `s.center_smooth n hn'`. Establish `hsnc : HasStrictNormalCrossingsWith (s.projectionToSpec n) (s.center n) (s.boundary n)`. Rewrite using `[MarkedSequenceOfBlowups.projectionToSpec_eq]`.

Conclude with `s.center_snc n hn'`. Establish `hbl : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc n) (s.center n)` using `s.isBlowupAlongIdealSheaf_blowupMorphism n hn'`. Establish `hbnd : s.boundary (n + 1) = List.map (Blowup.strictTransform (s.transitionMapSucc n) (s.center n)) (s.boundary n) ++ [Blowup.exceptionalIdeal (s.transitionMapSucc n) (s.center n)]` using `s.boundary_succ n hn'`. Establish `hExcMem : Blowup.exceptionalIdeal (s.transitionMapSucc n) (s.center n) ∈ s.boundary (n + 1)`. Rewrite using `[hbnd]`.

Simplify using the standard rewrite rules. Establish `hExcMem' : s.exceptionalDivisor n ∈ s.boundary (n + 1)`. Rewrite using `[exceptionalDivisor_eq_exceptionalIdeal]`. Conclude with `hExcMem`. Establish `hSTmem : ∀ D₀ ∈ s.boundary n, Blowup.strictTransform (s.transitionMapSucc n) (s.center n) D₀ ∈ s.boundary (n + 1)`.

Introduce `D₀ hD₀`. Rewrite using `[hbnd]`. Conclude with `List.mem_append_left _ (List.mem_map.2 ⟨D₀, hD₀, rfl⟩)`. Establish `hfac : ∀ D₀ ∈ s.boundary n, ∀ x' : ↥(s.schemeAt (n + 1)), ∃ (U : (s.schemeAt (n + 1)).Opens) (ε : ℕ), x' ∈ U ∧ (D₀.comap (s.transitionMapSucc n)).comap U.ι = (Blowup.strictTransform (s.transitionMapSucc n) (s.center n) D₀).comap U.ι * (Blowup.exceptionalIdeal (s.transitionMapSucc …`. Introduce `D₀ hD₀ x'`.

Take `⟨U, ε, hxU, _, _, hEq⟩` from `hG.monomialInputs.blowup_total_transform _ hTn (s.center n) hsm hsnc _ (s.transitionMapSucc n) hbl D₀ hD₀ x'`. Conclude with `⟨U, ε, hxU, hEq⟩`. Establish `hmonD : ∀ D₀ ∈ s.boundary n, IsMonomialIn (s.boundary (n + 1)) (D₀.comap (s.transitionMapSucc n))`. Introduce `D₀ hD₀`. Conclude with `isMonomialIn_of_locally_eq_mul_pow _ _ _ _ (hSTmem D₀ hD₀) hExcMem (hfac D₀ hD₀)`.

Establish `hmonM : IsMonomialIn (s.boundary (n + 1)) ((MarkedSequenceOfBlowups.monomialFactor s M T.mult n).comap (s.transitionMapSucc n))`. Use `isMonomialIn_of_forall_mem ?_ (hsp.monomial.comap (s.transitionMapSucc n))` and prove the remaining obligations. Introduce `D hD`. Take `⟨D₀, hD₀, rfl⟩` from `List.mem_map.1 hD`. Conclude with `hmonD D₀ hD₀`.

Use `⟨heq, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[MarkedSequenceOfBlowups.monomialFactor_succ]`. Break down `support_mul_subset _ _ hx with hx1 | hx2` into its components or cases. Rewrite `hx1` using `[support_comap_coe]`.

Take `⟨D₀, hD₀, hxD⟩` from `Set.mem_iUnion₂.1 (hsp.monomial_support hx1)`. Establish `hx' : x ∈ (↑((D₀.comap (s.transitionMapSucc n))).support : Set ↥(s.schemeAt (n + 1)))`. Rewrite using `[support_comap_coe]`. Conclude with `hxD`. Break down `support_subset_union_of_locally_eq_mul_pow _ _ _ (hfac D₀ hD₀) hx' with h1 | h2` into its components or cases.

Conclude with `Set.mem_iUnion₂.2 ⟨_, hSTmem D₀ hD₀, h1⟩`. Conclude with `Set.mem_iUnion₂.2 ⟨_, hExcMem, h2⟩`. Conclude with `Set.mem_iUnion₂.2 ⟨_, hExcMem', support_pow_subset _ _ hx2⟩`. Rewrite using `[MarkedSequenceOfBlowups.monomialFactor_succ]`. Conclude with `isMonomialIn_mul _ hmonM (isMonomialIn_pow _ (isMonomialIn_of_mem hExcMem') _)`.

Introduce `D hD C hCirr hCsubD hCmax hCsub`. Rewrite `hD` using `[hbnd]`. Break down `List.mem_append.1 hD with hD' | hD'` into its components or cases. Take `⟨D₀, hD₀, rfl⟩` from `List.mem_map.1 hD'`. Take `⟨η', C0, hCeq, _, hC0comp, _, hC0eq⟩` from `hG.strictTransform_components _ hTn (s.center n) hsm hsnc _ (s.transitionMapSucc n) hbl D₀ hD₀ C (isIrreducibleComponentOf_of_maximal hCirr hCsubD hCmax)`.

Take `⟨hc1, hc2, hc3⟩` from `isIrreducible_subset_maximal_of_isIrreducibleComponentOf hC0comp`. Establish `hηC : η' ∈ C`. Rewrite using `[hCeq]`. Conclude with `subset_closure (Set.mem_singleton η')`. Establish `h2 : η' ∈ (↑((s.ideal n).comap (s.transitionMapSucc n)).support : Set ↥(s.schemeAt (n + 1)))`.

Rewrite using `[← s.ideal_succ n hn']`. Conclude with `support_subset_support_mul_right _ _ (hCsub hηC)`. Rewrite `h2` using `[support_comap_coe]`. Establish `hsub0 : C0 ⊆ (↑(s.ideal n).support : Set ↥(s.schemeAt n))`. Rewrite using `[hC0eq]`.

Conclude with `closure_minimal (Set.singleton_subset_iff.2 h2) (s.ideal n).support.2`. Conclude with `hsp.transversal D₀ hD₀ C0 hc1 hc2 hc3 hsub0`. Rewrite `hD'` using `[List.mem_singleton]`. Substitute `hD'` using the available equality. Conclude with `hG.exceptional_components_not_subset _ hTn (s.center n) hsm hsnc _ (s.transitionMapSucc n) hbl (s.ideal n) μ (orderAt_eq_of_mem_center_support s hord n hn') (s.ideal (n + 1)) (s.ideal_succ n hn') C (isIrreducibleComponentOf_of_maximal hCirr hCsubD hCmax) hCsub`.

Use `⟨hsplit_all i hi, ?_⟩` and prove the remaining obligations. Introduce `hilt`. Use `⟨fun x hx => orderAt_eq_of_mem_center_support s hord i hilt x hx, ?_, ?_⟩` and prove the remaining obligations. Use `subset_orderAtLeastLocus_of_eq_mul _ _ _ (hsplit_all i hi).eq_mul T.mult _ ?_` and prove the remaining obligations. Introduce `x hx`.

Conclude with `orderAtLeastLocus_subset_of_le (s.ideal i) hμ (s.center_order i hilt hx)`. Conclude with `⟨_, exceptionalDivisor_pow_mul_comap_mul_eq_comap s T.mult hμ i hilt _ _ (hsplit_all i hi).eq_mul⟩`.
-/
theorem isMonomialSplitting_controlledTransform_monomialFactor (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    {M N : T.scheme.IdealSheafData} (hsplit : IsMonomialSplitting T.boundary T.ideal M N)
    {μ : ℕ} (hμ : T.mult ≤ μ) (s : MarkedSequenceOfBlowups T.structMap N μ T.boundary)
    (hord : ∀ i ≤ s.length, ∀ x : ↥(s.schemeAt i), orderAt (s.ideal i) x ≤ (μ : ℕ∞))
    (i : ℕ) (hi : i ≤ s.length) :
    IsMonomialSplitting (s.boundary i) (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i)
        (MarkedSequenceOfBlowups.monomialFactor s M T.mult i) (s.ideal i) ∧
      (i < s.length →
        (∀ x ∈ (s.center i).support, orderAt (s.ideal i) x = (μ : ℕ∞)) ∧
        (↑(s.center i).support : Set ↥(s.schemeAt i)) ⊆
          orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i) T.mult ∧
        ∃ Bd : (s.schemeAt (i + 1)).IdealSheafData,
          s.exceptionalDivisor i ^ T.mult * Bd =
            (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i).comap (s.transitionMapSucc i)) := by
  have hECNC : EffectiveCartierSupportContainsNoComponent.{u} := effectiveCartierSupportContainsNoComponent
  have hadm : (T.withIdealAndMult N μ).IsAdmissible := hT.withIdealAndMult hsplit hμ
  have hsplit_all : ∀ j, j ≤ s.length →
      IsMonomialSplitting (s.boundary j) (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult j)
        (MarkedSequenceOfBlowups.monomialFactor s M T.mult j) (s.ideal j) := by
    intro j
    induction j with
    | zero =>
        intro _
        rw [s.boundary_zero, s.ideal_zero]
        exact hsplit.comap_iso s.isoZero
    | succ n ih =>
        intro hn
        have hn' : n < s.length := hn
        have hsp := ih (le_of_lt hn')
        have hdiv : s.exceptionalDivisor n ^ T.mult *
            ((MarkedSequenceOfBlowups.monomialFactor s M T.mult n).comap (s.transitionMapSucc n)
              * s.exceptionalDivisor n ^ (μ - T.mult) * s.ideal (n + 1))
            = (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult n).comap (s.transitionMapSucc n) :=
          exceptionalDivisor_pow_mul_comap_mul_eq_comap s T.mult hμ n hn' _ _ hsp.eq_mul
        have htw := exceptionalDivisor_pow_mul_controlledTransform_succ s T.ideal T.mult n ⟨_, hdiv⟩
        have heq : MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult (n + 1)
            = MarkedSequenceOfBlowups.monomialFactor s M T.mult (n + 1) * s.ideal (n + 1) := by
          refine eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul (isLocallyGeneratedByNonZeroDivisor_exceptionalDivisor s n hn')
            T.mult ?_
          rw [htw, ← hdiv]
          simp only [MarkedSequenceOfBlowups.monomialFactor_succ, mul_comm, mul_left_comm]
        have hTn := MarkedIdealWithBoundary.IsAdmissible.transformAt hECNC hadm s n (le_of_lt hn')
        have hsm : AlgebraicGeometry.Smooth ((s.center n).subschemeι ≫ s.projectionToSpec n) := by
          rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
          exact s.center_smooth n hn'
        have hsnc : HasStrictNormalCrossingsWith (s.projectionToSpec n) (s.center n) (s.boundary n) := by
          rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
          exact s.center_snc n hn'
        have hbl : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc n) (s.center n) := s.isBlowupAlongIdealSheaf_blowupMorphism n hn'
        have hbnd : s.boundary (n + 1) =
            List.map (Blowup.strictTransform (s.transitionMapSucc n) (s.center n)) (s.boundary n) ++
              [Blowup.exceptionalIdeal (s.transitionMapSucc n) (s.center n)] := s.boundary_succ n hn'
        have hExcMem : Blowup.exceptionalIdeal (s.transitionMapSucc n) (s.center n) ∈ s.boundary (n + 1) := by
          rw [hbnd]
          simp
        have hExcMem' : s.exceptionalDivisor n ∈ s.boundary (n + 1) := by
          rw [exceptionalDivisor_eq_exceptionalIdeal]
          exact hExcMem
        have hSTmem : ∀ D₀ ∈ s.boundary n,
            Blowup.strictTransform (s.transitionMapSucc n) (s.center n) D₀ ∈ s.boundary (n + 1) := by
          intro D₀ hD₀
          rw [hbnd]
          exact List.mem_append_left _ (List.mem_map.2 ⟨D₀, hD₀, rfl⟩)
        have hfac : ∀ D₀ ∈ s.boundary n, ∀ x' : ↥(s.schemeAt (n + 1)),
            ∃ (U : (s.schemeAt (n + 1)).Opens) (ε : ℕ), x' ∈ U ∧
              (D₀.comap (s.transitionMapSucc n)).comap U.ι =
                (Blowup.strictTransform (s.transitionMapSucc n) (s.center n) D₀).comap U.ι *
                  (Blowup.exceptionalIdeal (s.transitionMapSucc n) (s.center n)).comap U.ι ^ ε := by
          intro D₀ hD₀ x'
          obtain ⟨U, ε, hxU, _, _, hEq⟩ :=
            hG.monomialInputs.blowup_total_transform _ hTn (s.center n) hsm hsnc _
              (s.transitionMapSucc n) hbl D₀ hD₀ x'
          exact ⟨U, ε, hxU, hEq⟩
        have hmonD : ∀ D₀ ∈ s.boundary n,
            IsMonomialIn (s.boundary (n + 1)) (D₀.comap (s.transitionMapSucc n)) := by
          intro D₀ hD₀
          exact isMonomialIn_of_locally_eq_mul_pow _ _ _ _ (hSTmem D₀ hD₀) hExcMem (hfac D₀ hD₀)
        have hmonM : IsMonomialIn (s.boundary (n + 1))
            ((MarkedSequenceOfBlowups.monomialFactor s M T.mult n).comap (s.transitionMapSucc n)) := by
          refine isMonomialIn_of_forall_mem ?_ (hsp.monomial.comap (s.transitionMapSucc n))
          intro D hD
          obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD
          exact hmonD D₀ hD₀
        refine ⟨heq, ?_, ?_, ?_⟩
        · intro x hx
          rw [MarkedSequenceOfBlowups.monomialFactor_succ] at hx
          rcases support_mul_subset _ _ hx with hx1 | hx2
          · rw [support_comap_coe] at hx1
            obtain ⟨D₀, hD₀, hxD⟩ := Set.mem_iUnion₂.1 (hsp.monomial_support hx1)
            have hx' : x ∈ (↑((D₀.comap (s.transitionMapSucc n))).support : Set ↥(s.schemeAt (n + 1))) := by
              rw [support_comap_coe]
              exact hxD
            rcases support_subset_union_of_locally_eq_mul_pow _ _ _ (hfac D₀ hD₀) hx' with h1 | h2
            · exact Set.mem_iUnion₂.2 ⟨_, hSTmem D₀ hD₀, h1⟩
            · exact Set.mem_iUnion₂.2 ⟨_, hExcMem, h2⟩
          · exact Set.mem_iUnion₂.2 ⟨_, hExcMem', support_pow_subset _ _ hx2⟩
        · rw [MarkedSequenceOfBlowups.monomialFactor_succ]
          exact isMonomialIn_mul _ hmonM (isMonomialIn_pow _ (isMonomialIn_of_mem hExcMem') _)
        · intro D hD C hCirr hCsubD hCmax hCsub
          rw [hbnd] at hD
          rcases List.mem_append.1 hD with hD' | hD'
          · obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD'
            obtain ⟨η', C0, hCeq, _, hC0comp, _, hC0eq⟩ :=
              hG.strictTransform_components _ hTn (s.center n) hsm hsnc _ (s.transitionMapSucc n) hbl
                D₀ hD₀ C (isIrreducibleComponentOf_of_maximal hCirr hCsubD hCmax)
            obtain ⟨hc1, hc2, hc3⟩ := isIrreducible_subset_maximal_of_isIrreducibleComponentOf hC0comp
            have hηC : η' ∈ C := by
              rw [hCeq]
              exact subset_closure (Set.mem_singleton η')
            have h2 : η' ∈
                (↑((s.ideal n).comap (s.transitionMapSucc n)).support : Set ↥(s.schemeAt (n + 1))) := by
              rw [← s.ideal_succ n hn']
              exact support_subset_support_mul_right _ _ (hCsub hηC)
            rw [support_comap_coe] at h2
            have hsub0 : C0 ⊆ (↑(s.ideal n).support : Set ↥(s.schemeAt n)) := by
              rw [hC0eq]
              exact closure_minimal (Set.singleton_subset_iff.2 h2) (s.ideal n).support.2
            exact hsp.transversal D₀ hD₀ C0 hc1 hc2 hc3 hsub0
          · rw [List.mem_singleton] at hD'
            subst hD'
            exact hG.exceptional_components_not_subset _ hTn (s.center n) hsm hsnc _
              (s.transitionMapSucc n) hbl (s.ideal n) μ (orderAt_eq_of_mem_center_support s hord n hn')
              (s.ideal (n + 1)) (s.ideal_succ n hn') C (isIrreducibleComponentOf_of_maximal hCirr hCsubD hCmax) hCsub
  refine ⟨hsplit_all i hi, ?_⟩
  intro hilt
  refine ⟨fun x hx => orderAt_eq_of_mem_center_support s hord i hilt x hx, ?_, ?_⟩
  · refine subset_orderAtLeastLocus_of_eq_mul _ _ _ (hsplit_all i hi).eq_mul T.mult _ ?_
    intro x hx
    exact orderAtLeastLocus_subset_of_le (s.ideal i) hμ (s.center_order i hilt hx)
  · exact ⟨_, exceptionalDivisor_pow_mul_comap_mul_eq_comap s T.mult hμ i hilt _ _ (hsplit_all i hi).eq_mul⟩

/- English proof (translation)
Establish `hself` using `(MarkedBlowupSequenceData.ofMarkedSequence s).isMarked_toBlowupSequenceData`. Use `⟨?_, ?_, hself.center_smooth, hself.center_snc⟩` and prove the remaining obligations. Introduce `i hi`. Establish `hi' : i < s.length` using `hi`. Take `⟨Bd, hBd⟩` from `((isMonomialSplitting_controlledTransform_monomialFactor hG hT hsplit hμ s hord i (le_of_lt hi')).2 hi').2.2`.

Conclude with `⟨Bd, hBd.trans (comap_controlledTransform_eq_comap_sequenceData s T.ideal T.mult i)⟩`. Introduce `i hi`. Establish `hi' : i < s.length` using `hi`. Establish `hsub` using `((isMonomialSplitting_controlledTransform_monomialFactor hG hT hsplit hμ s hord i (le_of_lt hi')).2 hi').2.1`. Introduce `x hx`.

Establish `h1 : (T.mult : ℕ∞) ≤ orderAt (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i) x` using `(mem_orderAtLeastLocus_iff _ _ _).1 (hsub hx)`. Establish `he : orderAt (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i) x = orderAt (((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData).controlledTransform T.ideal T.mult i) x` using `congrArg (fun J : (s.schemeAt i).IdealSheafData => orderAt J x) (controlledTransform_eq_sequenceData s T.ideal T.mult i)`. Conclude with `(mem_orderAtLeastLocus_iff _ _ _).2 (he ▸ h1)`.
-/
theorem isMarked_sequenceData_of_orderAt_le (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) {M N : T.scheme.IdealSheafData}
    (hsplit : IsMonomialSplitting T.boundary T.ideal M N)
    {μ : ℕ} (hμ : T.mult ≤ μ) (s : MarkedSequenceOfBlowups T.structMap N μ T.boundary)
    (hord : ∀ i ≤ s.length, ∀ x : ↥(s.schemeAt i), orderAt (s.ideal i) x ≤ (μ : ℕ∞)) :
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.IsMarked T.structMap T.ideal T.mult
      T.boundary := by
  have hself := (MarkedBlowupSequenceData.ofMarkedSequence s).isMarked_toBlowupSequenceData
  refine ⟨?_, ?_, hself.center_smooth, hself.center_snc⟩
  · intro i hi
    have hi' : i < s.length := hi
    obtain ⟨Bd, hBd⟩ := ((isMonomialSplitting_controlledTransform_monomialFactor hG hT hsplit hμ s hord i (le_of_lt hi')).2 hi').2.2
    exact ⟨Bd, hBd.trans (comap_controlledTransform_eq_comap_sequenceData s T.ideal T.mult i)⟩
  · intro i hi
    have hi' : i < s.length := hi
    have hsub := ((isMonomialSplitting_controlledTransform_monomialFactor hG hT hsplit hμ s hord i (le_of_lt hi')).2 hi').2.1
    intro x hx
    have h1 : (T.mult : ℕ∞) ≤ orderAt (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i) x :=
      (mem_orderAtLeastLocus_iff _ _ _).1 (hsub hx)
    have he : orderAt (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i) x
        = orderAt (((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData).controlledTransform T.ideal T.mult i) x :=
      congrArg (fun J : (s.schemeAt i).IdealSheafData => orderAt J x)
        (controlledTransform_eq_sequenceData s T.ideal T.mult i)
    exact (mem_orderAtLeastLocus_iff _ _ _).2 (he ▸ h1)

/- English proof (translation)
Establish `hsp` using `(isMonomialSplitting_controlledTransform_monomialFactor hG hT hsplit hμ s hord i (le_of_lt hi)).1`. Establish `hMsub : (↑(MarkedSequenceOfBlowups.monomialFactor s M T.mult i).support : Set ↥(s.schemeAt i)) ⊆ s.boundaryLocus i`. Introduce `x hx`. Take `⟨D, hD, hxD⟩` from `Set.mem_iUnion₂.1 (hsp.monomial_support hx)`. Conclude with `(MarkedSequenceOfBlowups.mem_boundaryLocus_iff s i x).2 ⟨D, hD, hxD⟩`.

Conclude with `PrincipalizationCertificate.toOrder (MarkedSequenceOfBlowups.monomialFactor s M T.mult i) (s.ideal i) μ hsp.eq_mul hMsub hμ (s.center_order i hi) (hcert i hi)`.
-/
theorem principalizationCertificate_controlledTransform (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    {M N : T.scheme.IdealSheafData} (hsplit : IsMonomialSplitting T.boundary T.ideal M N)
    {μ : ℕ} (hμ : T.mult ≤ μ) (s : MarkedSequenceOfBlowups T.structMap N μ T.boundary)
    (hord : ∀ i ≤ s.length, ∀ x : ↥(s.schemeAt i), orderAt (s.ideal i) x ≤ (μ : ℕ∞))
    (hcert : ∀ i < s.length,
      OrderCertificate (s.schemeAt i) (s.projectionToSpec i) (s.ideal i) μ (s.boundaryLocus i) (s.center i))
    (i : ℕ) (hi : i < s.length) :
    PrincipalizationCertificate (s.schemeAt i) (s.projectionToSpec i) (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i) T.mult
      (s.boundaryLocus i) (s.center i) := by
  have hsp := (isMonomialSplitting_controlledTransform_monomialFactor hG hT hsplit hμ s hord i (le_of_lt hi)).1
  have hMsub : (↑(MarkedSequenceOfBlowups.monomialFactor s M T.mult i).support : Set ↥(s.schemeAt i)) ⊆
      s.boundaryLocus i := by
    intro x hx
    obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 (hsp.monomial_support hx)
    exact (MarkedSequenceOfBlowups.mem_boundaryLocus_iff s i x).2 ⟨D, hD, hxD⟩
  exact PrincipalizationCertificate.toOrder (MarkedSequenceOfBlowups.monomialFactor s M T.mult i) (s.ideal i) μ hsp.eq_mul
    hMsub hμ (s.center_order i hi) (hcert i hi)

/- English proof (translation)
The claim follows from `maxOrder_lt_of_orderAtLeastLocus_eq_empty (s.ideal s.length) (hord s.length le_rfl) hμ hempty`.
-/
theorem maxOrder_ideal_length_lt_of_orderAtLeastLocus_eq_empty {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {N : X.IdealSheafData} {μ : ℕ}
    {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p N μ E)
    (hord : ∀ i ≤ s.length, ∀ x : ↥(s.schemeAt i), orderAt (s.ideal i) x ≤ (μ : ℕ∞))
    (hempty : orderAtLeastLocus (s.ideal s.length) μ = ∅) (hμ : 1 ≤ μ) :
    maxOrder (s.ideal s.length) < μ :=
  maxOrder_lt_of_orderAtLeastLocus_eq_empty (s.ideal s.length) (hord s.length le_rfl) hμ hempty

end

section

/- English proof (translation)
Break down `eq_or_ne a ⊤ with rfl | hne` into its components or cases. Conclude with `le_top`. Take `⟨n, rfl⟩` from `ENat.ne_top_iff_exists.mp hne`. Establish `h' : m ≤ n + s` using `by exact_mod_cast h`. Establish `h'' : m - s ≤ n` using `by omega`.

Conclude with `h''` after adjusting the coercions.
-/
private theorem cast_sub_le_of_cast_le_add {a : ℕ∞} {m s : ℕ}
    (h : (m : ℕ∞) ≤ a + (s : ℕ∞)) : ((m - s : ℕ) : ℕ∞) ≤ a := by
  rcases eq_or_ne a ⊤ with rfl | hne
  · exact le_top
  · obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hne
    have h' : m ≤ n + s := by exact_mod_cast h
    have h'' : m - s ≤ n := by omega
    exact_mod_cast h''

/- English proof (translation)
Break down `Nat.lt_or_ge sdeg m with hms | hms` into its components or cases. Use `hT.charZero` as an intermediate fact. Use `hT.smooth` as an intermediate fact. Establish `: AlgebraicGeometry.IsNoetherian T.scheme` using `hT.isNoetherian`. Establish `: AlgebraicGeometry.IsNoetherian X'` using `isNoetherian_of_isBlowupAlongIdealSheaf hbl`.

Establish `hsub : (↑Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus Mon (m - sdeg)`. Introduce `x hx`. Use `(mem_orderAtLeastLocus_iff Mon (m - sdeg) x).2 ?_` and prove the remaining obligations. Establish `h1 : (m : ℕ∞) ≤ orderAt Bd x` using `(mem_orderAtLeastLocus_iff Bd m x).1 (hZsub hx)`. Rewrite `h1` using `[hsplit.orderAt_eq_add T.structMap x, hordA x hx]`.

Conclude with `cast_sub_le_of_cast_le_add h1`. Establish `hle : Mon ≤ Z ^ (m - sdeg)` using `le_pow_of_hasStrictNormalCrossingsWith T.structMap Z Mon T.boundary hsnc (m - sdeg) hsub`. Take `⟨C, hC, -⟩` from `existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf π Z Mon (m - sdeg) hbl hle`. Use `⟨C, ?_⟩` and prove the remaining obligations. Establish `hms' : m - sdeg + sdeg = m` using `Nat.sub_add_cancel hms.le`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_add, hms']`. Use `_ = Blowup.exceptionalIdeal π Z ^ (m - sdeg) * C * Blowup.exceptionalIdeal π Z ^ sdeg := by`. Simplify using `only [mul_comm, mul_left_comm]`. Use `_ = Mon.comap π * Blowup.exceptionalIdeal π Z ^ sdeg := by rw [hC]`.

Use `⟨Mon.comap π * Blowup.exceptionalIdeal π Z ^ (sdeg - m), ?_⟩` and prove the remaining obligations. Establish `hpow : Blowup.exceptionalIdeal π Z ^ m * Blowup.exceptionalIdeal π Z ^ (sdeg - m) = Blowup.exceptionalIdeal π Z ^ sdeg`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hms]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc, mul_comm]`.

Use `_ = Mon.comap π * Blowup.exceptionalIdeal π Z ^ sdeg := by rw [hpow]`.
-/
theorem exists_exceptionalIdeal_pow_mul_eq_comap_mul_pow (_hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (Z : T.scheme.IdealSheafData)
    (_hsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap))
    (hsnc : HasStrictNormalCrossingsWith T.structMap Z T.boundary)
    (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (hbl : Blowup.IsBlowupAlongIdealSheaf π Z)
    (Bd Mon Ad : T.scheme.IdealSheafData) (m sdeg : ℕ)
    (hsplit : IsMonomialSplitting T.boundary Bd Mon Ad)
    (hZsub : (↑Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus Bd m)
    (hordA : ∀ x ∈ Z.support, orderAt Ad x = (sdeg : ℕ∞))
    (B' : X'.IdealSheafData) (_hB' : Blowup.exceptionalIdeal π Z ^ m * B' = Bd.comap π)
    (A' : X'.IdealSheafData) (_hA' : Blowup.exceptionalIdeal π Z ^ sdeg * A' = Ad.comap π) :
    ∃ C : X'.IdealSheafData,
      Blowup.exceptionalIdeal π Z ^ m * C = Mon.comap π * Blowup.exceptionalIdeal π Z ^ sdeg := by
  rcases Nat.lt_or_ge sdeg m with hms | hms
  · have := hT.charZero
    have := hT.smooth
    have : AlgebraicGeometry.IsNoetherian T.scheme := hT.isNoetherian
    have : AlgebraicGeometry.IsNoetherian X' := isNoetherian_of_isBlowupAlongIdealSheaf hbl
    have hsub : (↑Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus Mon (m - sdeg) := by
      intro x hx
      refine (mem_orderAtLeastLocus_iff Mon (m - sdeg) x).2 ?_
      have h1 : (m : ℕ∞) ≤ orderAt Bd x := (mem_orderAtLeastLocus_iff Bd m x).1 (hZsub hx)
      rw [hsplit.orderAt_eq_add T.structMap x, hordA x hx] at h1
      exact cast_sub_le_of_cast_le_add h1
    have hle : Mon ≤ Z ^ (m - sdeg) :=
      le_pow_of_hasStrictNormalCrossingsWith T.structMap Z Mon T.boundary hsnc (m - sdeg) hsub
    obtain ⟨C, hC, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf π Z Mon (m - sdeg) hbl hle
    refine ⟨C, ?_⟩
    have hms' : m - sdeg + sdeg = m := Nat.sub_add_cancel hms.le
    calc Blowup.exceptionalIdeal π Z ^ m * C
        = Blowup.exceptionalIdeal π Z ^ (m - sdeg) * Blowup.exceptionalIdeal π Z ^ sdeg * C := by
          rw [← pow_add, hms']
      _ = Blowup.exceptionalIdeal π Z ^ (m - sdeg) * C * Blowup.exceptionalIdeal π Z ^ sdeg := by
          simp only [mul_comm, mul_left_comm]
      _ = Mon.comap π * Blowup.exceptionalIdeal π Z ^ sdeg := by rw [hC]
  · refine ⟨Mon.comap π * Blowup.exceptionalIdeal π Z ^ (sdeg - m), ?_⟩
    have hpow : Blowup.exceptionalIdeal π Z ^ m * Blowup.exceptionalIdeal π Z ^ (sdeg - m)
        = Blowup.exceptionalIdeal π Z ^ sdeg := by
      rw [← pow_add, Nat.add_sub_cancel' hms]
    calc Blowup.exceptionalIdeal π Z ^ m * (Mon.comap π * Blowup.exceptionalIdeal π Z ^ (sdeg - m))
        = Mon.comap π * (Blowup.exceptionalIdeal π Z ^ m * Blowup.exceptionalIdeal π Z ^ (sdeg - m)) := by
          simp only [mul_assoc, mul_comm]
      _ = Mon.comap π * Blowup.exceptionalIdeal π Z ^ sdeg := by rw [hpow]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_closeds_compl_iff {Y : Scheme.{u}} (S : TopologicalSpace.Closeds ↥Y)
    (x : ↥Y) : x ∈ S.compl ↔ x ∉ S := Iff.rfl

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.one_eq_top]`. Conclude with `Blowup.comap_eq_top_of_notMem_support U.ι I (fun y => h y.1 y.2)`.
-/
private theorem comap_eq_one_of_forall_notMem_support {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (U : Y.Opens) (h : ∀ x : ↥Y, x ∈ U → x ∉ (↑I.support : Set ↥Y)) : I.comap U.ι = 1 := by
  rw [Scheme.IdealSheafData.one_eq_top]
  exact Blowup.comap_eq_top_of_notMem_support U.ι I (fun y => h y.1 y.2)

/- English proof (translation)
Establish `h` using `orderAt_comap_of_isOpenImmersion U.ι I ⟨x, hx⟩`. Simplify using `using h`.
-/
private theorem orderAt_comap_opens_ι {Y : Scheme.{u}} (U : Y.Opens) (I : Y.IdealSheafData)
    (x : ↥Y) (hx : x ∈ U) : orderAt (I.comap U.ι) ⟨x, hx⟩ = orderAt I x := by
  have h := orderAt_comap_of_isOpenImmersion U.ι I ⟨x, hx⟩
  simpa using h

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Rewrite using `[List.prod_nil, List.map_nil, List.prod_nil]`. Conclude with `comap_one f`.

Consider the case `cons D L ih`. Rewrite using `[List.prod_cons, Scheme.IdealSheafData.comap_mul, ih, List.map_cons, List.prod_cons]`.
-/
private theorem comap_list_prod {A B : Scheme.{u}} (f : A ⟶ B) :
    ∀ L : List B.IdealSheafData,
      (L.prod).comap f = (L.map (fun D : B.IdealSheafData => D.comap f)).prod := by
  intro L
  induction L with
  | nil =>
      rw [List.prod_nil, List.map_nil, List.prod_nil]
      exact comap_one f
  | cons D L ih =>
      rw [List.prod_cons, Scheme.IdealSheafData.comap_mul, ih, List.map_cons, List.prod_cons]

/- English proof (translation)
Proceed by induction on `hy using Submonoid.closure_induction with`. Consider the case `mem a ha`. Take `⟨D, hD, rfl⟩` from `ha`. Use `⟨[D], ?_, ?_⟩` and prove the remaining obligations. Introduce `D' hD'`.

Rewrite using `[List.mem_singleton.1 hD']`. Conclude with `hD`. Simplify using the standard rewrite rules. Consider the case `one => exact ⟨[], by simp, by simp⟩`. Consider the case `mul a b _ _ iha ihb`.

Take `⟨L1, h1, e1⟩` from `iha`. Take `⟨L2, h2, e2⟩` from `ihb`. Use `⟨L1 ++ L2, ?_, ?_⟩` and prove the remaining obligations. Introduce `D hD`. Break down `List.mem_append.1 hD with h | h` into its components or cases.

Conclude with `h1 D h`. Conclude with `h2 D h`. Rewrite using `[e1, e2, List.map_append, List.prod_append]`.
-/
private theorem exists_list_prod_eq_of_mem_closure {A B : Scheme.{u}} (f : A ⟶ B)
    (E : List B.IdealSheafData) {y : A.IdealSheafData}
    (hy : y ∈ Submonoid.closure ((fun D : B.IdealSheafData => D.comap f) '' {D | D ∈ E})) :
    ∃ L : List B.IdealSheafData, (∀ D ∈ L, D ∈ E) ∧
      y = (L.map (fun D : B.IdealSheafData => D.comap f)).prod := by
  induction hy using Submonoid.closure_induction with
  | mem a ha =>
      obtain ⟨D, hD, rfl⟩ := ha
      refine ⟨[D], ?_, ?_⟩
      · intro D' hD'
        rw [List.mem_singleton.1 hD']
        exact hD
      · simp
  | one => exact ⟨[], by simp, by simp⟩
  | mul a b _ _ iha ihb =>
      obtain ⟨L1, h1, e1⟩ := iha
      obtain ⟨L2, h2, e2⟩ := ihb
      refine ⟨L1 ++ L2, ?_, ?_⟩
      · intro D hD
        rcases List.mem_append.1 hD with h | h
        · exact h1 D h
        · exact h2 D h
      · rw [e1, e2, List.map_append, List.prod_append]

/- English proof (translation)
Use `⟨hne, ?_⟩` and prove the remaining obligations. Introduce `u v hu hv hsu hsv`. Take `⟨a, ha, hau⟩` from `hsu`. Take `⟨b, hb, hbv⟩` from `hsv`. Take `⟨c, hcS, hc⟩` from `hS.2 (u ∩ O) (v ∩ O) (hu.inter hO) (hv.inter hO) ⟨a, ha.1, hau, ha.2⟩ ⟨b, hb.1, hbv, hb.2⟩`.

Conclude with `⟨c, ⟨hcS, hc.1.2⟩, hc.1.1, hc.2.1⟩`.
-/
private theorem isIrreducible_inter_isOpen {α : Type u} [TopologicalSpace α] {S O : Set α}
    (hS : IsIrreducible S) (hO : IsOpen O) (hne : (S ∩ O).Nonempty) :
    IsIrreducible (S ∩ O) := by
  refine ⟨hne, ?_⟩
  intro u v hu hv hsu hsv
  obtain ⟨a, ha, hau⟩ := hsu
  obtain ⟨b, hb, hbv⟩ := hsv
  obtain ⟨c, hcS, hc⟩ :=
    hS.2 (u ∩ O) (v ∩ O) (hu.inter hO) (hv.inter hO) ⟨a, ha.1, hau, ha.2⟩ ⟨b, hb.1, hbv, hb.2⟩
  exact ⟨c, ⟨hcS, hc.1.2⟩, hc.1.1, hc.2.1⟩

/- English proof (translation)
Take `⟨η, hη⟩` from `QuasiSober.sober hS.closure isClosed_closure`. Conclude with `⟨η, hη⟩`.
-/
private theorem exists_closure_singleton_eq_closure (X : Scheme.{u}) {S : Set ↥X}
    (hS : IsIrreducible S) : ∃ η : ↥X, closure ({η} : Set ↥X) = closure S := by
  obtain ⟨η, hη⟩ := QuasiSober.sober hS.closure isClosed_closure
  exact ⟨η, hη⟩

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `h1 : closure ({η} : Set α) ⊆ Oᶜ` using `closure_minimal (Set.singleton_subset_iff.2 hx) hO.isClosed_compl`. Rewrite `h1` using `[hη]`. Take `⟨a, haS, haO⟩` from `hne`. Conclude with `(h1 (subset_closure haS)) haO`.
-/
private theorem mem_of_isOpen_of_closure_singleton_eq {α : Type u} [TopologicalSpace α] {S : Set α}
    {η : α} (hη : closure ({η} : Set α) = closure S) {O : Set α} (hO : IsOpen O)
    (hne : (S ∩ O).Nonempty) : η ∈ O := by
  by_contra hx
  have h1 : closure ({η} : Set α) ⊆ Oᶜ :=
    closure_minimal (Set.singleton_subset_iff.2 hx) hO.isClosed_compl
  rw [hη] at h1
  obtain ⟨a, haS, haO⟩ := hne
  exact (h1 (subset_closure haS)) haO

/- English proof (translation)
Establish `h1 : closure ({η} : Set α) ⊆ F` using `closure_minimal (Set.singleton_subset_iff.2 hmem) hF`. Rewrite `h1` using `[hη]`. Conclude with `fun a ha => h1 (subset_closure ha)`.
-/
private theorem subset_of_closure_singleton_eq_closure {α : Type u} [TopologicalSpace α]
    {S : Set α} {η : α} (hη : closure ({η} : Set α) = closure S) {F : Set α} (hF : IsClosed F)
    (hmem : η ∈ F) : S ⊆ F := by
  have h1 : closure ({η} : Set α) ⊆ F := closure_minimal (Set.singleton_subset_iff.2 hmem) hF
  rw [hη] at h1
  exact fun a ha => h1 (subset_closure ha)

/- English proof (translation)
Rewrite using `[AlgebraicGeometry.isNoetherian_Spec]`. Use `infer_instance`.
-/
private theorem isNoetherian_spec_field (k : Type u) [Field k] :
    AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of k)) := by
  rw [AlgebraicGeometry.isNoetherian_Spec]
  infer_instance

/- English proof (translation)
Use `hsm` as an intermediate fact. Use `hT.quasiCompact` as an intermediate fact. Establish `: AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of T.base))` using `isNoetherian_spec_field T.base`. Establish `: AlgebraicGeometry.LocallyOfFiniteType (Z.subschemeι ≫ T.structMap)` using `inferInstance`. Establish `: AlgebraicGeometry.QuasiCompact (Z.subschemeι ≫ T.structMap)` using `inferInstance`.

Conclude with `isNoetherian_of_locallyOfFiniteType (Z.subschemeι ≫ T.structMap)`.
-/
private theorem isNoetherian_subscheme_of_smooth (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (Z : T.scheme.IdealSheafData)
    (hsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap)) :
    AlgebraicGeometry.IsNoetherian Z.subscheme := by
  have := hsm
  have := hT.quasiCompact
  have : AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of T.base)) :=
    isNoetherian_spec_field T.base
  have : AlgebraicGeometry.LocallyOfFiniteType (Z.subschemeι ≫ T.structMap) := inferInstance
  have : AlgebraicGeometry.QuasiCompact (Z.subschemeι ≫ T.structMap) := inferInstance
  exact isNoetherian_of_locallyOfFiniteType (Z.subschemeι ≫ T.structMap)

/- English proof (translation)
Use `hT.charZero` as an intermediate fact. Use `hT.smooth` as an intermediate fact. Establish `: AlgebraicGeometry.IsNoetherian Z.subscheme` using `isNoetherian_subscheme_of_smooth T hT Z hsm`. Establish `: TopologicalSpace.NoetherianSpace ↥Z.subscheme` using `inferInstance`. Establish `hemb : Topology.IsClosedEmbedding (⇑(Z.subschemeι).base)` using `AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding Z.subschemeι`.

Establish `hrange : Set.range (⇑(Z.subschemeι).base) = (↑Z.support : Set ↥T.scheme)`. Rewrite using `[AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι]`. Choose the witnesses or unpack the hypotheses as in `⟨y', hy'⟩ : ∃ y' : ↥Z.subscheme, (Z.subschemeι).base y' = y := by`. Establish `h1 : y ∈ Set.range (⇑(Z.subschemeι).base)` using `by rw [hrange]; exact hy`. Conclude with `h1`.

Establish `hfin : (irreducibleComponents ↥Z.subscheme).Finite` using `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`. Establish `hC₁ : irreducibleComponent y' ∈ irreducibleComponents ↥Z.subscheme` using `irreducibleComponent_mem_irreducibleComponents y'`. Establish `hy'C : y' ∈ irreducibleComponent y'` using `mem_irreducibleComponent`. Establish `hRclosed : IsClosed (⋃ C ∈ {C : Set ↥Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧ C ≠ irreducibleComponent y'}, (⇑(Z.subschemeι).base) '' C)`. Use `Set.Finite.isClosed_biUnion (hfin.subset (fun C hC => hC.1)) ?_` and prove the remaining obligations.

Introduce `C hC`. Conclude with `hemb.isClosedMap _ (isClosed_of_mem_irreducibleComponents C hC.1)`. Establish `hyR : y ∉ (⋃ C ∈ {C : Set ↥Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧ C ≠ irreducibleComponent y'}, (⇑(Z.subschemeι).base) '' C)`. Introduce `hmem`. Take `⟨C, hC, hyC⟩` from `Set.mem_iUnion₂.1 hmem`.

Take `⟨c, hcC, hceq⟩` from `hyC`. Establish `hcy : c = y'` using `hemb.injective (by rw [hceq, hy'])`. Establish `hdisj` using `irreducibleComponentsDisjointOfSmooth T.base Z.subscheme (Z.subschemeι ≫ T.structMap) hsm C hC.1 (irreducibleComponent y') hC₁ hC.2`. Conclude with `(Set.disjoint_left.mp hdisj (hcy ▸ hcC)) hy'C`. Establish `hSV : (↑Z.support : Set ↥T.scheme) ∩ (⋃ C ∈ {C : Set ↥Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧ C ≠ irreducibleComponent y'}, (⇑(Z.subschemeι).base) '' C)ᶜ = ((⇑(Z.subschemeι).base) '' (irreducibleComponent y')) ∩ (⋃ C ∈ {C : Set ↥Z.subscheme | C ∈ irreducibleCompone …`.

Use `Set.Subset.antisymm ?_ ?_` and prove the remaining obligations. Introduce and unpack `a ⟨haS, haR⟩`. Rewrite `haS` using `[← hrange]`. Take `⟨c, rfl⟩` from `haS`. Use `⟨⟨c, ?_, rfl⟩, haR⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hcc`. Establish `hne : irreducibleComponent c ≠ irreducibleComponent y'`. Introduce `hEq`. Conclude with `hcc (hEq ▸ mem_irreducibleComponent)`. Conclude with `haR (Set.mem_iUnion₂.2 ⟨irreducibleComponent c, ⟨irreducibleComponent_mem_irreducibleComponents c, hne⟩, ⟨c, mem_irreducibleComponent, rfl⟩⟩)`.

Introduce and unpack `a ⟨haim, haR⟩`. Use `⟨?_, haR⟩` and prove the remaining obligations. Rewrite using `[← hrange]`. Conclude with `Set.image_subset_range _ _ haim`. Establish `hfinal : IsIrreducible ((↑Z.support : Set ↥T.scheme) ∩ (⋃ C ∈ {C : Set ↥Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧ C ≠ irreducibleComponent y'}, (⇑(Z.subschemeι).base) '' C)ᶜ)`.

Rewrite using `[hSV]`. Conclude with `isIrreducible_inter_isOpen (isIrreducible_irreducibleComponent.image _ hemb.continuous.continuousOn) hRclosed.isOpen_compl ⟨y, ⟨y', hy'C, hy'⟩, hyR⟩`. Conclude with `⟨⟨_, hRclosed.isOpen_compl⟩, hyR, hfinal⟩`.
-/
private theorem exists_opens_isIrreducible_support_inter (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (Z : T.scheme.IdealSheafData)
    (hsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap))
    (y : ↥T.scheme) (hy : y ∈ (↑Z.support : Set ↥T.scheme)) :
    ∃ V : T.scheme.Opens, y ∈ V ∧
      IsIrreducible ((↑Z.support : Set ↥T.scheme) ∩ (↑V : Set ↥T.scheme)) := by
  have := hT.charZero
  have := hT.smooth
  have : AlgebraicGeometry.IsNoetherian Z.subscheme := isNoetherian_subscheme_of_smooth T hT Z hsm
  have : TopologicalSpace.NoetherianSpace ↥Z.subscheme := inferInstance
  have hemb : Topology.IsClosedEmbedding (⇑(Z.subschemeι).base) :=
    AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding Z.subschemeι
  have hrange : Set.range (⇑(Z.subschemeι).base) = (↑Z.support : Set ↥T.scheme) := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι]
  obtain ⟨y', hy'⟩ : ∃ y' : ↥Z.subscheme, (Z.subschemeι).base y' = y := by
    have h1 : y ∈ Set.range (⇑(Z.subschemeι).base) := by rw [hrange]; exact hy
    exact h1
  have hfin : (irreducibleComponents ↥Z.subscheme).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hC₁ : irreducibleComponent y' ∈ irreducibleComponents ↥Z.subscheme :=
    irreducibleComponent_mem_irreducibleComponents y'
  have hy'C : y' ∈ irreducibleComponent y' := mem_irreducibleComponent
  have hRclosed : IsClosed
      (⋃ C ∈ {C : Set ↥Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧
        C ≠ irreducibleComponent y'}, (⇑(Z.subschemeι).base) '' C) := by
    refine Set.Finite.isClosed_biUnion (hfin.subset (fun C hC => hC.1)) ?_
    intro C hC
    exact hemb.isClosedMap _ (isClosed_of_mem_irreducibleComponents C hC.1)
  have hyR : y ∉ (⋃ C ∈ {C : Set ↥Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧
      C ≠ irreducibleComponent y'}, (⇑(Z.subschemeι).base) '' C) := by
    intro hmem
    obtain ⟨C, hC, hyC⟩ := Set.mem_iUnion₂.1 hmem
    obtain ⟨c, hcC, hceq⟩ := hyC
    have hcy : c = y' := hemb.injective (by rw [hceq, hy'])
    have hdisj := irreducibleComponentsDisjointOfSmooth T.base Z.subscheme (Z.subschemeι ≫ T.structMap) hsm
      C hC.1 (irreducibleComponent y') hC₁ hC.2
    exact (Set.disjoint_left.mp hdisj (hcy ▸ hcC)) hy'C
  have hSV : (↑Z.support : Set ↥T.scheme) ∩
        (⋃ C ∈ {C : Set ↥Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧
          C ≠ irreducibleComponent y'}, (⇑(Z.subschemeι).base) '' C)ᶜ
      = ((⇑(Z.subschemeι).base) '' (irreducibleComponent y')) ∩
        (⋃ C ∈ {C : Set ↥Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧
          C ≠ irreducibleComponent y'}, (⇑(Z.subschemeι).base) '' C)ᶜ := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro a ⟨haS, haR⟩
      rw [← hrange] at haS
      obtain ⟨c, rfl⟩ := haS
      refine ⟨⟨c, ?_, rfl⟩, haR⟩
      by_contra hcc
      have hne : irreducibleComponent c ≠ irreducibleComponent y' := by
        intro hEq
        exact hcc (hEq ▸ mem_irreducibleComponent)
      exact haR (Set.mem_iUnion₂.2 ⟨irreducibleComponent c,
        ⟨irreducibleComponent_mem_irreducibleComponents c, hne⟩,
        ⟨c, mem_irreducibleComponent, rfl⟩⟩)
    · rintro a ⟨haim, haR⟩
      refine ⟨?_, haR⟩
      rw [← hrange]
      exact Set.image_subset_range _ _ haim
  have hfinal : IsIrreducible ((↑Z.support : Set ↥T.scheme) ∩
      (⋃ C ∈ {C : Set ↥Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧
        C ≠ irreducibleComponent y'}, (⇑(Z.subschemeι).base) '' C)ᶜ) := by
    rw [hSV]
    exact isIrreducible_inter_isOpen
      (isIrreducible_irreducibleComponent.image _ hemb.continuous.continuousOn)
      hRclosed.isOpen_compl ⟨y, ⟨y', hy'C, hy'⟩, hyR⟩
  exact ⟨⟨_, hRclosed.isOpen_compl⟩, hyR, hfinal⟩

/- English proof (translation)
Establish `hExcMem : Blowup.exceptionalIdeal π Z ∈ List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]` using `by simp`. Establish `hSTmem : ∀ D₀ ∈ T.boundary, Blowup.strictTransform π Z D₀ ∈ List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]`. Introduce `D₀ hD₀`. Conclude with `List.mem_append_left _ (List.mem_map.2 ⟨D₀, hD₀, rfl⟩)`. Establish `hfac : ∀ D₀ ∈ T.boundary, ∀ x' : ↥X', ∃ (U : X'.Opens) (ε : ℕ), x' ∈ U ∧ (D₀.comap π).comap U.ι = (Blowup.strictTransform π Z D₀).comap U.ι * (Blowup.exceptionalIdeal π Z).comap U.ι ^ ε`.

Introduce `D₀ hD₀ x'`. Take `⟨U, ε, hxU, _, _, hEq⟩` from `hG.monomialInputs.blowup_total_transform T hT Z hsm hsnc X' π hbl D₀ hD₀ x'`. Conclude with `⟨U, ε, hxU, hEq⟩`. Establish `hmonD : ∀ D₀ ∈ T.boundary, IsMonomialIn (List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]) (D₀.comap π)` using `fun D₀ hD₀ => isMonomialIn_of_locally_eq_mul_pow _ _ _ _ (hSTmem D₀ hD₀) hExcMem (hfac D₀ hD₀)`. Use `isMonomialIn_of_forall_mem ?_ (hMon.comap π)` and prove the remaining obligations.

Introduce `D hD`. Take `⟨D₀, hD₀, rfl⟩` from `List.mem_map.1 hD`. Conclude with `hmonD D₀ hD₀`.
-/
private theorem isMonomialIn_comap_blowup (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (Z : T.scheme.IdealSheafData)
    (hsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap))
    (hsnc : HasStrictNormalCrossingsWith T.structMap Z T.boundary)
    (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (hbl : Blowup.IsBlowupAlongIdealSheaf π Z)
    (Mon : T.scheme.IdealSheafData) (hMon : IsMonomialIn T.boundary Mon) :
    IsMonomialIn (List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z])
      (Mon.comap π) := by
  have hExcMem : Blowup.exceptionalIdeal π Z ∈
      List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z] := by simp
  have hSTmem : ∀ D₀ ∈ T.boundary, Blowup.strictTransform π Z D₀ ∈
      List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z] := by
    intro D₀ hD₀
    exact List.mem_append_left _ (List.mem_map.2 ⟨D₀, hD₀, rfl⟩)
  have hfac : ∀ D₀ ∈ T.boundary, ∀ x' : ↥X',
      ∃ (U : X'.Opens) (ε : ℕ), x' ∈ U ∧
        (D₀.comap π).comap U.ι =
          (Blowup.strictTransform π Z D₀).comap U.ι * (Blowup.exceptionalIdeal π Z).comap U.ι ^ ε := by
    intro D₀ hD₀ x'
    obtain ⟨U, ε, hxU, _, _, hEq⟩ :=
      hG.monomialInputs.blowup_total_transform T hT Z hsm hsnc X' π hbl D₀ hD₀ x'
    exact ⟨U, ε, hxU, hEq⟩
  have hmonD : ∀ D₀ ∈ T.boundary,
      IsMonomialIn (List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z])
        (D₀.comap π) := fun D₀ hD₀ =>
    isMonomialIn_of_locally_eq_mul_pow _ _ _ _ (hSTmem D₀ hD₀) hExcMem (hfac D₀ hD₀)
  refine isMonomialIn_of_forall_mem ?_ (hMon.comap π)
  intro D hD
  obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD
  exact hmonD D₀ hD₀

/- English proof (translation)
Use `hT.charZero` as an intermediate fact. Use `hT.smooth` as an intermediate fact. Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`.

Introduce `_`. Use `⟨⊤, 1, 0, trivial, one_mem _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[List.prod_nil, comap_one, comap_one, pow_zero, mul_one]`. Rewrite using `[List.prod_nil, Scheme.IdealSheafData.one_eq_top, orderAt_top]`. Simplify using the standard rewrite rules.

Consider the case `cons D L ih`. Introduce `hall`. Establish `hD : D ∈ T.boundary` using `hall D List.mem_cons_self`. Take `⟨U₁, m₁, s₁, hx1, hm1, heq1, hord1⟩` from `ih (fun D' hD' => hall D' (List.mem_cons_of_mem _ hD'))`. Take `⟨U₂, ε, hx2, hε01, hεiff, heq2⟩` from `hG.monomialInputs.blowup_total_transform T hT Z hsm hsnc X' π hbl D hD x'`.

Establish `hDeq : (D.comap π).comap (U₁ ⊓ U₂).ι = (Blowup.strictTransform π Z D).comap (U₁ ⊓ U₂).ι * ((Blowup.exceptionalIdeal π Z).comap (U₁ ⊓ U₂).ι) ^ ε`. Establish `h : ((D.comap π).comap U₂.ι).comap (X'.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) = ((Blowup.strictTransform π Z D).comap U₂.ι * ((Blowup.exceptionalIdeal π Z).comap U₂.ι) ^ ε).comap (X'.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂))`. Rewrite using `[heq2]`. Simplify using `only [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow, comap_homOfLE] at h`. Conclude with `h`.

Establish `hLeq : ((L.prod).comap π).comap (U₁ ⊓ U₂).ι = (m₁.comap (X'.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))) * ((Blowup.exceptionalIdeal π Z).comap (U₁ ⊓ U₂).ι) ^ s₁`. Establish `h : (((L.prod).comap π).comap U₁.ι).comap (X'.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) = (m₁ * ((Blowup.exceptionalIdeal π Z).comap U₁.ι) ^ s₁).comap (X'.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))`. Rewrite using `[heq1]`. Simplify using `only [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow, comap_homOfLE] at h`. Conclude with `h`.

Establish `hordD : orderAt D z = (ε : ℕ∞)`. Break down `hε01 with h0 | h1` into its components or cases. Establish `hnotex : ¬ (∃ V : T.scheme.Opens, π.base x' ∈ V ∧ (↑Z.support : Set ↥T.scheme) ∩ (↑V : Set ↥T.scheme) ⊆ (↑D.support : Set ↥T.scheme))`. Introduce `hex`. Establish `h1' : ε = 1` using `hεiff.2 hex`.

Rewrite `h1'` using `[h0]`. Simplify using `at h1'`. Establish `hzn` using `hz0 D hD hnotex`. Rewrite using `[h0, (orderAt_eq_zero_iff_not_mem_support D z).2 hzn]`. Simplify using the standard rewrite rules.

Establish `hzm` using `hz1 D hD (hεiff.1 h1)`. Rewrite using `[h1, MonomialChart.orderAt_boundary_eq_one T hT D hD z hzm]`. Simplify using the standard rewrite rules. Use `⟨U₁ ⊓ U₂, (Blowup.strictTransform π Z D).comap (U₁ ⊓ U₂).ι * (m₁.comap (X'.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))), ε + s₁, ⟨hx1, hx2⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `mul_mem (Submonoid.subset_closure ⟨Blowup.strictTransform π Z D, ?_, rfl⟩) ?_` and prove the remaining obligations.

Conclude with `List.mem_map.2 ⟨D, hD, rfl⟩`. Conclude with `comap_homOfLE_mem_closure_comap (E := List.map (Blowup.strictTransform π Z) T.boundary) inf_le_left m₁ hm1`. Rewrite using `[List.prod_cons, Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_mul, hDeq, hLeq, pow_add, mul_mul_mul_comm]`. Rewrite using `[List.prod_cons, orderAt_mul T.base T.structMap D L.prod z, hordD, hord1, Nat.cast_add]`.
-/
private theorem exists_opens_comap_list_prod_eq_mul_exceptionalIdeal_pow (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (Z : T.scheme.IdealSheafData)
    (hsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap))
    (hsnc : HasStrictNormalCrossingsWith T.structMap Z T.boundary)
    (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (hbl : Blowup.IsBlowupAlongIdealSheaf π Z)
    (x' : ↥X') (z : ↥T.scheme)
    (hz1 : ∀ D ∈ T.boundary,
      (∃ V : T.scheme.Opens, π.base x' ∈ V ∧
        (↑Z.support : Set ↥T.scheme) ∩ (↑V : Set ↥T.scheme) ⊆ (↑D.support : Set ↥T.scheme)) →
      z ∈ D.support)
    (hz0 : ∀ D ∈ T.boundary,
      ¬ (∃ V : T.scheme.Opens, π.base x' ∈ V ∧
        (↑Z.support : Set ↥T.scheme) ∩ (↑V : Set ↥T.scheme) ⊆ (↑D.support : Set ↥T.scheme)) →
      z ∉ D.support) :
    ∀ L : List T.scheme.IdealSheafData, (∀ D ∈ L, D ∈ T.boundary) →
      ∃ (U : X'.Opens) (m : U.toScheme.IdealSheafData) (s : ℕ), x' ∈ U ∧
        m ∈ Submonoid.closure ((fun D : X'.IdealSheafData => D.comap U.ι) ''
          {D | D ∈ List.map (Blowup.strictTransform π Z) T.boundary}) ∧
        ((L.prod).comap π).comap U.ι = m * ((Blowup.exceptionalIdeal π Z).comap U.ι) ^ s ∧
        orderAt (L.prod) z = (s : ℕ∞) := by
  have := hT.charZero
  have := hT.smooth
  intro L
  induction L with
  | nil =>
      intro _
      refine ⟨⊤, 1, 0, trivial, one_mem _, ?_, ?_⟩
      · rw [List.prod_nil, comap_one, comap_one, pow_zero, mul_one]
      · rw [List.prod_nil, Scheme.IdealSheafData.one_eq_top, orderAt_top]
        simp
  | cons D L ih =>
      intro hall
      have hD : D ∈ T.boundary := hall D List.mem_cons_self
      obtain ⟨U₁, m₁, s₁, hx1, hm1, heq1, hord1⟩ :=
        ih (fun D' hD' => hall D' (List.mem_cons_of_mem _ hD'))
      obtain ⟨U₂, ε, hx2, hε01, hεiff, heq2⟩ :=
        hG.monomialInputs.blowup_total_transform T hT Z hsm hsnc X' π hbl D hD x'
      have hDeq : (D.comap π).comap (U₁ ⊓ U₂).ι
          = (Blowup.strictTransform π Z D).comap (U₁ ⊓ U₂).ι
            * ((Blowup.exceptionalIdeal π Z).comap (U₁ ⊓ U₂).ι) ^ ε := by
        have h : ((D.comap π).comap U₂.ι).comap
              (X'.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂))
            = ((Blowup.strictTransform π Z D).comap U₂.ι
              * ((Blowup.exceptionalIdeal π Z).comap U₂.ι) ^ ε).comap
                (X'.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) := by
          rw [heq2]
        simp only [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow,
          comap_homOfLE] at h
        exact h
      have hLeq : ((L.prod).comap π).comap (U₁ ⊓ U₂).ι
          = (m₁.comap (X'.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)))
            * ((Blowup.exceptionalIdeal π Z).comap (U₁ ⊓ U₂).ι) ^ s₁ := by
        have h : (((L.prod).comap π).comap U₁.ι).comap
              (X'.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
            = (m₁ * ((Blowup.exceptionalIdeal π Z).comap U₁.ι) ^ s₁).comap
                (X'.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) := by
          rw [heq1]
        simp only [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow,
          comap_homOfLE] at h
        exact h
      have hordD : orderAt D z = (ε : ℕ∞) := by
        rcases hε01 with h0 | h1
        · have hnotex : ¬ (∃ V : T.scheme.Opens, π.base x' ∈ V ∧
              (↑Z.support : Set ↥T.scheme) ∩ (↑V : Set ↥T.scheme)
                ⊆ (↑D.support : Set ↥T.scheme)) := by
            intro hex
            have h1' : ε = 1 := hεiff.2 hex
            rw [h0] at h1'
            simp at h1'
          have hzn := hz0 D hD hnotex
          rw [h0, (orderAt_eq_zero_iff_not_mem_support D z).2 hzn]
          simp
        · have hzm := hz1 D hD (hεiff.1 h1)
          rw [h1, MonomialChart.orderAt_boundary_eq_one T hT D hD z hzm]
          simp
      refine ⟨U₁ ⊓ U₂, (Blowup.strictTransform π Z D).comap (U₁ ⊓ U₂).ι
        * (m₁.comap (X'.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))), ε + s₁, ⟨hx1, hx2⟩, ?_, ?_, ?_⟩
      · refine mul_mem (Submonoid.subset_closure ⟨Blowup.strictTransform π Z D, ?_, rfl⟩) ?_
        · exact List.mem_map.2 ⟨D, hD, rfl⟩
        · exact comap_homOfLE_mem_closure_comap
            (E := List.map (Blowup.strictTransform π Z) T.boundary) inf_le_left m₁ hm1
      · rw [List.prod_cons, Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_mul,
          hDeq, hLeq, pow_add, mul_mul_mul_comm]
      · rw [List.prod_cons, orderAt_mul T.base T.structMap D L.prod z, hordD, hord1,
          Nat.cast_add]

/- English proof (translation)
Use `hT.charZero` as an intermediate fact. Use `hT.smooth` as an intermediate fact. Establish `hEC : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z)` using `isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hbl`. Establish `hExcMem : Blowup.exceptionalIdeal π Z ∈ List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]` using `by simp`. Establish `hMonComap` using `isMonomialIn_comap_blowup hG T hT Z hsm hsnc X' π hbl Mon hMon`.

Establish `hsubimg : ∀ U : X'.Opens, ((fun D : X'.IdealSheafData => D.comap U.ι) '' {D | D ∈ List.map (Blowup.strictTransform π Z) T.boundary}) ⊆ ((fun D : X'.IdealSheafData => D.comap U.ι) '' {D | D ∈ List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]})`. Introduce `U`. Conclude with `Set.image_mono (fun D hD => List.mem_append_left _ hD)`. Rewrite using `[isMonomialIn_iff_forall_exists_mem_closure]`. Introduce `x'`.

Distinguish the cases in `hx'E : x' ∈ (Blowup.exceptionalIdeal π Z).support`. Establish `hyZ : (π.base x') ∈ (↑Z.support : Set ↥T.scheme)`. Establish `h0 : (↑(Blowup.exceptionalIdeal π Z).support : Set ↥X') = ⇑π.base ⁻¹' (↑Z.support : Set ↥T.scheme)`. Rewrite using `[Blowup.exceptionalIdeal_eq_comap, support_comap_coe]`. Establish `h1 : x' ∈ (↑(Blowup.exceptionalIdeal π Z).support : Set ↥X')` using `hx'E`.

Rewrite `h1` using `[h0]`. Conclude with `h1`. Take `⟨V₀, hyV₀, hirr₀⟩` from `exists_opens_isIrreducible_support_inter T hT Z hsm (π.base x') hyZ`. Take `⟨W, hyW, hWmem⟩` from `(isMonomialIn_iff_forall_exists_mem_closure T.boundary Mon).1 hMon (π.base x')`. Take `⟨L, hLsub, hLeq⟩` from `exists_list_prod_eq_of_mem_closure W.ι T.boundary hWmem`.

Establish `hWeq : Mon.comap W.ι = (L.prod).comap W.ι`. Rewrite using `[comap_list_prod W.ι L]`. Conclude with `hLeq`. Establish `hyS₀ : π.base x' ∈ ((↑Z.support : Set ↥T.scheme) ∩ (↑V₀ : Set ↥T.scheme)) ∩ (↑W : Set ↥T.scheme)` using `⟨⟨hyZ, hyV₀⟩, hyW⟩`. Establish `hirr : IsIrreducible (((↑Z.support : Set ↥T.scheme) ∩ (↑V₀ : Set ↥T.scheme)) ∩ (↑W : Set ↥T.scheme))` using `isIrreducible_inter_isOpen hirr₀ W.2 ⟨_, hyS₀⟩`.

Take `⟨η, hη⟩` from `exists_closure_singleton_eq_closure T.scheme hirr`. Establish `hηZ : η ∈ (↑Z.support : Set ↥T.scheme)`. Establish `h1 : closure (((↑Z.support : Set ↥T.scheme) ∩ (↑V₀ : Set ↥T.scheme)) ∩ (↑W : Set ↥T.scheme)) ⊆ (↑Z.support : Set ↥T.scheme)` using `closure_minimal (fun a ha => ha.1.1) (Z.support).2`. Establish `h2 : η ∈ closure (((↑Z.support : Set ↥T.scheme) ∩ (↑V₀ : Set ↥T.scheme)) ∩ (↑W : Set ↥T.scheme))`. Rewrite using `[← hη]`.

Conclude with `subset_closure rfl`. Conclude with `h1 h2`. Establish `hηW : η ∈ W` using `mem_of_isOpen_of_closure_singleton_eq hη W.2 ⟨_, hyS₀, hyW⟩`. Establish `hz1 : ∀ D ∈ T.boundary, (∃ V : T.scheme.Opens, π.base x' ∈ V ∧ (↑Z.support : Set ↥T.scheme) ∩ (↑V : Set ↥T.scheme) ⊆ (↑D.support : Set ↥T.scheme)) → η ∈ D.support`. Introduce and unpack `D hD ⟨V, hyV, hsub⟩`.

Establish `hηV : η ∈ V` using `mem_of_isOpen_of_closure_singleton_eq hη V.2 ⟨_, hyS₀, hyV⟩`. Conclude with `hsub ⟨hηZ, hηV⟩`. Establish `hz0 : ∀ D ∈ T.boundary, ¬ (∃ V : T.scheme.Opens, π.base x' ∈ V ∧ (↑Z.support : Set ↥T.scheme) ∩ (↑V : Set ↥T.scheme) ⊆ (↑D.support : Set ↥T.scheme)) → η ∉ D.support`. Introduce `D _ hnot hmem`. Use `hnot ⟨V₀ ⊓ W, ⟨hyV₀, hyW⟩, ?_⟩` and prove the remaining obligations.

Establish `hsub` using `subset_of_closure_singleton_eq_closure hη (D.support).2 hmem`. Introduce `a ha`. Establish `ha1 : a ∈ (↑Z.support : Set ↥T.scheme)` using `ha.1`. Establish `ha2 : a ∈ (↑(V₀ ⊓ W) : Set ↥T.scheme)` using `ha.2`. Rewrite `ha2` using `[TopologicalSpace.Opens.coe_inf]`.

Conclude with `hsub ⟨⟨ha1, ha2.1⟩, ha2.2⟩`. Take `⟨U₂, m, s, hx2, hmclo, hUeq, hords⟩` from `exists_opens_comap_list_prod_eq_mul_exceptionalIdeal_pow hG T hT Z hsm hsnc X' π hbl x' η hz1 hz0 L hLsub`. Establish `hMonord : ((d : ℕ) : ℕ∞) ≤ orderAt Mon η`. Establish `h1 : η ∈ orderAtLeastLocus Z 1` using `(mem_orderAtLeastLocus_one_iff Z η).2 hηZ`. Establish `h2 : η ∈ orderAtLeastLocus (Z ^ d) (d * 1)` using `orderAtLeastLocus_subset_orderAtLeastLocus_pow Z d 1 h1`.

Rewrite `h2` using `[mul_one]`. Establish `h3 : ((d : ℕ) : ℕ∞) ≤ orderAt (Z ^ d) η` using `(mem_orderAtLeastLocus_iff _ _ _).1 h2`. Conclude with `le_trans h3 (orderAt_le_of_le hd η)`. Establish `hMonLprod : orderAt Mon η = orderAt (L.prod) η`. Rewrite using `[← orderAt_comap_opens_ι W Mon η hηW, ← orderAt_comap_opens_ι W (L.prod) η hηW, hWeq]`.

Establish `hds : d ≤ s`. Rewrite `hMonord` using `[hMonLprod, hords]`. Conclude with `hMonord` after adjusting the coercions. Use `⟨U₂ ⊓ π ⁻¹ᵁ W, ⟨hx2, hyW⟩, ?_⟩` and prove the remaining obligations. Establish `hkey : ∀ J : T.scheme.IdealSheafData, (J.comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι = (J.comap W.ι).comap (π.resLE W (U₂ ⊓ π ⁻¹ᵁ W) inf_le_right)`.

Introduce `J`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Scheme.Hom.resLE_comp_ι]`. Establish `hMonL : (Mon.comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι = ((L.prod).comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι`. Rewrite using `[hkey Mon, hkey (L.prod), hWeq]`. Establish `hfact : ((L.prod).comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι = (m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂))) * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ s`.

Establish `h : (((L.prod).comap π).comap U₂.ι).comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂)) = (m * ((Blowup.exceptionalIdeal π Z).comap U₂.ι) ^ s).comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂))`. Rewrite using `[hUeq]`. Simplify using `only [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow, comap_homOfLE] at h`. Conclude with `h`. Establish `hm' : (m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂))) ∈ Submonoid.closure ((fun D : X'.IdealSheafData => D.comap (U₂ ⊓ π ⁻¹ᵁ W).ι) '' {D | D ∈ List.map (Blowup.strictTransform π Z) T.boundary})` using `comap_homOfLE_mem_closure_comap (E := List.map (Blowup.strictTransform π Z) T.boundary) inf_le_left m hmclo`.

Establish `hexp : d + (s - d) = s` using `Nat.add_sub_cancel' hds`. Establish `hCmul : ((Blowup.exceptionalIdeal π Z) ^ d).comap (U₂ ⊓ π ⁻¹ᵁ W).ι * (C.comap (U₂ ⊓ π ⁻¹ᵁ W).ι) = ((Blowup.exceptionalIdeal π Z) ^ d).comap (U₂ ⊓ π ⁻¹ᵁ W).ι * ((m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂))) * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ (s - …`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Scheme.IdealSheafData.comap_mul]`. Use `_ = (Mon.comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι := by rw [hC]`.

Use `_ = ((L.prod).comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι := hMonL`. Use `_ = (m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂))) * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ s := hfact`. Use `_ = (m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂))) * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ (d + (s - d)) := by`. Rewrite using `[hexp]`. Use `_ = ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ d * ((m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂))) * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ (s - d)) := by`.

Rewrite using `[pow_add]`. Conclude with `mul_left_comm _ _ _`. Use `_ = ((Blowup.exceptionalIdeal π Z) ^ d).comap (U₂ ⊓ π ⁻¹ᵁ W).ι * ((m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂))) * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ (s - d)) := by`. Rewrite using `[Scheme.IdealSheafData.comap_pow]`. Establish `hCeq` using `(hEC.pow d).eq_of_mul_eq_mul_comap_opensι (U₂ ⊓ π ⁻¹ᵁ W) hCmul`.

Rewrite using `[hCeq]`. Establish `hEmem : (Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι ∈ ((fun D : X'.IdealSheafData => D.comap (U₂ ⊓ π ⁻¹ᵁ W).ι) '' {D | D ∈ List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]})` using `⟨Blowup.exceptionalIdeal π Z, hExcMem, rfl⟩`. Use `mul_mem (Submonoid.closure_mono (hsubimg (U₂ ⊓ π ⁻¹ᵁ W)) hm') ?_` and prove the remaining obligations. Conclude with `pow_mem (Submonoid.subset_closure hEmem) (s - d)`. Take `⟨U₀, hx0, hmem0⟩` from `(isMonomialIn_iff_forall_exists_mem_closure _ _).1 hMonComap x'`.

Establish `hxVc : x' ∈ (Blowup.exceptionalIdeal π Z).support.compl` using `(mem_closeds_compl_iff _ _).2 hx'E`. Use `⟨U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl, ⟨hx0, hxVc⟩, ?_⟩` and prove the remaining obligations. Establish `hE1 : (Blowup.exceptionalIdeal π Z).comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι = 1`. Use `comap_eq_one_of_forall_notMem_support _ _ ?_` and prove the remaining obligations. Introduce `x hx`.

Conclude with `(mem_closeds_compl_iff _ _).1 hx.2`. Establish `hCU : C.comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι = (Mon.comap π).comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[one_pow, one_mul]`. Use `_ = ((Blowup.exceptionalIdeal π Z).comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι) ^ d * C.comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι := by rw [hE1]`.

Use `_ = (((Blowup.exceptionalIdeal π Z) ^ d) * C).comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι := by`. Rewrite using `[Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow]`. Use `_ = (Mon.comap π).comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι := by rw [hC]`. Rewrite using `[hCU]`. Establish `hfin` using `comap_homOfLE_mem_closure_comap (E := List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]) (inf_le_left : U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl ≤ U₀) _ hmem0`.

Rewrite `hfin` using `[comap_homOfLE]`. Then use the resulting hypothesis.
-/
theorem isMonomialIn_of_exceptionalIdeal_pow_mul_eq_comap (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (Z : T.scheme.IdealSheafData)
    (hsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap))
    (hsnc : HasStrictNormalCrossingsWith T.structMap Z T.boundary)
    (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (hbl : Blowup.IsBlowupAlongIdealSheaf π Z)
    (Mon : T.scheme.IdealSheafData) (hMon : IsMonomialIn T.boundary Mon)
    (d : ℕ) (hd : Mon ≤ Z ^ d)
    (C : X'.IdealSheafData) (hC : Blowup.exceptionalIdeal π Z ^ d * C = Mon.comap π) :
    IsMonomialIn (List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]) C := by
  have := hT.charZero
  have := hT.smooth
  have hEC : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hbl
  have hExcMem : Blowup.exceptionalIdeal π Z ∈
      List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z] := by simp
  have hMonComap := isMonomialIn_comap_blowup hG T hT Z hsm hsnc X' π hbl Mon hMon
  have hsubimg : ∀ U : X'.Opens,
      ((fun D : X'.IdealSheafData => D.comap U.ι) ''
          {D | D ∈ List.map (Blowup.strictTransform π Z) T.boundary})
        ⊆ ((fun D : X'.IdealSheafData => D.comap U.ι) ''
          {D | D ∈ List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]}) := by
    intro U
    exact Set.image_mono (fun D hD => List.mem_append_left _ hD)
  rw [isMonomialIn_iff_forall_exists_mem_closure]
  intro x'
  by_cases hx'E : x' ∈ (Blowup.exceptionalIdeal π Z).support
  · have hyZ : (π.base x') ∈ (↑Z.support : Set ↥T.scheme) := by
      have h0 : (↑(Blowup.exceptionalIdeal π Z).support : Set ↥X')
          = ⇑π.base ⁻¹' (↑Z.support : Set ↥T.scheme) := by
        rw [Blowup.exceptionalIdeal_eq_comap, support_comap_coe]
      have h1 : x' ∈ (↑(Blowup.exceptionalIdeal π Z).support : Set ↥X') := hx'E
      rw [h0] at h1
      exact h1
    obtain ⟨V₀, hyV₀, hirr₀⟩ :=
      exists_opens_isIrreducible_support_inter T hT Z hsm (π.base x') hyZ
    obtain ⟨W, hyW, hWmem⟩ :=
      (isMonomialIn_iff_forall_exists_mem_closure T.boundary Mon).1 hMon (π.base x')
    obtain ⟨L, hLsub, hLeq⟩ := exists_list_prod_eq_of_mem_closure W.ι T.boundary hWmem
    have hWeq : Mon.comap W.ι = (L.prod).comap W.ι := by
      rw [comap_list_prod W.ι L]
      exact hLeq
    have hyS₀ : π.base x' ∈ ((↑Z.support : Set ↥T.scheme) ∩ (↑V₀ : Set ↥T.scheme))
        ∩ (↑W : Set ↥T.scheme) := ⟨⟨hyZ, hyV₀⟩, hyW⟩
    have hirr : IsIrreducible (((↑Z.support : Set ↥T.scheme) ∩ (↑V₀ : Set ↥T.scheme))
        ∩ (↑W : Set ↥T.scheme)) := isIrreducible_inter_isOpen hirr₀ W.2 ⟨_, hyS₀⟩
    obtain ⟨η, hη⟩ := exists_closure_singleton_eq_closure T.scheme hirr
    have hηZ : η ∈ (↑Z.support : Set ↥T.scheme) := by
      have h1 : closure (((↑Z.support : Set ↥T.scheme) ∩ (↑V₀ : Set ↥T.scheme))
          ∩ (↑W : Set ↥T.scheme)) ⊆ (↑Z.support : Set ↥T.scheme) :=
        closure_minimal (fun a ha => ha.1.1) (Z.support).2
      have h2 : η ∈ closure (((↑Z.support : Set ↥T.scheme) ∩ (↑V₀ : Set ↥T.scheme))
          ∩ (↑W : Set ↥T.scheme)) := by
        rw [← hη]
        exact subset_closure rfl
      exact h1 h2
    have hηW : η ∈ W := mem_of_isOpen_of_closure_singleton_eq hη W.2 ⟨_, hyS₀, hyW⟩
    have hz1 : ∀ D ∈ T.boundary, (∃ V : T.scheme.Opens, π.base x' ∈ V ∧
        (↑Z.support : Set ↥T.scheme) ∩ (↑V : Set ↥T.scheme) ⊆ (↑D.support : Set ↥T.scheme)) →
        η ∈ D.support := by
      rintro D hD ⟨V, hyV, hsub⟩
      have hηV : η ∈ V := mem_of_isOpen_of_closure_singleton_eq hη V.2 ⟨_, hyS₀, hyV⟩
      exact hsub ⟨hηZ, hηV⟩
    have hz0 : ∀ D ∈ T.boundary, ¬ (∃ V : T.scheme.Opens, π.base x' ∈ V ∧
        (↑Z.support : Set ↥T.scheme) ∩ (↑V : Set ↥T.scheme) ⊆ (↑D.support : Set ↥T.scheme)) →
        η ∉ D.support := by
      intro D _ hnot hmem
      refine hnot ⟨V₀ ⊓ W, ⟨hyV₀, hyW⟩, ?_⟩
      have hsub := subset_of_closure_singleton_eq_closure hη (D.support).2 hmem
      intro a ha
      have ha1 : a ∈ (↑Z.support : Set ↥T.scheme) := ha.1
      have ha2 : a ∈ (↑(V₀ ⊓ W) : Set ↥T.scheme) := ha.2
      rw [TopologicalSpace.Opens.coe_inf] at ha2
      exact hsub ⟨⟨ha1, ha2.1⟩, ha2.2⟩
    obtain ⟨U₂, m, s, hx2, hmclo, hUeq, hords⟩ :=
      exists_opens_comap_list_prod_eq_mul_exceptionalIdeal_pow hG T hT Z hsm hsnc X' π hbl x' η hz1 hz0 L hLsub
    have hMonord : ((d : ℕ) : ℕ∞) ≤ orderAt Mon η := by
      have h1 : η ∈ orderAtLeastLocus Z 1 := (mem_orderAtLeastLocus_one_iff Z η).2 hηZ
      have h2 : η ∈ orderAtLeastLocus (Z ^ d) (d * 1) := orderAtLeastLocus_subset_orderAtLeastLocus_pow Z d 1 h1
      rw [mul_one] at h2
      have h3 : ((d : ℕ) : ℕ∞) ≤ orderAt (Z ^ d) η := (mem_orderAtLeastLocus_iff _ _ _).1 h2
      exact le_trans h3 (orderAt_le_of_le hd η)
    have hMonLprod : orderAt Mon η = orderAt (L.prod) η := by
      rw [← orderAt_comap_opens_ι W Mon η hηW, ← orderAt_comap_opens_ι W (L.prod) η hηW, hWeq]
    have hds : d ≤ s := by
      rw [hMonLprod, hords] at hMonord
      exact_mod_cast hMonord
    refine ⟨U₂ ⊓ π ⁻¹ᵁ W, ⟨hx2, hyW⟩, ?_⟩
    have hkey : ∀ J : T.scheme.IdealSheafData,
        (J.comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι
          = (J.comap W.ι).comap (π.resLE W (U₂ ⊓ π ⁻¹ᵁ W) inf_le_right) := by
      intro J
      rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        Scheme.Hom.resLE_comp_ι]
    have hMonL : (Mon.comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι
        = ((L.prod).comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι := by
      rw [hkey Mon, hkey (L.prod), hWeq]
    have hfact : ((L.prod).comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι
        = (m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂)))
          * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ s := by
      have h : (((L.prod).comap π).comap U₂.ι).comap
            (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂))
          = (m * ((Blowup.exceptionalIdeal π Z).comap U₂.ι) ^ s).comap
              (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂)) := by
        rw [hUeq]
      simp only [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow,
        comap_homOfLE] at h
      exact h
    have hm' : (m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂))) ∈
        Submonoid.closure ((fun D : X'.IdealSheafData => D.comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ''
          {D | D ∈ List.map (Blowup.strictTransform π Z) T.boundary}) :=
      comap_homOfLE_mem_closure_comap (E := List.map (Blowup.strictTransform π Z) T.boundary)
        inf_le_left m hmclo
    have hexp : d + (s - d) = s := Nat.add_sub_cancel' hds
    have hCmul : ((Blowup.exceptionalIdeal π Z) ^ d).comap (U₂ ⊓ π ⁻¹ᵁ W).ι
          * (C.comap (U₂ ⊓ π ⁻¹ᵁ W).ι)
        = ((Blowup.exceptionalIdeal π Z) ^ d).comap (U₂ ⊓ π ⁻¹ᵁ W).ι
          * ((m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂)))
            * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ (s - d)) := by
      calc ((Blowup.exceptionalIdeal π Z) ^ d).comap (U₂ ⊓ π ⁻¹ᵁ W).ι
              * (C.comap (U₂ ⊓ π ⁻¹ᵁ W).ι)
          = (((Blowup.exceptionalIdeal π Z) ^ d) * C).comap (U₂ ⊓ π ⁻¹ᵁ W).ι := by
            rw [Scheme.IdealSheafData.comap_mul]
        _ = (Mon.comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι := by rw [hC]
        _ = ((L.prod).comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι := hMonL
        _ = (m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂)))
              * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ s := hfact
        _ = (m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂)))
              * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ (d + (s - d)) := by
            rw [hexp]
        _ = ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ d
              * ((m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂)))
                * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ (s - d)) := by
            rw [pow_add]
            exact mul_left_comm _ _ _
        _ = ((Blowup.exceptionalIdeal π Z) ^ d).comap (U₂ ⊓ π ⁻¹ᵁ W).ι
              * ((m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂)))
                * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ (s - d)) := by
            rw [Scheme.IdealSheafData.comap_pow]
    have hCeq := (hEC.pow d).eq_of_mul_eq_mul_comap_opensι (U₂ ⊓ π ⁻¹ᵁ W) hCmul
    rw [hCeq]
    have hEmem : (Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι ∈
        ((fun D : X'.IdealSheafData => D.comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ''
          {D | D ∈ List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]}) :=
      ⟨Blowup.exceptionalIdeal π Z, hExcMem, rfl⟩
    refine mul_mem (Submonoid.closure_mono (hsubimg (U₂ ⊓ π ⁻¹ᵁ W)) hm') ?_
    exact pow_mem (Submonoid.subset_closure hEmem) (s - d)
  · obtain ⟨U₀, hx0, hmem0⟩ :=
      (isMonomialIn_iff_forall_exists_mem_closure _ _).1 hMonComap x'
    have hxVc : x' ∈ (Blowup.exceptionalIdeal π Z).support.compl :=
      (mem_closeds_compl_iff _ _).2 hx'E
    refine ⟨U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl, ⟨hx0, hxVc⟩, ?_⟩
    have hE1 : (Blowup.exceptionalIdeal π Z).comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι = 1 := by
      refine comap_eq_one_of_forall_notMem_support _ _ ?_
      intro x hx
      exact (mem_closeds_compl_iff _ _).1 hx.2
    have hCU : C.comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι
        = (Mon.comap π).comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι := by
      calc C.comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι
          = (1 : (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).toScheme.IdealSheafData) ^ d
              * C.comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι := by
            rw [one_pow, one_mul]
        _ = ((Blowup.exceptionalIdeal π Z).comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι) ^ d
              * C.comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι := by rw [hE1]
        _ = (((Blowup.exceptionalIdeal π Z) ^ d) * C).comap
              (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι := by
            rw [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow]
        _ = (Mon.comap π).comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι := by rw [hC]
    rw [hCU]
    have hfin := comap_homOfLE_mem_closure_comap
      (E := List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z])
      (inf_le_left : U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl ≤ U₀) _ hmem0
    rwa [comap_homOfLE] at hfin

/- English proof (translation)
Use `hT.charZero` as an intermediate fact. Use `hT.smooth` as an intermediate fact. Establish `hEC : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z)` using `isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hbl`. Establish `hExcMem : Blowup.exceptionalIdeal π Z ∈ List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]`. Simplify using the standard rewrite rules.

Establish `hSTmem : ∀ D₀ ∈ T.boundary, Blowup.strictTransform π Z D₀ ∈ List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]`. Introduce `D₀ hD₀`. Conclude with `List.mem_append_left _ (List.mem_map.2 ⟨D₀, hD₀, rfl⟩)`. Establish `hfac : ∀ D₀ ∈ T.boundary, ∀ x' : ↥X', ∃ (U : X'.Opens) (ε : ℕ), x' ∈ U ∧ (D₀.comap π).comap U.ι = (Blowup.strictTransform π Z D₀).comap U.ι * (Blowup.exceptionalIdeal π Z).comap U.ι ^ ε`. Introduce `D₀ hD₀ x'`.

Take `⟨U, ε, hxU, _, _, hEq⟩` from `hG.monomialInputs.blowup_total_transform T hT Z hsm hsnc X' π hbl D₀ hD₀ x'`. Conclude with `⟨U, ε, hxU, hEq⟩`. Establish `hmonD : ∀ D₀ ∈ T.boundary, IsMonomialIn (List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]) (D₀.comap π)`. Introduce `D₀ hD₀`. Conclude with `isMonomialIn_of_locally_eq_mul_pow _ _ _ _ (hSTmem D₀ hD₀) hExcMem (hfac D₀ hD₀)`.

Establish `hmonMon : IsMonomialIn (List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]) (Mon.comap π)`. Use `isMonomialIn_of_forall_mem ?_ (hsplit.monomial.comap π)` and prove the remaining obligations. Introduce `D hD`. Take `⟨D₀, hD₀, rfl⟩` from `List.mem_map.1 hD`. Conclude with `hmonD D₀ hD₀`.

Establish `key : Blowup.exceptionalIdeal π Z ^ m * B' = Blowup.exceptionalIdeal π Z ^ m * (C * A')`. Rewrite using `[← mul_assoc (Blowup.exceptionalIdeal π Z ^ m) C A', hC, hB', hsplit.eq_mul, Scheme.IdealSheafData.comap_mul, mul_assoc (Mon.comap π) (Blowup.exceptionalIdeal π Z ^ sdeg) A', hA']`. Use `⟨(hEC.pow m).eq_of_mul_eq_mul key, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hx1 : x ∈ (↑(Blowup.exceptionalIdeal π Z ^ m * C).support : Set ↥X')` using `support_subset_support_mul_right _ C hx`.

Rewrite `hx1` using `[hC]`. Break down `support_mul_subset _ _ hx1 with h1 | h2` into its components or cases. Rewrite `h1` using `[support_comap_coe]`. Take `⟨D₀, hD₀, hxD⟩` from `Set.mem_iUnion₂.1 (hsplit.monomial_support h1)`. Establish `hx' : x ∈ (↑((D₀.comap π)).support : Set ↥X')`.

Rewrite using `[support_comap_coe]`. Conclude with `hxD`. Break down `support_subset_union_of_locally_eq_mul_pow _ _ _ (hfac D₀ hD₀) hx' with h3 | h4` into its components or cases. Conclude with `Set.mem_iUnion₂.2 ⟨_, hSTmem D₀ hD₀, h3⟩`. Conclude with `Set.mem_iUnion₂.2 ⟨_, hExcMem, h4⟩`.

Conclude with `Set.mem_iUnion₂.2 ⟨_, hExcMem, support_pow_subset _ _ h2⟩`. Break down `Nat.lt_or_ge sdeg m with hms | hms` into its components or cases. Establish `hsub : (↑Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus Mon (m - sdeg)`. Introduce `x hx`. Use `(mem_orderAtLeastLocus_iff Mon (m - sdeg) x).2 ?_` and prove the remaining obligations.

Establish `h1 : (m : ℕ∞) ≤ orderAt Bd x` using `(mem_orderAtLeastLocus_iff Bd m x).1 (hZsub hx)`. Rewrite `h1` using `[hsplit.orderAt_eq_add T.structMap x, hordA x hx]`. Conclude with `cast_sub_le_of_cast_le_add h1`. Establish `hle : Mon ≤ Z ^ (m - sdeg)` using `le_pow_of_hasStrictNormalCrossingsWith T.structMap Z Mon T.boundary hsnc (m - sdeg) hsub`. Establish `hC2 : Blowup.exceptionalIdeal π Z ^ (m - sdeg) * C = Mon.comap π`.

Use `(hEC.pow sdeg).eq_of_mul_eq_mul ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc (Blowup.exceptionalIdeal π Z ^ sdeg) (Blowup.exceptionalIdeal π Z ^ (m - sdeg)) C, ← pow_add, Nat.add_sub_cancel' hms.le, hC, mul_comm (Mon.comap π) (Blowup.exceptionalIdeal π Z ^ sdeg)]`. Conclude with `isMonomialIn_of_exceptionalIdeal_pow_mul_eq_comap hG T hT Z hsm hsnc X' π hbl Mon hsplit.monomial (m - sdeg) hle C hC2`. Establish `hC3 : C = Mon.comap π * Blowup.exceptionalIdeal π Z ^ (sdeg - m)`. Use `(hEC.pow m).eq_of_mul_eq_mul ?_` and prove the remaining obligations.

Rewrite using `[hC, ← mul_assoc (Blowup.exceptionalIdeal π Z ^ m) (Mon.comap π) (Blowup.exceptionalIdeal π Z ^ (sdeg - m)), mul_comm (Blowup.exceptionalIdeal π Z ^ m) (Mon.comap π), mul_assoc (Mon.comap π) (Blowup.exceptionalIdeal π Z ^ m) (Blowup.exceptionalIdeal π Z ^ (sdeg - m)), ← pow_add, …`. Rewrite using `[hC3]`. Conclude with `isMonomialIn_mul _ hmonMon (isMonomialIn_pow _ (isMonomialIn_of_mem hExcMem) _)`. Introduce and unpack `D hD Cs hCirr hCsubD hCmax hCA`. Break down `List.mem_append.1 hD with hD' | hD'` into its components or cases.

Take `⟨D₀, hD₀, rfl⟩` from `List.mem_map.1 hD'`. Take `⟨η', C0, hCeq, _, hC0comp, _, hC0eq⟩` from `hG.strictTransform_components T hT Z hsm hsnc X' π hbl D₀ hD₀ Cs (isIrreducibleComponentOf_of_maximal hCirr hCsubD hCmax)`. Take `⟨hc1, hc2, hc3⟩` from `isIrreducible_subset_maximal_of_isIrreducibleComponentOf hC0comp`. Establish `hηC : η' ∈ Cs`. Rewrite using `[hCeq]`.

Conclude with `subset_closure (Set.mem_singleton η')`. Establish `h2 : η' ∈ (↑(Ad.comap π).support : Set ↥X')`. Rewrite using `[← hA']`. Conclude with `support_subset_support_mul_right _ _ (hCA hηC)`. Rewrite `h2` using `[support_comap_coe]`.

Establish `hsub0 : C0 ⊆ (↑Ad.support : Set ↥T.scheme)`. Rewrite using `[hC0eq]`. Conclude with `closure_minimal (Set.singleton_subset_iff.2 h2) Ad.support.2`. Conclude with `hsplit.transversal D₀ hD₀ C0 hc1 hc2 hc3 hsub0`. Rewrite `hD'` using `[List.mem_singleton]`.

Substitute `hD'` using the available equality. Conclude with `hG.exceptional_components_not_subset T hT Z hsm hsnc X' π hbl Ad sdeg hordA A' hA' Cs (isIrreducibleComponentOf_of_maximal hCirr hCsubD hCmax) hCA`.
-/
theorem isMonomialSplitting_of_isBlowupAlongIdealSheaf (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (Z : T.scheme.IdealSheafData)
    (hsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap))
    (hsnc : HasStrictNormalCrossingsWith T.structMap Z T.boundary)
    (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (hbl : Blowup.IsBlowupAlongIdealSheaf π Z)
    (Bd Mon Ad : T.scheme.IdealSheafData) (m sdeg : ℕ)
    (hsplit : IsMonomialSplitting T.boundary Bd Mon Ad)
    (hZsub : (↑Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus Bd m)
    (hordA : ∀ x ∈ Z.support, orderAt Ad x = (sdeg : ℕ∞))
    (B' : X'.IdealSheafData) (hB' : Blowup.exceptionalIdeal π Z ^ m * B' = Bd.comap π)
    (A' : X'.IdealSheafData) (hA' : Blowup.exceptionalIdeal π Z ^ sdeg * A' = Ad.comap π)
    (C : X'.IdealSheafData)
    (hC : Blowup.exceptionalIdeal π Z ^ m * C = Mon.comap π * Blowup.exceptionalIdeal π Z ^ sdeg) :
    IsMonomialSplitting
      (List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]) B' C A' := by
  have := hT.charZero
  have := hT.smooth
  have hEC : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hbl
  have hExcMem : Blowup.exceptionalIdeal π Z ∈
      List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z] := by
    simp
  have hSTmem : ∀ D₀ ∈ T.boundary, Blowup.strictTransform π Z D₀ ∈
      List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z] := by
    intro D₀ hD₀
    exact List.mem_append_left _ (List.mem_map.2 ⟨D₀, hD₀, rfl⟩)
  have hfac : ∀ D₀ ∈ T.boundary, ∀ x' : ↥X',
      ∃ (U : X'.Opens) (ε : ℕ), x' ∈ U ∧
        (D₀.comap π).comap U.ι =
          (Blowup.strictTransform π Z D₀).comap U.ι * (Blowup.exceptionalIdeal π Z).comap U.ι ^ ε := by
    intro D₀ hD₀ x'
    obtain ⟨U, ε, hxU, _, _, hEq⟩ :=
      hG.monomialInputs.blowup_total_transform T hT Z hsm hsnc X' π hbl D₀ hD₀ x'
    exact ⟨U, ε, hxU, hEq⟩
  have hmonD : ∀ D₀ ∈ T.boundary,
      IsMonomialIn (List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z])
        (D₀.comap π) := by
    intro D₀ hD₀
    exact isMonomialIn_of_locally_eq_mul_pow _ _ _ _ (hSTmem D₀ hD₀) hExcMem (hfac D₀ hD₀)
  have hmonMon : IsMonomialIn (List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z])
      (Mon.comap π) := by
    refine isMonomialIn_of_forall_mem ?_ (hsplit.monomial.comap π)
    intro D hD
    obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD
    exact hmonD D₀ hD₀
  have key : Blowup.exceptionalIdeal π Z ^ m * B' = Blowup.exceptionalIdeal π Z ^ m * (C * A') := by
    rw [← mul_assoc (Blowup.exceptionalIdeal π Z ^ m) C A', hC, hB', hsplit.eq_mul,
      Scheme.IdealSheafData.comap_mul,
      mul_assoc (Mon.comap π) (Blowup.exceptionalIdeal π Z ^ sdeg) A', hA']
  refine ⟨(hEC.pow m).eq_of_mul_eq_mul key, ?_, ?_, ?_⟩
  · intro x hx
    have hx1 : x ∈ (↑(Blowup.exceptionalIdeal π Z ^ m * C).support : Set ↥X') :=
      support_subset_support_mul_right _ C hx
    rw [hC] at hx1
    rcases support_mul_subset _ _ hx1 with h1 | h2
    · rw [support_comap_coe] at h1
      obtain ⟨D₀, hD₀, hxD⟩ := Set.mem_iUnion₂.1 (hsplit.monomial_support h1)
      have hx' : x ∈ (↑((D₀.comap π)).support : Set ↥X') := by
        rw [support_comap_coe]
        exact hxD
      rcases support_subset_union_of_locally_eq_mul_pow _ _ _ (hfac D₀ hD₀) hx' with h3 | h4
      · exact Set.mem_iUnion₂.2 ⟨_, hSTmem D₀ hD₀, h3⟩
      · exact Set.mem_iUnion₂.2 ⟨_, hExcMem, h4⟩
    · exact Set.mem_iUnion₂.2 ⟨_, hExcMem, support_pow_subset _ _ h2⟩
  · rcases Nat.lt_or_ge sdeg m with hms | hms
    · have hsub : (↑Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus Mon (m - sdeg) := by
        intro x hx
        refine (mem_orderAtLeastLocus_iff Mon (m - sdeg) x).2 ?_
        have h1 : (m : ℕ∞) ≤ orderAt Bd x := (mem_orderAtLeastLocus_iff Bd m x).1 (hZsub hx)
        rw [hsplit.orderAt_eq_add T.structMap x, hordA x hx] at h1
        exact cast_sub_le_of_cast_le_add h1
      have hle : Mon ≤ Z ^ (m - sdeg) :=
        le_pow_of_hasStrictNormalCrossingsWith T.structMap Z Mon T.boundary hsnc (m - sdeg) hsub
      have hC2 : Blowup.exceptionalIdeal π Z ^ (m - sdeg) * C = Mon.comap π := by
        refine (hEC.pow sdeg).eq_of_mul_eq_mul ?_
        rw [← mul_assoc (Blowup.exceptionalIdeal π Z ^ sdeg) (Blowup.exceptionalIdeal π Z ^ (m - sdeg)) C,
          ← pow_add, Nat.add_sub_cancel' hms.le, hC,
          mul_comm (Mon.comap π) (Blowup.exceptionalIdeal π Z ^ sdeg)]
      exact isMonomialIn_of_exceptionalIdeal_pow_mul_eq_comap hG T hT Z hsm hsnc X' π hbl Mon
        hsplit.monomial (m - sdeg) hle C hC2
    · have hC3 : C = Mon.comap π * Blowup.exceptionalIdeal π Z ^ (sdeg - m) := by
        refine (hEC.pow m).eq_of_mul_eq_mul ?_
        rw [hC,
          ← mul_assoc (Blowup.exceptionalIdeal π Z ^ m) (Mon.comap π)
            (Blowup.exceptionalIdeal π Z ^ (sdeg - m)),
          mul_comm (Blowup.exceptionalIdeal π Z ^ m) (Mon.comap π),
          mul_assoc (Mon.comap π) (Blowup.exceptionalIdeal π Z ^ m)
            (Blowup.exceptionalIdeal π Z ^ (sdeg - m)),
          ← pow_add, Nat.add_sub_cancel' hms]
      rw [hC3]
      exact isMonomialIn_mul _ hmonMon (isMonomialIn_pow _ (isMonomialIn_of_mem hExcMem) _)
  · rintro D hD Cs hCirr hCsubD hCmax hCA
    rcases List.mem_append.1 hD with hD' | hD'
    · obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD'
      obtain ⟨η', C0, hCeq, _, hC0comp, _, hC0eq⟩ :=
        hG.strictTransform_components T hT Z hsm hsnc X' π hbl D₀ hD₀ Cs
          (isIrreducibleComponentOf_of_maximal hCirr hCsubD hCmax)
      obtain ⟨hc1, hc2, hc3⟩ := isIrreducible_subset_maximal_of_isIrreducibleComponentOf hC0comp
      have hηC : η' ∈ Cs := by
        rw [hCeq]
        exact subset_closure (Set.mem_singleton η')
      have h2 : η' ∈ (↑(Ad.comap π).support : Set ↥X') := by
        rw [← hA']
        exact support_subset_support_mul_right _ _ (hCA hηC)
      rw [support_comap_coe] at h2
      have hsub0 : C0 ⊆ (↑Ad.support : Set ↥T.scheme) := by
        rw [hC0eq]
        exact closure_minimal (Set.singleton_subset_iff.2 h2) Ad.support.2
      exact hsplit.transversal D₀ hD₀ C0 hc1 hc2 hc3 hsub0
    · rw [List.mem_singleton] at hD'
      subst hD'
      exact hG.exceptional_components_not_subset T hT Z hsm hsnc X' π hbl Ad sdeg hordA A' hA'
        Cs (isIrreducibleComponentOf_of_maximal hCirr hCsubD hCmax) hCA

end

end FunctorialResolution.EmbeddedResolution

end
