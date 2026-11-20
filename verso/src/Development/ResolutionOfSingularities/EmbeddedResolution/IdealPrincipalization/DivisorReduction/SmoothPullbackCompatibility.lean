import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The first j+1 entries of a nonempty list consist of its head followed by the first j entries of its tail. Equality of the two prefixes therefore gives equality of both heads and both shortened tails.
-/
private theorem cons_take_succ_inj {α : Type*} (j : ℕ) (a b : α) (t₁ t₂ : List α)
    (h : List.take (j + 1) (a :: t₁) = List.take (j + 1) (b :: t₂)) :
    a = b ∧ List.take j t₁ = List.take j t₂ :=
  Eq.mp (List.cons.injEq a (List.take j t₁) b (List.take j t₂)) h

/- English proof (authored)
The bounds make both lists nonempty. At index zero, equality of the one-entry prefixes gives equality of the heads. At successor index j+1, equality of the prefixes gives equality of the first j+1 entries of the tails. The index j is valid in both tails, so induction gives equality of those entries, which are the desired entries of the original lists.
-/
private theorem get_eq_get_of_take_add_one_eq {α : Type*} :
    ∀ (j : ℕ) (l₁ l₂ : List α), List.take (j + 1) l₁ = List.take (j + 1) l₂ →
      ∀ (h₁ : j < l₁.length) (h₂ : j < l₂.length), l₁.get ⟨j, h₁⟩ = l₂.get ⟨j, h₂⟩ := by
  intro j
  induction j with
  | zero =>
    intro l₁ l₂ htake h₁ h₂
    cases l₁ with
    | nil => exact absurd h₁ (Nat.not_lt_zero 0)
    | cons a t₁ =>
      cases l₂ with
      | nil => exact absurd h₂ (Nat.not_lt_zero 0)
      | cons b t₂ => exact (cons_take_succ_inj 0 a b t₁ t₂ htake).1
  | succ j ih =>
    intro l₁ l₂ htake h₁ h₂
    cases l₁ with
    | nil => exact absurd h₁ (Nat.not_lt_zero (j + 1))
    | cons a t₁ =>
      cases l₂ with
      | nil => exact absurd h₂ (Nat.not_lt_zero (j + 1))
      | cons b t₂ =>
        exact ih t₁ t₂ (cons_take_succ_inj (j + 1) a b t₁ t₂ htake).2
          (Nat.lt_of_succ_lt_succ h₁) (Nat.lt_of_succ_lt_succ h₂)

/- English proof (authored)
Apply the prefix comparison at index j. The equal prefixes include entry j, and the two bounds ensure that this entry exists in each list.
-/
theorem get_eq_get_of_take_succ_eq {α : Type*} (l₁ l₂ : List α) (j : ℕ)
    (htake : List.take (j + 1) l₁ = List.take (j + 1) l₂)
    (h₁ : j < l₁.length) (h₂ : j < l₂.length) :
    l₁.get ⟨j, h₁⟩ = l₂.get ⟨j, h₂⟩ :=
  get_eq_get_of_take_add_one_eq j l₁ l₂ htake h₁ h₂

/- English proof (authored)
Proceed down the list. A unit ideal can be dropped before pullback because it pulls back to the unit ideal and would be dropped afterwards. For an entry other than the unit ideal, both procedures pull back the same entry and keep it exactly when its pullback is different from the unit ideal. The tails agree by induction.
-/
private theorem nontrivialPart_map_comap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (l : List X.IdealSheafData) :
    MarkedIdealWithBoundary.nontrivialPart (l.map fun D => D.comap f) =
      MarkedIdealWithBoundary.nontrivialPart ((MarkedIdealWithBoundary.nontrivialPart l).map fun D => D.comap f) := by
  unfold MarkedIdealWithBoundary.nontrivialPart
  induction l with
  | nil => simp
  | cons D l ih =>
    by_cases hD : D = ⊤
    · subst hD
      simp [AlgebraicGeometry.Scheme.IdealSheafData.comap_top, ih]
    · simp [List.filter_cons, hD, ih]

/- English proof (authored)
The two boundary lists have equal ordered lists after removing unit ideals. The filtered pullback depends only on those filtered lists, because an original unit ideal pulls back to a unit ideal. Equal filtered lists therefore have equal filtered pullbacks.
-/
theorem MarkedIdealWithBoundary.SameNontrivialBoundary.comap {X Y : Scheme.{u}} (f : Y ⟶ X)
    {E E' : List X.IdealSheafData} (h : MarkedIdealWithBoundary.SameNontrivialBoundary E E') :
    MarkedIdealWithBoundary.SameNontrivialBoundary (E.map fun D => D.comap f) (E'.map fun D => D.comap f) := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff] at h ⊢
  rw [nontrivialPart_map_comap f E, nontrivialPart_map_comap f E', h]

/- English proof (authored)
Filtering the common head either prepends that head to each filtered tail or leaves each filtered tail as it stands. Since the filtered tails are equal, the resulting lists agree in either case.
-/
private theorem nontrivialPart_cons_congr {X : Scheme.{u}} {a : X.IdealSheafData}
    {s t : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.nontrivialPart s = MarkedIdealWithBoundary.nontrivialPart t) :
    MarkedIdealWithBoundary.nontrivialPart (a :: s) = MarkedIdealWithBoundary.nontrivialPart (a :: t) := by
  simp only [MarkedIdealWithBoundary.nontrivialPart] at h
  simp only [MarkedIdealWithBoundary.nontrivialPart]
  rw [List.filter_cons, List.filter_cons, h]

/- English proof (authored)
If the common head is kept, cancel it from the two equal filtered lists. If it is removed, the equality is already the equality of the filtered tails.
-/
private theorem nontrivialPart_eq_of_cons_eq {X : Scheme.{u}} {a : X.IdealSheafData}
    {s t : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.nontrivialPart (a :: s) = MarkedIdealWithBoundary.nontrivialPart (a :: t)) :
    MarkedIdealWithBoundary.nontrivialPart s = MarkedIdealWithBoundary.nontrivialPart t := by
  simp only [MarkedIdealWithBoundary.nontrivialPart] at h
  simp only [MarkedIdealWithBoundary.nontrivialPart]
  rw [List.filter_cons, List.filter_cons] at h
  split_ifs at h with hp
  · simpa using h
  · exact h

/- English proof (authored)
Use induction on the erased position. Equal prefixes of positive length force both lists to be empty or both to have the same head. In the empty case the two erased lists agree. In the nonempty case the filtered tails agree by cancellation of the common head. If the erased index is zero, this gives the result. At a successor index, the prefixes of the tails agree through the smaller index. Apply induction to the tails and then restore the common head before filtering.
-/
private theorem nontrivialPart_eraseIdx_eq_of_take_succ_eq {X : Scheme.{u}} (j : ℕ) :
    ∀ E E' : List X.IdealSheafData,
      MarkedIdealWithBoundary.nontrivialPart E = MarkedIdealWithBoundary.nontrivialPart E' →
      List.take (j + 1) E = List.take (j + 1) E' →
      MarkedIdealWithBoundary.nontrivialPart (E.eraseIdx j) = MarkedIdealWithBoundary.nontrivialPart (E'.eraseIdx j) := by
  induction j with
  | zero =>
    intro E E' h htake
    cases E with
    | nil =>
      cases E' with
      | nil => rfl
      | cons b t => simp at htake
    | cons a s =>
      cases E' with
      | nil => simp at htake
      | cons b t =>
        rw [List.take_succ_cons, List.take_succ_cons, List.cons.injEq] at htake
        obtain ⟨hab, -⟩ := htake
        subst hab
        exact nontrivialPart_eq_of_cons_eq h
  | succ j ih =>
    intro E E' h htake
    cases E with
    | nil =>
      cases E' with
      | nil => rfl
      | cons b t => simp at htake
    | cons a s =>
      cases E' with
      | nil => simp at htake
      | cons b t =>
        rw [List.take_succ_cons, List.take_succ_cons, List.cons.injEq] at htake
        obtain ⟨hab, htl⟩ := htake
        subst hab
        exact nontrivialPart_cons_congr (ih s t (nontrivialPart_eq_of_cons_eq h) htl)

/- English proof (authored)
Interpret the boundary equivalence as equality of the lists after removing unit ideals. The common prefix through j lets us delete that index from both lists while preserving this filtered equality. Interpreting the resulting filtered equality gives the claimed boundary equivalence.
-/
theorem MarkedIdealWithBoundary.SameNontrivialBoundary.eraseIdx {X : Scheme.{u}} {E E' : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary E E') (j : ℕ)
    (htake : List.take (j + 1) E = List.take (j + 1) E') :
    MarkedIdealWithBoundary.SameNontrivialBoundary (E.eraseIdx j) (E'.eraseIdx j) :=
  (MarkedIdealWithBoundary.sameNontrivialBoundary_iff _ _).2
    (nontrivialPart_eraseIdx_eq_of_take_succ_eq j E E' ((MarkedIdealWithBoundary.sameNontrivialBoundary_iff _ _).1 h) htake)

/- English proof (authored)
In the given pullback square, the morphism to S is the base change of the surjection from Y to X. Surjectivity of scheme morphisms is stable under base change.
-/
theorem surjective_snd_of_isPullback_of_surjective {X Y S S' : Scheme.{u}} (σ : S ⟶ X) (σ' : S' ⟶ Y) (φ : Y ⟶ X)
    (ψ : S' ⟶ S) [AlgebraicGeometry.Surjective φ] (hpb : IsPullback σ' ψ φ σ) :
    AlgebraicGeometry.Surjective ψ := by
  have hφ : AlgebraicGeometry.Surjective φ := inferInstance
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hφ

namespace DivisorReduction

/- English proof (authored)
The kernel of the original closed immersion is D. The kernel of the composite from the pulled back subscheme is the image ideal under h of the pullback of D. The adjunction for pullback and image of ideals gives inclusion of D in this image ideal.
-/
private theorem ker_subschemeι_le_ker_comp {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) :
    Scheme.Hom.ker D.subschemeι ≤ Scheme.Hom.ker (D'.subschemeι ≫ h) := by
  subst hD
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι, AlgebraicGeometry.Scheme.Hom.ker_comp,
    AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]
  exact AlgebraicGeometry.Scheme.IdealSheafData.le_map_comap D h

/- English proof (authored)
The map from the pulled back subscheme to the original ambient scheme has kernel containing D. The universal property of the closed subscheme defined by D therefore gives a factorization through its inclusion. Pulling any ambient ideal back along the two equal composites gives equal ideals, and the composition rule expresses them as the asserted two successive pullbacks.
-/
private theorem exists_subscheme_hom_comp_subschemeι_eq {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) :
    ∃ g : D'.subscheme ⟶ D.subscheme,
      g ≫ D.subschemeι = D'.subschemeι ≫ h ∧
        ∀ I₀ : X.IdealSheafData,
          (I₀.comap D.subschemeι).comap g = (I₀.comap h).comap D'.subschemeι := by
  have hsq : AlgebraicGeometry.IsClosedImmersion.lift D.subschemeι (D'.subschemeι ≫ h)
      (ker_subschemeι_le_ker_comp h D D' hD) ≫ D.subschemeι = D'.subschemeι ≫ h :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac ..
  refine ⟨AlgebraicGeometry.IsClosedImmersion.lift D.subschemeι (D'.subschemeι ≫ h)
      (ker_subschemeι_le_ker_comp h D D' hD), hsq, fun I₀ => ?_⟩
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hsq,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_comp]

def subschemeMapOfComap {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData) (D' : Y.IdealSheafData)
    (hD : D' = D.comap h) : D'.subscheme ⟶ D.subscheme :=
  (exists_subscheme_hom_comp_subschemeι_eq h D D' hD).choose

/- English proof (authored)
The induced map is chosen from the factorization of the composite through the original closed subscheme. The equality is the commutativity of that factorization square.
-/
theorem subschemeMapOfComap_comp {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) :
    subschemeMapOfComap h D D' hD ≫ D.subschemeι = D'.subschemeι ≫ h :=
  (exists_subscheme_hom_comp_subschemeι_eq h D D' hD).choose_spec.1

/- English proof (authored)
Pull back the ambient ideal along the commuting square of closed subschemes. The two paths from the pulled back subscheme to the original ambient scheme are equal, so pulling back in two stages along these paths gives the same ideal.
-/
theorem comap_subschemeMapOfComap {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) (I₀ : X.IdealSheafData) :
    (I₀.comap D.subschemeι).comap (subschemeMapOfComap h D D' hD) = (I₀.comap h).comap D'.subschemeι :=
  (exists_subscheme_hom_comp_subschemeι_eq h D D' hD).choose_spec.2 I₀

/- English proof (authored)
The square of subscheme inclusions gives the same two-step pullback for each ideal. Applying this entrywise preserves order, so the two resulting lists agree. Equivalently, compare the heads using the pullback equality and the tails by induction.
-/
private theorem map_comap_comap_subschemeι {X Y : Scheme.{u}} (h : Y ⟶ X)
    (D : X.IdealSheafData) (D' : Y.IdealSheafData) (hD : D' = D.comap h)
    (M : List X.IdealSheafData) :
    ((M.map fun I => I.comap h).map fun I => I.comap D'.subschemeι)
      = (M.map fun I => I.comap D.subschemeι).map fun I => I.comap (subschemeMapOfComap h D D' hD) := by
  induction M with
  | nil => rfl
  | cons I t ih =>
    simp only [List.map_cons]
    rw [comap_subschemeMapOfComap h D D' hD I, ih]

/- English proof (authored)
Pull back the given boundary equivalence to the pulled back divisor. Equivalence is preserved by pullback. On the side obtained from the original ambient boundary, the commuting square lets each entry be pulled back first to the original divisor and then along the induced divisor map. This gives the stated lists.
-/
theorem sameNontrivialBoundary_comap_subschemeι {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) (M : List X.IdealSheafData)
    (M' : List Y.IdealSheafData)
    (hM : MarkedIdealWithBoundary.SameNontrivialBoundary M' (M.map fun I => I.comap h)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (M'.map fun I => I.comap D'.subschemeι)
      ((M.map fun I => I.comap D.subschemeι).map fun I => I.comap (subschemeMapOfComap h D D' hD)) := by
  rw [← map_comap_comap_subschemeι h D D' hD M]
  exact hM.comap D'.subschemeι

def componentsInOrderLocusIdeal {X : Scheme.{u}} (I : X.IdealSheafData) (m : ℕ) (D : X.IdealSheafData) :
    X.IdealSheafData :=
  @dite X.IdealSheafData
    (IsOpen {x : ↥D.subscheme | connectedComponent x ⊆ ⇑D.subschemeι ⁻¹' orderAtLeastLocus I m})
    (Classical.propDecidable _)
    (fun hop =>
      Scheme.Hom.ker
        (Scheme.Opens.ι
            ({ carrier := {x : ↥D.subscheme |
                  connectedComponent x ⊆ ⇑D.subschemeι ⁻¹' orderAtLeastLocus I m},
                is_open' := hop } : D.subscheme.Opens) ≫
          D.subschemeι))
    (fun _ => ⊤)

/- English proof (authored)
Consider the union of components of the selected divisor contained in the marked order locus. When this union is open on the divisor, both ideals are the kernel of its inclusion into the ambient scheme. Otherwise both are the unit ideal by their defining convention.
-/
theorem containedComponentsIdeal_eq_componentsInOrderLocusIdeal (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) :
    containedComponentsIdeal T j hj = componentsInOrderLocusIdeal T.ideal T.mult (T.boundary.get ⟨j, hj⟩) := by
  unfold componentsInOrderLocusIdeal
  split_ifs with h
  · exact containedComponentsIdeal_eq_ker T j hj h
  · exact containedComponentsIdeal_eq_top_of_not_isOpen T j hj h

structure SmoothPullbackCompatibility : Prop where
  comap_ne_top : ∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [AlgebraicGeometry.Surjective h]
    (Z : X.IdealSheafData), Z ≠ ⊤ → Z.comap h ≠ ⊤
  coSupport_comap : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
      ∀ m : ℕ, orderAtLeastLocus (T.ideal.comap h) m = ⇑h ⁻¹' orderAtLeastLocus T.ideal m
  isPullback_inducedHom : ∀ (X Y : Scheme.{u}) (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h),
      IsPullback (subschemeMapOfComap h D D' hD) D'.subschemeι D.subschemeι h
  smooth_of_isPullback : ∀ (X Y S S' : Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y) (φ : Y ⟶ X)
    (ψ : S' ⟶ S), IsPullback σ' ψ φ σ → AlgebraicGeometry.Smooth φ → AlgebraicGeometry.Smooth ψ
  lowerIdealPre_comap : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
      ∀ (E' : List Y.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
          List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
          ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
          T.IsOrderBoundedByMult →
          containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = (containedComponentsIdeal T j hj).comap h →
            lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE =
              (lowerIdealAfterBlowup T j hj).comap h
  boundaryEquiv_restrictedBoundary_comap : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
      ∀ (E' : List Y.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
          List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
          ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
          T.IsOrderBoundedByMult →
          containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = (containedComponentsIdeal T j hj).comap h →
            MarkedIdealWithBoundary.SameNontrivialBoundary
              (List.take (E'.length - 1)
                ((lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE).eraseIdx j))
              (List.map (fun D => D.comap h)
                (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j)))
  preIdeal_comap : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
      ∀ (E' : List Y.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
          List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
          ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
            containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = (containedComponentsIdeal T j hj).comap h

def divisorPullbackMap (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData) (Y : Scheme.{u})
    (h : Y ⟶ T.scheme) (D' : Y.IdealSheafData) (hD : D' = (T.boundary.get ⟨j, hj⟩).comap h) :
    D'.subscheme ⟶ (restrictToBoundaryDivisor T j hj I₀ E₀).scheme :=
  subschemeMapOfComap h (T.boundary.get ⟨j, hj⟩) D' hD

/- English proof (authored)
The divisor map is the induced map from the closed subscheme defined by the pulled back ideal. The assumed pullback compatibility for induced maps of these closed subschemes gives the stated square.
-/
theorem isPullback_divisorPullbackMap (hbc : SmoothPullbackCompatibility.{u}) (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
    (E₀ : List T.scheme.IdealSheafData) (Y : Scheme.{u}) (h : Y ⟶ T.scheme)
    (D' : Y.IdealSheafData) (hD : D' = (T.boundary.get ⟨j, hj⟩).comap h) :
    IsPullback (divisorPullbackMap T j hj I₀ E₀ Y h D' hD) D'.subschemeι
      (T.boundary.get ⟨j, hj⟩).subschemeι h :=
  hbc.isPullback_inducedHom _ _ h _ D' hD

/- English proof (authored)
The boundary of the pulled back marked object is obtained by pulling back every original boundary entry and keeps the original length. The given equality of prefixes through j identifies its entry j with entry j of the replacement boundary. The former is the pullback of the original entry at that index.
-/
theorem get_eq_comap_get_boundary (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData)
    (hjE : j < E'.length)
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary) :
    E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap h := by
  have hb : (T.pullbackAlong Y q h).boundary = List.map (fun D => D.comap h) T.boundary :=
    MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h
  have htake' : List.take (j + 1) E' =
      List.take (j + 1) (List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary) := by
    rw [htake, hb]
    rfl
  have hlen : j < (List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary).length := by
    simpa using hj
  rw [get_eq_get_of_take_succ_eq E'
    (List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary) j htake' hjE hlen]
  simp

/- English proof (authored)
Substitute the equality of the divisor ideals. With the ambient ideal and marking fixed, the selected component construction is then applied to the same divisor.
-/
private theorem componentsInOrderLocusIdeal_congr {X : Scheme.{u}} (I : X.IdealSheafData) (m : ℕ)
    {D D' : X.IdealSheafData} (hD : D = D') :
    componentsInOrderLocusIdeal I m D = componentsInOrderLocusIdeal I m D' := by
  rw [hD]

/- English proof (authored)
The original pulled back boundary and its replacement agree in the prefix through j. Thus their selected divisor ideals are equal. Replacing the list leaves the ambient ideal and marking unchanged, and the contained-components construction depends only on these data and the selected divisor. The two center ideals are therefore equal.
-/
theorem containedComponentsIdeal_withBoundary (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData)
    (hjE : j < E'.length) (hj' : j < (T.pullbackAlong Y q h).boundary.length)
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary) :
    containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
      containedComponentsIdeal (T.pullbackAlong Y q h) j hj' := by
  have hget : E'.get ⟨j, hjE⟩ = ((T.pullbackAlong Y q h).boundary).get ⟨j, hj'⟩ :=
    get_eq_get_of_take_succ_eq E' ((T.pullbackAlong Y q h).boundary) j htake hjE hj'
  rw [containedComponentsIdeal_eq_componentsInOrderLocusIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE,
    containedComponentsIdeal_eq_componentsInOrderLocusIdeal (T.pullbackAlong Y q h) j hj']
  exact componentsInOrderLocusIdeal_congr _ _ hget

/- English proof (authored)
The assumed pullback compatibility for surjections applies to the given ideal, which differs from the unit ideal. It gives that the pulled back ideal also differs from the unit ideal.
-/
theorem comap_ne_top_of_surjective (hbc : SmoothPullbackCompatibility.{u}) {X Y : Scheme.{u}} (h : Y ⟶ X)
    [AlgebraicGeometry.Surjective h] (Z : X.IdealSheafData) (hZ : Z ≠ ⊤) : Z.comap h ≠ ⊤ :=
  hbc.comap_ne_top _ _ h Z hZ

/- English proof (authored)
Changing the boundary leaves the ideal of the pulled back marked object unchanged. The assumed smooth pullback rule for order loci therefore identifies the locus at any given threshold with the inverse image of the original locus.
-/
theorem orderAtLeastLocus_withBoundary_pullbackAlong (hbc : SmoothPullbackCompatibility.{u}) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h] (hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
    (m : ℕ) :
    orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal m = ⇑h ⁻¹' orderAtLeastLocus T.ideal m :=
  hbc.coSupport_comap T hV Y q h hq m

/- English proof (authored)
Without a preparatory blowup the lower ideal is the starting ideal, since its identity pullback fixes it. The replacement boundary leaves that ideal unchanged, and the starting ideal of the pulled back object is the pullback of the original ideal.
-/
theorem lowerIdealWithoutBlowup_withBoundary (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData) :
    lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E') = (lowerIdealWithoutBlowup T).comap h := by
  have h1 : ((T.pullbackAlong Y q h).withBoundary E').ideal = (T.pullbackAlong Y q h).ideal :=
    MarkedIdealWithBoundary.withBoundary_ideal (T.pullbackAlong Y q h) E'
  have h2 : (T.pullbackAlong Y q h).ideal = T.ideal.comap h :=
    MarkedIdealWithBoundary.pullbackAlong_ideal T Y q h
  simp [lowerIdealWithoutBlowup, h1, h2]
  exact AlgebraicGeometry.Scheme.IdealSheafData.comap_id ..

/- English proof (authored)
Deleting a valid index reduces the list length by one. Taking exactly that many entries of the shortened list returns the full shortened list.
-/
private theorem take_length_sub_one_eraseIdx {α : Type*} (l : List α) (j : ℕ) (hj : j < l.length) :
    List.take (l.length - 1) (l.eraseIdx j) = l.eraseIdx j := by
  refine List.take_of_length_le ?_
  have h2 := List.length_eraseIdx_add_one hj
  omega

/- English proof (authored)
Both lower boundaries before restriction are their respective starting boundaries. The selected index is valid on each side, so the prefixes of length one less than the corresponding original lengths retain the full erased lists. The equivalence of the pulled back and replacement boundaries persists after deletion of j because their prefixes through j agree. Deleting an index commutes with entrywise pullback, which identifies the first erased list with the pullback of the erased original boundary. This proves the required equivalence.
-/
theorem sameNontrivialBoundary_lowerBoundaryWithoutBlowup (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    (E' : List Y.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
    (hjE : j < E'.length) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (E'.length - 1)
        ((lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E')).eraseIdx j))
      (List.map (fun D => D.comap h)
        (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j))) := by
  have hpb : List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary
      = ((T.pullbackAlong Y q h).boundary : List Y.IdealSheafData) :=
    (MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h).symm
  have hBE' : MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary) E' :=
    (MarkedIdealWithBoundary.sameNontrivialBoundary_iff _ _).2
      ((congrArg (fun l : List Y.IdealSheafData => MarkedIdealWithBoundary.nontrivialPart l) hpb).trans
        ((MarkedIdealWithBoundary.sameNontrivialBoundary_iff _ _).1 hBE))
  have htake' : List.take (j + 1) E'
      = List.take (j + 1) (List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary) :=
    htake.trans (congrArg (fun l : List Y.IdealSheafData => List.take (j + 1) l) hpb.symm)
  have hmid : MarkedIdealWithBoundary.nontrivialPart (E'.eraseIdx j)
      = MarkedIdealWithBoundary.nontrivialPart
        ((List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary).eraseIdx j) :=
    (MarkedIdealWithBoundary.sameNontrivialBoundary_iff _ _).1 (hBE'.symm.eraseIdx j htake')
  have hmap : (List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary).eraseIdx j
      = List.map (fun D : T.scheme.IdealSheafData => D.comap h) (T.boundary.eraseIdx j) :=
    List.eraseIdx_map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary j
  have hA0 : ((lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E')) : List Y.IdealSheafData)
      = E' :=
    (lowerBoundaryWithoutBlowup_eq ((T.pullbackAlong Y q h).withBoundary E')).trans
      (MarkedIdealWithBoundary.withBoundary_boundary (T.pullbackAlong Y q h) E')
  have hLeq : List.take (E'.length - 1)
        (((lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E')) :
          List Y.IdealSheafData).eraseIdx j)
      = E'.eraseIdx j :=
    (congrArg (fun l : List Y.IdealSheafData =>
        List.take (E'.length - 1) (l.eraseIdx j)) hA0).trans
      (take_length_sub_one_eraseIdx E' j hjE)
  have hCeq : List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)
      = T.boundary.eraseIdx j :=
    (congrArg (fun l : List T.scheme.IdealSheafData =>
        List.take (T.boundary.length - 1) (l.eraseIdx j)) (lowerBoundaryWithoutBlowup_eq T)).trans
      (take_length_sub_one_eraseIdx T.boundary j hj)
  exact (MarkedIdealWithBoundary.sameNontrivialBoundary_iff _ _).2
    (((congrArg (fun l : List Y.IdealSheafData => MarkedIdealWithBoundary.nontrivialPart l) hLeq).trans
        (hmid.trans
          (congrArg (fun l : List Y.IdealSheafData => MarkedIdealWithBoundary.nontrivialPart l) hmap))).trans
      (congrArg (fun l : List T.scheme.IdealSheafData =>
          MarkedIdealWithBoundary.nontrivialPart
            (List.map (fun D : T.scheme.IdealSheafData => D.comap h) l)) hCeq.symm))

/- English proof (authored)
By the given center equality, the pulled back contained-components ideal is the contained-components ideal for the admissible replaced object. The supplied preparatory blowup property says that the identity is a blowup along that center.
-/
theorem isBlowupAlongIdealSheaf_id_comap_containedComponentsIdeal (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (j : ℕ)
    (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base))
    (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData)
    (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible) (hj : j < T.boundary.length)
    (hjE : j < E'.length)
    (heq : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = (containedComponentsIdeal T j hj).comap h) :
    Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) ((containedComponentsIdeal T j hj).comap h) := by
  rw [← heq]
  exact hfacts.isBlowup_id_preIdeal _ hV' j hjE

/- English proof (authored)
Substitute the equality of the two marked objects. Both assigned sequences now come from the same object with the same ambient type, so their underlying sequences are equal by reflexivity.
-/
private theorem heq_toSequenceOfBlowups_of_eq (L : PrincipalizationAssignment.{u}) {S₁ S₂ : MarkedIdealWithBoundary.{u}}
    (hS : S₁ = S₂) : HEq (L S₁).toSequenceOfBlowups (L S₂).toSequenceOfBlowups := by
  cases hS
  exact HEq.refl _

/- English proof (authored)
The two sequences over the same ambient scheme have the same type, so the given heterogeneous equality yields an ordinary equality. Substituting it transfers the strict pullback property.
-/
private theorem isStrictPullbackSequenceOfBlowups_of_heq {X' X : Scheme.{u}} (φ : X' ⟶ X) (B : SequenceOfBlowups X)
    {B₁ B₂ : SequenceOfBlowups X'} (hB : HEq B₁ B₂) (h : IsStrictPullbackBlowupSeq φ B₁ B) :
    IsStrictPullbackBlowupSeq φ B₂ B := by
  have hB' : B₁ = B₂ := eq_of_heq hB
  rw [← hB']
  exact h

/- English proof (authored)
The common prefix identifies the chosen divisor on the new ambient scheme with the pullback of the original divisor. Its induced map is smooth and surjective by the pullback square, and the square also shows that it respects the structure maps to the ground field. With unit contained-components ideals on both sides, use the lower ideal without a preparatory step. Its pullback formula and the commuting square identify the two lower ideals. After deletion of the selected boundary entry, the lower boundaries agree up to unit entries, and this equivalence survives restriction to the pulled back divisor.

Thus the pulled back lower object with the replacement boundary is precisely the lower object constructed on the new ambient scheme. Both lower objects are admissible by the unit-center case and have dimension below the induction bound by the dimension-drop result. The strict smooth pullback property of the lower-dimensional assignment applies. Substituting the identified marked object gives the claimed strict pullback of sequences.
-/
theorem isStrictPullbackBlowupSeq_restrictToDivisor_of_eq_top (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (n : ℕ)
    (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ)
    (hbc : SmoothPullbackCompatibility.{u}) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (hO : T.IsOrderBoundedByMult) (hbal : T.IsBalanced hV.locallyOfFiniteType)
    (hj : j < T.boundary.length) (hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth h]
    [AlgebraicGeometry.Surjective h] (hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
    (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
    (hdim' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
    (hO' : ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult)
    (hDB' : ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
    (hjE : j < E'.length)
    (hcs' : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult).Nonempty)
    (hZ : containedComponentsIdeal T j hj = ⊤)
    (hZ' : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = ⊤) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩)
        (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
      (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
      (L (restrictToDivisor T j hj)).toSequenceOfBlowups := by
  have hD : E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap h :=
    get_eq_comap_get_boundary T j hj Y q h E' hjE htake
  have hpb : IsPullback
      (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩) hD)
      (E'.get ⟨j, hjE⟩).subschemeι (T.boundary.get ⟨j, hj⟩).subschemeι h :=
    isPullback_divisorPullbackMap hbc T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
      (E'.get ⟨j, hjE⟩) hD
  have hsm : AlgebraicGeometry.Smooth
      (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩) hD) :=
    hbc.smooth_of_isPullback T.scheme Y (T.boundary.get ⟨j, hj⟩).subscheme
      (E'.get ⟨j, hjE⟩).subscheme (T.boundary.get ⟨j, hj⟩).subschemeι
      (E'.get ⟨j, hjE⟩).subschemeι h
      (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩) hD)
      hpb.flip inferInstance
  have hsj : AlgebraicGeometry.Surjective
      (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩) hD) :=
    surjective_snd_of_isPullback_of_surjective (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι h
      (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩) hD)
      hpb.flip
  have hq₀ : (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
        (E'.get ⟨j, hjE⟩) hD) ≫ (restrictToDivisor T j hj).structMap
      = (E'.get ⟨j, hjE⟩).subschemeι ≫ q := by
    have key : subschemeMapOfComap h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD ≫
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
          = (E'.get ⟨j, hjE⟩).subschemeι ≫ q := by
      rw [← Category.assoc, subschemeMapOfComap_comp, Category.assoc, hq]
    exact key
  have hideal : ((restrictToDivisor T j hj).ideal).comap
        (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩) hD)
      = (lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E')).comap
          (E'.get ⟨j, hjE⟩).subschemeι := by
    rw [lowerIdealWithoutBlowup_withBoundary T Y q h E']
    exact comap_subschemeMapOfComap h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD (lowerIdealWithoutBlowup T)
  have hTriple : ((restrictToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
          (E'.get ⟨j, hjE⟩) hD)).withBoundary
        ((restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)
      = restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE :=
    congrArg
      (fun J => T.withSchemeIdealBoundary (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q) J
        ((restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)) hideal
  have hBE₀ : MarkedIdealWithBoundary.SameNontrivialBoundary
      (((restrictToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
          ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
          (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
            (E'.get ⟨j, hjE⟩) hD)).boundary)
      ((restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary) := by
    rw [MarkedIdealWithBoundary.pullbackAlong_boundary]
    exact (sameNontrivialBoundary_comap_subschemeι h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD
      (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j))
      (List.take (E'.length - 1)
        ((lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E')).eraseIdx j))
      (sameNontrivialBoundary_lowerBoundaryWithoutBlowup T j hj Y q h E' hBE htake hjE)).symm
  have hValid₀ : (((restrictToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
          (E'.get ⟨j, hjE⟩) hD)).withBoundary
        ((restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)).IsAdmissible := by
    rw [hTriple]
    exact hfacts.valid_lowerTop ((T.pullbackAlong Y q h).withBoundary E') hV' hO' hDB' j hjE hZ'
  have hdim₀ : (((restrictToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
          (E'.get ⟨j, hjE⟩) hD)).withBoundary
        ((restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)).krullDimSucc < n := by
    rw [hTriple]
    exact lt_of_lt_of_le
      (hfacts.lowerTriple_dim_lt ((T.pullbackAlong Y q h).withBoundary E') hV' hcs' j hjE
        (lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))
        (lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))) hdim'
  have hmain := hL.smooth_pullback_strict (restrictToDivisor T j hj)
    (hfacts.valid_lowerTop T hV hO hbal j hj hZ)
    (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcs j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T))
      hdim)
    (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
    (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩) hD)
    hq₀ ((restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary) hBE₀ hValid₀ hdim₀
  exact isStrictPullbackSequenceOfBlowups_of_heq _ _ (heq_toSequenceOfBlowups_of_eq L hTriple) hmain

/- English proof (authored)
The chosen divisor is pulled back from the original one because the boundary prefixes agree through its index. The induced divisor map is smooth and surjective by base change and respects the structure maps. The new contained-components ideal is the pullback of the original one and differs from the unit ideal by surjectivity. The assumed compatibility for the preparatory transform identifies the two lower ideals after pulling back and restricting along the commuting square. The corresponding compatibility for the truncated boundaries, followed by pullback to the divisor, gives equivalence after removing unit entries.

It follows that the pulled back twisted lower object, equipped with the new lower boundary, equals the twisted lower object on the new ambient scheme. The nonunit-center admissibility result and dimension drop put both objects within the lower-dimensional assignment. Applying its strict smooth pullback property and substituting the equality of lower objects proves the claimed comparison.
-/
theorem isStrictPullbackBlowupSeq_restrictTwistedToDivisor (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (n : ℕ)
    (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ)
    (hbc : SmoothPullbackCompatibility.{u}) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (hO : T.IsOrderBoundedByMult) (hbal : T.IsBalanced hV.locallyOfFiniteType)
    (hj : j < T.boundary.length) (hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth h]
    [AlgebraicGeometry.Surjective h] (hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
    (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
    (hdim' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
    (hO' : ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult)
    (hDB' : ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
    (hjE : j < E'.length)
    (hcs' : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult).Nonempty)
    (hZ : containedComponentsIdeal T j hj ≠ ⊤)
    (hZ' : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
      (containedComponentsIdeal T j hj).comap h) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h (E'.get ⟨j, hjE⟩)
        (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
      (L (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
      (L (restrictTwistedToDivisor T j hj)).toSequenceOfBlowups := by
  have hD : E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap h :=
    get_eq_comap_get_boundary T j hj Y q h E' hjE htake
  have hZ'ne : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE ≠ ⊤ := by
    rw [hZ']
    exact comap_ne_top_of_surjective hbc h (containedComponentsIdeal T j hj) hZ
  have hpb : IsPullback
      (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
        (E'.get ⟨j, hjE⟩) hD)
      (E'.get ⟨j, hjE⟩).subschemeι (T.boundary.get ⟨j, hj⟩).subschemeι h :=
    isPullback_divisorPullbackMap hbc T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
      (E'.get ⟨j, hjE⟩) hD
  have hsm : AlgebraicGeometry.Smooth
      (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
        (E'.get ⟨j, hjE⟩) hD) :=
    hbc.smooth_of_isPullback T.scheme Y (T.boundary.get ⟨j, hj⟩).subscheme
      (E'.get ⟨j, hjE⟩).subscheme (T.boundary.get ⟨j, hj⟩).subschemeι
      (E'.get ⟨j, hjE⟩).subschemeι h
      (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
        (E'.get ⟨j, hjE⟩) hD)
      hpb.flip inferInstance
  have hsj : AlgebraicGeometry.Surjective
      (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
        (E'.get ⟨j, hjE⟩) hD) :=
    surjective_snd_of_isPullback_of_surjective (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι h
      (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
        (E'.get ⟨j, hjE⟩) hD)
      hpb.flip
  have hq₀ : (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
        (E'.get ⟨j, hjE⟩) hD) ≫ (restrictTwistedToDivisor T j hj).structMap
      = (E'.get ⟨j, hjE⟩).subschemeι ≫ q := by
    have key : subschemeMapOfComap h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD ≫
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
          = (E'.get ⟨j, hjE⟩).subschemeι ≫ q := by
      rw [← Category.assoc, subschemeMapOfComap_comp, Category.assoc, hq]
    exact key
  have hideal : ((restrictTwistedToDivisor T j hj).ideal).comap
        (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
          (E'.get ⟨j, hjE⟩) hD)
      = (lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE).comap
          (E'.get ⟨j, hjE⟩).subschemeι := by
    rw [hbc.lowerIdealPre_comap T hV Y q h hq E' hBE j hj hjE htake hV' hO hZ']
    exact comap_subschemeMapOfComap h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD (lowerIdealAfterBlowup T j hj)
  have hTriple : ((restrictTwistedToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
          (E'.get ⟨j, hjE⟩) hD)).withBoundary
        ((restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)
      = restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE :=
    congrArg
      (fun J => T.withSchemeIdealBoundary (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q) J
        ((restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)) hideal
  have hBE₀ : MarkedIdealWithBoundary.SameNontrivialBoundary
      (((restrictTwistedToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
          ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
          (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
            (E'.get ⟨j, hjE⟩) hD)).boundary)
      ((restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary) := by
    rw [MarkedIdealWithBoundary.pullbackAlong_boundary]
    exact (sameNontrivialBoundary_comap_subschemeι h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD
      (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j))
      (List.take (E'.length - 1)
        ((lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE).eraseIdx j))
      (hbc.boundaryEquiv_restrictedBoundary_comap T hV Y q h hq E' hBE j hj hjE htake hV' hO hZ')).symm
  have hValid₀ : (((restrictTwistedToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
          (E'.get ⟨j, hjE⟩) hD)).withBoundary
        ((restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)).IsAdmissible := by
    rw [hTriple]
    exact hfacts.valid_lowerPre ((T.pullbackAlong Y q h).withBoundary E') hV' hO' hDB' j hjE hZ'ne
  have hdim₀ : (((restrictTwistedToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
          (E'.get ⟨j, hjE⟩) hD)).withBoundary
        ((restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)).krullDimSucc < n := by
    rw [hTriple]
    exact lt_of_lt_of_le
      (hfacts.lowerTriple_dim_lt ((T.pullbackAlong Y q h).withBoundary E') hV' hcs' j hjE
        (lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)
        (lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)) hdim'
  have hmain := hL.smooth_pullback_strict (restrictTwistedToDivisor T j hj)
    (hfacts.valid_lowerPre T hV hO hbal j hj hZ)
    (lt_of_lt_of_le
      (hfacts.lowerTriple_dim_lt T hV hcs j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj))
      hdim)
    (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
    (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h (E'.get ⟨j, hjE⟩) hD)
    hq₀ ((restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary) hBE₀ hValid₀ hdim₀
  exact isStrictPullbackSequenceOfBlowups_of_heq _ _ (heq_toSequenceOfBlowups_of_eq L hTriple) hmain

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
