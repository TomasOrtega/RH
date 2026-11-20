import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure BlowupSequenceData (X : Scheme.{u}) : Type (u + 1) where
  length : ℕ
  obj : ℕ → Scheme.{u}
  map : ∀ i : ℕ, obj (i + 1) ⟶ obj i
  isoZero : obj 0 ≅ X
  center : ∀ i : ℕ, (obj i).IdealSheafData
  isBlowup : ∀ i, i < length → Blowup.IsBlowupAlongIdealSheaf (map i) (center i)

namespace BlowupSequenceData

variable {X : Scheme.{u}}

def projectionToBase (d : BlowupSequenceData X) : ∀ i : ℕ, d.obj i ⟶ X
  | 0 => d.isoZero.hom
  | (i + 1) => d.map i ≫ projectionToBase d i

@[simp]
/- English proof (authored)
The projection at stage zero is defined to be the forward map of the initial isomorphism to the base.
-/
theorem projectionToBase_zero (d : BlowupSequenceData X) : projectionToBase d 0 = d.isoZero.hom := rfl

@[simp]
/- English proof (authored)
The recursive definition of the projection at the next stage takes the transition to the current stage and then the current projection to the base.
-/
theorem projectionToBase_succ (d : BlowupSequenceData X) (i : ℕ) :
    projectionToBase d (i + 1) = d.map i ≫ projectionToBase d i := rfl

private def homAdd (d : BlowupSequenceData X) (i : ℕ) : ∀ k : ℕ, d.obj (i + k) ⟶ d.obj i
  | 0 => 𝟙 (d.obj i)
  | (k + 1) => d.map (i + k) ≫ homAdd d i k

private def homOfLE (d : BlowupSequenceData X) {i j : ℕ} (h : i ≤ j) : d.obj j ⟶ d.obj i :=
  eqToHom (congrArg d.obj (Nat.add_sub_cancel' h).symm) ≫ homAdd d i (j - i)

/- English proof (authored)
Substitute zero for the length. The two stages now coincide, so the identification of their objects is the identity. A composite of zero transitions is also the identity, and composing these identities gives the result.
-/
private theorem eqToHom_comp_iteratedBlowupMorphism_of_eq_zero (d : BlowupSequenceData X) (i k : ℕ)
    (h : d.obj i = d.obj (i + k)) (hk : k = 0) :
    eqToHom h ≫ homAdd d i k = 𝟙 (d.obj i) := by
  subst hk
  have h1 : homAdd d i 0 = 𝟙 (d.obj i) := rfl
  have h2 : eqToHom h = 𝟙 (d.obj i) := rfl
  rw [h1, h2]
  exact Category.id_comp (𝟙 (d.obj i))

/- English proof (authored)
A transition from stage $i$ to itself is defined using the length $i-i=0$. Both the index identification and the composite of zero steps are identities.
-/
private theorem towerMorphism_refl (d : BlowupSequenceData X) (i : ℕ) :
    homOfLE d (le_refl i) = 𝟙 (d.obj i) :=
  eqToHom_comp_iteratedBlowupMorphism_of_eq_zero d i (i - i)
    (congrArg d.obj (Nat.add_sub_cancel' (le_refl i)).symm) (Nat.sub_self i)

/- English proof (authored)
The zero-length composite in the recursive definition is the identity on its starting stage.
-/
private theorem iteratedBlowupMorphism_zero (d : BlowupSequenceData X) (i : ℕ) :
    homAdd d i 0 = 𝟙 (d.obj i) := rfl

/- English proof (authored)
In the recursion for a composite of $k+1$ steps ending at stage $i$, the first map goes from stage $i+k+1$ to $i+k$. The remaining $k$ steps form the composite ending at $i$.
-/
private theorem iteratedBlowupMorphism_succ (d : BlowupSequenceData X) (i k : ℕ) :
    homAdd d i (k + 1) = d.map (i + k) ≫ homAdd d i k := rfl

/- English proof (authored)
Identify the two equal indices at both the source and the target of the transition. The identification maps then become identities, and both composites are the same transition.
-/
private theorem blowupMorphism_comp_eqToHom (d : BlowupSequenceData X) {n m : ℕ} (h : n = m) :
    d.map n ≫ eqToHom (congrArg d.obj h) =
      eqToHom (show d.obj (n + 1) = d.obj (m + 1) by rw [h]) ≫ d.map m := by
  subst h
  simp

/- English proof (authored)
Replace either length by the other along the given equality. The composites now have the same source, and the intervening identification is the identity.
-/
private theorem iteratedBlowupMorphism_congr_length (d : BlowupSequenceData X) (i : ℕ) {k k' : ℕ} (h : k = k') :
    homAdd d i k =
      eqToHom (show d.obj (i + k) = d.obj (i + k') by rw [h]) ≫ homAdd d i k' := by
  subst h
  simp

/- English proof (authored)
Substitute one starting index for the other. The source and target identifications are identities, so the two sides are the same composite of the specified length.
-/
private theorem iteratedBlowupMorphism_congr_start (d : BlowupSequenceData X) {i i' : ℕ} (h : i = i') (k : ℕ) :
    homAdd d i k =
      eqToHom (show d.obj (i + k) = d.obj (i' + k) by rw [h]) ≫ homAdd d i' k ≫
        eqToHom (show d.obj i' = d.obj i by rw [h]) := by
  subst h
  simp

/- English proof (authored)
Induct on the number of steps in the part of the composite starting farthest from stage $i$. With zero steps, the assertion is the identity law. For the successor, extract the first transition and apply induction to the rest. Move the index identification past that transition, using the equalities of its source and target indices obtained by associating the sum. The resulting composite is the recursion for the sum of the two lengths.
-/
private theorem iteratedBlowupMorphism_comp_iteratedBlowupMorphism (d : BlowupSequenceData X) (i a b : ℕ) :
    homAdd d (i + a) b ≫ homAdd d i a =
      eqToHom (congrArg d.obj (Nat.add_assoc i a b)) ≫ homAdd d i (a + b) := by
  induction b with
  | zero =>
      show homAdd d (i + a) 0 ≫ homAdd d i a
          = eqToHom (rfl : d.obj (i + a) = d.obj (i + a)) ≫ homAdd d i a
      rw [iteratedBlowupMorphism_zero, eqToHom_refl, Category.id_comp]
      exact Category.id_comp _
  | succ b ih =>
      rw [iteratedBlowupMorphism_succ, Category.assoc, ih, ← Category.assoc,
        blowupMorphism_comp_eqToHom d (Nat.add_assoc i a b), Category.assoc]
      rfl

/- English proof (authored)
When $j=i+k$, subtraction gives $j-i=k$. Thus the composite defining the tower map has length $k$. After this replacement its initial identification is exactly the one induced by $j=i+k$.
-/
private theorem towerMorphism_eq_iteratedBlowupMorphism (d : BlowupSequenceData X) {i j : ℕ} (h : i ≤ j) (k : ℕ)
    (hk : j = i + k) :
    homOfLE d h = eqToHom (congrArg d.obj hk) ≫ homAdd d i k := by
  subst hk
  unfold homOfLE
  rw [iteratedBlowupMorphism_congr_length d i (show i + k - i = k by omega)]
  simp

/- English proof (authored)
Write the transition from $l$ to $j$ as a composite of $l-j$ steps and the transition from $j$ to $i$ as a composite of $j-i$ steps. Identify $j$ with $i+(j-i)$. Concatenation gives $(j-i)+(l-j)$ steps, which equals $l-i$ because $i\le j\le l$. The initial identifications compose to the one defining the transition from $l$ to $i$.
-/
private theorem towerMorphism_comp (d : BlowupSequenceData X) {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    homOfLE d hjl ≫ homOfLE d hij = homOfLE d (hij.trans hjl) := by
  rw [towerMorphism_eq_iteratedBlowupMorphism d hjl (l - j) (by omega), towerMorphism_eq_iteratedBlowupMorphism d hij (j - i) (by omega),
    towerMorphism_eq_iteratedBlowupMorphism d (hij.trans hjl) ((j - i) + (l - j)) (by omega),
    iteratedBlowupMorphism_congr_start d (show j = i + (j - i) by omega) (l - j)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [iteratedBlowupMorphism_comp_iteratedBlowupMorphism d i (j - i) (l - j)]
  simp

def tower (d : BlowupSequenceData X) : ℕᵒᵖ ⥤ Scheme.{u} where
  obj n := d.obj n.unop
  map f := homOfLE d (leOfHom f.unop)
  map_id n := towerMorphism_refl d n.unop
  map_comp f g := (towerMorphism_comp d (leOfHom g.unop) (leOfHom f.unop)).symm

@[simp]
/- English proof (authored)
The tower assigns to the opposite index corresponding to $i$ the stored stage object at $i$.
-/
theorem tower_obj (d : BlowupSequenceData X) (i : ℕ) : d.tower.obj (op i) = d.obj i := rfl

/- English proof (authored)
Expanding the one-step composite gives the adjacent transition followed by the zero-step identity. The right identity law removes that identity.
-/
private theorem iteratedBlowupMorphism_one (d : BlowupSequenceData X) (i : ℕ) :
    homAdd d i 1 = d.map i := by
  show d.map (i + 0) ≫ homAdd d i 0 = d.map i
  exact Category.comp_id _

/- English proof (authored)
Replace the second length by the equal first length. The source identification becomes the identity, so the two sides agree by the left identity law.
-/
private theorem eqToHom_comp_iteratedBlowupMorphism (d : BlowupSequenceData X) (i : ℕ) {k k' : ℕ} (h : k = k')
    (hobj : d.obj (i + k) = d.obj (i + k')) :
    eqToHom hobj ≫ homAdd d i k' = homAdd d i k := by
  subst h
  simp

/- English proof (authored)
The difference between consecutive indices is one. Replace the length in the tower map by one and cancel the resulting inverse source identifications. A one-step composite is the specified adjacent transition.
-/
private theorem towerMorphism_succ (d : BlowupSequenceData X) (i : ℕ) (h : i ≤ i + 1) :
    homOfLE d h = d.map i := by
  have h1 : i + 1 - i = 1 := by omega
  have h2 := eqToHom_comp_iteratedBlowupMorphism d i h1
    (show d.obj (i + (i + 1 - i)) = d.obj (i + 1) by rw [h1])
  unfold homOfLE
  rw [← h2, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  exact iteratedBlowupMorphism_one d i

@[simp]
/- English proof (authored)
By construction the tower sends the consecutive-index arrow to the transition from stage $i+1$ to stage $i$. The consecutive-index calculation identifies this transition with the stored map.
-/
theorem tower_map_succ (d : BlowupSequenceData X) (i : ℕ) :
    d.tower.map (CategoryTheory.homOfLE (Nat.le_succ i)).op = d.map i :=
  towerMorphism_succ d i (Nat.le_succ i)

/- English proof (authored)
Below the length of the sequence, the stored adjacent map is a blowup along the stored center. The tower map for these consecutive indices agrees with that adjacent map, so it has the same blowup property.
-/
theorem isBlowupAlongIdealSheaf_tower_map (d : BlowupSequenceData X) (i : ℕ) (hi : i < d.length) :
    Blowup.IsBlowupAlongIdealSheaf (d.tower.map (CategoryTheory.homOfLE (Nat.le_succ i)).op) (d.center i) := by
  have h := d.isBlowup i hi
  rw [tower_map_succ]
  exact h

def toSequenceOfBlowups (d : BlowupSequenceData X) : SequenceOfBlowups X where
  length := d.length
  tower := d.tower
  isoZero := d.isoZero
  center := d.center
  isBlowup := fun i hi => isBlowupAlongIdealSheaf_tower_map d i hi

@[simp]
/- English proof (authored)
The conversion builds the sequence of blowups with the length in the original data.
-/
theorem toSequenceOfBlowups_length (d : BlowupSequenceData X) : d.toSequenceOfBlowups.length = d.length := rfl

@[simp]
/- English proof (authored)
The tower of the converted sequence is the functor constructed from the original stage objects and their adjacent maps.
-/
theorem toSequenceOfBlowups_tower (d : BlowupSequenceData X) : d.toSequenceOfBlowups.tower = d.tower := rfl

/- English proof (authored)
The stage of the converted sequence is the corresponding object of its tower, which is the stage object originally given.
-/
theorem toSequenceOfBlowups_schemeAt (d : BlowupSequenceData X) (i : ℕ) : d.toSequenceOfBlowups.schemeAt i = d.obj i := rfl

@[simp]
/- English proof (authored)
The conversion uses the stored center ideal sheaf at each stage as the center of the sequence.
-/
theorem toSequenceOfBlowups_center (d : BlowupSequenceData X) (i : ℕ) : d.toSequenceOfBlowups.center i = d.center i := rfl

@[simp]
/- English proof (authored)
The conversion keeps the original isomorphism between stage zero and the base scheme.
-/
theorem toSequenceOfBlowups_isoObjZero (d : BlowupSequenceData X) : d.toSequenceOfBlowups.isoZero = d.isoZero := rfl

@[simp]
/- English proof (authored)
The adjacent transition of the converted sequence is the corresponding consecutive-index map of the tower. This tower map is the original adjacent map by the one-step computation.
-/
theorem toSequenceOfBlowups_blowupMorphism (d : BlowupSequenceData X) (i : ℕ) : d.toSequenceOfBlowups.transitionMapSucc i = d.map i :=
  tower_map_succ d i

@[simp]
/- English proof (authored)
At stage zero, both projections are the initial isomorphism, since the zero-to-zero transition is the identity. At a successor stage, both projections first take the common adjacent map and then the projection at the preceding stage. Induction gives equality at every stage.
-/
theorem toSequenceOfBlowups_projectionToBase (d : BlowupSequenceData X) (i : ℕ) : d.toSequenceOfBlowups.projectionToBase i = projectionToBase d i := by
  induction i with
  | zero =>
      have h0 : d.toSequenceOfBlowups.transitionMap (Nat.zero_le 0) = 𝟙 (d.toSequenceOfBlowups.schemeAt 0) :=
        d.toSequenceOfBlowups.tower.map_id (op 0)
      have h1 : d.toSequenceOfBlowups.projectionToBase 0 = d.toSequenceOfBlowups.transitionMap (Nat.zero_le 0) ≫ d.toSequenceOfBlowups.isoZero.hom :=
        SequenceOfBlowups.projectionToBase_def d.toSequenceOfBlowups 0
      have h2 : d.toSequenceOfBlowups.projectionToBase 0 = d.toSequenceOfBlowups.isoZero.hom := by
        rw [h1, h0, Category.id_comp]
      exact h2
  | succ j ih =>
      have h2 : d.toSequenceOfBlowups.transitionMap (Nat.le_succ j) = d.map j :=
        (SequenceOfBlowups.transitionMap_def d.toSequenceOfBlowups (Nat.le_succ j)).trans (tower_map_succ d j)
      have h3 : d.toSequenceOfBlowups.transitionMap (Nat.le_succ j) ≫ d.toSequenceOfBlowups.projectionToBase j
          = d.toSequenceOfBlowups.projectionToBase (j + 1) :=
        SequenceOfBlowups.transitionMap_comp_projectionToBase d.toSequenceOfBlowups (Nat.le_succ j)
      have h5 : d.toSequenceOfBlowups.transitionMap (Nat.le_succ j) ≫ d.toSequenceOfBlowups.projectionToBase j
          = d.map j ≫ projectionToBase d j := by
        rw [h2, ih]
        exact rfl
      exact h3.symm.trans h5

def ofSequenceOfBlowups (s : SequenceOfBlowups X) : BlowupSequenceData X where
  length := s.length
  obj := s.schemeAt
  map := s.transitionMapSucc
  isoZero := s.isoZero
  center := s.center
  isBlowup := fun i hi => s.isBlowupAlongIdealSheaf_blowupMorphism i hi

@[simp]
/- English proof (authored)
The data recovered from the sequence store the length of the sequence.
-/
theorem ofSequenceOfBlowups_length (s : SequenceOfBlowups X) : (ofSequenceOfBlowups s).length = s.length := rfl

@[simp]
/- English proof (authored)
The object stored at stage $i$ in the recovered data is the scheme of the original sequence at stage $i$.
-/
theorem ofSequenceOfBlowups_schemeAt (s : SequenceOfBlowups X) (i : ℕ) : (ofSequenceOfBlowups s).obj i = s.schemeAt i := rfl

@[simp]
/- English proof (authored)
The recovered data store the original sequence's transition from stage $i+1$ to stage $i$ as the map at index $i$.
-/
theorem ofSequenceOfBlowups_blowupMorphism (s : SequenceOfBlowups X) (i : ℕ) : (ofSequenceOfBlowups s).map i = s.transitionMapSucc i := rfl

@[simp]
/- English proof (authored)
The recovered data take their center at each index from the original sequence.
-/
theorem ofSequenceOfBlowups_center (s : SequenceOfBlowups X) (i : ℕ) : (ofSequenceOfBlowups s).center i = s.center i := rfl

@[simp]
/- English proof (authored)
The recovered data take their initial isomorphism directly from the original sequence.
-/
theorem ofSequenceOfBlowups_isoObjZero (s : SequenceOfBlowups X) : (ofSequenceOfBlowups s).isoZero = s.isoZero := rfl

/- English proof (authored)
At stage zero, the sequence's projection is the zero-to-zero transition followed by the initial isomorphism. The first map is the identity, leaving the initial isomorphism, which is also the data projection. The two projections satisfy the same successor recursion with the original adjacent maps, so induction gives equality.
-/
theorem ofSequenceOfBlowups_projectionToBase (s : SequenceOfBlowups X) (i : ℕ) : projectionToBase (ofSequenceOfBlowups s) i = s.projectionToBase i := by
  induction i with
  | zero =>
    have h1 : s.tower.map (CategoryTheory.homOfLE (le_refl (0 : ℕ))).op = 𝟙 (s.tower.obj (Opposite.op 0)) :=
      s.tower.map_id (Opposite.op 0)
    have h2 : s.projectionToBase 0 = s.isoZero.hom := by
      rw [SequenceOfBlowups.projectionToBase_def, SequenceOfBlowups.transitionMap_def, h1, Category.id_comp]
    exact h2.symm
  | succ i ih =>
    show (ofSequenceOfBlowups s).map i ≫ projectionToBase (ofSequenceOfBlowups s) i = s.projectionToBase (i + 1)
    rw [ih]
    show s.transitionMapSucc i ≫ s.projectionToBase i = s.projectionToBase (i + 1)
    rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_comp_projectionToBase]

end BlowupSequenceData

def emptyBlowupSequenceData (X : Scheme.{u}) : BlowupSequenceData X where
  length := 0
  obj := fun _ => X
  map := fun _ => 𝟙 X
  isoZero := Iso.refl X
  center := fun _ => ⊤
  isBlowup := fun i hi => absurd hi (Nat.not_lt_zero i)

@[simp]
/- English proof (authored)
The empty blowup data have length zero by construction.
-/
theorem emptyBlowupSequenceData_length (X : Scheme.{u}) : (emptyBlowupSequenceData X).length = 0 := rfl

@[simp]
/- English proof (authored)
Every stage in the empty blowup data is defined to be the base scheme.
-/
theorem emptyBlowupSequenceData_schemeAt (X : Scheme.{u}) (i : ℕ) : (emptyBlowupSequenceData X).obj i = X := rfl

@[simp]
/- English proof (authored)
All adjacent maps in the empty data are defined to be the identity of the base scheme.
-/
theorem emptyBlowupSequenceData_blowupMorphism (X : Scheme.{u}) (i : ℕ) : (emptyBlowupSequenceData X).map i = 𝟙 X := rfl

@[simp]
/- English proof (authored)
The constant stage data for an empty sequence use the unit ideal sheaf at every index, so all stored centers are empty.
-/
theorem emptyBlowupSequenceData_center (X : Scheme.{u}) (i : ℕ) : (emptyBlowupSequenceData X).center i = ⊤ := rfl

@[simp]
/- English proof (authored)
The initial stage of the empty sequence is the base scheme and its chosen identification with the base is the identity isomorphism.
-/
theorem emptyBlowupSequenceData_isoObjZero (X : Scheme.{u}) :
    (emptyBlowupSequenceData X).isoZero = Iso.refl X := rfl

structure MarkedBlowupSequenceData {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) extends BlowupSequenceData X where
  proj : ∀ i : ℕ, toBlowupSequenceData.obj i ⟶ X
  proj_zero : proj 0 = toBlowupSequenceData.isoZero.hom
  proj_succ : ∀ i : ℕ, proj (i + 1) = toBlowupSequenceData.map i ≫ proj i
  ideal : ∀ i : ℕ, (toBlowupSequenceData.obj i).IdealSheafData
  boundary : ∀ i : ℕ, List (toBlowupSequenceData.obj i).IdealSheafData
  ideal_zero : ideal 0 = I.comap toBlowupSequenceData.isoZero.hom
  boundary_zero : boundary 0 = E.map (fun D => D.comap toBlowupSequenceData.isoZero.hom)
  center_order : ∀ i, i < toBlowupSequenceData.length →
    ((toBlowupSequenceData.center i).support : Set ↥(toBlowupSequenceData.obj i)) ⊆ orderAtLeastLocus (ideal i) m
  center_smooth : ∀ i, i < toBlowupSequenceData.length →
    AlgebraicGeometry.Smooth ((toBlowupSequenceData.center i).subschemeι ≫ proj i ≫ p)
  center_snc : ∀ i, i < toBlowupSequenceData.length →
    HasStrictNormalCrossingsWith (proj i ≫ p) (toBlowupSequenceData.center i) (boundary i)
  ideal_succ : ∀ i, i < toBlowupSequenceData.length →
    Blowup.exceptionalIdeal (toBlowupSequenceData.map i) (toBlowupSequenceData.center i) ^ m * ideal (i + 1) =
      (ideal i).comap (toBlowupSequenceData.map i)
  boundary_succ : ∀ i, i < toBlowupSequenceData.length →
    boundary (i + 1) =
      (boundary i).map (Blowup.strictTransform (toBlowupSequenceData.map i) (toBlowupSequenceData.center i)) ++
        [Blowup.exceptionalIdeal (toBlowupSequenceData.map i) (toBlowupSequenceData.center i)]

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

/- English proof (authored)
The prescribed projection at stage zero is the initial isomorphism, just as for the projection constructed from the unmarked data. Their successor rules both compose the adjacent map with the preceding projection. Induction identifies the projections stage by stage.
-/
theorem projectionToBase_eq (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.proj i = BlowupSequenceData.projectionToBase d.toBlowupSequenceData i := by
  induction i with
  | zero =>
      rw [BlowupSequenceData.projectionToBase_zero]
      exact d.proj_zero
  | succ i ih =>
      rw [d.proj_succ i, BlowupSequenceData.projectionToBase_succ, ih]

/- English proof (authored)
The prescribed projection agrees with the recursive projection on the underlying data. Conversion of those data to a sequence preserves that recursive projection, so the prescribed and converted projections coincide.
-/
theorem projectionToBase_eq_toSequenceOfBlowups (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.proj i = d.toBlowupSequenceData.toSequenceOfBlowups.projectionToBase i :=
  (d.projectionToBase_eq i).trans (BlowupSequenceData.toSequenceOfBlowups_projectionToBase d.toBlowupSequenceData i).symm

/- English proof (authored)
At an index below the length, the marked data require the support of the center to lie in the locus where the stored ideal has order at least the specified mark. This is exactly the asserted inclusion.
-/
private theorem center_support_subset_orderAtLeastLocus (d : MarkedBlowupSequenceData p I m E) (i : ℕ)
    (hi : i < d.toBlowupSequenceData.length) :
    ((d.toBlowupSequenceData.center i).support : Set ↥(d.toBlowupSequenceData.obj i)) ⊆
      orderAtLeastLocus (d.ideal i) m :=
  d.center_order i hi

/- English proof (authored)
Use the smoothness of the center over the field from the marked data. Its structural map first includes it in the stage scheme and then projects to the base and to the field. The converted sequence has the same stage projection, so the structural map remains smooth.
-/
private theorem smooth_center_comp_projection (d : MarkedBlowupSequenceData p I m E) (i : ℕ)
    (hi : i < d.toBlowupSequenceData.length) :
    AlgebraicGeometry.Smooth
      ((d.toBlowupSequenceData.center i).subschemeι ≫ d.toBlowupSequenceData.toSequenceOfBlowups.projectionToBase i ≫ p) := by
  have h := d.center_smooth i hi
  rw [projectionToBase_eq_toSequenceOfBlowups d i] at h
  exact h

/- English proof (authored)
The marked data give strict normal crossings of the center with the current boundary for the stage map to the field. The converted sequence uses the same projection to the base and hence the same map to the field. The normal crossings condition therefore still holds.
-/
private theorem hasStrictNormalCrossingsWith_center_boundary (d : MarkedBlowupSequenceData p I m E) (i : ℕ)
    (hi : i < d.toBlowupSequenceData.length) :
    HasStrictNormalCrossingsWith (d.toBlowupSequenceData.toSequenceOfBlowups.projectionToBase i ≫ p) (d.toBlowupSequenceData.center i)
      (d.boundary i) := by
  have h := d.center_snc i hi
  rw [d.projectionToBase_eq_toSequenceOfBlowups i] at h
  exact h

/- English proof (authored)
The adjacent transition of the converted sequence is the stored map, and the center and stage ideals are retained. The exceptional ideal and the pullback ideal in the asserted relation thus agree with those in the marked data. The stored successor ideal relation gives the equality.
-/
private theorem exceptionalIdeal_pow_mul_ideal_succ_eq_comap (d : MarkedBlowupSequenceData p I m E) (i : ℕ)
    (hi : i < d.toBlowupSequenceData.length) :
    Blowup.exceptionalIdeal (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i)
          (show (d.toBlowupSequenceData.toSequenceOfBlowups.schemeAt i).IdealSheafData from d.toBlowupSequenceData.center i) ^ m *
        (show (d.toBlowupSequenceData.toSequenceOfBlowups.schemeAt (i + 1)).IdealSheafData from d.ideal (i + 1)) =
      (show (d.toBlowupSequenceData.toSequenceOfBlowups.schemeAt i).IdealSheafData from d.ideal i).comap
        (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i) := by
  have key := d.ideal_succ i hi
  have h : d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i = d.toBlowupSequenceData.map i :=
    BlowupSequenceData.toSequenceOfBlowups_blowupMorphism d.toBlowupSequenceData i
  rw [h]
  exact key

/- English proof (authored)
Apply the given successor boundary formula in the marked data. The converted sequence uses the same adjacent map and center, so each strict transform and the appended exceptional ideal agree with those in that formula.
-/
private theorem boundary_succ_eq_map_strictTransform_append (d : MarkedBlowupSequenceData p I m E) (i : ℕ)
    (hi : i < d.toBlowupSequenceData.length) :
    d.boundary (i + 1) =
      (d.boundary i).map
          (Blowup.strictTransform (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i) (d.toBlowupSequenceData.center i)) ++
        [Blowup.exceptionalIdeal (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i) (d.toBlowupSequenceData.center i)] := by
  have key := d.boundary_succ i hi
  have h : d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i = d.toBlowupSequenceData.map i :=
    BlowupSequenceData.toSequenceOfBlowups_blowupMorphism d.toBlowupSequenceData i
  rw [h]
  exact key

def toMarkedSequenceOfBlowups (d : MarkedBlowupSequenceData p I m E) : MarkedSequenceOfBlowups p I m E where
  toSequenceOfBlowups := d.toBlowupSequenceData.toSequenceOfBlowups
  ideal := d.ideal
  boundary := d.boundary
  ideal_zero := d.ideal_zero
  boundary_zero := d.boundary_zero
  center_smooth := fun i hi => smooth_center_comp_projection d i hi
  center_snc := fun i hi => hasStrictNormalCrossingsWith_center_boundary d i hi
  center_order := fun i hi => center_support_subset_orderAtLeastLocus d i hi
  ideal_succ := fun i hi => exceptionalIdeal_pow_mul_ideal_succ_eq_comap d i hi
  boundary_succ := fun i hi => boundary_succ_eq_map_strictTransform_append d i hi

@[simp]
/- English proof (authored)
The underlying sequence of the converted marked sequence is defined by converting the underlying unmarked data.
-/
theorem toMarkedSequence_toSequenceOfBlowups (d : MarkedBlowupSequenceData p I m E) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups = d.toBlowupSequenceData.toSequenceOfBlowups := rfl

@[simp]
/- English proof (authored)
The marked conversion uses the unmarked data conversion underneath, and that conversion has the original stored length.
-/
theorem toMarkedSequence_length (d : MarkedBlowupSequenceData p I m E) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length = d.toBlowupSequenceData.length := rfl

/- English proof (authored)
The underlying tower of the converted marked sequence uses the stored stage object at every index.
-/
theorem toMarkedSequence_schemeAt (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.schemeAt i = d.toBlowupSequenceData.obj i := rfl

@[simp]
/- English proof (authored)
The conversion takes the marked ideal at each stage directly from the data.
-/
theorem toMarkedSequence_ideal (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.ideal i = d.ideal i := rfl

@[simp]
/- English proof (authored)
The conversion takes the boundary list at each stage directly from the data.
-/
theorem toMarkedSequence_boundary (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.boundary i = d.boundary i := rfl

@[simp]
/- English proof (authored)
The underlying unmarked conversion uses the same center ideal sheaf at each stage, so adding the marked data leaves that center unchanged.
-/
theorem toMarkedSequence_center (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.center i = d.toBlowupSequenceData.center i := rfl

/- English proof (authored)
The underlying unmarked sequence is the one constructed from the data. Its adjacent transition was already identified with the stored adjacent map.
-/
theorem toMarkedSequence_blowupMorphism (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.transitionMapSucc i = d.toBlowupSequenceData.map i :=
  BlowupSequenceData.toSequenceOfBlowups_blowupMorphism d.toBlowupSequenceData i

/- English proof (authored)
The converted underlying sequence has the same projections as its unmarked data. Those projections agree stage by stage with the projections explicitly supplied by the marked data.
-/
theorem toMarkedSequence_projectionToBase (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase i = d.proj i :=
  (BlowupSequenceData.toSequenceOfBlowups_projectionToBase d.toBlowupSequenceData i).trans (d.projectionToBase_eq i).symm

@[simp]
/- English proof (authored)
The converted stage's map to the spectrum of the field is the projection to the original scheme followed by its structure map. The first map agrees with the projection supplied in the data.
-/
theorem toMarkedSequence_projectionToSpec (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.projectionToSpec i = d.proj i ≫ p := by
  rw [MarkedSequenceOfBlowups.projectionToSpec_eq, toMarkedSequence_projectionToBase]
  rfl

@[simp]
/- English proof (authored)
The length and the indexed ideals are preserved by conversion. The last ideal is therefore the stored ideal evaluated at that length.
-/
theorem toMarkedSequence_lastIdeal (d : MarkedBlowupSequenceData p I m E) :
    d.toMarkedSequenceOfBlowups.lastIdeal = d.ideal d.toBlowupSequenceData.length := rfl

/- English proof (authored)
The transition from stage zero to itself is the image of the identity in the index category, hence is the identity on the stage. The projection to the base is that identity followed by the stage-zero isomorphism. This isomorphism is the one stored by conversion to data.
-/
private theorem toSequenceOfBlowups_projectionToBase_zero (s : MarkedSequenceOfBlowups p I m E) :
    s.toSequenceOfBlowups.projectionToBase 0 = (BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups).isoZero.hom := by
  have h1 : s.toSequenceOfBlowups.tower.map (homOfLE (le_refl (0 : ℕ))).op
      = 𝟙 (s.toSequenceOfBlowups.tower.obj (Opposite.op 0)) :=
    s.toSequenceOfBlowups.tower.map_id (Opposite.op 0)
  show s.toSequenceOfBlowups.projectionToBase 0 = s.toSequenceOfBlowups.isoZero.hom
  rw [SequenceOfBlowups.projectionToBase_def, SequenceOfBlowups.transitionMap_def, h1, Category.id_comp]

/- English proof (authored)
The map stored at index $i$ is the original transition from $i+1$ to $i$. Composing it with the transition from $i$ to zero gives the transition from $i+1$ to zero by functoriality. Following both composites by the initial isomorphism gives the successor rule for projection to the base.
-/
private theorem toSequenceOfBlowups_projectionToBase_succ (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    s.toSequenceOfBlowups.projectionToBase (i + 1) =
      (BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups).map i ≫ s.toSequenceOfBlowups.projectionToBase i := by
  show s.toSequenceOfBlowups.projectionToBase (i + 1)
      = s.toSequenceOfBlowups.transitionMapSucc i ≫ s.toSequenceOfBlowups.projectionToBase i
  rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_comp_projectionToBase]

def ofMarkedSequence (s : MarkedSequenceOfBlowups p I m E) : MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups
  proj := fun i => s.toSequenceOfBlowups.projectionToBase i
  proj_zero := toSequenceOfBlowups_projectionToBase_zero s
  proj_succ := fun i => toSequenceOfBlowups_projectionToBase_succ s i
  ideal := s.ideal
  boundary := s.boundary
  ideal_zero := s.ideal_zero
  boundary_zero := s.boundary_zero
  center_order := fun i hi => s.center_order i hi
  center_smooth := fun i hi => s.center_smooth i hi
  center_snc := fun i hi => s.center_snc i hi
  ideal_succ := fun i hi => s.ideal_succ i hi
  boundary_succ := fun i hi => s.boundary_succ i hi

@[simp]
/- English proof (authored)
To recover marked data from a marked sequence, first recover blowup data from its underlying unmarked sequence. The remaining fields record the marking, so the underlying blowup data are the claimed data.
-/
theorem blowupSequenceData_ofMarkedSequence (s : MarkedSequenceOfBlowups p I m E) :
    (ofMarkedSequence s).toBlowupSequenceData = BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups := rfl

@[simp]
/- English proof (authored)
The length comes from the unmarked data extracted from the sequence, which store the original sequence length.
-/
theorem ofMarkedSequence_length (s : MarkedSequenceOfBlowups p I m E) :
    (ofMarkedSequence s).toBlowupSequenceData.length = s.toSequenceOfBlowups.length := rfl

@[simp]
/- English proof (authored)
The projection field of the recovered data assigns to each stage the original sequence's projection to the base.
-/
theorem ofMarkedSequence_projectionToBase (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (ofMarkedSequence s).proj i = s.toSequenceOfBlowups.projectionToBase i := rfl

@[simp]
/- English proof (authored)
The underlying recovered data store the original adjacent transition at every index.
-/
theorem ofMarkedSequence_blowupMorphism (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (ofMarkedSequence s).toBlowupSequenceData.map i = s.toSequenceOfBlowups.transitionMapSucc i := rfl

@[simp]
/- English proof (authored)
The marked ideal field of the recovered data is the original family of stage ideals.
-/
theorem ofMarkedSequence_ideal (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (ofMarkedSequence s).ideal i = s.ideal i := rfl

@[simp]
/- English proof (authored)
At the specified index the recovered data use the original stage's boundary list.
-/
theorem ofMarkedSequence_boundary_apply (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (ofMarkedSequence s).boundary i = s.boundary i := rfl

@[simp]
/- English proof (authored)
The recovered unmarked data use the center of the original sequence at each index.
-/
theorem ofMarkedSequence_center (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (ofMarkedSequence s).toBlowupSequenceData.center i = s.toSequenceOfBlowups.center i := rfl

end MarkedBlowupSequenceData

def emptyMarkedBlowupSequenceData {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) : MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := emptyBlowupSequenceData X
  proj := fun _ => 𝟙 X
  proj_zero := rfl
  proj_succ := fun _ => (Category.id_comp _).symm
  ideal := fun _ => I
  boundary := fun _ => E
  ideal_zero := (Scheme.IdealSheafData.comap_id I).symm
  boundary_zero := by simp [Scheme.IdealSheafData.comap_id]
  center_order := fun i hi => absurd hi (Nat.not_lt_zero i)
  center_smooth := fun i hi => absurd hi (Nat.not_lt_zero i)
  center_snc := fun i hi => absurd hi (Nat.not_lt_zero i)
  ideal_succ := fun i hi => absurd hi (Nat.not_lt_zero i)
  boundary_succ := fun i hi => absurd hi (Nat.not_lt_zero i)

@[simp]
/- English proof (authored)
The empty marked data are built on top of the empty unmarked data on the same base scheme.
-/
theorem emptyMarkedBlowupSequenceData_toBlowupSequenceData_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData = emptyBlowupSequenceData X := rfl

@[simp]
/- English proof (authored)
The underlying empty unmarked data have length zero, and the marking adds no steps.
-/
theorem emptyMarkedBlowupSequenceData_length {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length = 0 := rfl

@[simp]
/- English proof (authored)
The underlying empty unmarked data use the base scheme at each index.
-/
theorem emptyMarkedBlowupSequenceData_schemeAt {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (i : ℕ) :
    (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.obj i = X := rfl

@[simp]
/- English proof (authored)
The underlying empty unmarked data take the unit ideal sheaf as their center at every index.
-/
theorem emptyMarkedBlowupSequenceData_center {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (i : ℕ) :
    (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.center i = ⊤ := rfl

@[simp]
/- English proof (authored)
All stages are the base scheme, and the prescribed projection at every index is its identity map.
-/
theorem emptyMarkedBlowupSequenceData_projectionToBase {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (i : ℕ) :
    (emptyMarkedBlowupSequenceData p I m E).proj i = 𝟙 X := rfl

@[simp]
/- English proof (authored)
The family of ideals for the empty marked data is constant with value the given initial ideal.
-/
theorem emptyMarkedBlowupSequenceData_ideal {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (i : ℕ) :
    (emptyMarkedBlowupSequenceData p I m E).ideal i = I := rfl

@[simp]
/- English proof (authored)
The boundary family for the empty marked data is constant with value the original boundary list.
-/
theorem emptyMarkedBlowupSequenceData_boundary {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (i : ℕ) :
    (emptyMarkedBlowupSequenceData p I m E).boundary i = E := rfl

@[simp]
/- English proof (authored)
Conversion to a marked sequence retains the length of the underlying data. This length is zero for the empty data.
-/
theorem emptyMarkedBlowupSequenceData_toMarkedSequence_length {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    (emptyMarkedBlowupSequenceData p I m E).toMarkedSequenceOfBlowups.toSequenceOfBlowups.length = 0 := rfl

end FunctorialResolution.EmbeddedResolution
