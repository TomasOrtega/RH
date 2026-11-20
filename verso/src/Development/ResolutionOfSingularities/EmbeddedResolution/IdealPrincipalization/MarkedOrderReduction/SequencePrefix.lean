import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem comap_eqToHom_self {X : Scheme.{u}} (h : X = X) (J : X.IdealSheafData) :
    J.comap (eqToHom h) = J := by
  simp

/- English proof (translation)
Substitute `h1` using the available equality. Substitute `h2` using the available equality. Simplify using the standard rewrite rules.
-/
private theorem comap_eqToHom_trans {X Y Z : Scheme.{u}} (h1 : X = Y) (h2 : Y = Z)
    (J : Z.IdealSheafData) :
    (J.comap (eqToHom h2)).comap (eqToHom h1) = J.comap (eqToHom (h1.trans h2)) := by
  subst h1
  subst h2
  simp

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => rfl`. Consider the case `cons a l ih => rw [List.map_cons, ih, comap_eqToHom_self]`.
-/
private theorem map_comap_eqToHom_self {X : Scheme.{u}} (h : X = X) (L : List X.IdealSheafData) :
    List.map (fun D => D.comap (eqToHom h)) L = L := by
  induction L with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, ih, comap_eqToHom_self]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => rfl`. Consider the case `cons a l ih`. Rewrite using `[List.map_cons, List.map_cons, List.map_cons, ih, comap_eqToHom_trans]`.
-/
private theorem map_comap_eqToHom_trans {X Y Z : Scheme.{u}} (h1 : X = Y) (h2 : Y = Z)
    (L : List Z.IdealSheafData) :
    List.map (fun D => D.comap (eqToHom h1)) (List.map (fun D => D.comap (eqToHom h2)) L)
      = List.map (fun D => D.comap (eqToHom (h1.trans h2))) L := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih, comap_eqToHom_trans]

/- English proof (translation)
Substitute `h` using the available equality. Simplify using `only [eqToHom_refl, Category.id_comp] at hg ⊢`. Conclude with `hg.symm`.
-/
private theorem eq_eqToHom_comp_of_eq_eqToHom_symm_comp {A B C : Scheme.{u}} (f : A ⟶ C) (g : B ⟶ C) (h : A = B)
    (hg : g = eqToHom h.symm ≫ f) : f = eqToHom h ≫ g := by
  subst h
  simp only [eqToHom_refl, Category.id_comp] at hg ⊢
  exact hg.symm

/- English proof (translation)
Substitute `hd` using the available equality. Conclude with `(comap_eqToHom_self hobj _).symm`.
-/
private theorem blowupSequenceData_center_eq_comap_eqToHom {X : Scheme.{u}} {d d' : BlowupSequenceData X} (hd : d = d')
    (i : ℕ) (hobj : d.obj i = d'.obj i) :
    d.center i = (d'.center i).comap (eqToHom hobj) := by
  subst hd
  exact (comap_eqToHom_self hobj _).symm

/- English proof (translation)
Substitute `hd` using the available equality. Simplify using the standard rewrite rules.
-/
private theorem blowupSequenceData_blowupMorphism_comp_eqToHom {X : Scheme.{u}} {d d' : BlowupSequenceData X} (hd : d = d')
    (i : ℕ) (h0 : d.obj i = d'.obj i) (h1 : d.obj (i + 1) = d'.obj (i + 1)) :
    d.map i ≫ eqToHom h0 = eqToHom h1 ≫ d'.map i := by
  subst hd
  simp

/- English proof (translation)
Substitute `b` using the available equality. Substitute `c0` using the available equality. Substitute `a` using the available equality. Substitute `c1` using the available equality. Simplify using `only [eqToHom_refl, Category.comp_id, Category.id_comp] at key0 L ⊢`.

Conclude with `L.symm.trans key0.symm`.
-/
private theorem comp_eqToHom_eq_eqToHom_comp_of_eqToHom_conj {A B A' B' A'' B'' : Scheme.{u}}
    (f : A ⟶ B) (M : A'' ⟶ B'') (N : A' ⟶ B')
    (c0 : B'' = B') (c1 : A'' = A') (a : A' = A) (b : B = B')
    (hi0 : B = B'') (hi1 : A = A'')
    (key0 : M ≫ eqToHom c0 = eqToHom c1 ≫ N)
    (L : N = eqToHom a ≫ f ≫ eqToHom b) :
    f ≫ eqToHom hi0 = eqToHom hi1 ≫ M := by
  subst b
  subst c0
  subst a
  subst c1
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at key0 L ⊢
  exact L.symm.trans key0.symm

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

structure IsPrefix (s t : MarkedBlowupSequenceData p I m E) : Prop where
  length_le : s.length ≤ t.length
  obj_eq : ∀ i ≤ s.length, s.obj i = t.obj i
  proj_eq : ∀ (i : ℕ) (hi : i ≤ s.length), s.proj i = eqToHom (obj_eq i hi) ≫ t.proj i
  ideal_eq : ∀ (i : ℕ) (hi : i ≤ s.length),
    s.ideal i = (t.ideal i).comap (eqToHom (obj_eq i hi))
  boundary_eq : ∀ (i : ℕ) (hi : i ≤ s.length),
    s.boundary i = List.map (fun D => D.comap (eqToHom (obj_eq i hi))) (t.boundary i)
  center_eq : ∀ (i : ℕ) (hi : i < s.length),
    s.center i = (t.center i).comap (eqToHom (obj_eq i (Nat.le_of_lt hi)))
  map_eq : ∀ (i : ℕ) (hi : i < s.length),
    s.map i ≫ eqToHom (obj_eq i (Nat.le_of_lt hi)) =
      eqToHom (obj_eq (i + 1) (Nat.succ_le_of_lt hi)) ≫ t.map i

/- English proof (translation)
Use `⟨le_rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Simplify using the standard rewrite rules. Introduce `i hi`. Conclude with `(comap_eqToHom_self _ _).symm`.

Introduce `i hi`. Conclude with `(map_comap_eqToHom_self _ _).symm`. Introduce `i hi`. Conclude with `(comap_eqToHom_self _ _).symm`. Introduce `i hi`.

Simplify using the standard rewrite rules.
-/
theorem IsPrefix.refl (s : MarkedBlowupSequenceData p I m E) : s.IsPrefix s := by
  refine ⟨le_rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp
  · intro i hi
    exact (comap_eqToHom_self _ _).symm
  · intro i hi
    exact (map_comap_eqToHom_self _ _).symm
  · intro i hi
    exact (comap_eqToHom_self _ _).symm
  · intro i hi
    simp

/- English proof (translation)
Establish `hlen : s.length ≤ t.length` using `h.length_le`. Establish `hobj : ∀ i ≤ s.length, s.obj i = r.obj i` using `fun i hi => (h.obj_eq i hi).trans (h'.obj_eq i (hi.trans hlen))`. Use `⟨hlen.trans h'.length_le, hobj, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Rewrite using `[h.proj_eq i hi, h'.proj_eq i (hi.trans hlen), ← Category.assoc, eqToHom_trans]`.

Introduce `i hi`. Rewrite using `[h.ideal_eq i hi, h'.ideal_eq i (hi.trans hlen), comap_eqToHom_trans]`. Introduce `i hi`. Rewrite using `[h.boundary_eq i hi, h'.boundary_eq i (hi.trans hlen), map_comap_eqToHom_trans]`. Introduce `i hi`.

Rewrite using `[h.center_eq i hi, h'.center_eq i (lt_of_lt_of_le hi hlen), comap_eqToHom_trans]`. Introduce `i hi`. Establish `hi' : i < t.length` using `lt_of_lt_of_le hi hlen`. Rewrite using `[← eqToHom_trans (h.obj_eq i (Nat.le_of_lt hi)) (h'.obj_eq i (Nat.le_of_lt hi')), ← eqToHom_trans (h.obj_eq (i + 1) (Nat.succ_le_of_lt hi)) (h'.obj_eq (i + 1) (Nat.succ_le_of_lt hi')), ← Category.assoc, h.map_eq i hi, Category.assoc, h'.map_eq i hi', ← Category.assoc]`.
-/
theorem IsPrefix.trans {s t r : MarkedBlowupSequenceData p I m E} (h : s.IsPrefix t)
    (h' : t.IsPrefix r) : s.IsPrefix r := by
  have hlen : s.length ≤ t.length := h.length_le
  have hobj : ∀ i ≤ s.length, s.obj i = r.obj i := fun i hi =>
    (h.obj_eq i hi).trans (h'.obj_eq i (hi.trans hlen))
  refine ⟨hlen.trans h'.length_le, hobj, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [h.proj_eq i hi, h'.proj_eq i (hi.trans hlen), ← Category.assoc, eqToHom_trans]
  · intro i hi
    rw [h.ideal_eq i hi, h'.ideal_eq i (hi.trans hlen), comap_eqToHom_trans]
  · intro i hi
    rw [h.boundary_eq i hi, h'.boundary_eq i (hi.trans hlen), map_comap_eqToHom_trans]
  · intro i hi
    rw [h.center_eq i hi, h'.center_eq i (lt_of_lt_of_le hi hlen), comap_eqToHom_trans]
  · intro i hi
    have hi' : i < t.length := lt_of_lt_of_le hi hlen
    rw [← eqToHom_trans (h.obj_eq i (Nat.le_of_lt hi)) (h'.obj_eq i (Nat.le_of_lt hi')),
      ← eqToHom_trans (h.obj_eq (i + 1) (Nat.succ_le_of_lt hi))
        (h'.obj_eq (i + 1) (Nat.succ_le_of_lt hi')),
      ← Category.assoc, h.map_eq i hi, Category.assoc, h'.map_eq i hi', ← Category.assoc]

/- English proof (translation)
Establish `hobj : ∀ i ≤ s.length, s.obj i = (s.append t hinv).obj i` using `fun i hi => (s.append_schemeAt_of_le_length t hinv hi).symm`. Establish `hbd : (s.append t hinv).toBlowupSequenceData = s.appendToBlowupSequenceData t` using `s.append_toBlowupSequenceData t hinv`. Use `⟨?_, hobj, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MarkedBlowupSequenceData.append_length]`. Conclude with `Nat.le_add_right _ _`.

Introduce `i hi`. Establish `key : (s.append t hinv).proj i = eqToHom (hobj i hi).symm ≫ s.proj i`. Rewrite using `[s.append_projectionToBase t hinv i]`. Conclude with `s.appendProjectionToBase_of_le_length t hi`. Conclude with `eq_eqToHom_comp_of_eq_eqToHom_symm_comp (s.proj i) ((s.append t hinv).proj i) (hobj i hi) key`.

Introduce `i hi`. Establish `key : (s.append t hinv).ideal i = (s.ideal i).comap (eqToHom (hobj i hi).symm)`. Rewrite using `[s.append_ideal t hinv i]`. Conclude with `s.appendIdeal_of_le_length t hi`. Rewrite using `[key, comap_eqToHom_trans, comap_eqToHom_self]`.

Introduce `i hi`. Establish `key : (s.append t hinv).boundary i = List.map (fun D => D.comap (eqToHom (hobj i hi).symm)) (s.boundary i)`. Rewrite using `[s.append_boundary t hinv i]`. Conclude with `s.appendBoundary_of_le_length t hi`. Rewrite using `[key, map_comap_eqToHom_trans, map_comap_eqToHom_self]`.

Introduce `i hi`. Rewrite using `[blowupSequenceData_center_eq_comap_eqToHom hbd i (congrArg (fun d => BlowupSequenceData.obj d i) hbd), s.appendToBlowupSequenceData_center_of_lt_length t hi, comap_eqToHom_trans, comap_eqToHom_trans, comap_eqToHom_self]`. Introduce `i hi`. Establish `c0 : (s.append t hinv).obj i = (s.appendToBlowupSequenceData t).obj i` using `congrArg (fun d => BlowupSequenceData.obj d i) hbd`. Establish `c1 : (s.append t hinv).obj (i + 1) = (s.appendToBlowupSequenceData t).obj (i + 1)` using `congrArg (fun d => BlowupSequenceData.obj d (i + 1)) hbd`.

Conclude with `comp_eqToHom_eq_eqToHom_comp_of_eqToHom_conj (s.map i) ((s.append t hinv).map i) ((s.appendToBlowupSequenceData t).map i) c0 c1 _ _ _ _ (blowupSequenceData_blowupMorphism_comp_eqToHom hbd i c0 c1) (s.appendToBlowupSequenceData_blowupMorphism_of_lt_length t hi)`.
-/
theorem isPrefix_append (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (hinv : ComapIsoInvariance.{u}) : s.IsPrefix (s.append t hinv) := by
  have hobj : ∀ i ≤ s.length, s.obj i = (s.append t hinv).obj i := fun i hi =>
    (s.append_schemeAt_of_le_length t hinv hi).symm
  have hbd : (s.append t hinv).toBlowupSequenceData = s.appendToBlowupSequenceData t := s.append_toBlowupSequenceData t hinv
  refine ⟨?_, hobj, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MarkedBlowupSequenceData.append_length]
    exact Nat.le_add_right _ _
  · intro i hi
    have key : (s.append t hinv).proj i = eqToHom (hobj i hi).symm ≫ s.proj i := by
      rw [s.append_projectionToBase t hinv i]
      exact s.appendProjectionToBase_of_le_length t hi
    exact eq_eqToHom_comp_of_eq_eqToHom_symm_comp (s.proj i) ((s.append t hinv).proj i) (hobj i hi) key
  · intro i hi
    have key : (s.append t hinv).ideal i = (s.ideal i).comap (eqToHom (hobj i hi).symm) := by
      rw [s.append_ideal t hinv i]
      exact s.appendIdeal_of_le_length t hi
    rw [key, comap_eqToHom_trans, comap_eqToHom_self]
  · intro i hi
    have key : (s.append t hinv).boundary i =
        List.map (fun D => D.comap (eqToHom (hobj i hi).symm)) (s.boundary i) := by
      rw [s.append_boundary t hinv i]
      exact s.appendBoundary_of_le_length t hi
    rw [key, map_comap_eqToHom_trans, map_comap_eqToHom_self]
  · intro i hi
    rw [blowupSequenceData_center_eq_comap_eqToHom hbd i (congrArg (fun d => BlowupSequenceData.obj d i) hbd),
      s.appendToBlowupSequenceData_center_of_lt_length t hi, comap_eqToHom_trans, comap_eqToHom_trans, comap_eqToHom_self]
  · intro i hi
    have c0 : (s.append t hinv).obj i = (s.appendToBlowupSequenceData t).obj i :=
      congrArg (fun d => BlowupSequenceData.obj d i) hbd
    have c1 : (s.append t hinv).obj (i + 1) = (s.appendToBlowupSequenceData t).obj (i + 1) :=
      congrArg (fun d => BlowupSequenceData.obj d (i + 1)) hbd
    exact comp_eqToHom_eq_eqToHom_comp_of_eqToHom_conj (s.map i) ((s.append t hinv).map i) ((s.appendToBlowupSequenceData t).map i)
      c0 c1 _ _ _ _ (blowupSequenceData_blowupMorphism_comp_eqToHom hbd i c0 c1) (s.appendToBlowupSequenceData_blowupMorphism_of_lt_length t hi)

end MarkedBlowupSequenceData

section

def lastNonMonomialPart (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    (s.obj s.length).IdealSheafData :=
  nonMonomialPart (s.boundary s.length) (s.ideal s.length)

def maxOrderNonMonomial (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : ℕ :=
  maxOrder (lastNonMonomialPart T s)

def NonMonomialOrderReductionContinues (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : Prop :=
  T.mult ≤ maxOrderNonMonomial T s ∧
    (orderAtLeastLocus (lastNonMonomialPart T s) (maxOrderNonMonomial T s)).Nonempty

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem nonMonomialOrderReductionContinues_iff (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    NonMonomialOrderReductionContinues T s ↔
      T.mult ≤ maxOrderNonMonomial T s ∧
        (orderAtLeastLocus (lastNonMonomialPart T s) (maxOrderNonMonomial T s)).Nonempty :=
  Iff.rfl

def maxOrderNonMonomialOnOrderLocus (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : ℕ :=
  maxOrderOn (lastNonMonomialPart T s) (orderAtLeastLocus (s.ideal s.length) T.mult)

def CompanionIdealReductionContinues (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : Prop :=
  1 ≤ maxOrderNonMonomialOnOrderLocus T s

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem companionIdealReductionContinues_iff (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    CompanionIdealReductionContinues T s ↔ 1 ≤ maxOrderNonMonomialOnOrderLocus T s :=
  Iff.rfl

def companionIdeal (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    (s.obj s.length).IdealSheafData :=
  lastNonMonomialPart T s ^ T.mult ⊔ s.ideal s.length ^ maxOrderNonMonomialOnOrderLocus T s

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tripleAtLength_dim (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ) :
    (tripleAtLength T s J μ).krullDimSucc = krullDimSucc (s.obj s.length) :=
  rfl

end

section

def principalizationSeqAtEnd (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc) :
    MarkedSequenceOfBlowups (s.proj s.length ≫ T.structMap) J μ (s.boundary s.length) :=
  rc (tripleAtLength T s J μ) hd

/- English proof (translation)
Unfold `appendRecursivePrincipalization principalizationSeqAtEnd`. Rewrite using `[dif_pos hd]`.
-/
theorem appendRecursivePrincipalization_eq_appendIfMarked (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc) :
    appendRecursivePrincipalization hinv T rc s J μ = appendIfMarked hinv s J μ (principalizationSeqAtEnd T rc s J μ hd) := by
  unfold appendRecursivePrincipalization principalizationSeqAtEnd
  rw [dif_pos hd]

/- English proof (translation)
Establish `hr : markedDataOfSeq s J μ (principalizationSeqAtEnd T rc s J μ hd) = some ((MarkedBlowupSequenceData.ofMarkedSequence (principalizationSeqAtEnd T rc s J μ hd)).toBlowupSequenceData.toMarkedBlowupSequenceData (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s …`. Unfold `markedDataOfSeq`. Conclude with `dif_pos hm`. Rewrite using `[appendRecursivePrincipalization_eq_appendIfMarked hinv T rc s J μ hd]`. Unfold `appendIfMarked`.

Rewrite using `[hr]`.
-/
theorem appendRecursivePrincipalization_eq_append (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc)
    (hm : (MarkedBlowupSequenceData.ofMarkedSequence (principalizationSeqAtEnd T rc s J μ hd)).toBlowupSequenceData.IsMarked
      (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length)) :
    appendRecursivePrincipalization hinv T rc s J μ =
      s.append
        ((MarkedBlowupSequenceData.ofMarkedSequence (principalizationSeqAtEnd T rc s J μ hd)).toBlowupSequenceData.toMarkedBlowupSequenceData
          (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length) hm)
        hinv := by
  have hr : markedDataOfSeq s J μ (principalizationSeqAtEnd T rc s J μ hd) =
      some ((MarkedBlowupSequenceData.ofMarkedSequence (principalizationSeqAtEnd T rc s J μ hd)).toBlowupSequenceData.toMarkedBlowupSequenceData
        (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length) hm) := by
    unfold markedDataOfSeq
    exact dif_pos hm
  rw [appendRecursivePrincipalization_eq_appendIfMarked hinv T rc s J μ hd]
  unfold appendIfMarked
  rw [hr]

end

section

variable (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
  (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)

def extendByNonMonomialPart (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  appendRecursivePrincipalization hinv T rc s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)

def extendByCompanionIdeal (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  appendRecursivePrincipalization hinv T rc s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nonMonomialOrderReductionIter_zero :
    nonMonomialOrderReductionIter hinv T rc 0 = emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  rfl

/- English proof (translation)
Rewrite using `[nonMonomialOrderReductionIter]`. Conclude with `if_pos h`.
-/
theorem nonMonomialOrderReductionIter_succ_of_continues (f : ℕ) (h : NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T rc f)) :
    nonMonomialOrderReductionIter hinv T rc (f + 1) = extendByNonMonomialPart hinv T rc (nonMonomialOrderReductionIter hinv T rc f) := by
  rw [nonMonomialOrderReductionIter]
  exact if_pos h

/- English proof (translation)
Rewrite using `[nonMonomialOrderReductionIter]`. Conclude with `if_neg h`.
-/
theorem nonMonomialOrderReductionIter_succ_of_not_continues (f : ℕ) (h : ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T rc f)) :
    nonMonomialOrderReductionIter hinv T rc (f + 1) = nonMonomialOrderReductionIter hinv T rc f := by
  rw [nonMonomialOrderReductionIter]
  exact if_neg h

/- English proof (translation)
Introduce `g hg`. Proceed by induction on `g, hg using Nat.le_induction with`. Consider the case `base => rfl`. Consider the case `succ n hn ih`. Establish `hn' : ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T rc n)`.

Rewrite using `[ih]`. Conclude with `h`. Rewrite using `[nonMonomialOrderReductionIter_succ_of_not_continues hinv T rc n hn']`. Conclude with `ih`.
-/
theorem nonMonomialOrderReductionIter_eq_of_not_continues (f : ℕ) (h : ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T rc f)) :
    ∀ g, f ≤ g → nonMonomialOrderReductionIter hinv T rc g = nonMonomialOrderReductionIter hinv T rc f := by
  intro g hg
  induction g, hg using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have hn' : ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T rc n) := by
      rw [ih]
      exact h
    rw [nonMonomialOrderReductionIter_succ_of_not_continues hinv T rc n hn']
    exact ih

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nonMonomialOrderReduction_eq :
    nonMonomialOrderReduction hinv T rc =
      nonMonomialOrderReductionIter hinv T rc (maxOrder (nonMonomialPart T.boundary T.ideal) + 1) :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem companionIdealReductionIter_zero (s₀ : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    companionIdealReductionIter hinv T rc s₀ 0 = s₀ :=
  rfl

/- English proof (translation)
Rewrite using `[companionIdealReductionIter]`. Conclude with `if_pos h`.
-/
theorem companionIdealReductionIter_succ_of_continues (s₀ : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (f : ℕ) (h : CompanionIdealReductionContinues T (companionIdealReductionIter hinv T rc s₀ f)) :
    companionIdealReductionIter hinv T rc s₀ (f + 1) =
      extendByCompanionIdeal hinv T rc (companionIdealReductionIter hinv T rc s₀ f) := by
  rw [companionIdealReductionIter]
  exact if_pos h

/- English proof (translation)
Rewrite using `[companionIdealReductionIter]`. Conclude with `if_neg h`.
-/
theorem companionIdealReductionIter_succ_of_not_continues
    (s₀ : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (f : ℕ) (h : ¬ CompanionIdealReductionContinues T (companionIdealReductionIter hinv T rc s₀ f)) :
    companionIdealReductionIter hinv T rc s₀ (f + 1) = companionIdealReductionIter hinv T rc s₀ f := by
  rw [companionIdealReductionIter]
  exact if_neg h

/- English proof (translation)
Introduce `g hg`. Proceed by induction on `g, hg using Nat.le_induction with`. Consider the case `base => rfl`. Consider the case `succ n hn ih`. Establish `hn' : ¬ CompanionIdealReductionContinues T (companionIdealReductionIter hinv T rc s₀ n)`.

Rewrite using `[ih]`. Conclude with `h`. Rewrite using `[companionIdealReductionIter_succ_of_not_continues hinv T rc s₀ n hn']`. Conclude with `ih`.
-/
theorem companionIdealReductionIter_eq_of_not_continues
    (s₀ : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (f : ℕ) (h : ¬ CompanionIdealReductionContinues T (companionIdealReductionIter hinv T rc s₀ f)) :
    ∀ g, f ≤ g → companionIdealReductionIter hinv T rc s₀ g = companionIdealReductionIter hinv T rc s₀ f := by
  intro g hg
  induction g, hg using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have hn' : ¬ CompanionIdealReductionContinues T (companionIdealReductionIter hinv T rc s₀ n) := by
      rw [ih]
      exact h
    rw [companionIdealReductionIter_succ_of_not_continues hinv T rc s₀ n hn']
    exact ih

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem companionIdealReduction_eq :
    companionIdealReduction hinv T rc =
      companionIdealReductionIter hinv T rc (nonMonomialOrderReduction hinv T rc)
        (maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T rc) + 1) :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem orderReductionData_eq :
    orderReductionData hinv T rc =
      (companionIdealReduction hinv T rc).append
        (MarkedBlowupSequenceData.ofMarkedSequence
          (monomialPrincipalization hinv
            (tripleAtLength T (companionIdealReduction hinv T rc)
              ((companionIdealReduction hinv T rc).ideal (companionIdealReduction hinv T rc).length) T.mult)))
        hinv :=
  rfl

/- English proof (translation)
Unfold `orderReductionSeq`. Rewrite using `[if_neg h.ne_empty]`.
-/
theorem orderReductionSeq_eq_of_nonempty (h : (orderAtLeastLocus T.ideal T.mult).Nonempty) :
    orderReductionSeq hinv T rc = (orderReductionData hinv T rc).toMarkedSequenceOfBlowups := by
  unfold orderReductionSeq
  rw [if_neg h.ne_empty]

end

end FunctorialResolution.EmbeddedResolution

end
