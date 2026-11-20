import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def monomialBlowupStep (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) :=
  ofSingleBlowup (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)
    (centerAtLast s) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
/- English proof (authored)
The monomial step is constructed as the single blowup at the admissible last center. The single-blowup sequence has one step.
-/
theorem monomialBlowupStep_length (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).length = 1 :=
  ofSingleBlowup_length h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
/- English proof (authored)
The single-step sequence starts on the last scheme of the input sequence. Its zero stage is therefore that scheme.
-/
theorem monomialBlowupStep_schemeAt_zero (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).obj 0 = s.obj s.length :=
  ofSingleBlowup_schemeAt_zero h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
/- English proof (authored)
In the single-step data each positive index uses the scheme of the blowup. This blowup is along the last center of the input sequence.
-/
theorem monomialBlowupStep_schemeAt_succ (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) (i : ℕ) :
    (monomialBlowupStep s h).obj (i + 1) = Blowup.blowup (centerAtLast s) :=
  ofSingleBlowup_schemeAt_succ h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 i

@[simp]
/- English proof (authored)
The center used to form the single blowup is the given last center. It is the center at index zero of the single-step sequence.
-/
theorem monomialBlowupStep_center_zero (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).center 0 = centerAtLast s :=
  ofSingleBlowup_center_zero h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
/- English proof (authored)
The first step is the blowup along the last center. Its morphism is the projection from this blowup to the scheme carrying the center.
-/
theorem monomialBlowupStep_blowupMorphism_zero (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).map 0 = Blowup.blowup.proj (centerAtLast s) :=
  ofSingleBlowup_blowupMorphism_zero h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
/- English proof (authored)
The projection from stage one to the base of the single step is the blowup projection followed by the initial identification. That identification is the identity on the last scheme of the old sequence, leaving the blowup projection.
-/
theorem monomialBlowupStep_projectionToBase_one (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).proj 1 = Blowup.blowup.proj (centerAtLast s) :=
  ofSingleBlowup_projectionToBase_one h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
/- English proof (authored)
The marked ideal at stage one is the controlled transform under the single blowup. Pull back the last ideal and remove the mark-th power of the exceptional ideal, which is the pullback of the center. The residual ideal is the stated stage-one ideal.
-/
theorem monomialBlowupStep_ideal_one (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).ideal 1 =
      residualByPow ((s.ideal s.length).comap (Blowup.blowup.proj (centerAtLast s)))
        ((centerAtLast s).comap (Blowup.blowup.proj (centerAtLast s))) m :=
  ofSingleBlowup_ideal_one h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
/- English proof (authored)
The boundary rule for a single blowup replaces each old divisor by its strict transform in the same order and adds the exceptional ideal at the end. The old boundary here is the last boundary of the input sequence.
-/
theorem monomialBlowupStep_boundary_one (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).boundary 1 =
      List.map (Blowup.strictTransform (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s))
          (s.boundary s.length) ++
        [Blowup.exceptionalIdeal (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s)] :=
  ofSingleBlowup_boundary_one h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/- English proof (authored)
The single step's initial scheme is the old last scheme by construction. Its inverse initial isomorphism is exactly the morphism given by this identification in the indicated direction.
-/
theorem monomialBlowupStep_isoObjZero_inv (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).isoZero.inv = eqToHom (monomialBlowupStep_schemeAt_zero s h).symm :=
  rfl

/- English proof (authored)
The last center is admissible, so the operation chooses the branch appending a single blowup at that center. The appended sequence is the given monomial step.
-/
theorem blowupAtCenter_eq_append (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (h : IsAdmissibleCenter s) :
    blowupAtCenter hinv s = s.append (monomialBlowupStep s h) hinv := by
  unfold blowupAtCenter monomialBlowupStep
  rw [dif_pos h]

/- English proof (authored)
The operation appends the single-step sequence when the center is admissible. The length of an append is the sum of the lengths, so the new length is the old length plus one.
-/
theorem blowupAtCenter_length (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (h : IsAdmissibleCenter s) :
    (blowupAtCenter hinv s).length = s.length + 1 := by
  rw [blowupAtCenter_eq_append hinv s h, append_length, monomialBlowupStep_length]

/- English proof (authored)
If the current center were admissible, the successor would have one more blowup and the two lengths could not agree. Conversely, an inadmissible center makes the step return the current sequence, so the lengths agree. This is precisely stationarity at the given index.
-/
theorem isStationaryAt_iff_not_isAdmissibleCenter (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) (n : ℕ) :
    IsStationaryAt hinv s n ↔ ¬ IsAdmissibleCenter (monomialBlowupIterate hinv s n) := by
  constructor
  · intro h hstep
    have hl := blowupAtCenter_length hinv (monomialBlowupIterate hinv s n) hstep
    have h' : (blowupAtCenter hinv (monomialBlowupIterate hinv s n)).length
        = (monomialBlowupIterate hinv s n).length := h
    rw [hl] at h'
    omega
  · intro h
    show (blowupAtCenter hinv (monomialBlowupIterate hinv s n)).length
        = (monomialBlowupIterate hinv s n).length
    unfold blowupAtCenter
    rw [dif_neg h]

/- English proof (authored)
The index one greater than the original length belongs to the appended part with offset one. At that offset the single-step scheme is the blowup of the original last scheme along its last center.
-/
theorem blowupAtCenter_schemeAt_succ (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (h : IsAdmissibleCenter s) :
    (blowupAtCenter hinv s).obj (s.length + 1) = Blowup.blowup (centerAtLast s) := by
  have hlt : s.length < s.length + 1 := Nat.lt_succ_self s.length
  rw [blowupAtCenter_eq_append hinv s h, append_schemeAt_of_length_lt s (monomialBlowupStep s h) hinv hlt]
  have he : s.length + 1 - s.length = 0 + 1 := by omega
  rw [he, monomialBlowupStep_schemeAt_succ s h 0]

/- English proof (authored)
At the new last stage, the ideal of the append is the ideal at offset one of the single step, pulled back along the equality of the stage schemes. The single-step calculation identifies that ideal as the controlled transform by the exceptional power.
-/
theorem blowupAtCenter_ideal_succ (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (h : IsAdmissibleCenter s) :
    (blowupAtCenter hinv s).ideal (s.length + 1) =
      (residualByPow ((s.ideal s.length).comap (Blowup.blowup.proj (centerAtLast s)))
          ((centerAtLast s).comap (Blowup.blowup.proj (centerAtLast s))) m).comap
        (eqToHom (blowupAtCenter_schemeAt_succ hinv s h)) := by
  have key : ∀ d : MarkedBlowupSequenceData p I m E, d = s.append (monomialBlowupStep s h) hinv →
      ∀ hobj : d.obj (s.length + 1) = Blowup.blowup (centerAtLast s),
        d.ideal (s.length + 1) =
          (residualByPow ((s.ideal s.length).comap (Blowup.blowup.proj (centerAtLast s)))
              ((centerAtLast s).comap (Blowup.blowup.proj (centerAtLast s))) m).comap (eqToHom hobj) := by
    rintro d rfl hobj
    rewrite [append_ideal, appendIdeal_length_succ, monomialBlowupStep_ideal_one]
    rfl
  exact key (blowupAtCenter hinv s) (blowupAtCenter_eq_append hinv s h)
    (blowupAtCenter_schemeAt_succ hinv s h)

/- English proof (authored)
Replace the given sequence by its description as the append. The boundary one stage beyond the old length is obtained by transporting the boundary at offset one of the single step along the specified stage identification. At offset one that boundary consists of the strict transforms followed by the exceptional ideal.
-/
private theorem boundary_succ_of_eq_append (hinv : ComapIsoInvariance.{u})
    (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) (d : MarkedBlowupSequenceData p I m E)
    (hd : d = s.append (monomialBlowupStep s h) hinv)
    (e : d.obj (s.length + 1) = Blowup.blowup (centerAtLast s)) :
    d.boundary (s.length + 1) =
      List.map (fun D => D.comap (eqToHom e))
        (List.map (Blowup.strictTransform (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s))
            (s.boundary s.length) ++
          [Blowup.exceptionalIdeal (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s)]) := by
  subst hd
  refine Eq.trans (append_boundary s (monomialBlowupStep s h) hinv (s.length + 1)) ?_
  refine Eq.trans (appendBoundary_length_succ s (monomialBlowupStep s h)) ?_
  exact congrArg
    (List.map (fun D : (Blowup.blowup (centerAtLast s)).IdealSheafData => D.comap (eqToHom e)))
    (monomialBlowupStep_boundary_one s h)

/- English proof (authored)
For an admissible center the new sequence is the append of the monomial step. Its new last boundary is the strict transforms of the old last boundary with the exceptional ideal added, transported along the new scheme identification by the boundary formula for an append.
-/
theorem blowupAtCenter_boundary_succ (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (h : IsAdmissibleCenter s) :
    (blowupAtCenter hinv s).boundary (s.length + 1) =
      List.map (fun D => D.comap (eqToHom (blowupAtCenter_schemeAt_succ hinv s h)))
        (List.map (Blowup.strictTransform (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s))
            (s.boundary s.length) ++
          [Blowup.exceptionalIdeal (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s)]) :=
  boundary_succ_of_eq_append hinv s h (blowupAtCenter hinv s)
    (blowupAtCenter_eq_append hinv s h) (blowupAtCenter_schemeAt_succ hinv s h)

/- English proof (authored)
Beyond the first length, the projection first identifies the stage with the second sequence's stage at the difference of the indices. It then goes to the base of that sequence and through the last projection of the first. The difference is the given second index, giving the claimed composite.
-/
private theorem appendProjectionToBase_of_lt (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (i j : ℕ) (hi : s.length < i) (hj : i - s.length = j)
    (hobj : (s.appendToBlowupSequenceData t).obj i = t.obj j) :
    s.appendProjectionToBase t i = eqToHom hobj ≫ t.proj j ≫ s.proj s.length := by
  subst hj
  exact appendProjectionToBase_of_length_lt s t hi

/- English proof (authored)
Use the appended projection formula with offset one in the single step. Its projection to the joining scheme is the blowup projection. The projection to the original base is therefore the stage identification followed by the blowup projection and the original last projection.
-/
theorem blowupAtCenter_projectionToBase_succ (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (h : IsAdmissibleCenter s) :
    (blowupAtCenter hinv s).proj (s.length + 1) =
      eqToHom (blowupAtCenter_schemeAt_succ hinv s h) ≫ Blowup.blowup.proj (centerAtLast s) ≫ s.proj s.length := by
  have key : ∀ d : MarkedBlowupSequenceData p I m E, d = s.append (monomialBlowupStep s h) hinv →
      ∀ hobj : d.obj (s.length + 1) = Blowup.blowup (centerAtLast s),
        d.proj (s.length + 1) =
          eqToHom hobj ≫ Blowup.blowup.proj (centerAtLast s) ≫ s.proj s.length := by
    rintro d rfl hobj
    rewrite [append_projectionToBase,
      appendProjectionToBase_of_lt s (monomialBlowupStep s h) (s.length + 1) 1 (by omega) (by omega)
        (appendToBlowupSequenceData_schemeAt_length_succ s (monomialBlowupStep s h)),
      monomialBlowupStep_projectionToBase_one]
    rfl
  exact key (blowupAtCenter hinv s) (blowupAtCenter_eq_append hinv s h)
    (blowupAtCenter_schemeAt_succ hinv s h)

end MarkedBlowupSequenceData

section

variable {k : Type u} [Field k] {X : Scheme.{u}}

def monomialStallIndex (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) : ℕ :=
  sInf {n : ℕ | MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n}

/- English proof (authored)
The stationary indices form a nonempty set of natural numbers by hypothesis. Its infimum is its least member, so the defined stationary index is stationary.
-/
theorem isStationaryAt_monomialStallIndex (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData)
    (hex : ∃ n : ℕ, MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n) :
    MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) (monomialStallIndex hinv p I m E) := by
  exact Nat.sInf_mem hex

/- English proof (authored)
If this center were inadmissible, its index would be stationary. The infimum of the stationary indices would then be at most that index, contradicting the strict inequality with the defined stationary index.
-/
theorem isAdmissibleCenter_of_lt_monomialStallIndex (hinv : ComapIsoInvariance.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (n : ℕ) (hn : n < monomialStallIndex hinv p I m E) :
    MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) := by
  have hn' : n < sInf {j : ℕ | MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) j} := hn
  have hstall : ¬ MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n := by
    intro hmem
    have hle : sInf {j : ℕ | MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) j} ≤ n :=
      Nat.sInf_le hmem
    exact absurd hle (not_le.mpr hn')
  by_contra hstep
  exact hstall
    ((MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv (emptyMarkedBlowupSequenceData p I m E) n).mpr hstep)

/- English proof (authored)
The given index is stationary, so the least stationary index is at most it. The least stationary index is itself stationary, because the set is nonempty. If it were smaller, the assumption on earlier centers would make its center admissible, contradicting stationarity. The indices are equal.
-/
theorem monomialStallIndex_eq_of_isStationaryAt (hinv : ComapIsoInvariance.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (n : ℕ)
    (hstall : MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n)
    (hstep : ∀ j < n, MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) j)) :
    monomialStallIndex hinv p I m E = n := by
  have hne : ∃ j : ℕ, MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) j := ⟨n, hstall⟩
  have h1 : monomialStallIndex hinv p I m E ≤ n := Nat.sInf_le hstall
  refine le_antisymm h1 ?_
  by_contra hlt
  have hlt' : monomialStallIndex hinv p I m E < n := lt_of_not_ge hlt
  have hmem : MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E)
      (monomialStallIndex hinv p I m E) := Nat.sInf_mem hne
  exact ((MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv _ _).mp hmem) (hstep _ hlt')

/- English proof (authored)
The monomial sequence is defined by iterating from the empty sequence for the infimum of its stationary indices. That number is the stated stationary index.
-/
theorem monomialBlowupSeq_eq_monomialBlowupIterate (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) :
    monomialBlowupSeq hinv p I m E =
      MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
        (monomialStallIndex hinv p I m E) :=
  rfl

/- English proof (authored)
Induct on the number of iterations. At zero the sequence is the initial one. At a successor all earlier centers satisfy the induction hypothesis, and the current admissible center appends exactly one blowup. This increases both the actual length and the formula by one.
-/
private theorem monomialBlowupIterate_length {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (s : MarkedBlowupSequenceData p I m E) (n : ℕ) :
    (∀ j < n, MarkedBlowupSequenceData.IsAdmissibleCenter (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j)) →
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv s n).length = s.length + n := by
  induction n with
  | zero =>
      intro _
      rw [MarkedBlowupSequenceData.monomialBlowupIterate_zero, Nat.add_zero]
  | succ n ih =>
      intro hstep
      have h2 : MarkedBlowupSequenceData.IsAdmissibleCenter (MarkedBlowupSequenceData.monomialBlowupIterate hinv s n) :=
        hstep n (Nat.lt_succ_self n)
      have h1 := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
      have e1 : (MarkedBlowupSequenceData.monomialBlowupIterate hinv s (n + 1)).length
          = (MarkedBlowupSequenceData.monomialBlowupIterate hinv s n).length + 1 := by
        rw [MarkedBlowupSequenceData.monomialBlowupIterate_succ,
          MarkedBlowupSequenceData.blowupAtCenter_length hinv _ h2]
      omega

/- English proof (authored)
Before the first stationary index every center is admissible. Apply the iteration length formula from the empty sequence through that index. The initial length is zero, so the resulting length equals the stationary index.
-/
theorem monomialBlowupSeq_length (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) :
    (monomialBlowupSeq hinv p I m E).length = monomialStallIndex hinv p I m E := by
  have h := monomialBlowupIterate_length hinv (emptyMarkedBlowupSequenceData p I m E)
    (monomialStallIndex hinv p I m E)
    (fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j hj)
  rw [monomialBlowupSeq_eq_monomialBlowupIterate, h, emptyMarkedBlowupSequenceData_length, Nat.zero_add]

/- English proof (authored)
If the center is admissible, the operation appends a single step and the stages up to the old length continue to use the original schemes. If the center is inadmissible, the operation returns the sequence itself. Both cases give the stated equality.
-/
private theorem blowupAtCenter_schemeAt_of_le {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i ≤ d.length) :
    (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj i = d.obj i := by
  by_cases h : MarkedBlowupSequenceData.IsAdmissibleCenter d
  · rw [MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv d h]
    exact MarkedBlowupSequenceData.append_schemeAt_of_le_length d (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv hi
  · have hs : MarkedBlowupSequenceData.blowupAtCenter hinv d = d := by
      unfold MarkedBlowupSequenceData.blowupAtCenter
      rw [dif_neg h]
    rw [hs]

/- English proof (authored)
The operation appends one blowup if the center is admissible and otherwise returns the original sequence. The length either increases by one or stays equal, giving the inequality.
-/
private theorem length_le_blowupAtCenter_length {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) :
    d.length ≤ (MarkedBlowupSequenceData.blowupAtCenter hinv d).length := by
  by_cases h : MarkedBlowupSequenceData.IsAdmissibleCenter d
  · rw [MarkedBlowupSequenceData.blowupAtCenter_length hinv d h]
    omega
  · have hs : MarkedBlowupSequenceData.blowupAtCenter hinv d = d := by
      unfold MarkedBlowupSequenceData.blowupAtCenter
      rw [dif_neg h]
    exact le_of_eq (by rw [hs])

/- English proof (authored)
At zero both claims are immediate from the initial sequence. Induct on the number of steps. The next step does not reduce the length, so it preserves the lower bound. Each original index still lies within the preceding sequence by that bound. Its scheme survives the new step and agrees with the original scheme by induction.
-/
private theorem monomialBlowupIterate_length_le_and_schemeAt_eq {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) (j : ℕ) :
    d.length ≤ (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).length ∧
      ∀ i ≤ d.length, (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).obj i = d.obj i := by
  induction j with
  | zero =>
      refine ⟨?_, ?_⟩
      · exact le_of_eq (by rw [MarkedBlowupSequenceData.monomialBlowupIterate_zero])
      · intro i _
        rw [MarkedBlowupSequenceData.monomialBlowupIterate_zero]
  | succ j ih =>
      refine ⟨?_, ?_⟩
      · refine le_trans ih.1 ?_
        rw [MarkedBlowupSequenceData.monomialBlowupIterate_succ]
        exact length_le_blowupAtCenter_length hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j)
      · intro i hi
        rw [MarkedBlowupSequenceData.monomialBlowupIterate_succ,
          blowupAtCenter_schemeAt_of_le hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j) i
            (le_trans hi ih.1)]
        exact ih.2 i hi

/- English proof (authored)
Induct on the second iteration count. A zero second count returns the first iterate. For a successor, both expressions apply the same center step to the preceding expression, and those preceding expressions are equal by induction and associativity of addition.
-/
private theorem monomialBlowupIterate_add {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) (a b : ℕ) :
    MarkedBlowupSequenceData.monomialBlowupIterate hinv d (a + b) =
      MarkedBlowupSequenceData.monomialBlowupIterate hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d a) b := by
  induction b with
  | zero => rw [Nat.add_zero, MarkedBlowupSequenceData.monomialBlowupIterate_zero]
  | succ b ih =>
      rw [← Nat.add_assoc, MarkedBlowupSequenceData.monomialBlowupIterate_succ,
        MarkedBlowupSequenceData.monomialBlowupIterate_succ, ih]

/- English proof (authored)
Up to the given index, every step before it has an admissible center, so its iterate from the empty sequence has length equal to the index. Split the iteration to the stationary index into this iterate and the remaining iterations. Later iterations preserve all its stages. Thus the given stage in the full sequence is the last scheme of that earlier iterate.
-/
theorem monomialBlowupSeq_schemeAt (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (n : ℕ)
    (hn : n ≤ monomialStallIndex hinv p I m E) :
    (monomialBlowupSeq hinv p I m E).obj n =
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).obj
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length := by
  have hlen : (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length = n := by
    have h := monomialBlowupIterate_length hinv (emptyMarkedBlowupSequenceData p I m E) n
      (fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j (lt_of_lt_of_le hj hn))
    rw [emptyMarkedBlowupSequenceData_length, Nat.zero_add] at h
    exact h
  rw [hlen]
  have hsplit : monomialStallIndex hinv p I m E = n + (monomialStallIndex hinv p I m E - n) := by
    omega
  rw [monomialBlowupSeq_eq_monomialBlowupIterate, hsplit, monomialBlowupIterate_add hinv (emptyMarkedBlowupSequenceData p I m E) n
    (monomialStallIndex hinv p I m E - n)]
  exact (monomialBlowupIterate_length_le_and_schemeAt_eq hinv
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)
    (monomialStallIndex hinv p I m E - n)).2 n (le_of_eq hlen.symm)

/- English proof (authored)
The two identification morphisms come from opposite equalities of schemes and are inverse. The successive pullbacks therefore compose to pullback along the identity, giving the original ideal.
-/
private theorem comap_eqToHom_comap_eqToHom_symm {V W : Scheme.{u}} (h : V = W)
    (J : W.IdealSheafData) :
    (J.comap (eqToHom h)).comap (eqToHom h.symm) = J := by
  subst h
  simp

/- English proof (authored)
If the current center is admissible, the next iterate is formed by appending its single blowup, so the current sequence is its prefix. Otherwise the next iterate equals the current one, which is a prefix of itself.
-/
private theorem isPrefix_monomialBlowupIterate_succ {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) (j : ℕ) :
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j).IsPrefix
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv s (j + 1)) := by
  by_cases h : MarkedBlowupSequenceData.IsAdmissibleCenter (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j)
  · rw [MarkedBlowupSequenceData.monomialBlowupIterate_succ,
      MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv _ h]
    exact MarkedBlowupSequenceData.isPrefix_append _ _ hinv
  · have hs : MarkedBlowupSequenceData.blowupAtCenter hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j)
        = MarkedBlowupSequenceData.monomialBlowupIterate hinv s j := by
      unfold MarkedBlowupSequenceData.blowupAtCenter
      rw [dif_neg h]
    rw [MarkedBlowupSequenceData.monomialBlowupIterate_succ, hs]
    exact MarkedBlowupSequenceData.IsPrefix.refl _

/- English proof (authored)
Induct on the later index. At equality the iterate is its own prefix. If the earlier index is strictly below a successor, apply induction to the predecessor, then use the consecutive prefix relation and transitivity.
-/
private theorem isPrefix_monomialBlowupIterate_of_le {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) {i j : ℕ} (hij : i ≤ j) :
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv s i).IsPrefix
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j) := by
  induction j with
  | zero =>
      obtain rfl : i = 0 := Nat.le_zero.mp hij
      exact MarkedBlowupSequenceData.IsPrefix.refl _
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hij with h | h
      · subst h
        exact MarkedBlowupSequenceData.IsPrefix.refl _
      · exact (ih (Nat.lt_succ_iff.mp h)).trans (isPrefix_monomialBlowupIterate_succ hinv s n)

/- English proof (authored)
Identify the index with the length of the prefix. The prefix relation expresses its ideal at that stage as the pullback of the longer sequence's ideal under the prefix identification. Pull back along the inverse identification. The two transports cancel, yielding the given ideal on the longer sequence.
-/
private theorem ideal_eq_comap_of_isPrefix {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (A B : MarkedBlowupSequenceData p I m E) (n : ℕ) (hlen : A.length = n)
    (hpre : A.IsPrefix B) (hobj : B.obj n = A.obj A.length) :
    B.ideal n = (A.ideal A.length).comap (eqToHom hobj) := by
  subst hlen
  rw [hpre.ideal_eq A.length le_rfl]
  exact (comap_eqToHom_comap_eqToHom_symm (hpre.obj_eq A.length le_rfl) (B.ideal A.length)).symm

/- English proof (authored)
The iterate at the chosen index has that index as its length because every earlier center is admissible. It is a prefix of the full iteration to the stationary index. The ideal formula for a prefix therefore identifies the full sequence's ideal at that index with the transported last ideal of the chosen iterate.
-/
theorem monomialBlowupSeq_ideal (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (n : ℕ)
    (hn : n ≤ monomialStallIndex hinv p I m E) :
    (monomialBlowupSeq hinv p I m E).ideal n =
      ((MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).ideal
          (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length).comap
        (eqToHom (monomialBlowupSeq_schemeAt hinv p I m E n hn)) := by
  have hstep : ∀ j < n, MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) j) :=
    fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j (lt_of_lt_of_le hj hn)
  have hlen : (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length = n := by
    rw [monomialBlowupIterate_length hinv (emptyMarkedBlowupSequenceData p I m E) n hstep,
      emptyMarkedBlowupSequenceData_length, Nat.zero_add]
  have hpre : (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).IsPrefix
      (monomialBlowupSeq hinv p I m E) := by
    rw [monomialBlowupSeq_eq_monomialBlowupIterate]
    exact isPrefix_monomialBlowupIterate_of_le hinv (emptyMarkedBlowupSequenceData p I m E) hn
  exact ideal_eq_comap_of_isPrefix
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)
    (monomialBlowupSeq hinv p I m E) n hlen hpre (monomialBlowupSeq_schemeAt hinv p I m E n hn)

/- English proof (authored)
An equality of the scheme with itself induces the identity morphism. Pullback of the ideal along that morphism leaves it unchanged.
-/
private theorem comap_eqToHom_self {Y : Scheme.{u}} (q : Y = Y) (Z : Y.IdealSheafData) :
    Z.comap (eqToHom q) = Z := by
  simp

/- English proof (authored)
Every boundary entry pulls back to itself along the identity induced by the equality. Therefore the mapped list equals the original list.
-/
private theorem map_comap_eqToHom_self {Y : Scheme.{u}} (q : Y = Y) (L : List Y.IdealSheafData) :
    List.map (fun D => D.comap (eqToHom q)) L = L := by
  induction L with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, ih, comap_eqToHom_self]

/- English proof (authored)
The changes of scheme identification along the two equalities compose to the change along their combined equality. By functoriality the two successive pullbacks equal the single pullback along that composite.
-/
private theorem comap_eqToHom_comp {A B C : Scheme.{u}} (hAB : A = B) (hBC : B = C) (hAC : A = C)
    (D : C.IdealSheafData) :
    (D.comap (eqToHom hBC)).comap (eqToHom hAB) = D.comap (eqToHom hAC) := by
  cases hAB
  cases hBC
  simp only [comap_eqToHom_self]

/- English proof (authored)
For each list entry, the two successive ideal pullbacks along the scheme identifications equal pullback along the combined identification. Applying this equality at every position gives equality of the lists.
-/
private theorem map_comap_eqToHom_comp {A B C : Scheme.{u}} (hAB : A = B) (hBC : B = C)
    (hAC : A = C) (L : List C.IdealSheafData) :
    List.map (fun D : B.IdealSheafData => D.comap (eqToHom hAB))
        (List.map (fun D : C.IdealSheafData => D.comap (eqToHom hBC)) L)
      = List.map (fun D : C.IdealSheafData => D.comap (eqToHom hAC)) L := by
  induction L with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih, comap_eqToHom_comp hAB hBC hAC]

/- English proof (authored)
The admissible step is an append. At a stage up to the old length, the boundary formula for appends takes the original boundary and pulls each ideal back along the stage identification. This gives the stated list.
-/
private theorem blowupAtCenter_boundary_of_le (hinv : ComapIsoInvariance.{u})
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (h : MarkedBlowupSequenceData.IsAdmissibleCenter s) (i : ℕ) (hi : i ≤ s.length)
    (ho : (MarkedBlowupSequenceData.blowupAtCenter hinv s).obj i = s.obj i) :
    (MarkedBlowupSequenceData.blowupAtCenter hinv s).boundary i =
      List.map (fun D => D.comap (eqToHom ho)) (s.boundary i) := by
  have key : ∀ d : MarkedBlowupSequenceData p I m E,
      d = s.append (MarkedBlowupSequenceData.monomialBlowupStep s h) hinv →
      ∀ ho' : d.obj i = s.obj i,
        d.boundary i = List.map (fun D => D.comap (eqToHom ho')) (s.boundary i) := by
    rintro d rfl ho'
    refine Eq.trans
      (MarkedBlowupSequenceData.append_boundary s (MarkedBlowupSequenceData.monomialBlowupStep s h) hinv i) ?_
    exact MarkedBlowupSequenceData.appendBoundary_of_le_length s (MarkedBlowupSequenceData.monomialBlowupStep s h) hi
  exact key (MarkedBlowupSequenceData.blowupAtCenter hinv s)
    (MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv s h) ho

/- English proof (authored)
Induct on the number of further steps. With zero steps the identification is the identity. In a successor, the earlier stage is still within the preceding sequence because its length has grown. The latest admissible step transports the preceding boundary, and induction identifies that preceding boundary with the transported original boundary. Combining the two identification morphisms gives the stated direct pullback of each original entry.
-/
private theorem monomialBlowupIterate_boundary_of_le (hinv : ComapIsoInvariance.{u})
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i ≤ s.length) (d : ℕ) :
    (∀ j < d, MarkedBlowupSequenceData.IsAdmissibleCenter (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j)) →
      ∀ ho : (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).obj i = s.obj i,
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).boundary i =
          List.map (fun D => D.comap (eqToHom ho)) (s.boundary i) := by
  induction d with
  | zero =>
      intro _ ho
      exact (map_comap_eqToHom_self ho (s.boundary i)).symm
  | succ d ih =>
      intro hstep ho
      have h2 : MarkedBlowupSequenceData.IsAdmissibleCenter (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d) :=
        hstep d (Nat.lt_succ_self d)
      have hlen : (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).length = s.length + d :=
        monomialBlowupIterate_length hinv s d (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
      have hi' : i ≤ (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).length := by omega
      have hobj1 : (MarkedBlowupSequenceData.blowupAtCenter hinv
            (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d)).obj i
          = (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).obj i :=
        blowupAtCenter_schemeAt_of_le hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d) i hi'
      have hobj2 : (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).obj i = s.obj i :=
        Eq.trans hobj1.symm ho
      have hstep1 := blowupAtCenter_boundary_of_le hinv
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d) h2 i hi' hobj1
      have hprev := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj)) hobj2
      exact Eq.trans hstep1
        (Eq.trans (congrArg (List.map (fun D => D.comap (eqToHom hobj1))) hprev)
          (map_comap_eqToHom_comp hobj1 hobj2 ho (s.boundary i)))

/- English proof (authored)
Use the equality of indices to replace the index on the second sequence with the specified index on the first. The boundary formula at that common index then applies with the given scheme identification.
-/
private theorem boundary_eq_map_comap_of_index_eq
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (d t : MarkedBlowupSequenceData p I m E) (n L : ℕ) (hL : L = n)
    (hb : ∀ ho : d.obj n = t.obj n,
      d.boundary n = List.map (fun D => D.comap (eqToHom ho)) (t.boundary n))
    (H : d.obj n = t.obj L) :
    d.boundary n = List.map (fun D => D.comap (eqToHom H)) (t.boundary L) := by
  subst hL
  exact hb H

/- English proof (authored)
The iterate at the given index has length equal to that index. Express the full sequence as this iterate followed by the remaining iterations to the first stationary index. Each remaining step before that index has an admissible center, so iteration preserves the earlier boundary under the stage identification. At the given index that boundary is the earlier iterate's last boundary, giving the formula.
-/
theorem monomialBlowupSeq_boundary (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (n : ℕ)
    (hn : n ≤ monomialStallIndex hinv p I m E) :
    (monomialBlowupSeq hinv p I m E).boundary n =
      List.map (fun D => D.comap (eqToHom (monomialBlowupSeq_schemeAt hinv p I m E n hn)))
        ((MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).boundary
          (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length) := by
  have hsteps0 : ∀ j < n, MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) j) :=
    fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j (lt_of_lt_of_le hj hn)
  have hlen : (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length = n := by
    rw [monomialBlowupIterate_length hinv (emptyMarkedBlowupSequenceData p I m E) n hsteps0,
      emptyMarkedBlowupSequenceData_length, Nat.zero_add]
  have h1 : n + (monomialStallIndex hinv p I m E - n) = monomialStallIndex hinv p I m E := by omega
  have hseq : monomialBlowupSeq hinv p I m E =
      MarkedBlowupSequenceData.monomialBlowupIterate hinv
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)
        (monomialStallIndex hinv p I m E - n) := by
    have h2 : MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
        (n + (monomialStallIndex hinv p I m E - n))
        = MarkedBlowupSequenceData.monomialBlowupIterate hinv
            (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)
            (monomialStallIndex hinv p I m E - n) :=
      monomialBlowupIterate_add hinv (emptyMarkedBlowupSequenceData p I m E) n (monomialStallIndex hinv p I m E - n)
    rw [h1] at h2
    exact Eq.trans (monomialBlowupSeq_eq_monomialBlowupIterate hinv p I m E) h2
  have hstepsn : ∀ j < monomialStallIndex hinv p I m E - n, MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) j) := by
    intro j hj
    have h3 : MarkedBlowupSequenceData.monomialBlowupIterate hinv
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) j
        = MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) (n + j) :=
      (monomialBlowupIterate_add hinv (emptyMarkedBlowupSequenceData p I m E) n j).symm
    rw [h3]
    exact isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E (n + j) (by omega)
  have key : ∀ d : MarkedBlowupSequenceData p I m E,
      d = MarkedBlowupSequenceData.monomialBlowupIterate hinv
            (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)
            (monomialStallIndex hinv p I m E - n) →
      ∀ ho : d.obj n = (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).obj n,
        d.boundary n = List.map (fun D => D.comap (eqToHom ho))
          ((MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).boundary n) := by
    rintro d rfl ho
    exact monomialBlowupIterate_boundary_of_le hinv
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) n (by omega)
      (monomialStallIndex hinv p I m E - n) hstepsn ho
  exact boundary_eq_map_comap_of_index_eq (monomialBlowupSeq hinv p I m E)
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) n
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length hlen
    (key (monomialBlowupSeq hinv p I m E) hseq) (monomialBlowupSeq_schemeAt hinv p I m E n hn)

/- English proof (authored)
The marked append uses the center ideals of its appended underlying blowup data. Thus at any index its center agrees with the underlying center.
-/
private theorem append_center_eq_appendToBlowupSequenceData_center {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (hinv : ComapIsoInvariance.{u}) (i : ℕ) :
    (s.append t hinv).center i = (s.appendToBlowupSequenceData t).center i :=
  rfl

/- English proof (authored)
If a new blowup is appended, every center strictly before the old length belongs to the first part of the append. Its ideal is the former center pulled back along the identification of the stages. If the center is inadmissible, the sequence is unchanged and the identification pullback is the identity. The formula holds in either case.
-/
private theorem blowupAtCenter_center_of_lt {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i < d.length)
    (e : (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj i = d.obj i) :
    (MarkedBlowupSequenceData.blowupAtCenter hinv d).center i = (d.center i).comap (eqToHom e) := by
  by_cases h : MarkedBlowupSequenceData.IsAdmissibleCenter d
  · have key : ∀ D : MarkedBlowupSequenceData p I m E,
        D = d.append (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv →
        ∀ eD : D.obj i = d.obj i, D.center i = (d.center i).comap (eqToHom eD) := by
      rintro D rfl eD
      refine Eq.trans
        (append_center_eq_appendToBlowupSequenceData_center d (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv i) ?_
      exact MarkedBlowupSequenceData.appendToBlowupSequenceData_center_of_lt_length d (MarkedBlowupSequenceData.monomialBlowupStep d h) hi
    exact key (MarkedBlowupSequenceData.blowupAtCenter hinv d)
      (MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv d h) e
  · have hs : MarkedBlowupSequenceData.blowupAtCenter hinv d = d := by
      unfold MarkedBlowupSequenceData.blowupAtCenter
      rw [dif_neg h]
    have key : ∀ D : MarkedBlowupSequenceData p I m E, D = d →
        ∀ eD : D.obj i = d.obj i, D.center i = (d.center i).comap (eqToHom eD) := by
      rintro D rfl eD
      exact (comap_eqToHom_self eD _).symm
    exact key (MarkedBlowupSequenceData.blowupAtCenter hinv d) hs e

/- English proof (authored)
Induct on the number of further iterations. At zero the center is the original one under an identity pullback. At a successor, the earlier index stays strictly within the preceding length by its lower bound. The one-step center formula identifies it with the transported preceding center, and induction identifies that center with the transported original one. Compose the two pullbacks along the identifications.
-/
private theorem monomialBlowupIterate_center_of_lt {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i < d.length) (j : ℕ) :
    ∀ e : (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).obj i = d.obj i,
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).center i = (d.center i).comap (eqToHom e) := by
  induction j with
  | zero =>
      intro e
      exact (comap_eqToHom_self e (d.center i)).symm
  | succ j ih =>
      intro e
      have e2 : (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).obj i = d.obj i :=
        (monomialBlowupIterate_length_le_and_schemeAt_eq hinv d j).2 i (le_of_lt hi)
      have hij : i < (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).length :=
        lt_of_lt_of_le hi (monomialBlowupIterate_length_le_and_schemeAt_eq hinv d j).1
      have e1 : (MarkedBlowupSequenceData.blowupAtCenter hinv
            (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j)).obj i
          = (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).obj i :=
        blowupAtCenter_schemeAt_of_le hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j) i (le_of_lt hij)
      refine Eq.trans
        (blowupAtCenter_center_of_lt hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j) i hij e1) ?_
      rw [ih e2]
      exact comap_eqToHom_comp e1 e2 e (d.center i)

/- English proof (authored)
At the old last index, the append takes the initial center of the single step. This center is formed by pulling back through the inverse initial isomorphism of that step and through the identification of the joining scheme. The inverse initial isomorphism itself is the identification with the zero stage. Combining the two identifications gives the supplied equality of schemes. The initial center of the single step is the old last center, yielding the formula.
-/
private theorem blowupAtCenter_center_of_eq_length {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) (h : MarkedBlowupSequenceData.IsAdmissibleCenter d) (i : ℕ) (hi : i = d.length)
    (e : (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj i = d.obj d.length) :
    (MarkedBlowupSequenceData.blowupAtCenter hinv d).center i =
      (MarkedBlowupSequenceData.centerAtLast d).comap (eqToHom e) := by
  subst hi
  have key : ∀ D : MarkedBlowupSequenceData p I m E,
      D = d.append (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv →
      ∀ eD : D.obj d.length = d.obj d.length,
        D.center d.length = (MarkedBlowupSequenceData.centerAtLast d).comap (eqToHom eD) := by
    rintro D rfl eD
    have hc : (d.appendToBlowupSequenceData (MarkedBlowupSequenceData.monomialBlowupStep d h)).obj d.length
        = d.obj d.length :=
      MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_le_length d (MarkedBlowupSequenceData.monomialBlowupStep d h) (le_refl d.length)
    have e3 : (d.appendToBlowupSequenceData (MarkedBlowupSequenceData.monomialBlowupStep d h)).obj d.length
        = (MarkedBlowupSequenceData.monomialBlowupStep d h).obj 0 :=
      hc.trans (MarkedBlowupSequenceData.monomialBlowupStep_schemeAt_zero d h).symm
    have s1 : (d.append (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv).center d.length
        = (((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap
            (MarkedBlowupSequenceData.monomialBlowupStep d h).isoZero.inv).comap (eqToHom hc) :=
      MarkedBlowupSequenceData.appendToBlowupSequenceData_center_length d (MarkedBlowupSequenceData.monomialBlowupStep d h)
    have s2 : (((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap
            (MarkedBlowupSequenceData.monomialBlowupStep d h).isoZero.inv).comap (eqToHom hc)
        = (((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap
            (eqToHom (MarkedBlowupSequenceData.monomialBlowupStep_schemeAt_zero d h).symm)).comap (eqToHom hc) := by
      rw [MarkedBlowupSequenceData.monomialBlowupStep_isoObjZero_inv]
    have s3 : (((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap
            (eqToHom (MarkedBlowupSequenceData.monomialBlowupStep_schemeAt_zero d h).symm)).comap (eqToHom hc)
        = ((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap (eqToHom e3) :=
      comap_eqToHom_comp hc (MarkedBlowupSequenceData.monomialBlowupStep_schemeAt_zero d h).symm e3
        ((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0)
    have s4 : ((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap (eqToHom e3)
        = (MarkedBlowupSequenceData.centerAtLast d).comap (eqToHom eD) := by
      rw [MarkedBlowupSequenceData.monomialBlowupStep_center_zero]
      rfl
    exact s1.trans (s2.trans (s3.trans s4))
  exact key (MarkedBlowupSequenceData.blowupAtCenter hinv d)
    (MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv d h) e

/- English proof (authored)
The first added blowup increases the length to the given index plus one. At the given index its center is the former last center under the joining identification. Further iterations preserve all centers strictly within this new length, transporting them by their stage identifications. Composing with the join identification gives the stated pullback.
-/
private theorem center_monomialBlowupIterate_blowupAtCenter_eq {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (d : MarkedBlowupSequenceData p I m E) (n : ℕ) (hlen : d.length = n)
    (h : MarkedBlowupSequenceData.IsAdmissibleCenter d) (r : ℕ) (D : MarkedBlowupSequenceData p I m E)
    (hD : D = MarkedBlowupSequenceData.monomialBlowupIterate hinv (MarkedBlowupSequenceData.blowupAtCenter hinv d) r)
    (eD : D.obj n = d.obj d.length) :
    D.center n = (MarkedBlowupSequenceData.centerAtLast d).comap (eqToHom eD) := by
  subst hD
  have hl1 : (MarkedBlowupSequenceData.blowupAtCenter hinv d).length = n + 1 := by
    rw [MarkedBlowupSequenceData.blowupAtCenter_length hinv d h, hlen]
  have hn1 : n < (MarkedBlowupSequenceData.blowupAtCenter hinv d).length := by omega
  have e1 : (MarkedBlowupSequenceData.monomialBlowupIterate hinv
        (MarkedBlowupSequenceData.blowupAtCenter hinv d) r).obj n
      = (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj n :=
    (monomialBlowupIterate_length_le_and_schemeAt_eq hinv (MarkedBlowupSequenceData.blowupAtCenter hinv d) r).2 n
      (le_of_lt hn1)
  have ejunc : (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj n = d.obj d.length :=
    (blowupAtCenter_schemeAt_of_le hinv d n (le_of_eq hlen.symm)).trans (congrArg d.obj hlen.symm)
  rw [monomialBlowupIterate_center_of_lt hinv (MarkedBlowupSequenceData.blowupAtCenter hinv d) n hn1 r e1,
    blowupAtCenter_center_of_eq_length hinv d h n hlen.symm ejunc]
  exact comap_eqToHom_comp e1 ejunc eD (MarkedBlowupSequenceData.centerAtLast d)

/- English proof (authored)
Before the first stationary index the iterate at the chosen index has length equal to that index and an admissible last center. Split the full iteration into that iterate, its next blowup and the remaining steps. The next blowup uses the last center of the iterate, and the remaining steps preserve it by the earlier-center formula. Transporting it to the stage of the complete sequence gives the claim.
-/
theorem monomialBlowupSeq_center (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (n : ℕ)
    (hn : n < monomialStallIndex hinv p I m E) :
    (monomialBlowupSeq hinv p I m E).center n =
      (MarkedBlowupSequenceData.centerAtLast
          (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)).comap
        (eqToHom (monomialBlowupSeq_schemeAt hinv p I m E n (Nat.le_of_lt hn))) := by
  have hlen : (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length = n := by
    have h := monomialBlowupIterate_length hinv (emptyMarkedBlowupSequenceData p I m E) n
      (fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j (lt_trans hj hn))
    rw [emptyMarkedBlowupSequenceData_length, Nat.zero_add] at h
    exact h
  have hstep : MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) :=
    isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E n hn
  have hsplit : monomialStallIndex hinv p I m E
      = (n + 1) + (monomialStallIndex hinv p I m E - (n + 1)) := by
    omega
  have h1 : MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
        (monomialStallIndex hinv p I m E)
      = MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
          ((n + 1) + (monomialStallIndex hinv p I m E - (n + 1))) := by
    rw [← hsplit]
  have hseq : monomialBlowupSeq hinv p I m E =
      MarkedBlowupSequenceData.monomialBlowupIterate hinv
        (MarkedBlowupSequenceData.blowupAtCenter hinv
          (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n))
        (monomialStallIndex hinv p I m E - (n + 1)) := by
    rw [monomialBlowupSeq_eq_monomialBlowupIterate, h1,
      monomialBlowupIterate_add hinv (emptyMarkedBlowupSequenceData p I m E) (n + 1)
        (monomialStallIndex hinv p I m E - (n + 1)),
      MarkedBlowupSequenceData.monomialBlowupIterate_succ]
  exact center_monomialBlowupIterate_blowupAtCenter_eq hinv
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) n
    hlen hstep (monomialStallIndex hinv p I m E - (n + 1)) (monomialBlowupSeq hinv p I m E) hseq
    (monomialBlowupSeq_schemeAt hinv p I m E n (Nat.le_of_lt hn))

end

namespace MarkedBlowupSequenceData

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def monomialStallIndex (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) : ℕ :=
  sInf {n : ℕ | IsStationaryAt hinv s n}

/- English proof (authored)
The stationary index of a sequence is defined as the infimum of the indices where the next step leaves its length unchanged.
-/
theorem monomialStallIndex_eq_sInf (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) :
    monomialStallIndex hinv s = sInf {n : ℕ | IsStationaryAt hinv s n} :=
  rfl

def monomialIterateUntilStall (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) :
    MarkedBlowupSequenceData p I m E :=
  monomialBlowupIterate hinv s (monomialStallIndex hinv s)

/- English proof (authored)
Iteration until stationarity is defined as iteration for the stationary index of the supplied sequence. This is the expression on the right.
-/
theorem monomialIterateUntilStall_eq_monomialBlowupIterate (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) :
    monomialIterateUntilStall hinv s = monomialBlowupIterate hinv s (monomialStallIndex hinv s) :=
  rfl

/- English proof (authored)
With an inadmissible initial center, the sequence is stationary at iteration zero. Its stationary index is the infimum of a set of natural numbers containing zero, so that infimum is zero.
-/
theorem monomialStallIndex_eq_zero_of_not_isAdmissibleCenter (hinv : ComapIsoInvariance.{u})
    (s : MarkedBlowupSequenceData p I m E) (h : ¬ IsAdmissibleCenter s) : monomialStallIndex hinv s = 0 := by
  have h0 : IsStationaryAt hinv s 0 := (isStationaryAt_iff_not_isAdmissibleCenter hinv s 0).mpr h
  show sInf {n : ℕ | IsStationaryAt hinv s n} = 0
  exact Nat.le_zero.mp (Nat.sInf_le h0)

end

end MarkedBlowupSequenceData

section

variable {k : Type u} [Field k] {X : Scheme.{u}}

/- English proof (authored)
Both expressions take the infimum of stationary indices for the iteration whose initial sequence is empty. They therefore agree.
-/
theorem monomialStallIndex_eq_monomialStallIndex_empty (hinv : ComapIsoInvariance.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    monomialStallIndex hinv p I m E =
      MarkedBlowupSequenceData.monomialStallIndex hinv (emptyMarkedBlowupSequenceData p I m E) :=
  rfl

/- English proof (authored)
Start with the empty marked sequence. The monomial sequence and the construction that iterates until stationarity both run it for the infimum of the same set of stationary indices.
-/
theorem monomialBlowupSeq_eq_monomialIterateUntilStall (hinv : ComapIsoInvariance.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    monomialBlowupSeq hinv p I m E =
      MarkedBlowupSequenceData.monomialIterateUntilStall hinv (emptyMarkedBlowupSequenceData p I m E) :=
  rfl

end

end FunctorialResolution.EmbeddedResolution

end
