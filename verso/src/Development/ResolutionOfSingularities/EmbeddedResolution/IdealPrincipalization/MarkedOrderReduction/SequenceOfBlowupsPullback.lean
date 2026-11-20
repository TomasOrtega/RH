import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace BlowupSequenceData

variable {X : Scheme.{u}}

def transitionMap (d : BlowupSequenceData X) {i i' : ℕ} (h : i ≤ i') : d.obj i' ⟶ d.obj i :=
  d.toSequenceOfBlowups.transitionMap h

/- English proof (authored)
The transition on the data is defined as the transition on the reconstructed sequence, so the two descriptions give the same morphism.
-/
theorem toSequenceOfBlowups_transitionMap (d : BlowupSequenceData X) {i i' : ℕ} (h : i ≤ i') :
    d.toSequenceOfBlowups.transitionMap h = d.transitionMap h := rfl

/- English proof (authored)
A transition from a later stage to an earlier one is the composite of the intervening blowups. Cutting this string at an intermediate stage and composing the two pieces gives the full transition by associativity.
-/
theorem transitionMap_comp_transitionMap (d : BlowupSequenceData X) {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    d.transitionMap hjl ≫ d.transitionMap hij = d.transitionMap (hij.trans hjl) :=
  d.toSequenceOfBlowups.transitionMap_trans hij hjl

/- English proof (authored)
The transition from a stage to itself is the empty composite of blowup morphisms. The empty composite is the identity of that stage.
-/
theorem transitionMap_refl (d : BlowupSequenceData X) (i : ℕ) : d.transitionMap (le_refl i) = 𝟙 (d.obj i) := by
  exact d.toSequenceOfBlowups.transitionMap_self_eq_id (le_refl i)

/- English proof (authored)
A transition between adjacent stages contains exactly one blowup morphism. The reconstructed sequence uses the morphism stored at that position in the data, so the transition equals that morphism.
-/
theorem transitionMap_succ (d : BlowupSequenceData X) (i : ℕ) : d.transitionMap (Nat.le_succ i) = d.map i := by
  have h1 : d.toSequenceOfBlowups.transitionMapSucc i = d.map i := d.toSequenceOfBlowups_blowupMorphism i
  have h2 : d.toSequenceOfBlowups.transitionMapSucc i = d.toSequenceOfBlowups.transitionMap (Nat.le_succ i) :=
    d.toSequenceOfBlowups.blowupMorphism_eq_transitionMap i
  exact h2.symm.trans h1

@[reassoc]
/- English proof (authored)
In the reconstructed sequence the projection to the base is the transition to stage zero followed by the initial isomorphism to the base. Reconstruction preserves the projection, transition and initial isomorphism, giving the formula on the data.
-/
theorem transitionMap_zero_comp_isoObjZero_hom (d : BlowupSequenceData X) (n : ℕ) :
    d.transitionMap (Nat.zero_le n) ≫ d.isoZero.hom = d.projectionToBase n := by
  have h := d.toSequenceOfBlowups.projectionToBase_def n
  rw [BlowupSequenceData.toSequenceOfBlowups_projectionToBase, BlowupSequenceData.toSequenceOfBlowups_transitionMap, BlowupSequenceData.toSequenceOfBlowups_isoObjZero] at h
  exact h.symm

/- English proof (authored)
Adding zero to the length of the first sequence leaves its length. The appended sequence agrees with the first one through that stage, so the scheme is the last scheme of the first sequence.
-/
private theorem append_schemeAt_length_add_zero (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) :
    (s.append t).obj (s.length + 0) = s.obj s.length := by
  have h : s.length + 0 ≤ s.length := le_of_eq (Nat.add_zero _)
  exact (append_schemeAt_of_le_length s t h).trans (congrArg s.obj (Nat.add_zero _))

/- English proof (authored)
This stage is strictly beyond the end of the first sequence. There the appended sequence uses the second sequence, with its index obtained by subtracting the length of the first. The resulting index is the given positive index.
-/
private theorem append_schemeAt_length_add_succ (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (i : ℕ) : (s.append t).obj (s.length + (i + 1)) = t.obj (i + 1) := by
  have h : s.length < s.length + (i + 1) := by omega
  have h2 : s.length + (i + 1) - s.length = i + 1 := by omega
  rw [append_schemeAt_of_length_lt s t h, h2]

def concatObjAddIso (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) :
    ∀ i : ℕ, (s.append t).obj (s.length + i) ≅ t.obj i
  | 0 => eqToIso (append_schemeAt_length_add_zero s t) ≪≫ t.isoZero.symm
  | (i + 1) => eqToIso (append_schemeAt_length_add_succ s t i)

/- English proof (authored)
The two changes of scheme identification following the initial isomorphism are inverses. After they cancel, the initial isomorphism and its inverse are adjacent and cancel as well. The remaining change of identification at the source is the unique one coming from the given equality of schemes.
-/
private theorem eqToHom_comp_blowupMorphism_zero_isoObjZero_cancel {Y : Scheme.{u}} (d : BlowupSequenceData Y) {U V : Scheme.{u}}
    (h1 : U = d.obj 1) (h2 : Y = V) (h3 : V = Y) (h4 : U = d.obj 1) :
    (eqToHom h1 ≫ d.map 0 ≫ d.isoZero.hom ≫ eqToHom h2) ≫ eqToHom h3 ≫ d.isoZero.inv =
      eqToHom h4 ≫ d.map 0 := by
  subst h2
  simp

/- English proof (authored)
Use the equality of indices to identify the two stages and their blowup morphisms. The opposite changes of identification at the target then cancel, and the two changes at the source come from the same equality. The composites coincide.
-/
private theorem eqToHom_comp_blowupMorphism_congr {Y : Scheme.{u}} (d : BlowupSequenceData Y) {a b : ℕ} (hab : a = b)
    {U V : Scheme.{u}} (hU : U = d.obj (a + 1)) (hV : V = d.obj a)
    (e1 : V = d.obj b) (e2 : U = d.obj (b + 1)) :
    (eqToHom hU ≫ d.map a ≫ eqToHom hV.symm) ≫ eqToHom e1 = eqToHom e2 ≫ d.map b := by
  subst hab
  subst hU
  subst hV
  simp

/- English proof (authored)
At the join, the appended blowup is the first blowup of the second sequence followed by the isomorphism from its initial stage to the last stage of the first sequence, using the designated identifications at the source and target. The comparison at the join uses the inverse initial isomorphism. Cancelling this pair and the intervening scheme identifications leaves the comparison at stage one followed by the first blowup of the second sequence.
-/
private theorem append_blowupMorphism_zero_comp_concatObjAddIso (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) :
    (s.append t).map s.length ≫ (concatObjAddIso s t 0).hom =
      (concatObjAddIso s t 1).hom ≫ t.map 0 := by
  rw [append_blowupMorphism_length s t]
  exact eqToHom_comp_blowupMorphism_zero_isoObjZero_cancel t (append_schemeAt_length_succ s t)
    (append_schemeAt_of_le_length s t (le_refl s.length)).symm (append_schemeAt_length_add_zero s t)
    (append_schemeAt_length_add_succ s t 0)

/- English proof (authored)
At a positive offset from the join the appended morphism is the blowup of the second sequence at that offset, transported along the two stage identifications. Subtracting the length of the first sequence recovers the offset. Composing with the comparison at the target cancels the target transport and leaves the comparison at the source followed by the same blowup.
-/
private theorem append_blowupMorphism_succ_comp_concatObjAddIso (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) (k : ℕ) :
    (s.append t).map (s.length + (k + 1)) ≫ (concatObjAddIso s t (k + 1)).hom =
      (concatObjAddIso s t (k + 1 + 1)).hom ≫ t.map (k + 1) := by
  have hgt : s.length < s.length + (k + 1) := by omega
  have hab : s.length + (k + 1) - s.length = k + 1 := by omega
  rw [append_blowupMorphism_of_length_lt s t hgt]
  exact eqToHom_comp_blowupMorphism_congr t hab (append_schemeAt_succ_of_length_lt s t hgt) (append_schemeAt_of_length_lt s t hgt)
    (append_schemeAt_length_add_succ s t k) (append_schemeAt_length_add_succ s t (k + 1))

@[reassoc]
/- English proof (authored)
At offset zero the comparison includes the inverse initial isomorphism of the second sequence, so use the blowup identity at the join. At every positive offset use the identity for an appended blowup strictly beyond the join. These cases exhaust the blowups of the second sequence.
-/
theorem append_blowupMorphism_comp_concatObjAddIso (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) (i : ℕ) :
    (s.append t).map (s.length + i) ≫ (concatObjAddIso s t i).hom =
      (concatObjAddIso s t (i + 1)).hom ≫ t.map i := by
  cases i with
  | zero => exact append_blowupMorphism_zero_comp_concatObjAddIso s t
  | succ k => exact append_blowupMorphism_succ_comp_concatObjAddIso s t k

@[reassoc]
/- English proof (authored)
Induct on the number of steps in the transition. At distance zero both transitions are identities. For the next step, split off the last blowup, commute the preceding transition past its stage comparison by induction, and commute the last blowup past its comparison by the adjacent-stage identity. The resulting blowups on the second sequence compose to its full transition.
-/
theorem append_transitionMap_comp_concatObjAddIso (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) {i i' : ℕ}
    (h : i ≤ i') :
    (s.append t).transitionMap (Nat.add_le_add_left h s.length) ≫ (concatObjAddIso s t i).hom =
      (concatObjAddIso s t i').hom ≫ t.transitionMap h := by
  induction i', h using Nat.le_induction with
  | base =>
      rw [transitionMap_refl, transitionMap_refl, Category.id_comp, Category.comp_id]
  | succ n hn ih =>
      have e1 : (s.append t).transitionMap (Nat.le_succ (s.length + n)) ≫
            (s.append t).transitionMap (Nat.add_le_add_left hn s.length) =
          (s.append t).transitionMap (Nat.add_le_add_left (Nat.le_succ_of_le hn) s.length) :=
        (s.append t).transitionMap_comp_transitionMap (Nat.add_le_add_left hn s.length) (Nat.le_succ (s.length + n))
      have e2 : (s.append t).transitionMap (Nat.le_succ (s.length + n)) =
          (s.append t).map (s.length + n) :=
        (s.append t).transitionMap_succ (s.length + n)
      have e3 : t.transitionMap (Nat.le_succ n) ≫ t.transitionMap hn = t.transitionMap (Nat.le_succ_of_le hn) :=
        t.transitionMap_comp_transitionMap hn (Nat.le_succ n)
      have e4 : t.transitionMap (Nat.le_succ n) = t.map n := t.transitionMap_succ n
      calc (s.append t).transitionMap (Nat.add_le_add_left (Nat.le_succ_of_le hn) s.length) ≫
            (concatObjAddIso s t i).hom
          = ((s.append t).map (s.length + n) ≫
              (s.append t).transitionMap (Nat.add_le_add_left hn s.length)) ≫
              (concatObjAddIso s t i).hom := by
            rw [← e2, e1]
        _ = (s.append t).map (s.length + n) ≫
              ((s.append t).transitionMap (Nat.add_le_add_left hn s.length) ≫ (concatObjAddIso s t i).hom) :=
            Category.assoc _ _ _
        _ = (s.append t).map (s.length + n) ≫ ((concatObjAddIso s t n).hom ≫ t.transitionMap hn) := by
            rw [ih]
        _ = ((s.append t).map (s.length + n) ≫ (concatObjAddIso s t n).hom) ≫ t.transitionMap hn :=
            (Category.assoc _ _ _).symm
        _ = ((concatObjAddIso s t (n + 1)).hom ≫ t.map n) ≫ t.transitionMap hn := by
            rw [append_blowupMorphism_comp_concatObjAddIso]
        _ = (concatObjAddIso s t (n + 1)).hom ≫ (t.map n ≫ t.transitionMap hn) := Category.assoc _ _ _
        _ = (concatObjAddIso s t (n + 1)).hom ≫ t.transitionMap (Nat.le_succ_of_le hn) := by
            rw [← e4, e3]

end BlowupSequenceData

structure SequenceOfBlowupsPullback {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) where
  idx : ℕ → ℕ
  map : ∀ j : ℕ, j ≤ s'.length → (s'.schemeAt j ⟶ s.schemeAt (idx j))
  idx_length : idx s'.length = s.length
  idx_lt : ∀ j : ℕ, j < s'.length → idx j < s.length
  idx_strictMono : ∀ j : ℕ, j < s'.length → idx j < idx (j + 1)
  isPullback : ∀ (j : ℕ) (hj : j ≤ s'.length),
    IsPullback (map j hj) (s'.projectionToBase j) (s.projectionToBase (idx j)) φ
  step : ∀ (j : ℕ) (hj : j < s'.length),
    s'.transitionMapSucc j ≫ map j (le_of_lt hj) =
      map (j + 1) hj ≫ s.transitionMap (le_of_lt (idx_strictMono j hj))
  center_comap : ∀ (j : ℕ) (hj : j < s'.length),
    s'.center j = (s.center (idx j)).comap (map j (le_of_lt hj))
  center_ne_top : ∀ j : ℕ, j < s'.length → s'.center j ≠ ⊤
  omitted : ∀ (i : ℕ), i < s.length → (∀ j : ℕ, j < s'.length → idx j ≠ i) →
    ∀ z : ↥(s.schemeAt i), z ∈ (s.center i).support → ∀ x' : ↥X',
      φ.base x' ≠ (s.projectionToBase i).base z

namespace SequenceOfBlowupsPullback

variable {X X' : Scheme.{u}} {φ : X' ⟶ X}

def lastMap {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s) :
    s'.schemeAt s'.length ⟶ s.schemeAt s.length :=
  c.map s'.length le_rfl ≫ eqToHom (congrArg s.schemeAt c.idx_length)

/- English proof (authored)
Identify the two indices using their equality. Their stage schemes and their projections coincide, and the intervening identification morphism becomes the identity. The new square is the original pullback square.
-/
private theorem isPullback_comp_eqToHom {A B Y : Scheme.{u}} {ψ : B ⟶ A} {t : SequenceOfBlowups A}
    {n m : ℕ} (hn : n = m) (f : Y ⟶ t.schemeAt n) (g : Y ⟶ B)
    (h : IsPullback f g (t.projectionToBase n) ψ) :
    IsPullback (f ≫ eqToHom (congrArg t.schemeAt hn)) g (t.projectionToBase m) ψ := by
  subst hn
  rw [eqToHom_refl, Category.comp_id]
  exact h

/- English proof (authored)
The pullback data give a pullback square at the last upper stage. Its matching lower index is the last lower index. Transport the lower stage along this equality to get the square with the designated last-stage map.
-/
theorem isPullback_lastMap {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (c : SequenceOfBlowupsPullback φ s' s) :
    IsPullback c.lastMap (s'.projectionToBase s'.length) (s.projectionToBase s.length) φ := by
  show IsPullback (c.map s'.length le_rfl ≫ eqToHom (congrArg s.schemeAt c.idx_length))
      (s'.projectionToBase s'.length) (s.projectionToBase s.length) φ
  exact isPullback_comp_eqToHom c.idx_length _ _ (c.isPullback s'.length le_rfl)

/- English proof (authored)
Induct on the later index. There is no smaller natural number in the zero case. At a successor, strict increase from its predecessor is part of the data. A smaller index either is the predecessor or lies before it. In the latter case compose the strict inequality from induction with the last strict increase.
-/
private theorem index_lt_index_of_lt {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ i j : ℕ, j ≤ s'.length → i < j → c.idx i < c.idx j := by
  intro i j
  induction j with
  | zero => intro _ h; exact absurd h (Nat.not_lt_zero i)
  | succ n ih =>
      intro hn hij
      have hn' : n < s'.length := Nat.lt_of_succ_le hn
      have hstep : c.idx n < c.idx (n + 1) := c.idx_strictMono n hn'
      by_cases hcase : i < n
      · exact lt_trans (ih (le_of_lt hn') hcase) hstep
      · have hie : i = n := by omega
        subst hie
        exact hstep

/- English proof (authored)
The two composites from the pullback to the common target agree by the pullback square. Evaluating their underlying maps at the given point equates the two images.
-/
private theorem pullback_condition_base_apply {Y Z W : Scheme.{u}} (f : Y ⟶ W) (g : Z ⟶ W)
    (x : ↥(pullback f g)) :
    f.base ((pullback.fst f g).base x) = g.base ((pullback.snd f g).base x) := by
  have h : (pullback.fst f g ≫ f).base x = (pullback.snd f g ≫ g).base x := by
    rw [pullback.condition]
  simpa using h

/- English proof (authored)
An ideal sheaf has empty support exactly when it is the unit ideal. Since this ideal is proper, its support contains a point.
-/
private theorem exists_mem_support_of_ne_top {Y : Scheme.{u}} (J : Y.IdealSheafData) (h : J ≠ ⊤) :
    ∃ x : ↥Y, x ∈ J.support := by
  by_contra hc
  push Not at hc
  have hb : J.support = ⊥ := by
    ext y
    simpa using hc y
  exact h ((AlgebraicGeometry.Scheme.IdealSheafData.support_eq_bot_iff J).mp hb)

private def isoPullback {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)
    (i : ℕ) (hi : i ≤ s'.length) : s'.schemeAt i ≅ pullback φ (s.projectionToBase (c.idx i)) :=
  ((c.isPullback i hi).flip).isoPullback

/- English proof (authored)
Order the factors with the upper base first. The canonical isomorphism from the upper stage to the pullback is induced by the upper projection and the comparison to the lower stage. Its composite with the first projection is therefore the upper projection.
-/
private theorem pullbackIso_hom_fst {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (c : SequenceOfBlowupsPullback φ s' s) (i : ℕ) (hi : i ≤ s'.length) :
    (isoPullback c i hi).hom ≫ pullback.fst φ (s.projectionToBase (c.idx i)) = s'.projectionToBase i :=
  IsPullback.isoPullback_hom_fst _

/- English proof (authored)
The canonical isomorphism from the upper stage to the pullback is induced by the upper projection and the comparison to the lower stage. The universal property identifies its composite with the second projection as that comparison.
-/
private theorem pullbackIso_hom_snd {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (c : SequenceOfBlowupsPullback φ s' s) (i : ℕ) (hi : i ≤ s'.length) :
    (isoPullback c i hi).hom ≫ pullback.snd φ (s.projectionToBase (c.idx i)) = c.map i hi :=
  IsPullback.isoPullback_hom_snd _

/- English proof (authored)
Use the given matching indices and the canonical isomorphisms supplied by the stage squares. Strict increase for any two stages follows from strict increase at consecutive ones, and the bounds and final index come from the data. If a lower center is omitted, a point in its pulled-back support would give an upper base point and a lower center point with equal image, contrary to the omission condition. If a lower center is matched, its pullback has nonempty support because its further pullback under the stage isomorphism is the specified proper upper center. The stage isomorphisms preserve the maps to the upper base by the first projection formula. They preserve transitions because the two composites into the pullback have equal first projections by transitivity of the base projection and equal second projections by the step equation. The center equation follows from the second projection formula.
-/
theorem isPullbackSequenceOfBlowups {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (c : SequenceOfBlowupsPullback φ s' s) : IsPullbackBlowupSequence φ s' s := by
  refine ⟨c.idx, fun i hi => isoPullback c i hi, c.idx_lt, index_lt_index_of_lt c, c.idx_length,
    ?_, ?_, ?_, ?_⟩
  · intro i hi
    constructor
    · rintro ⟨x, hx⟩
      by_contra hcon
      push Not at hcon
      exact c.omitted i hi hcon _ (Scheme.IdealSheafData.mem_support_comap.mp hx) _
        (pullback_condition_base_apply φ (s.projectionToBase i) x)
    · rintro ⟨j, hj, rfl⟩
      refine exists_mem_support_of_ne_top _ ?_
      intro htop
      refine c.center_ne_top j hj ?_
      rw [c.center_comap j hj, ← pullbackIso_hom_snd c j (le_of_lt hj),
        Scheme.IdealSheafData.comap_comp, htop,
        AlgebraicGeometry.Scheme.IdealSheafData.comap_top]
  · intro i hi
    exact pullbackIso_hom_fst c i hi
  · intro i hi hr
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackIso_hom_fst, Category.assoc, SequenceOfBlowups.pullbackTransitionMap_comp_fst,
        pullbackIso_hom_fst, SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_comp_projectionToBase]
    · rw [Category.assoc, pullbackIso_hom_snd, Category.assoc, SequenceOfBlowups.pullbackTransitionMap_comp_snd,
        ← Category.assoc, pullbackIso_hom_snd]
      exact c.step i hi
  · intro i hi
    rw [pullbackIso_hom_snd]
    exact c.center_comap i hi

/- English proof (authored)
Reconstructing a sequence preserves its length. Thus the given index is before the end of the upper sequence. Its match is before the end of the lower sequence by the pullback data, and this is also the length stored in the lower data.
-/
theorem blowupSequenceData_index_lt_length {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (j : ℕ) (hj : j < d'.length) :
    c.idx j < d.length := by
  have h : j < d'.toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length]
    exact hj
  have h2 := c.idx_lt j h
  rwa [BlowupSequenceData.toSequenceOfBlowups_length] at h2

/- English proof (authored)
The bound on the upper index holds in the reconstructed sequence because reconstruction preserves the length. Apply the strict-increase condition of the pullback data to this consecutive pair.
-/
theorem blowupSequenceData_index_lt_index_succ {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (j : ℕ) (hj : j < d'.length) :
    c.idx j < c.idx (j + 1) :=
  c.idx_strictMono j (by rw [BlowupSequenceData.toSequenceOfBlowups_length]; exact hj)

/- English proof (authored)
The last upper index is matched to the last lower one. Reconstruction leaves both lengths equal to those of the original data, giving the same equality for the data.
-/
theorem index_length_eq_length {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) : c.idx d'.length = d.length := by
  simpa only [BlowupSequenceData.toSequenceOfBlowups_length] using c.idx_length

@[reassoc]
/- English proof (authored)
Apply the step equation of the pullback comparison at the given upper index. Reconstruction uses the stored upper blowup as its adjacent transition and the reconstructed lower transition as the transition on the data. Those identifications give the stated equation.
-/
theorem blowupSequenceData_blowupMorphism_comp_map {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (j : ℕ) (hj : j < d'.length) :
    d'.map j ≫ c.map j (le_of_lt hj) =
      c.map (j + 1) hj ≫ d.transitionMap (le_of_lt (c.blowupSequenceData_index_lt_index_succ j hj)) := by
  have hj' : j < d'.toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length]
    exact hj
  have h := c.step j hj'
  rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism] at h
  exact h

section

def concatIndex (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ) : ℕ :=
  if j < s'.length then c.idx j else s.length + e.idx (j - s'.length)

/- English proof (authored)
Before the end of the upper first sequence, the matching for the append uses the matching of the two first sequences. This gives the original lower index.
-/
theorem concatIndex_of_lt (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ) (h : j < s'.length) :
    concatIndex s t s' t' c e j = c.idx j := if_pos h

/- English proof (authored)
At or after the join, subtract the length of the upper first sequence to get an index in the upper second sequence. Match that index in the lower second sequence and add the length of the lower first sequence to express it as an index in the append.
-/
theorem concatIndex_of_ge (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ) (h : s'.length ≤ j) :
    concatIndex s t s' t' c e j = s.length + e.idx (j - s'.length) := if_neg (not_lt.2 h)

/- English proof (authored)
The matched index is that of the first comparison and is strictly below the length of the lower first sequence. At that index the lower append uses the scheme of the lower first sequence, giving the identification.
-/
private theorem append_schemeAt_concatIndex_of_lt (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ) (h : j < s'.length) :
    s.obj (c.idx j) = (s.append t).obj (concatIndex s t s' t' c e j) := by
  rw [concatIndex_of_lt s t s' t' c e j h]
  exact (BlowupSequenceData.append_schemeAt_of_le_length s t (le_of_lt (c.blowupSequenceData_index_lt_length j h))).symm

/- English proof (authored)
At or beyond the join, subtracting the first length and then adding it recovers the index. Taking the scheme at the two equal indices gives the identification.
-/
private theorem append_schemeAt_eq_length_add_sub (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (j : ℕ) (h : s'.length ≤ j) :
    (s'.append t').obj j = (s'.append t').obj (s'.length + (j - s'.length)) := by
  have h2 : s'.length + (j - s'.length) = j := by omega
  rw [h2]

/- English proof (authored)
At or after the upper join, the matching index is the lower first length plus the lower second-sequence match of the upper offset. Taking the lower appended scheme at this expression gives the same scheme as taking it at the matching index.
-/
private theorem append_schemeAt_concatIndex_of_le (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ) (h : s'.length ≤ j) :
    (s.append t).obj (s.length + e.idx (j - s'.length)) =
      (s.append t).obj (concatIndex s t s' t' c e j) := by
  rw [concatIndex_of_ge s t s' t' c e j h]

/- English proof (authored)
The total length is the first length plus the second length. Subtracting the first length from the upper bound gives the second length. If the index lies before the join, the nonnegative difference is zero and the bound still holds.
-/
private theorem sub_length_le_of_le_length_add (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (j : ℕ) (hj : j ≤ s'.length + t'.length) : j - s'.length ≤ t'.length := by
  omega

def concatMapOfLtLength (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ) (h : j < s'.length) :
    (s'.append t').obj j ⟶ (s.append t).obj (concatIndex s t s' t' c e j) :=
  eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h)) ≫ c.map j (le_of_lt h) ≫
    eqToHom (append_schemeAt_concatIndex_of_lt s t s' t' c e j h)

def concatMapAddLength (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (i : ℕ) (hi : i ≤ t'.length) :
    (s'.append t').obj (s'.length + i) ⟶ (s.append t).obj (s.length + e.idx i) :=
  (BlowupSequenceData.concatObjAddIso s' t' i).hom ≫ e.map i hi ≫ (BlowupSequenceData.concatObjAddIso s t (e.idx i)).inv

def concatMap (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ)
    (hj : j ≤ s'.length + t'.length) :
    (s'.append t').obj j ⟶ (s.append t).obj (concatIndex s t s' t' c e j) :=
  if h : j < s'.length then concatMapOfLtLength s t s' t' c e j h
  else
    eqToHom (append_schemeAt_eq_length_add_sub s' t' j (not_lt.1 h)) ≫
      concatMapAddLength s t s' t' c e (j - s'.length) (sub_length_le_of_le_length_add s' t' j hj) ≫
      eqToHom (append_schemeAt_concatIndex_of_le s t s' t' c e j (not_lt.1 h))

/- English proof (authored)
At the last upper stage the offset beyond the upper first sequence is the full length of the upper second sequence. The second comparison matches that to the full length of the lower second sequence. Adding the lower first length gives the last lower stage.
-/
private theorem concatIndex_length_add_length (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) :
    concatIndex s t s' t' c e (s'.length + t'.length) = s.length + t.length := by
  rw [concatIndex_of_ge s t s' t' c e (s'.length + t'.length) (Nat.le_add_right _ _)]
  have h : s'.length + t'.length - s'.length = t'.length := by omega
  rw [h, e.index_length_eq_length]

/- English proof (authored)
Before the upper join the matched index is below the lower first length, hence below the total. At or after the join, subtract the upper first length to get an offset strictly below the upper second length. The second comparison matches this to an offset strictly below the lower second length. Adding the lower first length gives the desired strict bound.
-/
private theorem concatIndex_lt_length_add_length (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ)
    (hj : j < s'.length + t'.length) :
    concatIndex s t s' t' c e j < s.length + t.length := by
  by_cases h : j < s'.length
  · rw [concatIndex_of_lt s t s' t' c e j h]
    have hc := c.blowupSequenceData_index_lt_length j h
    omega
  · have hge : s'.length ≤ j := not_lt.1 h
    rw [concatIndex_of_ge s t s' t' c e j hge]
    have hlt : j - s'.length < t'.length := by omega
    have he := e.blowupSequenceData_index_lt_length (j - s'.length) hlt
    omega

/- English proof (authored)
If both indices precede the upper join, the first comparison is strictly increasing at this step. If the step crosses the join, the first match is below the lower first length and the second is at least that length. If both indices are at or beyond the join, their offsets differ by one, so the second comparison is strictly increasing and adding the same lower first length preserves the inequality.
-/
private theorem concatIndex_lt_concatIndex_succ (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ)
    (hj : j < s'.length + t'.length) :
    concatIndex s t s' t' c e j < concatIndex s t s' t' c e (j + 1) := by
  by_cases h : j < s'.length
  · rw [concatIndex_of_lt s t s' t' c e j h]
    by_cases h2 : j + 1 < s'.length
    · rw [concatIndex_of_lt s t s' t' c e (j + 1) h2]
      exact c.blowupSequenceData_index_lt_index_succ j h
    · rw [concatIndex_of_ge s t s' t' c e (j + 1) (by omega)]
      have hlt : c.idx j < s.length := c.blowupSequenceData_index_lt_length j h
      omega
  · have hge : s'.length ≤ j := by omega
    rw [concatIndex_of_ge s t s' t' c e j hge,
      concatIndex_of_ge s t s' t' c e (j + 1) (by omega)]
    have hsub : j + 1 - s'.length = (j - s'.length) + 1 := by omega
    rw [hsub]
    have hlt : j - s'.length < t'.length := by omega
    have hstep : e.idx (j - s'.length) < e.idx ((j - s'.length) + 1) :=
      e.blowupSequenceData_index_lt_index_succ (j - s'.length) hlt
    omega

/- English proof (authored)
The isomorphism on the source and the identity on its base form a pullback square for the source projection. Paste this square horizontally with the given pullback square. The pasted maps are the two given maps precomposed with the isomorphism.
-/
private theorem isPullback_iso_hom_comp {A A' B Y Z : Scheme.{u}} (u : A' ≅ A)
    {f : A ⟶ B} {g : A ⟶ Y} {k : B ⟶ Z} {ψ : Y ⟶ Z} (h : IsPullback f g k ψ) :
    IsPullback (u.hom ≫ f) (u.hom ≫ g) k ψ := by
  have h1 : IsPullback u.hom (u.hom ≫ g) g (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have h2 := h1.paste_horiz h
  simpa using h2

/- English proof (authored)
The isomorphism on the top right and the identity on the lower right form a pullback square, with the projection from the replacement scheme obtained using the inverse isomorphism. Paste this on the right of the original square to obtain the new one.
-/
private theorem isPullback_comp_iso_hom {A B B' Y Z : Scheme.{u}} (v : B ≅ B')
    {f : A ⟶ B} {g : A ⟶ Y} {k : B ⟶ Z} {ψ : Y ⟶ Z} (h : IsPullback f g k ψ) :
    IsPullback (f ≫ v.hom) g (v.inv ≫ k) ψ := by
  have h1 : IsPullback v.hom k (v.inv ≫ k) (𝟙 Z) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have h2 := h.paste_horiz h1
  simpa using h2

/- English proof (authored)
First transport the right-hand scheme along its isomorphism, using its inverse to adjust the projection. Then transport the upper left scheme, precomposing its two arrows by the source isomorphism. Both transports preserve the pullback property, and the prescribed equalities identify the resulting maps.
-/
private theorem isPullback_of_iso {A A' B B' Y Z : Scheme.{u}} (u : A' ≅ A) (v : B ≅ B')
    {f : A ⟶ B} {g : A ⟶ Y} {k : B ⟶ Z} {ψ : Y ⟶ Z}
    {F : A' ⟶ B'} {G : A' ⟶ Y} {K : B' ⟶ Z} (h : IsPullback f g k ψ)
    (hF : F = u.hom ≫ f ≫ v.hom) (hG : G = u.hom ≫ g) (hK : K = v.inv ≫ k) :
    IsPullback F G K ψ := by
  subst hF
  subst hG
  subst hK
  exact isPullback_iso_hom_comp u (isPullback_comp_iso_hom v h)

/- English proof (authored)
Both sides compose the same five morphisms in the same order. Successive applications of associativity give the displayed grouping.
-/
private theorem comp_assoc_outer {A B C D E F : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C)
    (f : C ⟶ D) (g : D ⟶ E) (w : E ⟶ F) :
    p ≫ (q ≫ f ≫ g) ≫ w = (p ≫ q) ≫ f ≫ g ≫ w := by
  simp

/- English proof (authored)
At the join the projection is the projection of the last stage of the first sequence under its identification with the appended stage. The comparison with the second sequence then applies the inverse initial isomorphism, while the second projection at stage zero applies that initial isomorphism. These two maps cancel, giving the join projection.
-/
private theorem append_projectionToBase_length_add_zero {Y : Scheme.{u}} (a : BlowupSequenceData Y)
    (b : BlowupSequenceData (a.obj a.length)) :
    (a.append b).projectionToBase (a.length + 0) =
      (BlowupSequenceData.concatObjAddIso a b 0).hom ≫ b.projectionToBase 0 ≫ a.projectionToBase a.length := by
  have h1 := BlowupSequenceData.projectionToBase_append_of_le_length a b (le_refl a.length)
  have h2 : (BlowupSequenceData.concatObjAddIso a b 0).hom =
      eqToHom (BlowupSequenceData.append_schemeAt_length_add_zero a b) ≫ b.isoZero.inv := rfl
  show (a.append b).projectionToBase a.length =
      (BlowupSequenceData.concatObjAddIso a b 0).hom ≫ b.projectionToBase 0 ≫ a.projectionToBase a.length
  rw [h1, h2, b.projectionToBase_zero]
  simp

/- English proof (authored)
The positive offset places the stage beyond the join. Its projection thus goes through the second sequence at the index obtained by subtracting the first length, then through the final projection of the first sequence. The difference is the stated positive offset, and the initial change of identification is exactly the comparison at that offset.
-/
private theorem append_projectionToBase_length_add_succ {Y : Scheme.{u}} (a : BlowupSequenceData Y)
    (b : BlowupSequenceData (a.obj a.length)) (n : ℕ) :
    (a.append b).projectionToBase (a.length + (n + 1)) =
      (BlowupSequenceData.concatObjAddIso a b (n + 1)).hom ≫ b.projectionToBase (n + 1) ≫ a.projectionToBase a.length := by
  have hgt : a.length < a.length + (n + 1) := by omega
  have hsub : a.length + (n + 1) - a.length = n + 1 := by omega
  have h1 := BlowupSequenceData.projectionToBase_append_of_length_lt a b hgt
  have h2 := BlowupSequenceData.projectionToBase_congr b hsub
  have h3 : (BlowupSequenceData.concatObjAddIso a b (n + 1)).hom =
      eqToHom (BlowupSequenceData.append_schemeAt_length_add_succ a b n) := rfl
  rw [h1, h2, h3]
  simp

/- English proof (authored)
At offset zero the formula is the projection at the join. At a positive offset it is the projection from a stage strictly beyond the join. The two preceding identities give the same factorization in their respective cases.
-/
private theorem append_projectionToBase_length_add {Y : Scheme.{u}} (a : BlowupSequenceData Y)
    (b : BlowupSequenceData (a.obj a.length)) (i : ℕ) :
    (a.append b).projectionToBase (a.length + i) =
      (BlowupSequenceData.concatObjAddIso a b i).hom ≫ b.projectionToBase i ≫ a.projectionToBase a.length := by
  cases i with
  | zero => exact append_projectionToBase_length_add_zero a b
  | succ n => exact append_projectionToBase_length_add_succ a b n

/- English proof (authored)
Use the equality of indices to work at the earlier index. The append preserves the first sequence at stages up to its end, so the projection is the projection of the first sequence preceded by the identification of the stage schemes. Reconstruction preserves these projections.
-/
private theorem append_projectionToBase_eq_of_le_length {Y : Scheme.{u}} (a : BlowupSequenceData Y)
    (b : BlowupSequenceData (a.obj a.length)) {n i : ℕ} (hni : n = i) (hi : i ≤ a.length)
    (hobj : a.obj i = (a.append b).obj n) :
    (a.append b).toSequenceOfBlowups.projectionToBase n = eqToHom hobj.symm ≫ a.toSequenceOfBlowups.projectionToBase i := by
  subst hni
  have h1 := BlowupSequenceData.projectionToBase_append_of_le_length a b hi
  simp only [BlowupSequenceData.toSequenceOfBlowups_projectionToBase, h1]
  rfl

/- English proof (authored)
Replace the index by the first length plus the stated offset. The change of identification for this equality is then the identity. Apply the factorization of the appended projection through the second sequence and the last stage of the first, which also holds after reconstruction.
-/
private theorem append_projectionToBase_eq_of_eq_length_add {Y : Scheme.{u}} (a : BlowupSequenceData Y)
    (b : BlowupSequenceData (a.obj a.length)) {n i : ℕ} (hni : n = a.length + i)
    (hobj : (a.append b).obj n = (a.append b).obj (a.length + i)) :
    (a.append b).toSequenceOfBlowups.projectionToBase n =
      (eqToHom hobj ≫ (BlowupSequenceData.concatObjAddIso a b i).hom) ≫
        b.toSequenceOfBlowups.projectionToBase i ≫ a.toSequenceOfBlowups.projectionToBase a.length := by
  subst hni
  simp only [BlowupSequenceData.toSequenceOfBlowups_projectionToBase, append_projectionToBase_length_add a b i, eqToHom_refl, Category.id_comp]
  rfl

/- English proof (authored)
Before the upper join, the new comparison is the first comparison transported by the appended stage identifications, which also carry the projections to the base. At or beyond the join, the comparison for the second sequences gives a pullback square over the last-stage map of the first comparison. Paste it vertically with the last-stage pullback square of the first comparison. The resulting projections are the successive projections through the second and first sequences. Transport the stage schemes to the corresponding appended stages. The projection factorization and the definition of the comparison identify the resulting square with the stated one.
-/
private theorem isPullback_concatMap (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ)
    (hj : j ≤ s'.length + t'.length) :
    IsPullback (concatMap s t s' t' c e j hj) ((s'.append t').toSequenceOfBlowups.projectionToBase j)
      ((s.append t).toSequenceOfBlowups.projectionToBase (concatIndex s t s' t' c e j)) φ := by
  by_cases h : j < s'.length
  · have hmap : concatMap s t s' t' c e j hj = concatMapOfLtLength s t s' t' c e j h := dif_pos h
    have hidx : concatIndex s t s' t' c e j = c.idx j := concatIndex_of_lt s t s' t' c e j h
    have hobj : s.obj (c.idx j) = (s.append t).obj (concatIndex s t s' t' c e j) :=
      append_schemeAt_concatIndex_of_lt s t s' t' c e j h
    refine isPullback_of_iso (eqToIso (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h)))
      (eqToIso hobj) (c.isPullback j (le_of_lt h)) ?_ ?_ ?_
    · exact hmap
    · exact append_projectionToBase_eq_of_le_length s' t' (show j = j from rfl) (le_of_lt h)
        (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h)).symm
    · exact append_projectionToBase_eq_of_le_length s t hidx (le_of_lt (c.blowupSequenceData_index_lt_length j h)) hobj
  · have hge : s'.length ≤ j := not_lt.1 h
    have hji : j = s'.length + (j - s'.length) := by omega
    have hidx : concatIndex s t s' t' c e j = s.length + e.idx (j - s'.length) :=
      concatIndex_of_ge s t s' t' c e j hge
    have hmap : concatMap s t s' t' c e j hj =
        eqToHom (append_schemeAt_eq_length_add_sub s' t' j hge) ≫
          concatMapAddLength s t s' t' c e (j - s'.length) (sub_length_le_of_le_length_add s' t' j hj) ≫
          eqToHom (append_schemeAt_concatIndex_of_le s t s' t' c e j hge) := dif_neg h
    refine isPullback_of_iso
      (eqToIso (append_schemeAt_eq_length_add_sub s' t' j hge) ≪≫
        BlowupSequenceData.concatObjAddIso s' t' (j - s'.length))
      ((BlowupSequenceData.concatObjAddIso s t (e.idx (j - s'.length))).symm ≪≫
        eqToIso (append_schemeAt_concatIndex_of_le s t s' t' c e j hge))
      ((e.isPullback (j - s'.length) (sub_length_le_of_le_length_add s' t' j hj)).paste_vert
        c.isPullback_lastMap) ?_ ?_ ?_
    · rw [hmap]
      simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
      exact comp_assoc_outer _ _ _ _ _
    · exact append_projectionToBase_eq_of_eq_length_add s' t' hji (append_schemeAt_eq_length_add_sub s' t' j hge)
    · exact append_projectionToBase_eq_of_eq_length_add s t hidx (append_schemeAt_concatIndex_of_le s t s' t' c e j hge).symm

/- English proof (authored)
Combine the second and third morphisms using associativity. The full composite is unchanged.
-/
private theorem comp_assoc_inner_pair {A B C D E F : Scheme.{u}}
    (f1 : A ⟶ B) (f2 : B ⟶ C) (f3 : C ⟶ D) (f4 : D ⟶ E) (f5 : E ⟶ F) :
    f1 ≫ f2 ≫ f3 ≫ f4 ≫ f5 = f1 ≫ (f2 ≫ f3) ≫ f4 ≫ f5 := by
  rw [Category.assoc]

private def mapOfToSequenceOfBlowups {s' : BlowupSequenceData X'} {s : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups) (j : ℕ) (hj : j ≤ s'.length) :
    s'.obj j ⟶ s.obj (c.idx j) := c.map j hj

private def mapOverLastMap {s' : BlowupSequenceData X'} {s : BlowupSequenceData X}
    {t' : BlowupSequenceData (s'.obj s'.length)} {t : BlowupSequenceData (s.obj s.length)}
    {c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups}
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (i : ℕ) (hi : i ≤ t'.length) :
    t'.obj i ⟶ t.obj (e.idx i) := e.map i hi

/- English proof (authored)
Use the compatibility of the first comparison with a blowup in the upper first sequence. The corresponding lower transition goes between the two matched lower stages, and the comparisons are the same maps on the reconstructed sequences and the data.
-/
private theorem blowupMorphism_comp_lowerMap {s' : BlowupSequenceData X'} {s : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups) (j : ℕ) (hj : j < s'.length) :
    s'.map j ≫ mapOfToSequenceOfBlowups c j (le_of_lt hj) =
      mapOfToSequenceOfBlowups c (j + 1) hj ≫ s.transitionMap (le_of_lt (c.blowupSequenceData_index_lt_index_succ j hj)) :=
  c.blowupSequenceData_blowupMorphism_comp_map j hj

/- English proof (authored)
The step equation for the first comparison equates the two maps to the earlier lower stage. Compose each with the given map out of that stage and reassociate.
-/
private theorem blowupMorphism_comp_lowerMap_assoc {s' : BlowupSequenceData X'} {s : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups) (j : ℕ) (hj : j < s'.length)
    {W : Scheme.{u}} (g : s.obj (c.idx j) ⟶ W) :
    s'.map j ≫ mapOfToSequenceOfBlowups c j (le_of_lt hj) ≫ g =
      mapOfToSequenceOfBlowups c (j + 1) hj ≫ s.transitionMap (le_of_lt (c.blowupSequenceData_index_lt_index_succ j hj)) ≫ g := by
  rw [← Category.assoc, blowupMorphism_comp_lowerMap, Category.assoc]

/- English proof (authored)
Identify the two upper indices by their equality. This also identifies their matched lower indices, so both scheme identification morphisms are identities and the comparison maps coincide.
-/
private theorem lowerMap_congr {s' : BlowupSequenceData X'} {s : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups) {a b : ℕ} (hab : a = b)
    (ha : a ≤ s'.length) (hb : b ≤ s'.length)
    (E1 : s'.obj a = s'.obj b) (E2 : s.obj (c.idx b) = s.obj (c.idx a)) :
    mapOfToSequenceOfBlowups c a ha = eqToHom E1 ≫ mapOfToSequenceOfBlowups c b hb ≫ eqToHom E2 := by
  subst hab
  simp

/- English proof (authored)
The last-stage map is defined by taking the comparison at the last upper stage and then identifying the matched lower stage with the last lower stage. The matching of endpoints supplies precisely that identification.
-/
private theorem lastMap_eq_lowerMap {s' : BlowupSequenceData X'} {s : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (E : s.obj (c.idx s'.length) = s.obj s.length) :
    c.lastMap = mapOfToSequenceOfBlowups c s'.length le_rfl ≫ eqToHom E := rfl

/- English proof (authored)
Apply the step equation for the second comparison, whose base morphism is the last-stage map of the first comparison. The adjacent upper blowup is the stored morphism and the lower transition runs between the matched second-sequence indices.
-/
private theorem blowupMorphism_comp_upperMap {s' : BlowupSequenceData X'} {s : BlowupSequenceData X}
    {t' : BlowupSequenceData (s'.obj s'.length)} {t : BlowupSequenceData (s.obj s.length)}
    {c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups}
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (i : ℕ) (hi : i < t'.length) :
    t'.map i ≫ mapOverLastMap e i (le_of_lt hi) =
      mapOverLastMap e (i + 1) hi ≫ t.transitionMap (le_of_lt (e.blowupSequenceData_index_lt_index_succ i hi)) :=
  e.blowupSequenceData_blowupMorphism_comp_map i hi

/- English proof (authored)
Postcompose the step equation for the second comparison with the given morphism from the earlier lower stage. Associativity gives the displayed composites.
-/
private theorem blowupMorphism_comp_upperMap_assoc {s' : BlowupSequenceData X'} {s : BlowupSequenceData X}
    {t' : BlowupSequenceData (s'.obj s'.length)} {t : BlowupSequenceData (s.obj s.length)}
    {c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups}
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (i : ℕ) (hi : i < t'.length)
    {W : Scheme.{u}} (g : t.obj (e.idx i) ⟶ W) :
    t'.map i ≫ mapOverLastMap e i (le_of_lt hi) ≫ g =
      mapOverLastMap e (i + 1) hi ≫ t.transitionMap (le_of_lt (e.blowupSequenceData_index_lt_index_succ i hi)) ≫ g := by
  rw [← Category.assoc, blowupMorphism_comp_upperMap, Category.assoc]

/- English proof (authored)
The pullback square for stage zero of the upper second sequence commutes. The projection from the matched lower stage is the transition to stage zero followed by the lower initial isomorphism. The projection at upper stage zero is the upper initial isomorphism. Substituting these two expressions into the commutative square gives the equation.
-/
private theorem upperMap_zero_comp_isoObjZero {s' : BlowupSequenceData X'} {s : BlowupSequenceData X}
    {t' : BlowupSequenceData (s'.obj s'.length)} {t : BlowupSequenceData (s.obj s.length)}
    {c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups}
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) :
    mapOverLastMap e 0 (Nat.zero_le _) ≫ t.transitionMap (Nat.zero_le (e.idx 0)) ≫ t.isoZero.hom =
      t'.isoZero.hom ≫ c.lastMap := by
  have e1 : t.transitionMap (Nat.zero_le (e.idx 0)) ≫ t.isoZero.hom = t.toSequenceOfBlowups.projectionToBase (e.idx 0) :=
    (BlowupSequenceData.transitionMap_zero_comp_isoObjZero_hom t (e.idx 0)).trans
      (BlowupSequenceData.toSequenceOfBlowups_projectionToBase t (e.idx 0)).symm
  have e2 : t'.toSequenceOfBlowups.projectionToBase 0 = t'.isoZero.hom :=
    (BlowupSequenceData.toSequenceOfBlowups_projectionToBase t' 0).trans (BlowupSequenceData.projectionToBase_zero t')
  have hw := (e.isPullback 0 (Nat.zero_le _)).w
  have A : mapOverLastMap e 0 (Nat.zero_le _) ≫ t.transitionMap (Nat.zero_le (e.idx 0)) ≫ t.isoZero.hom =
      e.map 0 (Nat.zero_le _) ≫ t.toSequenceOfBlowups.projectionToBase (e.idx 0) :=
    congrArg (fun g => e.map 0 (Nat.zero_le _) ≫ g) e1
  have B : t'.toSequenceOfBlowups.projectionToBase 0 ≫ c.lastMap = t'.isoZero.hom ≫ c.lastMap :=
    congrArg (fun g => g ≫ c.lastMap) e2
  exact A.trans (hw.trans B)

/- English proof (authored)
Use the stage-zero equation for the second comparison, then postcompose both sides with the given map from the last lower stage of the first sequence. Reassociate the composites.
-/
private theorem upperMap_zero_comp_isoObjZero_assoc {s' : BlowupSequenceData X'} {s : BlowupSequenceData X}
    {t' : BlowupSequenceData (s'.obj s'.length)} {t : BlowupSequenceData (s.obj s.length)}
    {c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups}
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) {W : Scheme.{u}}
    (g : s.obj s.length ⟶ W) :
    mapOverLastMap e 0 (Nat.zero_le _) ≫ t.transitionMap (Nat.zero_le (e.idx 0)) ≫ t.isoZero.hom ≫ g =
      t'.isoZero.hom ≫ c.lastMap ≫ g := by
  have h := upperMap_zero_comp_isoObjZero e
  calc mapOverLastMap e 0 (Nat.zero_le _) ≫ t.transitionMap (Nat.zero_le (e.idx 0)) ≫ t.isoZero.hom ≫ g
      = (mapOverLastMap e 0 (Nat.zero_le _) ≫ t.transitionMap (Nat.zero_le (e.idx 0)) ≫
          t.isoZero.hom) ≫ g := by
        simp only [Category.assoc]
    _ = (t'.isoZero.hom ≫ c.lastMap) ≫ g := congrArg (fun m => m ≫ g) h
    _ = t'.isoZero.hom ≫ c.lastMap ≫ g := Category.assoc _ _ _

/- English proof (authored)
Substitute the equalities of both endpoint indices. The scheme identifications become identities and the two transitions are the composite over the same interval.
-/
private theorem transitionMap_congr {Y : Scheme.{u}} (d : BlowupSequenceData Y) {a b a' b' : ℕ}
    (ha : a = a') (hb : b = b') (h : a ≤ b) (h' : a' ≤ b')
    (E1 : d.obj b = d.obj b') (E2 : d.obj a' = d.obj a) :
    d.transitionMap h = eqToHom E1 ≫ d.transitionMap h' ≫ eqToHom E2 := by
  subst ha
  subst hb
  simp

/- English proof (authored)
Induct on the distance between the chosen stages. At distance zero both transitions are identities and the scheme identifications cancel. For a longer transition, split off the last adjacent blowup. It is a blowup of the first sequence under the stage identifications because its source lies at or before the join. Substitute the induction formula for the shorter transition, cancel the identifications at the intermediate stage, and compose the two first-sequence transitions.
-/
private theorem append_transitionMap_of_le_length {Y : Scheme.{u}} (s : BlowupSequenceData Y)
    (t : BlowupSequenceData (s.obj s.length)) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ s.length) :
    (s.append t).transitionMap hab =
      eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t hb) ≫ s.transitionMap hab ≫
        eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t (le_trans hab hb)).symm := by
  revert hb
  induction b, hab using Nat.le_induction with
  | base =>
      intro hb
      rw [BlowupSequenceData.transitionMap_refl, BlowupSequenceData.transitionMap_refl]
      simp
  | succ m hm ih =>
      intro hb
      have hmlt : m < s.length := hb
      have hm' : m ≤ s.length := le_of_lt hmlt
      rw [← BlowupSequenceData.transitionMap_comp_transitionMap (s.append t) hm (Nat.le_succ m), BlowupSequenceData.transitionMap_succ,
        BlowupSequenceData.append_blowupMorphism_of_lt_length s t hmlt, ih hm', ← BlowupSequenceData.transitionMap_comp_transitionMap s hm (Nat.le_succ m),
        ← BlowupSequenceData.transitionMap_succ s m]
      simp

/- English proof (authored)
Start with the commuting square for the direct comparisons of the two stages. Precompose it with the inverse of the later comparison and postcompose it with the inverse of the earlier comparison. Cancelling both inverse pairs gives the formula.
-/
private theorem concatObjAddIso_inv_comp_transitionMap {Y : Scheme.{u}} (s : BlowupSequenceData Y)
    (t : BlowupSequenceData (s.obj s.length)) {a b : ℕ} (h : a ≤ b) (hd : s.length + a ≤ s.length + b) :
    (BlowupSequenceData.concatObjAddIso s t b).inv ≫ (s.append t).transitionMap hd =
      t.transitionMap h ≫ (BlowupSequenceData.concatObjAddIso s t a).inv := by
  have key := BlowupSequenceData.append_transitionMap_comp_concatObjAddIso s t h
  calc (BlowupSequenceData.concatObjAddIso s t b).inv ≫ (s.append t).transitionMap hd
      = (BlowupSequenceData.concatObjAddIso s t b).inv ≫
          ((s.append t).transitionMap hd ≫ (BlowupSequenceData.concatObjAddIso s t a).hom) ≫
            (BlowupSequenceData.concatObjAddIso s t a).inv := by simp
    _ = (BlowupSequenceData.concatObjAddIso s t b).inv ≫
          ((BlowupSequenceData.concatObjAddIso s t b).hom ≫ t.transitionMap h) ≫
            (BlowupSequenceData.concatObjAddIso s t a).inv := by rw [key]
    _ = t.transitionMap h ≫ (BlowupSequenceData.concatObjAddIso s t a).inv := by simp

/- English proof (authored)
The inverse comparison commutes with the transition between the two stages. Postcompose this equality with the given morphism out of the earlier appended stage and use associativity.
-/
private theorem concatObjAddIso_inv_comp_transitionMap_assoc {Y : Scheme.{u}} (s : BlowupSequenceData Y)
    (t : BlowupSequenceData (s.obj s.length)) {a b : ℕ} (h : a ≤ b) (hd : s.length + a ≤ s.length + b)
    {W : Scheme.{u}} (g : (s.append t).obj (s.length + a) ⟶ W) :
    (BlowupSequenceData.concatObjAddIso s t b).inv ≫ (s.append t).transitionMap hd ≫ g =
      t.transitionMap h ≫ (BlowupSequenceData.concatObjAddIso s t a).inv ≫ g := by
  rw [← Category.assoc, concatObjAddIso_inv_comp_transitionMap s t h hd, Category.assoc]

/- English proof (authored)
Split the appended transition at the join. The inverse comparison carries the first segment to the transition in the second sequence down to stage zero, followed by the inverse comparison at the join. That inverse uses the initial isomorphism to reach the last stage of the first sequence. The remaining segment is a transition of the first sequence transported by the stage identifications. Cancel the two identifications at the join to obtain the formula.
-/
private theorem concatObjAddIso_inv_comp_transitionMap_of_le_length {Y : Scheme.{u}} (s : BlowupSequenceData Y)
    (t : BlowupSequenceData (s.obj s.length)) {m i : ℕ} (hm : m ≤ s.length) (h : m ≤ s.length + i) :
    (BlowupSequenceData.concatObjAddIso s t i).inv ≫ (s.append t).transitionMap h =
      t.transitionMap (Nat.zero_le i) ≫ t.isoZero.hom ≫ s.transitionMap hm ≫
        eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t hm).symm := by
  have h2 : (BlowupSequenceData.concatObjAddIso s t 0).inv =
      t.isoZero.hom ≫ eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t (le_refl s.length)).symm := rfl
  have h1 : (BlowupSequenceData.concatObjAddIso s t i).inv ≫ (s.append t).transitionMap (Nat.le_add_right s.length i) =
      t.transitionMap (Nat.zero_le i) ≫ (BlowupSequenceData.concatObjAddIso s t 0).inv :=
    concatObjAddIso_inv_comp_transitionMap s t (Nat.zero_le i) (Nat.le_add_right s.length i)
  have h3 : (s.append t).transitionMap hm =
      eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t (le_refl s.length)) ≫ s.transitionMap hm ≫
        eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t hm).symm :=
    append_transitionMap_of_le_length s t hm (le_refl s.length)
  calc (BlowupSequenceData.concatObjAddIso s t i).inv ≫ (s.append t).transitionMap h
      = (BlowupSequenceData.concatObjAddIso s t i).inv ≫
          (s.append t).transitionMap (Nat.le_add_right s.length i) ≫ (s.append t).transitionMap hm := by
        rw [BlowupSequenceData.transitionMap_comp_transitionMap]
    _ = (t.transitionMap (Nat.zero_le i) ≫ (BlowupSequenceData.concatObjAddIso s t 0).inv) ≫
          (s.append t).transitionMap hm := by
        rw [← Category.assoc, h1]
    _ = t.transitionMap (Nat.zero_le i) ≫ t.isoZero.hom ≫ s.transitionMap hm ≫
          eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t hm).symm := by
        rw [h2, h3]
        simp

/- English proof (authored)
Apply the factorization of the inverse comparison followed by the transition across the join. Postcompose the factorization with the given morphism out of the earlier appended stage and reassociate.
-/
private theorem concatObjAddIso_inv_comp_transitionMap_of_le_length_assoc {Y : Scheme.{u}} (s : BlowupSequenceData Y)
    (t : BlowupSequenceData (s.obj s.length)) {m i : ℕ} (hm : m ≤ s.length) (h : m ≤ s.length + i)
    {W : Scheme.{u}} (g : (s.append t).obj m ⟶ W) :
    (BlowupSequenceData.concatObjAddIso s t i).inv ≫ (s.append t).transitionMap h ≫ g =
      t.transitionMap (Nat.zero_le i) ≫ t.isoZero.hom ≫ s.transitionMap hm ≫
        eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t hm).symm ≫ g := by
  rw [← Category.assoc, concatObjAddIso_inv_comp_transitionMap_of_le_length s t hm h]
  simp

/- English proof (authored)
At offset zero the appended stage is identified with the last scheme of the first sequence. The comparison then uses the inverse initial isomorphism to reach the zero stage of the second sequence. Its forward morphism is this composite.
-/
private theorem concatObjAddIso_zero_hom {Y : Scheme.{u}} (s : BlowupSequenceData Y)
    (t : BlowupSequenceData (s.obj s.length)) :
    (BlowupSequenceData.concatObjAddIso s t 0).hom =
      eqToHom (BlowupSequenceData.append_schemeAt_length_add_zero s t) ≫ t.isoZero.inv := rfl

private def appendMapAdd (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (i : ℕ) (hi : i ≤ t'.length) :
    (s'.append t').obj (s'.length + i) ⟶ (s.append t).obj (s.length + e.idx i) :=
  (BlowupSequenceData.concatObjAddIso s' t' i).hom ≫ mapOverLastMap e i hi ≫
    (BlowupSequenceData.concatObjAddIso s t (e.idx i)).inv

/- English proof (authored)
Use the equality of offsets to identify the two instances of the second comparison. The endpoint scheme identifications are those associated to the same equalities on both sides. Hence the full composites agree.
-/
private theorem upperConcatMap_congr (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) {j r q : ℕ} (hr : r = q)
    (hrle : r ≤ t'.length) (hq : q ≤ t'.length)
    (A : (s'.append t').obj j = (s'.append t').obj (s'.length + r))
    (B : (s.append t).obj (s.length + e.idx r) = (s.append t).obj (concatIndex s t s' t' c e j))
    (E1 : (s'.append t').obj j = (s'.append t').obj (s'.length + q))
    (E2 : (s.append t).obj (s.length + e.idx q) =
      (s.append t).obj (concatIndex s t s' t' c e j)) :
    eqToHom A ≫ appendMapAdd s t s' t' c e r hrle ≫ eqToHom B =
      eqToHom E1 ≫ appendMapAdd s t s' t' c e q hq ≫ eqToHom E2 := by
  subst hr
  rfl

/- English proof (authored)
Before the upper join the definition chooses the first comparison. Its source and target identifications are the specified identifications between the two first sequences and the appended stages, giving the formula.
-/
private theorem concatMap_eq_lowerMap_of_lt (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ)
    (hj : j ≤ s'.length + t'.length) (h : j < s'.length)
    (A : (s'.append t').obj j = s'.obj j)
    (B : s.obj (c.idx j) = (s.append t).obj (concatIndex s t s' t' c e j)) :
    concatMap s t s' t' c e j hj = eqToHom A ≫ mapOfToSequenceOfBlowups c j (le_of_lt h) ≫ eqToHom B :=
  dif_pos h

/- English proof (authored)
At or after the upper join the definition takes the comparison of the second sequences at the difference between the stage index and the upper first length. Replace that difference by the equal given offset. The corresponding endpoint identifications give the stated composite.
-/
private theorem concatMap_eq_upperConcatMap_of_le (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j q : ℕ)
    (hj : j ≤ s'.length + t'.length) (hge : s'.length ≤ j) (hjq : j - s'.length = q)
    (hq : q ≤ t'.length)
    (E1 : (s'.append t').obj j = (s'.append t').obj (s'.length + q))
    (E2 : (s.append t).obj (s.length + e.idx q) =
      (s.append t).obj (concatIndex s t s' t' c e j)) :
    concatMap s t s' t' c e j hj =
      eqToHom E1 ≫ appendMapAdd s t s' t' c e q hq ≫ eqToHom E2 := by
  have h0 : concatMap s t s' t' c e j hj =
      eqToHom (append_schemeAt_eq_length_add_sub s' t' j hge) ≫
        appendMapAdd s t s' t' c e (j - s'.length) (sub_length_le_of_le_length_add s' t' j hj) ≫
        eqToHom (append_schemeAt_concatIndex_of_le s t s' t' c e j hge) := dif_neg (not_lt.2 hge)
  exact h0.trans (upperConcatMap_congr s t s' t' c e hjq (sub_length_le_of_le_length_add s' t' j hj) hq
    (append_schemeAt_eq_length_add_sub s' t' j hge) (append_schemeAt_concatIndex_of_le s t s' t' c e j hge) E1 E2)

/- English proof (authored)
If both upper stages precede the join, their lower matches lie in the lower first sequence. Identify the appended maps with those of the first comparison and apply its step equation. If the second upper stage is the join, its second-sequence comparison starts at offset zero. Split the lower transition at the lower join, and use the stage-zero square of the second comparison to replace the initial second-sequence composite by the last map of the first comparison. The upper initial isomorphism cancels its inverse, reducing the result to the last step equation of the first comparison. If both upper stages are at or after the join, write their offsets as consecutive integers. The stage isomorphisms carry the blowup and the lower transition to those in the second sequences. The step equation of the second comparison then gives the desired equality.
-/
private theorem blowupMorphism_comp_concatMap (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ)
    (hj : j < s'.length + t'.length)
    (hd : concatIndex s t s' t' c e j ≤ concatIndex s t s' t' c e (j + 1)) :
    (s'.append t').map j ≫ concatMap s t s' t' c e j (le_of_lt hj) =
      concatMap s t s' t' c e (j + 1) hj ≫ (s.append t).transitionMap hd := by
  by_cases hlt : j < s'.length
  · by_cases h1 : j + 1 < s'.length
    · have hcj : c.idx j < s.length := c.blowupSequenceData_index_lt_length j hlt
      have hc1 : c.idx (j + 1) < s.length := c.blowupSequenceData_index_lt_length (j + 1) h1
      have hmono : c.idx j ≤ c.idx (j + 1) := le_of_lt (c.blowupSequenceData_index_lt_index_succ j hlt)
      rw [BlowupSequenceData.append_blowupMorphism_of_lt_length s' t' hlt,
        concatMap_eq_lowerMap_of_lt s t s' t' c e j (le_of_lt hj) hlt
          (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt hlt))
          (append_schemeAt_concatIndex_of_lt s t s' t' c e j hlt),
        concatMap_eq_lowerMap_of_lt s t s' t' c e (j + 1) hj h1
          (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h1))
          (append_schemeAt_concatIndex_of_lt s t s' t' c e (j + 1) h1),
        transitionMap_congr (s.append t) (concatIndex_of_lt s t s' t' c e j hlt)
          (concatIndex_of_lt s t s' t' c e (j + 1) h1) hd hmono
          (congrArg (s.append t).obj (concatIndex_of_lt s t s' t' c e (j + 1) h1))
          (congrArg (s.append t).obj (concatIndex_of_lt s t s' t' c e j hlt)).symm,
        append_transitionMap_of_le_length s t hmono (le_of_lt hc1)]
      simp [blowupMorphism_comp_lowerMap_assoc c j hlt]
    · have hjn : j + 1 = s'.length := by omega
      have hcj : c.idx j < s.length := c.blowupSequenceData_index_lt_length j hlt
      have hidxlen' : c.idx s'.length = s.length := c.index_length_eq_length
      have hidxlen : c.idx (j + 1) = s.length := by rw [hjn]; exact hidxlen'
      have hidx0 : concatIndex s t s' t' c e j = c.idx j := concatIndex_of_lt s t s' t' c e j hlt
      have hidx1 : concatIndex s t s' t' c e (j + 1) = s.length + e.idx 0 := by
        rw [concatIndex_of_ge s t s' t' c e (j + 1) (le_of_eq hjn.symm),
          show j + 1 - s'.length = 0 by omega]
      have hdle : c.idx j ≤ s.length + e.idx 0 :=
        le_trans (le_of_lt hcj) (Nat.le_add_right _ _)
      rw [BlowupSequenceData.append_blowupMorphism_of_lt_length s' t' hlt,
        concatMap_eq_lowerMap_of_lt s t s' t' c e j (le_of_lt hj) hlt
          (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt hlt))
          (append_schemeAt_concatIndex_of_lt s t s' t' c e j hlt),
        concatMap_eq_upperConcatMap_of_le s t s' t' c e (j + 1) 0 hj (le_of_eq hjn.symm)
          (show j + 1 - s'.length = 0 by omega) (Nat.zero_le _)
          (congrArg (s'.append t').obj (show j + 1 = s'.length + 0 by omega))
          (congrArg (s.append t).obj hidx1.symm),
        transitionMap_congr (s.append t) hidx0 hidx1 hd hdle
          (congrArg (s.append t).obj hidx1)
          (congrArg (s.append t).obj hidx0).symm]
      simp only [appendMapAdd, concatObjAddIso_zero_hom, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]
      rw [concatObjAddIso_inv_comp_transitionMap_of_le_length_assoc s t (le_of_lt hcj) hdle, upperMap_zero_comp_isoObjZero_assoc e,
        blowupMorphism_comp_lowerMap_assoc c j hlt,
        lowerMap_congr c hjn hlt le_rfl (congrArg s'.obj hjn)
          (congrArg (fun n => s.obj (c.idx n)) hjn.symm),
        transitionMap_congr s (rfl : c.idx j = c.idx j) hidxlen
          (le_of_lt (c.blowupSequenceData_index_lt_index_succ j hlt)) (le_of_lt hcj)
          (congrArg s.obj hidxlen) rfl,
        lastMap_eq_lowerMap c (congrArg s.obj hidxlen')]
      simp
      all_goals exact comp_assoc_inner_pair _ _ _ _ _
  · have hge : s'.length ≤ j := not_lt.1 hlt
    obtain ⟨q, rfl⟩ : ∃ q, j = s'.length + q := ⟨j - s'.length, by omega⟩
    have hq1 : q < t'.length := by omega
    have hmono : e.idx q < e.idx (q + 1) := e.blowupSequenceData_index_lt_index_succ q hq1
    have hidxj : concatIndex s t s' t' c e (s'.length + q) = s.length + e.idx q := by
      rw [concatIndex_of_ge s t s' t' c e (s'.length + q) (Nat.le_add_right _ _),
        show s'.length + q - s'.length = q by omega]
    have hidxj1 : concatIndex s t s' t' c e (s'.length + q + 1) = s.length + e.idx (q + 1) := by
      rw [concatIndex_of_ge s t s' t' c e (s'.length + q + 1) (by omega),
        show s'.length + q + 1 - s'.length = q + 1 by omega]
    rw [concatMap_eq_upperConcatMap_of_le s t s' t' c e (s'.length + q) q (le_of_lt hj)
        (Nat.le_add_right _ _)
        (show s'.length + q - s'.length = q by omega) (le_of_lt hq1) rfl
        (congrArg (s.append t).obj hidxj.symm),
      concatMap_eq_upperConcatMap_of_le s t s' t' c e (s'.length + q + 1) (q + 1) hj (by omega)
        (show s'.length + q + 1 - s'.length = q + 1 by omega) hq1 rfl
        (congrArg (s.append t).obj hidxj1.symm),
      transitionMap_congr (s.append t) hidxj hidxj1 hd
        (show s.length + e.idx q ≤ s.length + e.idx (q + 1) by omega)
        (congrArg (s.append t).obj hidxj1) (congrArg (s.append t).obj hidxj).symm]
    simp only [appendMapAdd, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [BlowupSequenceData.append_blowupMorphism_comp_concatObjAddIso_assoc, blowupMorphism_comp_upperMap_assoc e q hq1,
      concatObjAddIso_inv_comp_transitionMap_assoc s t (le_of_lt hmono)]

/- English proof (authored)
The reconstructed upper sequence uses the stored appended morphism for the step. The lower transition is the one in the data at the given matched indices. Apply the appended step equation on the data.
-/
private theorem toSequenceOfBlowups_blowupMorphism_comp_concatMap (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ)
    (hj : j < s'.length + t'.length) :
    (s'.append t').toSequenceOfBlowups.transitionMapSucc j ≫ concatMap s t s' t' c e j (le_of_lt hj) =
      concatMap s t s' t' c e (j + 1) hj ≫
        (s.append t).toSequenceOfBlowups.transitionMap (le_of_lt (concatIndex_lt_concatIndex_succ s t s' t' c e j hj)) := by
  rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism]
  exact blowupMorphism_comp_concatMap s t s' t' c e j hj _

/- English proof (authored)
Reassociate so that the inverse isomorphism and its forward morphism are adjacent. Their composite is the identity, leaving the first two morphisms.
-/
private theorem comp_comp_inv_comp_hom {A B C D : Scheme.{u}} (g : A ⟶ B) (m : B ⟶ C) (ι : D ≅ C) :
    (g ≫ m ≫ ι.inv) ≫ ι.hom = g ≫ m := by
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/- English proof (authored)
Identify the last two schemes using their equality. The two changes of identification are inverse and compose to the identity, leaving the first two morphisms.
-/
private theorem comp_comp_eqToHom_comp_eqToHom {A B C D : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ C)
    (h1 : C = D) (h2 : D = C) :
    (g ≫ f ≫ eqToHom h1) ≫ eqToHom h2 = g ≫ f := by
  subst h1
  simp only [eqToHom_refl, Category.comp_id]

/- English proof (authored)
The appended comparison at the given offset is formed by the upper stage isomorphism, the second-sequence comparison and the inverse lower stage isomorphism. Postcomposing with the lower stage isomorphism cancels its inverse, leaving the first two maps.
-/
private theorem concatMapAddLength_comp_concatObjAddIso_hom (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (i : ℕ) (hi : i ≤ t'.length) :
    concatMapAddLength s t s' t' c e i hi ≫ (BlowupSequenceData.concatObjAddIso s t (e.idx i)).hom =
      (BlowupSequenceData.concatObjAddIso s' t' i).hom ≫ e.map i hi :=
  comp_comp_inv_comp_hom (BlowupSequenceData.concatObjAddIso s' t' i).hom (e.map i hi)
    (BlowupSequenceData.concatObjAddIso s t (e.idx i))

/- English proof (authored)
Substitute the equality of indices. The centers are then the same ideal sheaf, and the morphisms for the two scheme identifications coincide. The two pullbacks agree.
-/
private theorem center_comap_eqToHom_congr {Y : Scheme.{u}} (d : BlowupSequenceData Y) {a b : ℕ}
    (hab : a = b) {W : Scheme.{u}} (hW : W = d.obj a) (hW' : W = d.obj b) :
    (d.center a).comap (eqToHom hW) = (d.center b).comap (eqToHom hW') := by
  subst hab
  rfl

/- English proof (authored)
Identify the two center indices. The ideals and their final scheme identification morphisms coincide. The preceding maps are the same, so the pullback ideals agree.
-/
private theorem center_comap_comp_eqToHom_congr {Y : Scheme.{u}} (d : BlowupSequenceData Y) {a b : ℕ}
    (hab : a = b) {Z Z' W : Scheme.{u}} (p : Z ⟶ Z') (f : Z' ⟶ W)
    (hW : W = d.obj a) (hW' : W = d.obj b) :
    (d.center a).comap (p ≫ f ≫ eqToHom hW) = (d.center b).comap (p ≫ f ≫ eqToHom hW') := by
  subst hab
  rfl

/- English proof (authored)
After identifying the indices the final identification morphism is the identity. Composing with it leaves the original morphism and the same ideal to pull back.
-/
private theorem center_comap_comp_eqToHom {Y : Scheme.{u}} (d : BlowupSequenceData Y) {a b : ℕ}
    (hab : b = a) {Z : Scheme.{u}} (v : Z ⟶ d.obj b) (q : d.obj b = d.obj a) :
    (d.center a).comap (v ≫ eqToHom q) = (d.center b).comap v := by
  subst hab
  simp

/- English proof (authored)
At the join the appended center is obtained from the first center of the second sequence via the inverse initial isomorphism and the identification of the joining scheme. Functoriality of ideal pullback makes this the pullback along the stage comparison. At any positive offset the appended center is the center of the second sequence at the index obtained by subtracting the first length, pulled back along the stage identification. This index is exactly the positive offset.
-/
private theorem append_center_length_add (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (n : ℕ) :
    (s.append t).center (s.length + n) =
      (t.center n).comap (BlowupSequenceData.concatObjAddIso s t n).hom := by
  cases n with
  | zero =>
    refine Eq.trans (BlowupSequenceData.append_center_length s t) ?_
    exact (Scheme.IdealSheafData.comap_comp (t.center 0)
      (eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t (le_refl s.length))) t.isoZero.inv).symm
  | succ k =>
    have hlt : s.length < s.length + (k + 1) := by omega
    have hsub : s.length + (k + 1) - s.length = k + 1 := by omega
    refine Eq.trans (BlowupSequenceData.append_center_of_length_lt s t hlt) ?_
    exact center_comap_eqToHom_congr t hsub (BlowupSequenceData.append_schemeAt_of_length_lt s t hlt)
      (BlowupSequenceData.append_schemeAt_length_add_succ s t k)

/- English proof (authored)
Replace the two offsets by their common value. The source identification becomes the identity, and the two comparisons and their target identifications coincide.
-/
private theorem concatMapAddLength_congr (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) {a b : ℕ} (hab : a = b)
    (ha : a ≤ t'.length) (hb : b ≤ t'.length) {W : Scheme.{u}}
    (h1 : (s'.append t').obj (s'.length + b) = (s'.append t').obj (s'.length + a))
    (h2 : (s.append t).obj (s.length + e.idx a) = W)
    (h2' : (s.append t).obj (s.length + e.idx b) = W) :
    eqToHom h1 ≫ concatMapAddLength s t s' t' c e a ha ≫ eqToHom h2 =
      concatMapAddLength s t s' t' c e b hb ≫ eqToHom h2' := by
  subst hab
  rw [eqToHom_refl, Category.id_comp]

/- English proof (authored)
Before the upper join the comparison is obtained by identifying the source with the upper first stage, using the first comparison, and identifying the lower first stage with its stage in the append. This is the first branch of the comparison.
-/
private theorem concatMap_eq_map_of_lt (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ)
    (hj : j ≤ s'.length + t'.length) (h : j < s'.length) :
    concatMap s t s' t' c e j hj =
      eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h)) ≫ c.map j (le_of_lt h) ≫
        eqToHom (append_schemeAt_concatIndex_of_lt s t s' t' c e j h) := dif_pos h

/- English proof (authored)
Before the upper join, both centers are transported from the first sequences. Pull the lower center back along the appended comparison and cancel the inverse identifications of the lower stages. The first comparison gives the upper first-sequence center, and the remaining upper identification gives the appended center. At or beyond the join, express each center as the pullback of its second-sequence center along the stage isomorphism. The appended comparison followed by the lower stage isomorphism is the upper stage isomorphism followed by the second comparison. Thus the second comparison's center equation and functoriality of pullback give the appended center equation.
-/
private theorem append_center_eq_comap_concatMap (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ)
    (hj : j < s'.length + t'.length) :
    (s'.append t').toSequenceOfBlowups.center j =
      ((s.append t).toSequenceOfBlowups.center (concatIndex s t s' t' c e j)).comap
        (concatMap s t s' t' c e j (le_of_lt hj)) := by
  show (s'.append t').center j =
      ((s.append t).center (concatIndex s t s' t' c e j)).comap
        (concatMap s t s' t' c e j (le_of_lt hj))
  by_cases h : j < s'.length
  · have hci : c.idx j < s.length := c.blowupSequenceData_index_lt_length j h
    have hidxA : concatIndex s t s' t' c e j = c.idx j := concatIndex_of_lt s t s' t' c e j h
    have hc : s'.center j = (s.center (c.idx j)).comap (c.map j (le_of_lt h)) :=
      c.center_comap j (by rw [BlowupSequenceData.toSequenceOfBlowups_length]; exact h)
    have hmA : (eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h)) ≫ c.map j (le_of_lt h) ≫
          eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t (le_of_lt hci)).symm) ≫
          eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t (le_of_lt hci)) =
        eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h)) ≫ c.map j (le_of_lt h) :=
      comp_comp_eqToHom_comp_eqToHom _ _ _ _
    rw [concatMap_eq_map_of_lt s t s' t' c e j (le_of_lt hj) h,
      center_comap_comp_eqToHom_congr (s.append t) hidxA
        (eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h))) (c.map j (le_of_lt h))
        (append_schemeAt_concatIndex_of_lt s t s' t' c e j h)
        (BlowupSequenceData.append_schemeAt_of_le_length s t (le_of_lt hci)).symm,
      BlowupSequenceData.append_center_of_lt_length s t hci, ← Scheme.IdealSheafData.comap_comp, hmA,
      BlowupSequenceData.append_center_of_lt_length s' t' h, hc]
    exact (Scheme.IdealSheafData.comap_comp _ _ _).symm
  · have hge : s'.length ≤ j := not_lt.1 h
    obtain ⟨i, rfl⟩ : ∃ i, j = s'.length + i := ⟨j - s'.length, by omega⟩
    have hit : i < t'.length := by omega
    have hile : i ≤ t'.length := le_of_lt hit
    have hsub : s'.length + i - s'.length = i := by omega
    have hidx : concatIndex s t s' t' c e (s'.length + i) = s.length + e.idx i := by
      rw [concatIndex_of_ge s t s' t' c e (s'.length + i) hge, hsub]
    have hmapGe : concatMap s t s' t' c e (s'.length + i) (le_of_lt hj) =
        eqToHom (append_schemeAt_eq_length_add_sub s' t' (s'.length + i) hge) ≫
          concatMapAddLength s t s' t' c e (s'.length + i - s'.length)
            (sub_length_le_of_le_length_add s' t' (s'.length + i) (le_of_lt hj)) ≫
          eqToHom (append_schemeAt_concatIndex_of_le s t s' t' c e (s'.length + i) hge) :=
      dif_neg (not_lt.2 hge)
    have hshift := concatMapAddLength_congr s t s' t' c e hsub
      (sub_length_le_of_le_length_add s' t' (s'.length + i) (le_of_lt hj)) hile
      (append_schemeAt_eq_length_add_sub s' t' (s'.length + i) hge)
      (append_schemeAt_concatIndex_of_le s t s' t' c e (s'.length + i) hge)
      (congrArg (s.append t).obj hidx.symm)
    have hmor : concatMapAddLength s t s' t' c e i hile ≫ (BlowupSequenceData.concatObjAddIso s t (e.idx i)).hom =
        (BlowupSequenceData.concatObjAddIso s' t' i).hom ≫ e.map i hile :=
      concatMapAddLength_comp_concatObjAddIso_hom s t s' t' c e i hile
    have hcen : t'.center i = (t.center (e.idx i)).comap (e.map i hile) :=
      e.center_comap i (by rw [BlowupSequenceData.toSequenceOfBlowups_length]; exact hit)
    rw [hmapGe, hshift,
      center_comap_comp_eqToHom (s.append t) hidx.symm (concatMapAddLength s t s' t' c e i hile)
        (congrArg (s.append t).obj hidx.symm),
      append_center_length_add s t (e.idx i), ← Scheme.IdealSheafData.comap_comp, hmor,
      append_center_length_add s' t' i, hcen]
    exact (Scheme.IdealSheafData.comap_comp _ _ _).symm

/- English proof (authored)
Choose a point of the support of the proper ideal. The inverse isomorphism gives a point upstairs whose image is the chosen point. The support of a pulled-back ideal is the inverse image of the support, so this point lies in the support upstairs. The pulled-back ideal is therefore proper.
-/
private theorem comap_iso_hom_ne_top {Y Z : Scheme.{u}} (g : Y ≅ Z) (J : Z.IdealSheafData)
    (hJ : J ≠ ⊤) : J.comap g.hom ≠ ⊤ := by
  obtain ⟨x, hx⟩ := exists_mem_support_of_ne_top J hJ
  have h1 : (g.inv ≫ g.hom).base x ∈ J.support := by
    rw [g.inv_hom_id]
    simpa using hx
  have h2 : g.hom.base (g.inv.base x) ∈ J.support := by simpa using h1
  exact AlgebraicGeometry.Scheme.IdealSheafData.ne_top_of_mem_support (J.comap g.hom)
    (g.inv.base x) (AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.mpr h2)

/- English proof (authored)
Equality of the schemes gives an isomorphism whose forward map is the stated identification. Pullback along an isomorphism preserves nonempty support and hence preserves a proper ideal.
-/
private theorem comap_eqToHom_ne_top {Y Z : Scheme.{u}} (h : Y = Z) (J : Z.IdealSheafData)
    (hJ : J ≠ ⊤) : J.comap (eqToHom h) ≠ ⊤ :=
  comap_iso_hom_ne_top (eqToIso h) J hJ

/- English proof (authored)
Before the upper join the center is transported from the upper first sequence, where it is proper by the first comparison. At the join, the given bound guarantees the second sequence has a first blowup. Its center is proper by the second comparison, and the appended center is its pullback along the inverse initial isomorphism and the scheme identification. After the join the center comes from the corresponding positive offset of the second sequence, again proper by the second comparison. Each transport is an isomorphism, so all these centers remain proper.
-/
private theorem append_center_ne_top (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ)
    (hj : j < s'.length + t'.length) : (s'.append t').toSequenceOfBlowups.center j ≠ ⊤ := by
  show (s'.append t').center j ≠ ⊤
  rcases lt_trichotomy j s'.length with h | h | h
  · have hne : s'.center j ≠ ⊤ :=
      c.center_ne_top j (by rw [BlowupSequenceData.toSequenceOfBlowups_length]; exact h)
    rw [BlowupSequenceData.append_center_of_lt_length s' t' h]
    exact comap_eqToHom_ne_top _ _ hne
  · subst h
    have ht : 0 < t'.length := by omega
    have h0 : t'.center 0 ≠ ⊤ :=
      e.center_ne_top 0 (by rw [BlowupSequenceData.toSequenceOfBlowups_length]; exact ht)
    have h2' : (t'.center 0).comap t'.isoZero.inv ≠ ⊤ :=
      comap_iso_hom_ne_top t'.isoZero.symm (t'.center 0) h0
    rw [BlowupSequenceData.append_center_length s' t']
    exact comap_eqToHom_ne_top _ _ h2'
  · have hsub : j - s'.length < t'.length := by omega
    have hne : t'.center (j - s'.length) ≠ ⊤ :=
      e.center_ne_top (j - s'.length) (by rw [BlowupSequenceData.toSequenceOfBlowups_length]; exact hsub)
    rw [BlowupSequenceData.append_center_of_length_lt s' t' h]
    exact comap_eqToHom_ne_top _ _ hne

/- English proof (authored)
Two points with the same image have a lift to the canonical scheme pullback with those projections. Carry this lift to the given pullback by the inverse of the canonical isomorphism. This inverse intertwines the given first projection with the canonical first projection, so the resulting point projects to the required point.
-/
private theorem exists_preimage_of_isPullback {A A' Z Z' : Scheme.{u}} {p : A' ⟶ A} {q : A' ⟶ Z'}
    {f : A ⟶ Z} {g : Z' ⟶ Z} (h : IsPullback p q f g) (a : ↥A) (b : ↥Z')
    (hab : f.base a = g.base b) : ∃ a' : ↥A', p.base a' = a := by
  obtain ⟨w, hw1, _hw2⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback a b hab
  refine ⟨h.isoPullback.inv.base w, ?_⟩
  have h2 : h.isoPullback.hom ≫ pullback.fst f g = p := h.isoPullback_hom_fst
  have key : h.isoPullback.inv ≫ p = pullback.fst f g := by
    calc h.isoPullback.inv ≫ p
        = h.isoPullback.inv ≫ h.isoPullback.hom ≫ pullback.fst f g := by rw [h2]
      _ = pullback.fst f g := by rw [Iso.inv_hom_id_assoc]
  calc p.base (h.isoPullback.inv.base w)
      = (h.isoPullback.inv ≫ p).base w := rfl
    _ = (pullback.fst f g).base w := by rw [key]
    _ = a := hw1

/- English proof (authored)
The reconstructed sequence retains the ideal of the center at every index. Its support is therefore the same set, and the given point belongs to it.
-/
private theorem mem_toSequenceOfBlowups_center_support {Y : Scheme.{u}} (d : BlowupSequenceData Y) (i : ℕ)
    (w : ↥(d.toSequenceOfBlowups.schemeAt i)) (hw : w ∈ (d.center i).support) :
    w ∈ (d.toSequenceOfBlowups.center i).support := by
  rw [BlowupSequenceData.toSequenceOfBlowups_center]
  exact hw

/- English proof (authored)
Adding zero leaves the index equal to the length. The two changes of scheme identification and the two projections therefore agree.
-/
private theorem eqToHom_comp_projectionToBase_length_add_zero {Y : Scheme.{u}} (s : BlowupSequenceData Y)
    (t : BlowupSequenceData (s.obj s.length))
    (h1 : (s.append t).obj (s.length + 0) = s.obj (s.length + 0))
    (h2 : (s.append t).obj (s.length + 0) = s.obj s.length) :
    eqToHom h1 ≫ s.projectionToBase (s.length + 0) = eqToHom h2 ≫ s.projectionToBase s.length := rfl

/- English proof (authored)
At offset zero, the projection is the projection of the last stage of the first sequence under the scheme identification. In the proposed factorization the inverse initial isomorphism of the second sequence cancels its stage-zero projection, giving this same map. For a successor offset, factor through the preceding appended stage by its blowup. Substitute the induction formula and use the adjacent-stage comparison to move that blowup into the second sequence. There the blowup followed by the preceding projection is exactly the successor projection.
-/
private theorem projectionToBase_append_length_add {Y : Scheme.{u}} (s : BlowupSequenceData Y)
    (t : BlowupSequenceData (s.obj s.length)) (n : ℕ) :
    (s.append t).projectionToBase (s.length + n) =
      (BlowupSequenceData.concatObjAddIso s t n).hom ≫ t.projectionToBase n ≫ s.projectionToBase s.length := by
  induction n with
  | zero =>
      have hA : (BlowupSequenceData.concatObjAddIso s t 0).hom ≫ t.projectionToBase 0 ≫ s.projectionToBase s.length =
          eqToHom (BlowupSequenceData.append_schemeAt_length_add_zero s t) ≫ s.projectionToBase s.length := by
        rw [concatObjAddIso_zero_hom, BlowupSequenceData.projectionToBase_zero, Category.assoc, Iso.inv_hom_id_assoc]
      exact ((BlowupSequenceData.projectionToBase_append_of_le_length s t (le_of_eq (Nat.add_zero s.length))).trans
        (eqToHom_comp_projectionToBase_length_add_zero s t _ _)).trans hA.symm
  | succ n ih =>
      have hs : (s.append t).projectionToBase (s.length + (n + 1)) =
          (s.append t).map (s.length + n) ≫ (s.append t).projectionToBase (s.length + n) :=
        BlowupSequenceData.projectionToBase_succ (s.append t) (s.length + n)
      rw [hs, ih, BlowupSequenceData.append_blowupMorphism_comp_concatObjAddIso_assoc, ← Category.assoc (t.map n),
        ← BlowupSequenceData.projectionToBase_succ]

/- English proof (authored)
Suppose a point on an omitted lower center projects to the image of an upper base point. Before the lower join, identify the center and projection with those of the first sequence. A first-sequence match would also be an appended match, so the omission condition for the first comparison excludes this common image. At or after the lower join, use the lower stage isomorphism to take the center point to the corresponding center in the second sequence. Its projection to the lower joining scheme and the upper base point have the same image in the lower base by the projection factorization. The last-stage pullback square of the first comparison lifts them to a point of the upper joining scheme. The offset of the lower center is omitted in the second comparison, since a match at any upper second offset would give an appended match. The lifted point and the lower center point now contradict the omission condition for the second comparison.
-/
private theorem append_projectionToBase_ne_of_forall_concatIndex_ne (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (i : ℕ)
    (hi : i < s.length + t.length)
    (hmiss : ∀ j : ℕ, j < s'.length + t'.length → concatIndex s t s' t' c e j ≠ i)
    (z : ↥((s.append t).toSequenceOfBlowups.schemeAt i)) (hz : z ∈ ((s.append t).toSequenceOfBlowups.center i).support)
    (x' : ↥X') :
    φ.base x' ≠ ((s.append t).toSequenceOfBlowups.projectionToBase i).base z := by
  intro heq
  have hzc : z ∈ ((s.append t).center i).support := by
    rw [BlowupSequenceData.toSequenceOfBlowups_center] at hz
    exact hz
  have heqp : φ.base x' = ((s.append t).projectionToBase i).base z :=
    heq.trans (congrArg (fun m : (s.append t).toSequenceOfBlowups.schemeAt i ⟶ X => m.base z)
      (BlowupSequenceData.toSequenceOfBlowups_projectionToBase (s.append t) i))
  by_cases hlt : i < s.length
  · have hobj : (s.append t).obj i = s.obj i := BlowupSequenceData.append_schemeAt_of_le_length s t (le_of_lt hlt)
    rw [BlowupSequenceData.append_center_of_lt_length s t hlt] at hzc
    have hzs : (eqToHom hobj).base z ∈ (s.center i).support :=
      Scheme.IdealSheafData.mem_support_comap.mp hzc
    have heq2 : φ.base x' = (s.projectionToBase i).base ((eqToHom hobj).base z) :=
      (heqp.trans (congrArg (fun m : (s.append t).obj i ⟶ X => m.base z)
          (BlowupSequenceData.projectionToBase_append_of_le_length s t (le_of_lt hlt)))).trans rfl
    refine c.omitted i ?_ ?_ ((eqToHom hobj).base z) ?_ x' ?_
    · rw [BlowupSequenceData.toSequenceOfBlowups_length]
      exact hlt
    · intro j hj hji
      rw [BlowupSequenceData.toSequenceOfBlowups_length] at hj
      exact hmiss j (by omega) ((concatIndex_of_lt s t s' t' c e j hj).trans hji)
    · exact mem_toSequenceOfBlowups_center_support s i _ hzs
    · exact heq2.trans (congrArg (fun m : s.obj i ⟶ X => m.base ((eqToHom hobj).base z))
        (BlowupSequenceData.toSequenceOfBlowups_projectionToBase s i)).symm
  · have hge : s.length ≤ i := not_lt.1 hlt
    obtain ⟨n, rfl⟩ : ∃ n, i = s.length + n := ⟨i - s.length, by omega⟩
    have hn : n < t.length := by omega
    rw [append_center_length_add s t n] at hzc
    have hzt : ((BlowupSequenceData.concatObjAddIso s t n).hom).base z ∈ (t.center n).support :=
      Scheme.IdealSheafData.mem_support_comap.mp hzc
    have heq2 : φ.base x' =
        (s.projectionToBase s.length).base ((t.projectionToBase n).base (((BlowupSequenceData.concatObjAddIso s t n).hom).base z)) :=
      (heqp.trans (congrArg (fun m : (s.append t).obj (s.length + n) ⟶ X => m.base z)
          (projectionToBase_append_length_add s t n))).trans rfl
    have hsm : (s.toSequenceOfBlowups.projectionToBase s.toSequenceOfBlowups.length).base
        ((t.projectionToBase n).base (((BlowupSequenceData.concatObjAddIso s t n).hom).base z)) = φ.base x' :=
      (congrArg (fun m : s.obj s.length ⟶ X =>
          m.base ((t.projectionToBase n).base (((BlowupSequenceData.concatObjAddIso s t n).hom).base z)))
        (BlowupSequenceData.toSequenceOfBlowups_projectionToBase s s.toSequenceOfBlowups.length)).trans heq2.symm
    obtain ⟨a', ha'⟩ := exists_preimage_of_isPullback c.isPullback_lastMap
      ((t.projectionToBase n).base (((BlowupSequenceData.concatObjAddIso s t n).hom).base z)) x' hsm
    refine e.omitted n ?_ ?_ (((BlowupSequenceData.concatObjAddIso s t n).hom).base z) ?_ a' ?_
    · rw [BlowupSequenceData.toSequenceOfBlowups_length]
      exact hn
    · intro m hm hmn
      rw [BlowupSequenceData.toSequenceOfBlowups_length] at hm
      refine hmiss (s'.length + m) (by omega) ?_
      rw [concatIndex_of_ge s t s' t' c e (s'.length + m) (Nat.le_add_right _ _),
        show s'.length + m - s'.length = m by omega, hmn]
    · exact mem_toSequenceOfBlowups_center_support t n _ hzt
    · exact ha'.trans (congrArg (fun m : t.obj n ⟶ s.obj s.length =>
        m.base (((BlowupSequenceData.concatObjAddIso s t n).hom).base z))
        (BlowupSequenceData.toSequenceOfBlowups_projectionToBase t n)).symm

def concat (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) :
    SequenceOfBlowupsPullback φ (s'.append t').toSequenceOfBlowups (s.append t).toSequenceOfBlowups where
  idx := concatIndex s t s' t' c e
  map := concatMap s t s' t' c e
  idx_length := concatIndex_length_add_length s t s' t' c e
  idx_lt := concatIndex_lt_length_add_length s t s' t' c e
  idx_strictMono := concatIndex_lt_concatIndex_succ s t s' t' c e
  isPullback := isPullback_concatMap s t s' t' c e
  step := toSequenceOfBlowups_blowupMorphism_comp_concatMap s t s' t' c e
  center_comap := append_center_eq_comap_concatMap s t s' t' c e
  center_ne_top := append_center_ne_top s t s' t' c e
  omitted := append_projectionToBase_ne_of_forall_concatIndex_ne s t s' t' c e

end

end SequenceOfBlowupsPullback

/- English proof (authored)
Use the given matching, and take each comparison to be the given stage isomorphism followed by the second pullback projection. The index conditions follow from the matching, and the first projection condition and the stage isomorphism give the required pullback squares. Postcomposing compatibility of the stage isomorphisms with the second projection gives the step equation, because the induced transition on pullbacks projects to the lower transition. The center equation is part of the given relation. Each matched lower center has nonempty support after pullback, and transporting that support across the stage isomorphism makes the corresponding upper center proper. Finally, a lower center point sharing its image with an upper base point would lift to a point of the canonical pullback in the support of the pulled-back center. The support criterion would then match this lower index, contrary to its omission.
-/
theorem IsPullbackBlowupSequence.nonempty_sequenceOfBlowupsPullback {X X' : Scheme.{u}} {φ : X' ⟶ X}
    {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (h : IsPullbackBlowupSequence φ s' s) :
    Nonempty (SequenceOfBlowupsPullback φ s' s) := by
  obtain ⟨idx, e, hlt, hmono, hlen, hsup, hfst, hstep, hcen⟩ := h
  refine ⟨{
    idx := idx
    map := fun j hj => (e j hj).hom ≫ pullback.snd φ (s.projectionToBase (idx j))
    idx_length := hlen
    idx_lt := hlt
    idx_strictMono := fun j hj => hmono j (j + 1) hj (Nat.lt_succ_self j)
    isPullback := ?_
    step := ?_
    center_comap := ?_
    center_ne_top := ?_
    omitted := ?_ }⟩
  · intro j hj
    have hp : IsPullback ((e j hj).hom ≫ pullback.snd φ (s.projectionToBase (idx j)))
        ((e j hj).hom ≫ pullback.fst φ (s.projectionToBase (idx j))) (s.projectionToBase (idx j)) φ :=
      SequenceOfBlowupsPullback.isPullback_iso_hom_comp (e j hj)
        (IsPullback.of_hasPullback φ (s.projectionToBase (idx j))).flip
    rw [hfst j hj] at hp
    exact hp
  · intro j hj
    have hr : idx j ≤ idx (j + 1) := le_of_lt (hmono j (j + 1) hj (Nat.lt_succ_self j))
    have hs2 : (s'.transitionMapSucc j ≫ (e j (le_of_lt hj)).hom) ≫
          pullback.snd φ (s.projectionToBase (idx j)) =
        ((e (j + 1) hj).hom ≫ s.pullbackTransitionMap φ hr) ≫ pullback.snd φ (s.projectionToBase (idx j)) :=
      congrArg (fun m => m ≫ pullback.snd φ (s.projectionToBase (idx j))) (hstep j hj hr)
    calc s'.transitionMapSucc j ≫ ((e j (le_of_lt hj)).hom ≫ pullback.snd φ (s.projectionToBase (idx j)))
        = (s'.transitionMapSucc j ≫ (e j (le_of_lt hj)).hom) ≫
            pullback.snd φ (s.projectionToBase (idx j)) := (Category.assoc _ _ _).symm
      _ = ((e (j + 1) hj).hom ≫ s.pullbackTransitionMap φ hr) ≫
            pullback.snd φ (s.projectionToBase (idx j)) := hs2
      _ = (e (j + 1) hj).hom ≫
            (s.pullbackTransitionMap φ hr ≫ pullback.snd φ (s.projectionToBase (idx j))) := Category.assoc _ _ _
      _ = (e (j + 1) hj).hom ≫
            (pullback.snd φ (s.projectionToBase (idx (j + 1))) ≫ s.transitionMap hr) := by
              rw [SequenceOfBlowups.pullbackTransitionMap_comp_snd]
      _ = ((e (j + 1) hj).hom ≫ pullback.snd φ (s.projectionToBase (idx (j + 1)))) ≫
            s.transitionMap hr := (Category.assoc _ _ _).symm
  · exact hcen
  · intro j hj htop
    obtain ⟨x, hx⟩ := (hsup (idx j) (hlt j hj)).mpr ⟨j, hj, rfl⟩
    refine AlgebraicGeometry.Scheme.IdealSheafData.ne_top_of_mem_support _ x hx ?_
    have h1 : (s.center (idx j)).comap
        ((e j (le_of_lt hj)).hom ≫ pullback.snd φ (s.projectionToBase (idx j))) = ⊤ :=
      (hcen j hj).symm.trans htop
    have h2 : ((s.center (idx j)).comap
          ((e j (le_of_lt hj)).hom ≫ pullback.snd φ (s.projectionToBase (idx j)))).comap
          (e j (le_of_lt hj)).inv =
        (⊤ : (s'.schemeAt j).IdealSheafData).comap (e j (le_of_lt hj)).inv := by
      rw [h1]
    rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id_assoc,
      AlgebraicGeometry.Scheme.IdealSheafData.comap_top] at h2
    exact h2
  · intro i hi hmiss z hz x' heq
    obtain ⟨w, _, hw2⟩ :=
      AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback x' z heq
    have hmem : w ∈ ((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support := by
      have hw : (pullback.snd φ (s.projectionToBase i)).base w ∈ (s.center i).support := by
        rw [hw2]
        exact hz
      exact AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.mpr hw
    obtain ⟨j, hj, hji⟩ := (hsup i hi).mp ⟨w, hmem⟩
    exact hmiss j hj hji

/- English proof (authored)
Forget the markings on both pairs of sequences. The underlying blowups of a marked append are the append of its underlying blowups. Compose the two given pullback comparisons by the append construction, which uses the last-stage comparison of the first pair as the base map for the second. The resulting stage data give the asserted pullback relation.
-/
theorem isPullbackBlowupSequence_append_same_field {k : Type u} [Field k] {X X' : Scheme.{u}} (φ : X' ⟶ X)
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData}
    {p' : X' ⟶ Spec (CommRingCat.of k)} {I' : X'.IdealSheafData} {m' : ℕ}
    {E' : List X'.IdealSheafData}
    (S : MarkedBlowupSequenceData p I m E)
    (T : MarkedBlowupSequenceData (S.proj S.toBlowupSequenceData.length ≫ p) (S.ideal S.toBlowupSequenceData.length) m
      (S.boundary S.toBlowupSequenceData.length))
    (S' : MarkedBlowupSequenceData p' I' m' E')
    (T' : MarkedBlowupSequenceData (S'.proj S'.toBlowupSequenceData.length ≫ p') (S'.ideal S'.toBlowupSequenceData.length)
      m' (S'.boundary S'.toBlowupSequenceData.length))
    (hinv : ComapIsoInvariance.{u})
    (c : SequenceOfBlowupsPullback φ S'.toBlowupSequenceData.toSequenceOfBlowups S.toBlowupSequenceData.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap T'.toBlowupSequenceData.toSequenceOfBlowups T.toBlowupSequenceData.toSequenceOfBlowups) :
    IsPullbackBlowupSequence φ (S'.append T' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have C : SequenceOfBlowupsPullback φ (S'.toBlowupSequenceData.append T'.toBlowupSequenceData).toSequenceOfBlowups
      (S.toBlowupSequenceData.append T.toBlowupSequenceData).toSequenceOfBlowups :=
    SequenceOfBlowupsPullback.concat S.toBlowupSequenceData T.toBlowupSequenceData S'.toBlowupSequenceData T'.toBlowupSequenceData c e
  have h1 : (S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups =
      (S.toBlowupSequenceData.append T.toBlowupSequenceData).toSequenceOfBlowups :=
    MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups (S.append T hinv)
  have h2 : (S'.append T' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups =
      (S'.toBlowupSequenceData.append T'.toBlowupSequenceData).toSequenceOfBlowups :=
    MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups (S'.append T' hinv)
  rw [h1, h2]
  exact C.isPullbackSequenceOfBlowups

/- English proof (authored)
For each field, passing from a marked append to its unmarked blowups gives the append of the unmarked factors. The concatenation of the two comparisons is a construction on these unmarked schemes and morphisms over the given base map, so it applies with either field for the markings. Passing from its comparison data to the pullback relation proves the result.
-/
theorem isPullbackBlowupSequence_append_of_two_fields {k k' : Type u} [Field k] [Field k']
    {X X' : Scheme.{u}} (φ : X' ⟶ X)
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData}
    {p' : X' ⟶ Spec (CommRingCat.of k')} {I' : X'.IdealSheafData} {m' : ℕ}
    {E' : List X'.IdealSheafData}
    (S : MarkedBlowupSequenceData p I m E)
    (T : MarkedBlowupSequenceData (S.proj S.toBlowupSequenceData.length ≫ p) (S.ideal S.toBlowupSequenceData.length) m
      (S.boundary S.toBlowupSequenceData.length))
    (S' : MarkedBlowupSequenceData p' I' m' E')
    (T' : MarkedBlowupSequenceData (S'.proj S'.toBlowupSequenceData.length ≫ p') (S'.ideal S'.toBlowupSequenceData.length)
      m' (S'.boundary S'.toBlowupSequenceData.length))
    (hinv : ComapIsoInvariance.{u})
    (c : SequenceOfBlowupsPullback φ S'.toBlowupSequenceData.toSequenceOfBlowups S.toBlowupSequenceData.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap T'.toBlowupSequenceData.toSequenceOfBlowups T.toBlowupSequenceData.toSequenceOfBlowups) :
    IsPullbackBlowupSequence φ (S'.append T' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have C : SequenceOfBlowupsPullback φ (S'.toBlowupSequenceData.append T'.toBlowupSequenceData).toSequenceOfBlowups
      (S.toBlowupSequenceData.append T.toBlowupSequenceData).toSequenceOfBlowups :=
    SequenceOfBlowupsPullback.concat S.toBlowupSequenceData T.toBlowupSequenceData S'.toBlowupSequenceData T'.toBlowupSequenceData c e
  have h1 : (S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups =
      (S.toBlowupSequenceData.append T.toBlowupSequenceData).toSequenceOfBlowups :=
    MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups (S.append T hinv)
  have h2 : (S'.append T' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups =
      (S'.toBlowupSequenceData.append T'.toBlowupSequenceData).toSequenceOfBlowups :=
    MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups (S'.append T' hinv)
  rw [h1, h2]
  exact C.isPullbackSequenceOfBlowups

end FunctorialResolution.EmbeddedResolution

end
