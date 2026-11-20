import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
At stage zero compatibility with the projection is the initial compatibility. At a successor factor each projection through the preceding stage, use the commuting transition square, and apply the preceding projection equality. Induction proves compatibility with all projections.
-/
private theorem iso_hom_comp_projectionToBase {X' : Scheme.{u}} {s' s'' : SequenceOfBlowups X'}
    (ε : ∀ i : ℕ, i ≤ s'.length → (s'.schemeAt i ≅ s''.schemeAt i))
    (h0 : (ε 0 (Nat.zero_le _)).hom ≫ s''.isoZero.hom = s'.isoZero.hom)
    (hst : ∀ i : ℕ, ∀ hi : i < s'.length,
      (ε (i + 1) hi).hom ≫ s''.transitionMapSucc i = s'.transitionMapSucc i ≫ (ε i hi.le).hom) :
    ∀ i : ℕ, ∀ hi : i ≤ s'.length, (ε i hi).hom ≫ s''.projectionToBase i = s'.projectionToBase i := by
  intro i
  induction i with
  | zero =>
    intro hi
    rw [s''.projectionToBase_zero, s'.projectionToBase_zero]
    exact h0
  | succ n ih =>
    intro hi
    rw [s''.projectionToBase_succ n, s'.projectionToBase_succ n, ← Category.assoc,
      hst n hi, Category.assoc, ih (Nat.le_of_succ_le hi)]

private def pullbackProjectionToBaseIsoOfEq {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X) {a b : ℕ}
    (h : a = b) :
    Limits.pullback φ (s.projectionToBase a) ≅ Limits.pullback φ (s.projectionToBase b) :=
  eqToIso (by rw [h])

/- English proof (authored)
Identify the equal stage indices. The resulting pullbacks coincide and the comparison isomorphism is the identity, so it preserves the first projection.
-/
private theorem pullbackIsoOfEq_hom_fst {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X)
    {a b : ℕ} (h : a = b) :
    (pullbackProjectionToBaseIsoOfEq φ s h).hom ≫ Limits.pullback.fst φ (s.projectionToBase b)
      = Limits.pullback.fst φ (s.projectionToBase a) := by
  subst h
  simp [pullbackProjectionToBaseIsoOfEq]

/- English proof (authored)
Identify each pair of equal stage indices. The comparison isomorphisms become identities, and the two order proofs determine the same transition. Both sides reduce to that transition.
-/
private theorem pullbackIsoOfEq_hom_comp_pullbackTransitionMap {X X' : Scheme.{u}} (φ : X' ⟶ X)
    (s : SequenceOfBlowups X) {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (hab : a ≤ b) (hab' : a' ≤ b') :
    (pullbackProjectionToBaseIsoOfEq φ s hb).hom ≫ s.pullbackTransitionMap φ hab'
      = s.pullbackTransitionMap φ hab ≫ (pullbackProjectionToBaseIsoOfEq φ s ha).hom := by
  subst ha
  subst hb
  have hpr : hab = hab' := rfl
  subst hpr
  simp [pullbackProjectionToBaseIsoOfEq]

/- English proof (authored)
After identifying the stage indices, the centers and second projections coincide and the comparison isomorphism is the identity. Both sides pull back the same center along the same map.
-/
private theorem comap_pullbackIsoOfEq {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X) {a b : ℕ}
    (h : a = b) {W : Scheme.{u}} (g : W ⟶ Limits.pullback φ (s.projectionToBase a)) :
    (s.center b).comap (g ≫ (pullbackProjectionToBaseIsoOfEq φ s h).hom ≫ Limits.pullback.snd φ (s.projectionToBase b))
      = (s.center a).comap (g ≫ Limits.pullback.snd φ (s.projectionToBase a)) := by
  subst h
  simp [pullbackProjectionToBaseIsoOfEq]

/- English proof (authored)
Induct strongly on the common index. If the first value were greater than the second value, the second value would occur in the first enumeration at a strictly earlier index by strict growth and equality of the enumerated subsets. At that earlier index the induction hypothesis bounds the first value by the second enumeration’s value there. Strict growth of the second enumeration makes this earlier value smaller than its present value, a contradiction.
-/
private theorem strictMono_enumeration_le {n m L : ℕ} {r q : ℕ → ℕ} {P : ℕ → Prop}
    (hr2 : ∀ i j : ℕ, j ≤ n → i < j → r i < r j)
    (hq1 : ∀ i, i < m → q i < L)
    (hq2 : ∀ i j : ℕ, j ≤ m → i < j → q i < q j)
    (hr4 : ∀ i, i < L → (P i ↔ ∃ j, j < n ∧ r j = i))
    (hq4 : ∀ i, i < L → (P i ↔ ∃ j, j < m ∧ q j = i)) :
    ∀ i, i < n → i < m → r i ≤ q i := by
  have main : ∀ k i : ℕ, i < k → i < n → i < m → r i ≤ q i := by
    intro k
    induction k with
    | zero => intro i hik; exact absurd hik (Nat.not_lt_zero i)
    | succ k ih =>
      intro i hik hin him
      by_contra hcon
      push Not at hcon
      have hqL : q i < L := hq1 i him
      obtain ⟨j, hjn, hj⟩ := (hr4 (q i) hqL).mp ((hq4 (q i) hqL).mpr ⟨i, him, rfl⟩)
      have hji : j < i := by
        by_contra hc
        push Not at hc
        rcases Nat.eq_or_lt_of_le hc with h' | h'
        · rw [← h'] at hj
          omega
        · have hlt := hr2 i j hjn.le h'
          omega
      have h1 : r j ≤ q j := ih j (by omega) (by omega) (by omega)
      have h2 : q j < q i := hq2 j i him.le hji
      omega
  intro i hin him
  exact main (i + 1) i (Nat.lt_succ_self i) hin him

/- English proof (authored)
The comparison inequality in both directions makes the enumerations equal at every index before both endpoints. If the endpoints differed, the longer enumeration would have a value at the shorter endpoint that must occur at an earlier index of the shorter enumeration. Equality on earlier indices and strict growth would make it strictly smaller than itself. Thus the lengths agree. At their common final index both values equal the prescribed endpoint, giving full equality.
-/
private theorem strictMono_enumeration_unique {n m L : ℕ} {r q : ℕ → ℕ} {P : ℕ → Prop}
    (hr1 : ∀ i, i < n → r i < L)
    (hr2 : ∀ i j : ℕ, j ≤ n → i < j → r i < r j)
    (hrn : r n = L)
    (hr4 : ∀ i, i < L → (P i ↔ ∃ j, j < n ∧ r j = i))
    (hq1 : ∀ i, i < m → q i < L)
    (hq2 : ∀ i j : ℕ, j ≤ m → i < j → q i < q j)
    (hqm : q m = L)
    (hq4 : ∀ i, i < L → (P i ↔ ∃ j, j < m ∧ q j = i)) :
    n = m ∧ ∀ i, i ≤ n → r i = q i := by
  have le1 := strictMono_enumeration_le hr2 hq1 hq2 hr4 hq4
  have le2 := strictMono_enumeration_le hq2 hr1 hr2 hq4 hr4
  have heq : ∀ i, i < n → i < m → r i = q i := fun i h1 h2 =>
    le_antisymm (le1 i h1 h2) (le2 i h2 h1)
  have hnm : n = m := by
    rcases lt_trichotomy n m with hlt | heqnm | hgt
    · exfalso
      have hqn : q n < L := hq1 n hlt
      obtain ⟨j, hjn, hj⟩ := (hr4 (q n) hqn).mp ((hq4 (q n) hqn).mpr ⟨n, hlt, rfl⟩)
      have ha : r j = q j := heq j hjn (hjn.trans hlt)
      have hb : q j < q n := hq2 j n hlt.le hjn
      omega
    · exact heqnm
    · exfalso
      have hrm : r m < L := hr1 m hgt
      obtain ⟨j, hjm, hj⟩ := (hq4 (r m) hrm).mp ((hr4 (r m) hrm).mpr ⟨m, hgt, rfl⟩)
      have ha : r j = q j := heq j (hjm.trans hgt) hjm
      have hb : r j < r m := hr2 j m hgt.le hjm
      omega
  refine ⟨hnm, ?_⟩
  intro i hi
  rcases Nat.eq_or_lt_of_le hi with h | h
  · rw [h, hrn, hnm, hqm]
  · exact heq i h (by omega)

namespace IsPullbackBlowupSequence

/- English proof (authored)
Keep the retained indices and compose the old pullback comparisons with the inverse of the stage isomorphisms to the new sequence. The lengths are equal, so the indexing and retention statements still hold. The inverse isomorphisms commute with projections to the base and with the transitions, giving the new comparison equations. The center identity follows by pulling the original center equality back along the inverse isomorphism and using the original isomorphism’s center compatibility.
-/
theorem of_isomorphic {X X' : Scheme.{u}} {φ : X' ⟶ X} {s : SequenceOfBlowups X} {s' s'' : SequenceOfBlowups X'}
    (h : IsPullbackBlowupSequence φ s' s) (e : s'.Isomorphic s'') : IsPullbackBlowupSequence φ s'' s := by
  obtain ⟨r, E, hr1, hr2, hr3, hr4, hfst, hstepE, hcen⟩ := h
  obtain ⟨hlen, ε, h0, hst, hc⟩ := e
  have hcl : ∀ i : ℕ, i ≤ s''.length → i ≤ s'.length := fun i hi => le_of_le_of_eq hi hlen.symm
  have hcl' : ∀ i : ℕ, i < s''.length → i < s'.length := fun i hi => lt_of_lt_of_eq hi hlen.symm
  have hproj := iso_hom_comp_projectionToBase ε h0 hst
  refine ⟨r, fun i hi => (ε i (hcl i hi)).symm ≪≫ E i (hcl i hi),
    fun i hi => hr1 i (hcl' i hi), fun i j hj hij => hr2 i j (hcl j hj) hij,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hlen]; exact hr3
  · intro i hi
    rw [hr4 i hi, hlen]
  · intro i hi
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hfst i (hcl i hi)]
    rw [← hproj i (hcl i hi)]
    simp
  · intro i hi hr
    have h1 := hstepE i (hcl' i hi) hr
    have h2 := hst i (hcl' i hi)
    have key : s''.transitionMapSucc i ≫ (ε i (hcl i hi.le)).inv
        = (ε (i + 1) (hcl' i hi)).inv ≫ s'.transitionMapSucc i := by
      rw [← Iso.cancel_iso_hom_left (ε (i + 1) (hcl' i hi)), ← Category.assoc, h2]
      simp
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, key, Category.assoc, h1, Category.assoc]
  · intro i hi
    have h1 := hcen i (hcl' i hi)
    have h2 := hc i (hcl' i hi)
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [Scheme.IdealSheafData.comap_comp, ← h1, ← h2, ← Scheme.IdealSheafData.comap_comp,
      Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

/- English proof (authored)
The retained-index functions are strictly increasing enumerations of the same indices with nonempty pulled-back centers and have the same terminal value. Hence the lengths and all the retained indices agree. At each stage map the first sequence to the canonical pullback, identify the pullbacks for the equal indices, and then use the inverse comparison to the second sequence. The first projection equations give compatibility at zero. The transition equations agree because the transport between equal stage indices commutes with pullback transitions. The center pullback formulas similarly identify the centers under the stage isomorphisms. These facts give an isomorphism of sequences.
-/
theorem isomorphic {X X' : Scheme.{u}} {φ : X' ⟶ X} {s : SequenceOfBlowups X} {s' s'' : SequenceOfBlowups X'}
    (h : IsPullbackBlowupSequence φ s' s) (h' : IsPullbackBlowupSequence φ s'' s) : s'.Isomorphic s'' := by
  obtain ⟨r, E, hr1, hr2, hr3, hr4, hfst, hstepE, hcen⟩ := h
  obtain ⟨q, G, hq1, hq2, hq3, hq4, gfst, gstep, gcen⟩ := h'
  obtain ⟨hnm, hall⟩ := strictMono_enumeration_unique hr1 hr2 hr3 hr4 hq1 hq2 hq3 hq4
  refine ⟨hnm, fun i hi => E i hi ≪≫ pullbackProjectionToBaseIsoOfEq φ s (hall i hi) ≪≫
    (G i (le_of_le_of_eq hi hnm)).symm, ?_, ?_, ?_⟩
  · have hG0 : (G 0 (le_of_le_of_eq (Nat.zero_le _) hnm)).inv ≫ s''.projectionToBase 0
        = Limits.pullback.fst φ (s.projectionToBase (q 0)) := by
      rw [← gfst 0 (le_of_le_of_eq (Nat.zero_le _) hnm)]
      simp
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← s''.projectionToBase_zero, hG0, pullbackIsoOfEq_hom_fst, hfst 0 (Nat.zero_le _),
      s'.projectionToBase_zero]
  · intro i hi
    have hr : r i ≤ r (i + 1) := (hr2 i (i + 1) hi (Nat.lt_succ_self i)).le
    have hq' : q i ≤ q (i + 1) :=
      (hq2 i (i + 1) (le_of_le_of_eq hi hnm) (Nat.lt_succ_self i)).le
    have h1 := hstepE i hi hr
    have h2 := gstep i (lt_of_lt_of_eq hi hnm) hq'
    have hGinv : (G (i + 1) (le_of_le_of_eq hi hnm)).inv ≫ s''.transitionMapSucc i
        = s.pullbackTransitionMap φ hq' ≫ (G i (le_of_le_of_eq (Nat.le_of_succ_le hi) hnm)).inv := by
      rw [← Iso.cancel_iso_hom_left (G (i + 1) (le_of_le_of_eq hi hnm)), ← Category.assoc,
        Iso.hom_inv_id, Category.id_comp, ← Category.assoc, ← h2]
      simp
    have htrans := pullbackIsoOfEq_hom_comp_pullbackTransitionMap φ s (hall i (Nat.le_of_succ_le hi))
      (hall (i + 1) hi) hr hq'
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hGinv]
    rw [reassoc_of% h1, reassoc_of% htrans]
  · intro i hi
    have h1 := hcen i hi
    have h2 := gcen i (lt_of_lt_of_eq hi hnm)
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [h2, h1, ← Scheme.IdealSheafData.comap_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact comap_pullbackIsoOfEq φ s (hall i (Nat.le_of_succ_le hi)) _

end IsPullbackBlowupSequence

end FunctorialResolution.EmbeddedResolution
