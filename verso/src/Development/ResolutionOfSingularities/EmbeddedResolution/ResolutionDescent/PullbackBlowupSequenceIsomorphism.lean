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

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `hi`. Rewrite using `[s''.projectionToBase_zero, s'.projectionToBase_zero]`.

Conclude with `h0`. Consider the case `succ n ih`. Introduce `hi`. Rewrite using `[s''.projectionToBase_succ n, s'.projectionToBase_succ n, ← Category.assoc, hst n hi, Category.assoc, ih (Nat.le_of_succ_le hi)]`.
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

/- English proof (translation)
Substitute `h` using the available equality. Simplify using `[pullbackProjectionToBaseIsoOfEq]`.
-/
private theorem pullbackIsoOfEq_hom_fst {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X)
    {a b : ℕ} (h : a = b) :
    (pullbackProjectionToBaseIsoOfEq φ s h).hom ≫ Limits.pullback.fst φ (s.projectionToBase b)
      = Limits.pullback.fst φ (s.projectionToBase a) := by
  subst h
  simp [pullbackProjectionToBaseIsoOfEq]

/- English proof (translation)
Substitute `ha` using the available equality. Substitute `hb` using the available equality. Establish `hpr : hab = hab'` using `rfl`. Substitute `hpr` using the available equality. Simplify using `[pullbackProjectionToBaseIsoOfEq]`.
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

/- English proof (translation)
Substitute `h` using the available equality. Simplify using `[pullbackProjectionToBaseIsoOfEq]`.
-/
private theorem comap_pullbackIsoOfEq {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X) {a b : ℕ}
    (h : a = b) {W : Scheme.{u}} (g : W ⟶ Limits.pullback φ (s.projectionToBase a)) :
    (s.center b).comap (g ≫ (pullbackProjectionToBaseIsoOfEq φ s h).hom ≫ Limits.pullback.snd φ (s.projectionToBase b))
      = (s.center a).comap (g ≫ Limits.pullback.snd φ (s.projectionToBase a)) := by
  subst h
  simp [pullbackProjectionToBaseIsoOfEq]

/- English proof (translation)
Establish `main : ∀ k i : ℕ, i < k → i < n → i < m → r i ≤ q i`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro i hik`. Conclude with `absurd hik (Nat.not_lt_zero i)`.

Consider the case `succ k ih`. Introduce `i hik hin him`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hqL : q i < L` using `hq1 i him`.

Take `⟨j, hjn, hj⟩` from `(hr4 (q i) hqL).mp ((hq4 (q i) hqL).mpr ⟨i, him, rfl⟩)`. Establish `hji : j < i`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Break down `Nat.eq_or_lt_of_le hc with h' | h'` into its components or cases.

Rewrite `hj` using `[← h']`. Use linear arithmetic over natural numbers and integers. Establish `hlt` using `hr2 i j hjn.le h'`. Use linear arithmetic over natural numbers and integers. Establish `h1 : r j ≤ q j` using `ih j (by omega) (by omega) (by omega)`.

Establish `h2 : q j < q i` using `hq2 j i him.le hji`. Use linear arithmetic over natural numbers and integers. Introduce `i hin him`. Conclude with `main (i + 1) i (Nat.lt_succ_self i) hin him`.
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

/- English proof (translation)
Establish `le1` using `strictMono_enumeration_le hr2 hq1 hq2 hr4 hq4`. Establish `le2` using `strictMono_enumeration_le hq2 hr1 hr2 hq4 hr4`. Establish `heq : ∀ i, i < n → i < m → r i = q i` using `fun i h1 h2 => le_antisymm (le1 i h1 h2) (le2 i h2 h1)`. Establish `hnm : n = m`. Break down `lt_trichotomy n m with hlt | heqnm | hgt` into its components or cases.

It suffices to derive a contradiction. Establish `hqn : q n < L` using `hq1 n hlt`. Take `⟨j, hjn, hj⟩` from `(hr4 (q n) hqn).mp ((hq4 (q n) hqn).mpr ⟨n, hlt, rfl⟩)`. Establish `ha : r j = q j` using `heq j hjn (hjn.trans hlt)`. Establish `hb : q j < q n` using `hq2 j n hlt.le hjn`.

Use linear arithmetic over natural numbers and integers. Conclude with `heqnm`. It suffices to derive a contradiction. Establish `hrm : r m < L` using `hr1 m hgt`. Take `⟨j, hjm, hj⟩` from `(hq4 (r m) hrm).mp ((hr4 (r m) hrm).mpr ⟨m, hgt, rfl⟩)`.

Establish `ha : r j = q j` using `heq j (hjm.trans hgt) hjm`. Establish `hb : r j < r m` using `hr2 j m hgt.le hjm`. Use linear arithmetic over natural numbers and integers. Use `⟨hnm, ?_⟩` and prove the remaining obligations. Introduce `i hi`.

Break down `Nat.eq_or_lt_of_le hi with h | h` into its components or cases. Rewrite using `[h, hrn, hnm, hqm]`. Conclude with `heq i h (by omega)`.
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

/- English proof (translation)
Take `⟨r, E, hr1, hr2, hr3, hr4, hfst, hstepE, hcen⟩` from `h`. Take `⟨hlen, ε, h0, hst, hc⟩` from `e`. Establish `hcl : ∀ i : ℕ, i ≤ s''.length → i ≤ s'.length` using `fun i hi => le_of_le_of_eq hi hlen.symm`. Establish `hcl' : ∀ i : ℕ, i < s''.length → i < s'.length` using `fun i hi => lt_of_lt_of_eq hi hlen.symm`. Establish `hproj` using `iso_hom_comp_projectionToBase ε h0 hst`.

Use `⟨r, fun i hi => (ε i (hcl i hi)).symm ≪≫ E i (hcl i hi), fun i hi => hr1 i (hcl' i hi), fun i j hj hij => hr2 i j (hcl j hj) hij, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hlen]`. Conclude with `hr3`. Introduce `i hi`. Rewrite using `[hr4 i hi, hlen]`.

Introduce `i hi`. Simplify using `only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hfst i (hcl i hi)]`. Rewrite using `[← hproj i (hcl i hi)]`. Simplify using the standard rewrite rules. Introduce `i hi hr`.

Establish `h1` using `hstepE i (hcl' i hi) hr`. Establish `h2` using `hst i (hcl' i hi)`. Establish `key : s''.transitionMapSucc i ≫ (ε i (hcl i hi.le)).inv = (ε (i + 1) (hcl' i hi)).inv ≫ s'.transitionMapSucc i`. Rewrite using `[← Iso.cancel_iso_hom_left (ε (i + 1) (hcl' i hi)), ← Category.assoc, h2]`. Simplify using the standard rewrite rules.

Simplify using `only [Iso.trans_hom, Iso.symm_hom]`. Rewrite using `[← Category.assoc, key, Category.assoc, h1, Category.assoc]`. Introduce `i hi`. Establish `h1` using `hcen i (hcl' i hi)`. Establish `h2` using `hc i (hcl' i hi)`.

Simplify using `only [Iso.trans_hom, Iso.symm_hom, Category.assoc]`. Rewrite using `[Scheme.IdealSheafData.comap_comp, ← h1, ← h2, ← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]`.
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

/- English proof (translation)
Take `⟨r, E, hr1, hr2, hr3, hr4, hfst, hstepE, hcen⟩` from `h`. Take `⟨q, G, hq1, hq2, hq3, hq4, gfst, gstep, gcen⟩` from `h'`. Take `⟨hnm, hall⟩` from `strictMono_enumeration_unique hr1 hr2 hr3 hr4 hq1 hq2 hq3 hq4`. Use `⟨hnm, fun i hi => E i hi ≪≫ pullbackProjectionToBaseIsoOfEq φ s (hall i hi) ≪≫ (G i (le_of_le_of_eq hi hnm)).symm, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hG0 : (G 0 (le_of_le_of_eq (Nat.zero_le _) hnm)).inv ≫ s''.projectionToBase 0 = Limits.pullback.fst φ (s.projectionToBase (q 0))`.

Rewrite using `[← gfst 0 (le_of_le_of_eq (Nat.zero_le _) hnm)]`. Simplify using the standard rewrite rules. Simplify using `only [Iso.trans_hom, Iso.symm_hom, Category.assoc]`. Rewrite using `[← s''.projectionToBase_zero, hG0, pullbackIsoOfEq_hom_fst, hfst 0 (Nat.zero_le _), s'.projectionToBase_zero]`. Introduce `i hi`.

Establish `hr : r i ≤ r (i + 1)` using `(hr2 i (i + 1) hi (Nat.lt_succ_self i)).le`. Establish `hq' : q i ≤ q (i + 1)` using `(hq2 i (i + 1) (le_of_le_of_eq hi hnm) (Nat.lt_succ_self i)).le`. Establish `h1` using `hstepE i hi hr`. Establish `h2` using `gstep i (lt_of_lt_of_eq hi hnm) hq'`. Establish `hGinv : (G (i + 1) (le_of_le_of_eq hi hnm)).inv ≫ s''.transitionMapSucc i = s.pullbackTransitionMap φ hq' ≫ (G i (le_of_le_of_eq (Nat.le_of_succ_le hi) hnm)).inv`.

Rewrite using `[← Iso.cancel_iso_hom_left (G (i + 1) (le_of_le_of_eq hi hnm)), ← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc, ← h2]`. Simplify using the standard rewrite rules. Establish `htrans` using `pullbackIsoOfEq_hom_comp_pullbackTransitionMap φ s (hall i (Nat.le_of_succ_le hi)) (hall (i + 1) hi) hr hq'`. Simplify using `only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hGinv]`. Rewrite using `[reassoc_of% h1, reassoc_of% htrans]`.

Introduce `i hi`. Establish `h1` using `hcen i hi`. Establish `h2` using `gcen i (lt_of_lt_of_eq hi hnm)`. Simplify using `only [Iso.trans_hom, Iso.symm_hom]`. Rewrite using `[h2, h1, ← Scheme.IdealSheafData.comap_comp]`.

Simplify using `only [Category.assoc, Iso.inv_hom_id_assoc]`. Conclude with `comap_pullbackIsoOfEq φ s (hall i (Nat.le_of_succ_le hi)) _`.
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
