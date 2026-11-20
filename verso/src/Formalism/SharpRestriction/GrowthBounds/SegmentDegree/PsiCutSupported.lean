import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.KillOfEmpty
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NegDminusLeMu

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Dict

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ}

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Separate the alternatives or extract the components of the hypothesis. Substitute using the available equality.

A detailed English derivation is pending.
-/
theorem kfr_lt (hV : F.Valid L₁ N₁) (j : ℤ) {a b : ℕ} (hab : a < b) (hb : b < r) : F.fr j a < F.fr j b := by
  induction b with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
    · exact (ih h (by omega)).trans (hV.2.2.1 j k hb)
    · subst h
      exact hV.2.2.1 j a hb

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem kfr_le (hV : F.Valid L₁ N₁) (j : ℤ) {a b : ℕ} (hab : a ≤ b) (hb : b < r) : F.fr j a ≤ F.fr j b := by
  rcases hab.lt_or_eq with h | h
  · exact (kfr_lt F hV j h hb).le
  · subst h
    exact le_rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem k_mem_letters (j x : ℤ) :
    x ∈ F.letters j ↔ (F.fr (j - 1) 0 ≤ x ∧ x ≤ F.fr j (r - 1)) ∧ posOf n' x ∈ F.TT := by
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem k_fr_mem_letters (hV : F.Valid L₁ N₁) (j : ℤ) {t : ℕ} (ht : t < r) : F.fr j t ∈ F.letters j := by
  rw [k_mem_letters]
  have h4 := hV.2.2.2.1 (j - 1)
  rw [sub_add_cancel] at h4
  have h5 := (hV.2.2.2.2.1 j t ht).1
  have a1 := kfr_le F hV (j - 1) (Nat.zero_le (r - 1)) (by omega)
  have a2 := kfr_le F hV j (Nat.zero_le t) ht
  have a3 := kfr_le F hV j (by omega : t ≤ r - 1) (by omega)
  exact ⟨⟨by omega, a3⟩, h5⟩

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem card_filter_lt_orderIsoOfFin_eq (s : Finset ℤ) {n : ℕ} (h : s.card = n) (i : Fin n) :
    (s.filter (fun y => y < ((s.orderIsoOfFin h i : s) : ℤ))).card = i.val := by
  set e := s.orderIsoOfFin h with he_def
  have hs : s.filter (fun y => y < ((e i : s) : ℤ)) =
      (Finset.Iio i).image (fun k => ((e k : s) : ℤ)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨hy, hlt⟩
      obtain ⟨k, hk⟩ := e.surjective ⟨y, hy⟩
      refine ⟨k, ?_, by rw [hk]⟩
      have hkl : ((e k : s) : ℤ) < ((e i : s) : ℤ) := by
        rw [hk]
        exact hlt
      exact e.lt_iff_lt.mp (Subtype.coe_lt_coe.mp hkl)
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(e k).2, Subtype.coe_lt_coe.mpr (e.lt_iff_lt.mpr hk)⟩
  rw [hs, Finset.card_image_of_injective _ (fun a b hab => e.injective (Subtype.ext hab)), Fin.card_Iio]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Substitute using the available equality. Supply the required witnesses or components. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Substitute using the available equality. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
private theorem filter_fr_le_letters_eq_image_Ico (hV : F.Valid L₁ N₁) (j : ℤ) {t : ℕ} (ht : t < r) :
    (F.letters j).filter (fun y => F.fr j t ≤ y) = (Finset.Ico t r).image (F.fr j) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨hx, htx⟩
    rw [k_mem_letters] at hx
    obtain ⟨⟨_, hxr⟩, hxT⟩ := hx
    have key : ∀ d u, r - 1 - u = d → u < r → F.fr j u ≤ x → ∃ a, (u ≤ a ∧ a < r) ∧ F.fr j a = x := by
      intro d
      induction d with
      | zero =>
        intro u hu hur hux
        have hu' : u = r - 1 := by omega
        subst hu'
        exact ⟨r - 1, ⟨le_rfl, hur⟩, le_antisymm hux hxr⟩
      | succ d ih =>
        intro u hu hur hux
        rcases hux.lt_or_eq with hlt | heq
        · have hu1 : u + 1 < r := by
            by_contra hc
            have hu2 : u = r - 1 := by omega
            subst hu2
            exact absurd hxr (not_le.mpr hlt)
          by_cases hnext : F.fr j (u + 1) ≤ x
          · obtain ⟨a, ⟨ha1, ha2⟩, ha3⟩ := ih (u + 1) (by omega) hu1 hnext
            exact ⟨a, ⟨by omega, ha2⟩, ha3⟩
          · exact absurd hxT (hV.2.2.2.2.2.1 j u x hu1 hlt (not_le.mp hnext))
        · exact ⟨u, ⟨le_rfl, hur⟩, heq⟩
    exact key _ t rfl ht htx
  · rintro ⟨a, ⟨hta, har⟩, rfl⟩
    exact ⟨k_fr_mem_letters F hV j har, kfr_le F hV j hta har⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Assume the negation of the conclusion and derive a contradiction. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
private theorem card_filter_lt_fr_add_sub_eq_segN (hV : F.Valid L₁ N₁) (j : ℤ) {t : ℕ} (ht : t < r) :
    ((F.letters j).filter (fun y => y < F.fr j t)).card + (r - t) = segN F j := by
  have h1 := Finset.card_filter_add_card_filter_not (s := F.letters j) (fun y => y < F.fr j t)
  have h2 : (F.letters j).filter (fun y => ¬ y < F.fr j t) =
      (F.letters j).filter (fun y => F.fr j t ≤ y) := by
    apply Finset.filter_congr
    intro y _
    exact not_lt
  rw [h2, filter_fr_le_letters_eq_image_Ico F hV j ht, Finset.card_image_of_injOn, Nat.card_Ico] at h1
  · exact h1
  · intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact (kfr_lt F hV j h hb.2).ne hab
    · exact (kfr_lt F hV j h ha.2).ne' hab

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify by unfolding definitions. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem segE_eq_fr_iff' (hV : F.Valid L₁ N₁) (j : ℤ) (i : Fin (segN F j)) {t : ℕ} (ht : t < r) :
    segE F j i = F.fr j t ↔ i.val = segN F j - r + t := by
  have hcnt := card_filter_lt_fr_add_sub_eq_segN F hV j ht
  have h0 := card_filter_lt_fr_add_sub_eq_segN F hV j (t := 0) (by omega)
  have hA := card_filter_lt_orderIsoOfFin_eq (F.letters j) (rfl : (F.letters j).card = segN F j) i
  constructor
  · intro h
    have hE : segE F j i = (((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j) i :
        F.letters j) : ℤ) := rfl
    rw [← hE, h] at hA
    omega
  · intro h
    obtain ⟨k, hk⟩ := ((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j)).surjective
      ⟨F.fr j t, k_fr_mem_letters F hV j ht⟩
    have hB := card_filter_lt_orderIsoOfFin_eq (F.letters j) (rfl : (F.letters j).card = segN F j) k
    rw [hk] at hB
    dsimp only at hB
    have hki : k = i := Fin.ext (by omega)
    have hk2 : segE F j k = F.fr j t := by
      show (((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j) k : F.letters j) : ℤ) = _
      rw [hk]
    rw [← hki]
    exact hk2

/- English proof (translation)
Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem k_r_le_segN (hV : F.Valid L₁ N₁) (hr : 0 < r) (j : ℤ) : r ≤ segN F j := by
  have h0 := card_filter_lt_fr_add_sub_eq_segN F hV j (t := 0) hr
  omega

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem segE_eq_fr_iff (hV : F.Valid L₁ N₁) (j : ℤ) (i : Fin (segN F j)) {t : ℕ} (ht : t < r) :
    segE F j i = F.fr j t ↔ i.val = segN F j - r + t := segE_eq_fr_iff' F hV j i ht

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem segE_lt_fr_iff (hV : F.Valid L₁ N₁) (hr : 0 < r) (j : ℤ) (i : Fin (segN F j)) :
    segE F j i < F.fr j 0 ↔ i.val < segN F j - r := by
  obtain ⟨k, hk⟩ := ((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j)).surjective
    ⟨F.fr j 0, k_fr_mem_letters F hV j hr⟩
  have hseg : segE F j k = F.fr j 0 := by
    show (((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j) k : F.letters j) : ℤ) = _
    rw [hk]
  have hkv := (segE_eq_fr_iff' F hV j k hr).mp hseg
  rw [← hseg]
  refine (Subtype.coe_lt_coe.trans ((OrderIso.lt_iff_lt
    ((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j))).trans
      Fin.lt_iff_val_lt_val)).trans ?_
  constructor <;> intro h <;> omega

end Dict

section Supp

variable {R : Type} [CommRing R] {N r : ℕ}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation. Treat this case separately. Treat this case separately.

A detailed English derivation is pending.
-/
theorem Kcol_supported (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ N, ∀ J, Kcol R ν c j J ∈ supported R {v : Fin N × Fin r | v.1.val < j} := by
  intro j
  induction j with
  | zero =>
    intro _ J
    rw [Kcol.eq_1]
    unfold extOne
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ j ih =>
    intro hj J
    have hS : ∀ J', Kcol R ν c j J' ∈ supported R {v : Fin N × Fin r | v.1.val < j + 1} := by
      intro J'
      refine supported_mono (fun v hv => ?_) (ih (by omega) J')
      simp only [Set.mem_setOf_eq] at hv ⊢
      omega
    have hx : ∀ m, letVec R ⟨j, by omega⟩ m ∈ supported R {v : Fin N × Fin r | v.1.val < j + 1} := by
      intro m
      show X ((⟨j, by omega⟩ : Fin N), m) ∈ Algebra.adjoin R (X '' _)
      exact Algebra.subset_adjoin ⟨((⟨j, by omega⟩ : Fin N), m), by simp, rfl⟩
    rw [Kcol_succ ν c j (by omega)]
    unfold colStep wedgeR contrR
    split_ifs <;> first
      | exact hS J
      | exact sum_mem (fun m _ => mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) (hx m)) (hS _))

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Psi_cut_supported (n0 : ℕ) (hn : n0 ≤ N) (ν : Fin (N + 1) → Fin r → ℤ) (I : ℤ → Finset (Fin r)) :
    Psi R (cutPath n0 ν) I ∈ supported R {v : Fin N × Fin r | v.1.val < n0} := by
  unfold Psi
  refine prod_mem (fun c _ => ?_)
  rw [Kcol_cut n0 ν c N le_rfl, min_eq_right hn]
  exact Kcol_supported ν c n0 hn (I c)

end Supp

end Formalism.MainNotions.SelectionLemmas.Pf
