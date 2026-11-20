import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.KillOfEmpty
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NegDminusLeMu

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Dict

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ}

/- English proof (translation)
Proceed by induction on `b with`. Consider the case `zero => omega`. Consider the case `succ k ih`. Break down `Nat.lt_succ_iff_lt_or_eq.mp hab with h | h` into its components or cases. Conclude with `(ih h (by omega)).trans (hV.2.2.1 j k hb)`.

Substitute `h` using the available equality. Conclude with `hV.2.2.1 j a hb`.
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
Break down `hab.lt_or_eq with h | h` into its components or cases. Conclude with `(kfr_lt F hV j h hb).le`. Substitute `h` using the available equality. Conclude with `le_rfl`.
-/
theorem kfr_le (hV : F.Valid L₁ N₁) (j : ℤ) {a b : ℕ} (hab : a ≤ b) (hb : b < r) : F.fr j a ≤ F.fr j b := by
  rcases hab.lt_or_eq with h | h
  · exact (kfr_lt F hV j h hb).le
  · subst h
    exact le_rfl

/- English proof (translation)
Simplify using `only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]`.
-/
theorem k_mem_letters (j x : ℤ) :
    x ∈ F.letters j ↔ (F.fr (j - 1) 0 ≤ x ∧ x ≤ F.fr j (r - 1)) ∧ posOf n' x ∈ F.TT := by
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]

/- English proof (translation)
Rewrite using `[k_mem_letters]`. Establish `h4` using `hV.2.2.2.1 (j - 1)`. Rewrite `h4` using `[sub_add_cancel]`. Establish `h5` using `(hV.2.2.2.2.1 j t ht).1`. Establish `a1` using `kfr_le F hV (j - 1) (Nat.zero_le (r - 1)) (by omega)`.

Establish `a2` using `kfr_le F hV j (Nat.zero_le t) ht`. Establish `a3` using `kfr_le F hV j (by omega : t ≤ r - 1) (by omega)`. Conclude with `⟨⟨by omega, a3⟩, h5⟩`.
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
Use `set e := s.orderIsoOfFin h with he_def`. Establish `hs : s.filter (fun y => y < ((e i : s) : ℤ)) = (Finset.Iio i).image (fun k => ((e k : s) : ℤ))`. Use extensionality with `y`. Simplify using `only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hy, hlt⟩`. Take `⟨k, hk⟩` from `e.surjective ⟨y, hy⟩`. Use `⟨k, ?_, by rw [hk]⟩` and prove the remaining obligations. Establish `hkl : ((e k : s) : ℤ) < ((e i : s) : ℤ)`. Rewrite using `[hk]`.

Conclude with `hlt`. Conclude with `e.lt_iff_lt.mp (Subtype.coe_lt_coe.mp hkl)`. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨(e k).2, Subtype.coe_lt_coe.mpr (e.lt_iff_lt.mpr hk)⟩`. Rewrite using `[hs, Finset.card_image_of_injective _ (fun a b hab => e.injective (Subtype.ext hab)), Fin.card_Iio]`.
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
Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, htx⟩`. Rewrite `hx` using `[k_mem_letters]`.

Take `⟨⟨_, hxr⟩, hxT⟩` from `hx`. Establish `key : ∀ d u, r - 1 - u = d → u < r → F.fr j u ≤ x → ∃ a, (u ≤ a ∧ a < r) ∧ F.fr j a = x`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`.

Introduce `u hu hur hux`. Establish `hu' : u = r - 1` using `by omega`. Substitute `hu'` using the available equality. Conclude with `⟨r - 1, ⟨le_rfl, hur⟩, le_antisymm hux hxr⟩`. Consider the case `succ d ih`.

Introduce `u hu hur hux`. Break down `hux.lt_or_eq with hlt | heq` into its components or cases. Establish `hu1 : u + 1 < r`. Assume the negation of the conclusion as `hc`. Establish `hu2 : u = r - 1` using `by omega`.

Substitute `hu2` using the available equality. Conclude with `absurd hxr (not_le.mpr hlt)`. Distinguish the cases in `hnext : F.fr j (u + 1) ≤ x`. Take `⟨a, ⟨ha1, ha2⟩, ha3⟩` from `ih (u + 1) (by omega) hu1 hnext`. Conclude with `⟨a, ⟨by omega, ha2⟩, ha3⟩`.

Conclude with `absurd hxT (hV.2.2.2.2.2.1 j u x hu1 hlt (not_le.mp hnext))`. Conclude with `⟨u, ⟨le_rfl, hur⟩, heq⟩`. Conclude with `key _ t rfl ht htx`. Introduce and unpack `⟨a, ⟨hta, har⟩, rfl⟩`. Conclude with `⟨k_fr_mem_letters F hV j har, kfr_le F hV j hta har⟩`.
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
Establish `h1` using `Finset.card_filter_add_card_filter_not (s := F.letters j) (fun y => y < F.fr j t)`. Establish `h2 : (F.letters j).filter (fun y => ¬ y < F.fr j t) = (F.letters j).filter (fun y => F.fr j t ≤ y)`. Apply `Finset.filter_congr` to reduce the goal to its premises. Introduce `y _`. Conclude with `not_lt`.

Rewrite `h1` using `[h2, filter_fr_le_letters_eq_image_Ico F hV j ht, Finset.card_image_of_injOn, Nat.card_Ico]`. Conclude with `h1`. Introduce `a ha b hb hab`. Simplify using `only [Finset.coe_Ico, Set.mem_Ico] at ha hb`. Assume the negation of the conclusion as `hne`.

Break down `Nat.lt_or_gt_of_ne hne with h | h` into its components or cases. Conclude with `(kfr_lt F hV j h hb.2).ne hab`. Conclude with `(kfr_lt F hV j h ha.2).ne' hab`.
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
Establish `hcnt` using `card_filter_lt_fr_add_sub_eq_segN F hV j ht`. Establish `h0` using `card_filter_lt_fr_add_sub_eq_segN F hV j (t := 0) (by omega)`. Establish `hA` using `card_filter_lt_orderIsoOfFin_eq (F.letters j) (rfl : (F.letters j).card = segN F j) i`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `hE : segE F j i = (((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j) i : F.letters j) : ℤ)` using `rfl`. Rewrite `hA` using `[← hE, h]`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Take `⟨k, hk⟩` from `((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j)).surjective ⟨F.fr j t, k_fr_mem_letters F hV j ht⟩`.

Establish `hB` using `card_filter_lt_orderIsoOfFin_eq (F.letters j) (rfl : (F.letters j).card = segN F j) k`. Rewrite `hB` using `[hk]`. Simplify using `only at hB`. Establish `hki : k = i` using `Fin.ext (by omega)`. Establish `hk2 : segE F j k = F.fr j t` using `by show (((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j) k : F.letters j) : ℤ) = _`.

Rewrite using `[hk]`. Rewrite using `[← hki]`. Conclude with `hk2`.
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
Establish `h0` using `card_filter_lt_fr_add_sub_eq_segN F hV j (t := 0) hr`. Use linear arithmetic over natural numbers and integers.
-/
theorem k_r_le_segN (hV : F.Valid L₁ N₁) (hr : 0 < r) (j : ℤ) : r ≤ segN F j := by
  have h0 := card_filter_lt_fr_add_sub_eq_segN F hV j (t := 0) hr
  omega

/- English proof (translation)
The claim follows from `segE_eq_fr_iff' F hV j i ht`.
-/
theorem segE_eq_fr_iff (hV : F.Valid L₁ N₁) (j : ℤ) (i : Fin (segN F j)) {t : ℕ} (ht : t < r) :
    segE F j i = F.fr j t ↔ i.val = segN F j - r + t := segE_eq_fr_iff' F hV j i ht

/- English proof (translation)
Take `⟨k, hk⟩` from `((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j)).surjective ⟨F.fr j 0, k_fr_mem_letters F hV j hr⟩`. Establish `hseg : segE F j k = F.fr j 0` using `by show (((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j) k : F.letters j) : ℤ) = _`. Rewrite using `[hk]`. Establish `hkv` using `(segE_eq_fr_iff' F hV j k hr).mp hseg`. Rewrite using `[← hseg]`.

Use `(Subtype.coe_lt_coe.trans ((OrderIso.lt_iff_lt ((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j))).trans Fin.lt_iff_val_lt_val)).trans ?_` and prove the remaining obligations. Apply the tactic sequence `constructor <;> intro h <;> omega`.
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
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_ J`. Rewrite using `[Kcol.eq_1]`.

Unfold `extOne`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Consider the case `succ j ih`.

Introduce `hj J`. Establish `hS : ∀ J', Kcol R ν c j J' ∈ supported R {v : Fin N × Fin r | v.1.val < j + 1}`. Introduce `J'`. Use `supported_mono (fun v hv => ?_) (ih (by omega) J')` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hv ⊢`.

Use linear arithmetic over natural numbers and integers. Establish `hx : ∀ m, letVec R ⟨j, by omega⟩ m ∈ supported R {v : Fin N × Fin r | v.1.val < j + 1}`. Introduce `m`. Use `show X ((⟨j, by omega⟩ : Fin N), m) ∈ Algebra.adjoin R (X '' _)`. Conclude with `Algebra.subset_adjoin ⟨((⟨j, by omega⟩ : Fin N), m), by simp, rfl⟩`.

Rewrite using `[Kcol_succ ν c j (by omega)]`. Unfold `colStep wedgeR contrR`. Apply the tactic sequence `split_ifs <;> first`. Consider the case `exact hS J`. Consider the case `exact sum_mem (fun m _ => mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) (hx m)) (hS _))`.
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
Unfold `Psi`. Use `prod_mem (fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[Kcol_cut n0 ν c N le_rfl, min_eq_right hn]`. Conclude with `Kcol_supported ν c n0 hn (I c)`.
-/
theorem Psi_cut_supported (n0 : ℕ) (hn : n0 ≤ N) (ν : Fin (N + 1) → Fin r → ℤ) (I : ℤ → Finset (Fin r)) :
    Psi R (cutPath n0 ν) I ∈ supported R {v : Fin N × Fin r | v.1.val < n0} := by
  unfold Psi
  refine prod_mem (fun c _ => ?_)
  rw [Kcol_cut n0 ν c N le_rfl, min_eq_right hn]
  exact Kcol_supported ν c n0 hn (I c)

end Supp

end Formalism.MainNotions.SelectionLemmas.Pf
