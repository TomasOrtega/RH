import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc

noncomputable section

open scoped Classical BigOperators

namespace Formalism.L2.SG.Pf.AtPt

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

def pSig {K : Type*} : List (K × ℕ) → ℕ → ℕ
  | [], i => i
  | (_, s) :: bs, i => if i < s then s - 1 - i else s + pSig bs (i - s)

def pTau {K : Type*} [Zero K] : List (K × ℕ) → ℕ → K
  | [], _ => 0
  | (t, s) :: bs, i => if i < s then t else pTau bs (i - s)

def pSt {K : Type*} : List (K × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (_, s) :: bs, i => if i < s then 0 else s + pSt bs (i - s)

def pSz {K : Type*} : List (K × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (_, s) :: bs, i => if i < s then s else pSz bs (i - s)

/- English proof (translation)
Proceed by induction on `bs generalizing i j with`. Consider the case `nil => simp [ptEntry, pTau]`. Consider the case `cons b bs ih`. Take `⟨t, s⟩` from `b`. Simplify using `only [ptEntry, ih, pSig, pTau]`.

Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem ptEntry_eq {K : Type*} [Zero K] (bs : List (K × ℕ)) (i j : ℕ) :
    ptEntry bs i j = if j = pSig bs i then pTau bs i else 0 := by
  induction bs generalizing i j with
  | nil => simp [ptEntry, pTau]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [ptEntry, ih, pSig, pTau]
    split_ifs <;> first | rfl | omega

/- English proof (translation)
Proceed by induction on `bs generalizing i with`. Consider the case `nil => rfl`. Consider the case `cons b bs ih`. Take `⟨t, s⟩` from `b`. Establish `h` using `ih (i - s)`.

Simplify using `only [pSig]`. Apply the tactic sequence `split_ifs <;> (try simp only [Nat.add_sub_cancel_left] at *) <;> omega`.
-/
theorem pSig_pSig {K : Type*} (bs : List (K × ℕ)) (i : ℕ) : pSig bs (pSig bs i) = i := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    have h := ih (i - s)
    simp only [pSig]
    split_ifs <;> (try simp only [Nat.add_sub_cancel_left] at *) <;> omega

/- English proof (translation)
Proceed by induction on `bs generalizing i with`. Consider the case `nil => rfl`. Consider the case `cons b bs ih`. Take `⟨t, s⟩` from `b`. Establish `h` using `ih (i - s)`.

Simplify using `only [pSig, pTau]`. Apply the tactic sequence `split_ifs <;> (try simp only [Nat.add_sub_cancel_left] at *) <;> first | rfl | omega`.
-/
theorem pTau_pSig {K : Type*} [Zero K] (bs : List (K × ℕ)) (i : ℕ) : pTau bs (pSig bs i) = pTau bs i := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    have h := ih (i - s)
    simp only [pSig, pTau]
    split_ifs <;> (try simp only [Nat.add_sub_cancel_left] at *) <;> first | rfl | omega

/- English proof (translation)
Proceed by induction on `bs generalizing i with`. Consider the case `nil => simp at h`. Consider the case `cons b bs ih`. Take `⟨t, s⟩` from `b`. Simplify using `only [List.map_cons, List.sum_cons] at h`.

Simplify using `only [pTau]`. Use `split_ifs with hi`. Conclude with `hbs _ List.mem_cons_self`. Conclude with `ih (fun b hb => hbs b (List.mem_cons_of_mem _ hb)) (i - s) (by omega)`.
-/
theorem pTau_ne {K : Type*} [Zero K] (bs : List (K × ℕ)) (hbs : ∀ b ∈ bs, b.1 ≠ 0)
    (i : ℕ) (h : i < (bs.map Prod.snd).sum) : pTau bs i ≠ 0 := by
  induction bs generalizing i with
  | nil => simp at h
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at h
    simp only [pTau]
    split_ifs with hi
    · exact hbs _ List.mem_cons_self
    · exact ih (fun b hb => hbs b (List.mem_cons_of_mem _ hb)) (i - s) (by omega)

/- English proof (translation)
Proceed by induction on `bs generalizing i with`. Consider the case `nil => simp at h`. Consider the case `cons b bs ih`. Take `⟨t, s⟩` from `b`. Simplify using `only [List.map_cons, List.sum_cons] at h ⊢`.

Simplify using `only [pSt, pSz, pSig]`. Use `split_ifs with hi`. Use `⟨by omega, by omega, by omega, by omega, fun h1 => by omega⟩` and prove the remaining obligations. Take `⟨a1, a2, a3, a4, a5⟩` from `ih (i - s) (by omega)`. Use `⟨by omega, by omega, by omega, by omega, fun h1 => by have := a5 (by omega); omega⟩` and prove the remaining obligations.
-/
theorem pBlock {K : Type*} (bs : List (K × ℕ)) (i : ℕ) (h : i < (bs.map Prod.snd).sum) :
    pSt bs i ≤ i ∧ i < pSt bs i + pSz bs i ∧ i + pSig bs i + 1 = 2 * pSt bs i + pSz bs i ∧
      pSt bs i + pSz bs i ≤ (bs.map Prod.snd).sum ∧
      (i + 1 = (bs.map Prod.snd).sum → pSt bs i + pSz bs i = (bs.map Prod.snd).sum) := by
  induction bs generalizing i with
  | nil => simp at h
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at h ⊢
    simp only [pSt, pSz, pSig]
    split_ifs with hi
    · refine ⟨by omega, by omega, by omega, by omega, fun h1 => by omega⟩
    · obtain ⟨a1, a2, a3, a4, a5⟩ := ih (i - s) (by omega)
      refine ⟨by omega, by omega, by omega, by omega, fun h1 => by have := a5 (by omega); omega⟩

/- English proof (translation)
Proceed by induction on `bs generalizing a i with`. Consider the case `nil => rfl`. Consider the case `cons b bs ih`. Take `⟨t, s⟩` from `b`. Simplify using `only [mapBlocks, pSig, ih]`.
-/
theorem pSig_map {A B : Type} (f : ℕ → ℕ → A → B) (bs : List (A × ℕ)) (a i : ℕ) :
    pSig (mapBlocks f a bs) i = pSig bs i := by
  induction bs generalizing a i with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [mapBlocks, pSig, ih]

/- English proof (translation)
Proceed by induction on `bs generalizing a i with`. Consider the case `nil => simp at h`. Consider the case `cons b bs ih`. Take `⟨t, s⟩` from `b`. Simplify using `only [List.map_cons, List.sum_cons] at h`.

Simplify using `only [mapBlocks, pTau, pSt, pSz]`. Use `split_ifs with hi`. Simplify using the standard rewrite rules. Rewrite using `[ih (a + s) (i - s) (by omega)]; congr 1; omega`.
-/
theorem pTau_map {A B : Type} [Zero A] [Zero B] (f : ℕ → ℕ → A → B) (bs : List (A × ℕ)) (a i : ℕ)
    (h : i < (bs.map Prod.snd).sum) :
    pTau (mapBlocks f a bs) i = f (a + pSt bs i) (pSz bs i) (pTau bs i) := by
  induction bs generalizing a i with
  | nil => simp at h
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at h
    simp only [mapBlocks, pTau, pSt, pSz]
    split_ifs with hi
    · simp
    · rw [ih (a + s) (i - s) (by omega)]; congr 1; omega

section Tri

variable {R : Type*} [CommRing R] {n : ℕ}

def IsLo (L : Matrix (Fin n) (Fin n) R) : Prop := (∀ a, L a a = 1) ∧ ∀ a b, a < b → L a b = 0

def IsUp (U : Matrix (Fin n) (Fin n) R) : Prop := (∀ a, U a a = 1) ∧ ∀ a b, a < b → U b a = 0

/- English proof (translation)
Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Rewrite using `[h.1, h'.1, one_mul]`. Introduce `c _ hc`. Break down `lt_or_gt_of_ne hc with hc | hc` into its components or cases.

Rewrite using `[h'.2 c a hc, mul_zero]`. Rewrite using `[h.2 a c hc, zero_mul]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations.

Break down `lt_or_ge a c with hc | hc` into its components or cases. Rewrite using `[h.2 a c hc, zero_mul]`. Rewrite using `[h'.2 c b (lt_of_le_of_lt hc hab), mul_zero]`.
-/
theorem isLo_mul {L L' : Matrix (Fin n) (Fin n) R} (h : IsLo L) (h' : IsLo L') : IsLo (L * L') := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [h.1, h'.1, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hc | hc
      · rw [h'.2 c a hc, mul_zero]
      · rw [h.2 a c hc, zero_mul]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge a c with hc | hc
    · rw [h.2 a c hc, zero_mul]
    · rw [h'.2 c b (lt_of_le_of_lt hc hab), mul_zero]

/- English proof (translation)
Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Rewrite using `[h.1, h'.1, one_mul]`. Introduce `c _ hc`. Break down `lt_or_gt_of_ne hc with hc | hc` into its components or cases.

Rewrite using `[h.2 c a hc, zero_mul]`. Rewrite using `[h'.2 a c hc, mul_zero]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations.

Break down `lt_or_ge c b with hc | hc` into its components or cases. Rewrite using `[h.2 c b hc, zero_mul]`. Rewrite using `[h'.2 a c (lt_of_lt_of_le hab hc), mul_zero]`.
-/
theorem isUp_mul {U U' : Matrix (Fin n) (Fin n) R} (h : IsUp U) (h' : IsUp U') : IsUp (U * U') := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [h.1, h'.1, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hc | hc
      · rw [h.2 c a hc, zero_mul]
      · rw [h'.2 a c hc, mul_zero]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c b with hc | hc
    · rw [h.2 c b hc, zero_mul]
    · rw [h'.2 a c (lt_of_lt_of_le hab hc), mul_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a => h.1 a, fun a b hab => h.2 a b hab⟩`.
-/
theorem isLo_transpose {U : Matrix (Fin n) (Fin n) R} (h : IsUp U) : IsLo U.transpose :=
  ⟨fun a => h.1 a, fun a b hab => h.2 a b hab⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a => h.1 a, fun a b hab => h.2 a b hab⟩`.
-/
theorem isUp_transpose {L : Matrix (Fin n) (Fin n) R} (h : IsLo L) : IsUp L.transpose :=
  ⟨fun a => h.1 a, fun a b hab => h.2 a b hab⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a => by simp [h.1 a], fun a b hab => by simp [h.2 a b hab]⟩`.
-/
theorem isLo_map {S : Type*} [CommRing S] (f : R →+* S) {L : Matrix (Fin n) (Fin n) R} (h : IsLo L) :
    IsLo (L.map f) :=
  ⟨fun a => by simp [h.1 a], fun a b hab => by simp [h.2 a b hab]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a => by simp [h.1 a], fun a b hab => by simp [h.2 a b hab]⟩`.
-/
theorem isUp_map {S : Type*} [CommRing S] (f : R →+* S) {U : Matrix (Fin n) (Fin n) R} (h : IsUp U) :
    IsUp (U.map f) :=
  ⟨fun a => by simp [h.1 a], fun a b hab => by simp [h.2 a b hab]⟩

/- English proof (translation)
Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, h.1, mul_one, hd]`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, h.2 a b hab, mul_zero, zero_mul]`.
-/
theorem isLo_conj {L : Matrix (Fin n) (Fin n) R} (h : IsLo L) (d d' : Fin n → R) (hd : ∀ a, d a * d' a = 1) :
    IsLo (Matrix.diagonal d * L * Matrix.diagonal d') := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul, h.1, mul_one, hd]
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul, h.2 a b hab, mul_zero, zero_mul]

/- English proof (translation)
Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, h.1, mul_one, hd]`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, h.2 a b hab, mul_zero, zero_mul]`.
-/
theorem isUp_conj {U : Matrix (Fin n) (Fin n) R} (h : IsUp U) (d d' : Fin n → R) (hd : ∀ a, d a * d' a = 1) :
    IsUp (Matrix.diagonal d * U * Matrix.diagonal d') := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul, h.1, mul_one, hd]
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul, h.2 a b hab, mul_zero, zero_mul]

def Ecorner (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun a b => if a = Fin.last n ∧ b = Fin.last n then 1 else 0

/- English proof (translation)
Use extensionality with `a b`. Establish `hLa : ∀ c, L a c * (if c = Fin.last n then (1 : R) else 0) = if a = Fin.last n ∧ c = Fin.last n then 1 else 0`. Introduce `c`. Distinguish the cases in `hc : c = Fin.last n`. Substitute `hc` using the available equality.

Distinguish the cases in `ha : a = Fin.last n`. Substitute `ha` using the available equality. Simplify using `[hL.1]`. Establish `: a < Fin.last n` using `lt_of_le_of_ne (Fin.le_last a) ha`. Simplify using `[hL.2 _ _ this, ha]`.

Simplify using `[hc]`. Simplify using `only [Matrix.mul_apply, Ecorner, Matrix.of_apply]`. Establish `e1 : ∀ c, (∑ d, L a d * (if d = Fin.last n ∧ c = Fin.last n then (1 : R) else 0)) = if a = Fin.last n ∧ c = Fin.last n then 1 else 0`. Introduce `c`. Rewrite using `[Finset.sum_eq_single (Fin.last n)]`.

Distinguish the cases in `hc : c = Fin.last n`. Substitute `hc` using the available equality. Distinguish the cases in `ha : a = Fin.last n`. Substitute `ha` using the available equality. Simplify using `[hL.1]`.

Establish `: a < Fin.last n` using `lt_of_le_of_ne (Fin.le_last a) ha`. Simplify using `[hL.2 _ _ this, ha]`. Simplify using `[hc]`. Introduce `d _ hd`. Simplify using `[hd]`.

Simplify using the standard rewrite rules. Simplify using `only [e1]`. Rewrite using `[Finset.sum_eq_single (Fin.last n)]`. Distinguish the cases in `hb : b = Fin.last n`. Substitute `hb` using the available equality.

Distinguish the cases in `ha : a = Fin.last n`. Substitute `ha` using the available equality. Simplify using `[hU.1]`. Simplify using `[ha]`. Establish `: b < Fin.last n` using `lt_of_le_of_ne (Fin.le_last b) hb`.

Simplify using `[hU.2 _ _ this, hb]`. Introduce `d _ hd`. Simplify using `[hd]`. Simplify using the standard rewrite rules.
-/
theorem lo_corner_up {L U : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hL : IsLo L) (hU : IsUp U) :
    L * Ecorner n * U = Ecorner n := by
  ext a b
  have hLa : ∀ c, L a c * (if c = Fin.last n then (1 : R) else 0) = if a = Fin.last n ∧ c = Fin.last n then 1 else 0 := by
    intro c
    by_cases hc : c = Fin.last n
    · subst hc
      by_cases ha : a = Fin.last n
      · subst ha; simp [hL.1]
      · have : a < Fin.last n := lt_of_le_of_ne (Fin.le_last a) ha
        simp [hL.2 _ _ this, ha]
    · simp [hc]
  simp only [Matrix.mul_apply, Ecorner, Matrix.of_apply]
  have e1 : ∀ c, (∑ d, L a d * (if d = Fin.last n ∧ c = Fin.last n then (1 : R) else 0)) =
      if a = Fin.last n ∧ c = Fin.last n then 1 else 0 := by
    intro c
    rw [Finset.sum_eq_single (Fin.last n)]
    · by_cases hc : c = Fin.last n
      · subst hc
        by_cases ha : a = Fin.last n
        · subst ha; simp [hL.1]
        · have : a < Fin.last n := lt_of_le_of_ne (Fin.le_last a) ha
          simp [hL.2 _ _ this, ha]
      · simp [hc]
    · intro d _ hd; simp [hd]
    · simp
  simp only [e1]
  rw [Finset.sum_eq_single (Fin.last n)]
  · by_cases hb : b = Fin.last n
    · subst hb
      by_cases ha : a = Fin.last n
      · subst ha; simp [hU.1]
      · simp [ha]
    · have : b < Fin.last n := lt_of_le_of_ne (Fin.le_last b) hb
      simp [hU.2 _ _ this, hb]
  · intro d _ hd; simp [hd]
  · simp

/- English proof (translation)
Establish `base : L * M * U - c • Ecorner n = L * (M - c • Ecorner n) * U`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hL hU]`. Distinguish the cases in `hl : σ (Fin.last n) = Fin.last n`. Conclude with `⟨L, U, hL, hU, by rw [if_pos hl, base]⟩`. Rewrite using `[if_neg hl, zero_smul, sub_zero] set j0 := σ (Fin.last n) with hj0`.

Establish `hj0lt : j0 < Fin.last n` using `lt_of_le_of_ne (Fin.le_last _) hl`. Take `⟨u, hu'⟩` from `hu hl`. Set `N : Matrix (Fin (n + 1)) (Fin (n + 1)) R` to `Matrix.of fun a b => if a = j0 ∧ b = Fin.last n then c * ↑u⁻¹ else 0`. Establish `hV : IsUp (1 - N)`. Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations.

Establish `: ¬ (a = j0 ∧ a = Fin.last n)` using `fun h => hl (h.1.symm.trans h.2)`. Simplify using `[N, this]`. Establish `h1 : ¬ (b = j0 ∧ a = Fin.last n)`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `absurd hab (not_lt.2 (Fin.le_last _))`.

Simplify using `[N, Matrix.one_apply_ne (ne_of_lt hab).symm, h1]`. Establish `hMN : M * N = c • Ecorner n`. Use extensionality with `a b`. Simplify using `only [N, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Ecorner, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single j0]`.

Distinguish the cases in `ha : a = Fin.last n`. Substitute `ha` using the available equality. Distinguish the cases in `hb : b = Fin.last n`. Substitute `hb` using the available equality. Simplify using `only [and_self, if_true, mul_one]`.

Rewrite using `[← hu', mul_comm c, ← mul_assoc, Units.mul_inv, one_mul]`. Simplify using `[hb]`. Establish `: M a j0 = 0` using `hM a j0 (fun h => ha (by rw [← hσ a, ← h, hj0, hσ]))`. Simplify using `[this, ha]`. Introduce `d _ hd`.

Simplify using `[hd]`. Simplify using the standard rewrite rules. Establish `hMV : M - c • Ecorner n = M * (1 - N)`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one, hMN]`. Use `⟨L, (1 - N) * U, hL, isUp_mul hV hU, ?_⟩` and prove the remaining obligations.

Rewrite using `[base, hMV, Matrix.mul_assoc L (M * (1 - N)), Matrix.mul_assoc M (1 - N) U, ← Matrix.mul_assoc L M]`.
-/
theorem corner_form (σ : Fin (n + 1) → Fin (n + 1)) (hσ : ∀ a, σ (σ a) = a)
    {L U M : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hL : IsLo L) (hU : IsUp U)
    (hM : ∀ a b, b ≠ σ a → M a b = 0) (c : R) (hu : σ (Fin.last n) ≠ Fin.last n → IsUnit (M (Fin.last n) (σ (Fin.last n)))) :
    ∃ L' U' : Matrix (Fin (n + 1)) (Fin (n + 1)) R, IsLo L' ∧ IsUp U' ∧
      L * M * U - c • Ecorner n = L' * (M - (if σ (Fin.last n) = Fin.last n then c else 0) • Ecorner n) * U' := by
  have base : L * M * U - c • Ecorner n = L * (M - c • Ecorner n) * U := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hL hU]
  by_cases hl : σ (Fin.last n) = Fin.last n
  · exact ⟨L, U, hL, hU, by rw [if_pos hl, base]⟩
  · rw [if_neg hl, zero_smul, sub_zero]
    set j0 := σ (Fin.last n) with hj0
    have hj0lt : j0 < Fin.last n := lt_of_le_of_ne (Fin.le_last _) hl
    obtain ⟨u, hu'⟩ := hu hl
    let N : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
      Matrix.of fun a b => if a = j0 ∧ b = Fin.last n then c * ↑u⁻¹ else 0
    have hV : IsUp (1 - N) := by
      refine ⟨fun a => ?_, fun a b hab => ?_⟩
      · have : ¬ (a = j0 ∧ a = Fin.last n) := fun h => hl (h.1.symm.trans h.2)
        simp [N, this]
      · have h1 : ¬ (b = j0 ∧ a = Fin.last n) := by
          rintro ⟨rfl, rfl⟩; exact absurd hab (not_lt.2 (Fin.le_last _))
        simp [N, Matrix.one_apply_ne (ne_of_lt hab).symm, h1]
    have hMN : M * N = c • Ecorner n := by
      ext a b
      simp only [N, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Ecorner, smul_eq_mul]
      rw [Finset.sum_eq_single j0]
      · by_cases ha : a = Fin.last n
        · subst ha
          by_cases hb : b = Fin.last n
          · subst hb
            simp only [and_self, if_true, mul_one]
            rw [← hu', mul_comm c, ← mul_assoc, Units.mul_inv, one_mul]
          · simp [hb]
        · have : M a j0 = 0 := hM a j0 (fun h => ha (by rw [← hσ a, ← h, hj0, hσ]))
          simp [this, ha]
      · intro d _ hd; simp [hd]
      · simp
    have hMV : M - c • Ecorner n = M * (1 - N) := by
      rw [Matrix.mul_sub, Matrix.mul_one, hMN]
    refine ⟨L, (1 - N) * U, hL, isUp_mul hV hU, ?_⟩
    rw [base, hMV, Matrix.mul_assoc L (M * (1 - N)), Matrix.mul_assoc M (1 - N) U, ← Matrix.mul_assoc L M]

end Tri

end Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf.AtPt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Simplify using `only [LocFacts₂, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem localForm_smul (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)
    (c c' : (D.s.atP p).Ep) (x y : Vp D p) :
    LocFacts₂ M p (c' • x) (c • y) = c' * (M p).L.cj c * LocFacts₂ M p x y := by
  simp only [LocFacts₂, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [frameAct, brS, map_sum, map_smul, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, ZhatL, Formalism.MainNotions.S.Zhat, frame]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
theorem brS_frameAct {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) (a b : Fin (D.R.rS + 1)) :
    brS (VS D) (frameAct (frame F') ξ b) (frame F a) =
      (ZhatL F F' * ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) a b := by
  simp only [frameAct, brS, map_sum, map_smul, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, ZhatL,
    Formalism.MainNotions.S.Zhat, frame]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]

/- English proof (translation)
Simplify using `only [Loc.HermSp.Zhat, Matrix.of_apply, locH, locHerm, locTerm]`. Rewrite using `[localForm_smul, Z.hcj p, baseChangeAt_form Z.M p (Z.hcj p), brS_frameAct]`.
-/
theorem zhat_loc (Z : LocDat D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) (p : PlF D)
    (a b : Fin (D.R.rS + 1)) :
    (locH Z p).Zhat (locTerm Z p Λ F F' Tn T'n).f (locTerm Z p Λ F F' Tn T'n).f' a b =
      (sgnP' D p b * frFac Z.δ p b) * (D.s.atP p).cj (sgnP D p a * frFac Z.δ p a) *
        (D.s.atP p).ιE ((ZhatL F F' *
          ((admXi D Λ F F')⁻¹).map (algebraMap (𝓞 D.host.E) D.host.E)) a b) := by
  simp only [Loc.HermSp.Zhat, Matrix.of_apply, locH, locHerm, locTerm]
  rw [localForm_smul, Z.hcj p, baseChangeAt_form Z.M p (Z.hcj p), brS_frameAct]

def yP (Z : LocDat D) (p : PlF D) : (D.s.atP p).Fp :=
  Z.δ p * (D.s.atP p).ιF ((uP p : ℚ) : D.host.F)

/- English proof (translation)
Unfold `gpart`. Establish `h0` using `(D.host.g_prime 0).ne_zero`. Establish `h1` using `(D.host.g_prime 1).ne_zero`. Apply the tactic sequence `split_ifs <;> simp [h0, h1]`.
-/
theorem gpart_ne (p : PlF D) : (gpart p : ℚ) ≠ 0 := by
  unfold gpart
  have h0 := (D.host.g_prime 0).ne_zero
  have h1 := (D.host.g_prime 1).ne_zero
  split_ifs <;> simp [h0, h1]

/- English proof (translation)
Unfold `yP`. Use `mul_ne_zero (Z.agree p).2.1 ?_` and prove the remaining obligations. Rewrite using `[map_ne_zero]`. Establish `hg : (gS D : ℚ) ≠ 0`. Unfold `gS`.

Establish `h0` using `(D.host.g_prime 0).ne_zero`. Establish `h1` using `(D.host.g_prime 1).ne_zero`. Simplify using `[h0, h1]`. Establish `: uP p ≠ 0` using `by unfold uP; exact div_ne_zero (gpart_ne p) hg`. Conclude with `this` after adjusting the coercions.
-/
theorem yP_ne (Z : LocDat D) (p : PlF D) : yP Z p ≠ 0 := by
  unfold yP
  refine mul_ne_zero (Z.agree p).2.1 ?_
  rw [map_ne_zero]
  have hg : (gS D : ℚ) ≠ 0 := by
    unfold gS
    have h0 := (D.host.g_prime 0).ne_zero
    have h1 := (D.host.g_prime 1).ne_zero
    simp [h0, h1]
  have : uP p ≠ 0 := by unfold uP; exact div_ne_zero (gpart_ne p) hg
  exact_mod_cast this

/- English proof (translation)
Unfold `frFac`. Establish `e1 : (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((uP p : ℚ) : D.host.F))`. Rewrite using `[← (D.s.atP p).compat, map_ratCast (algebraMap D.host.F D.host.E)]`. Rewrite using `[e1, ← map_mul, ← map_pow]`. Establish `hy : (yP Z p) ^ (D.R.rS - a.val) ≠ 0` using `pow_ne_zero _ (yP_ne Z p)`.

Use `Ring.inverse_unit ((Units.mk0 _ hy).map (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).toMonoidHom)` as an intermediate fact. Simplify using `only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.coe_map_inv, Units.val_inv_eq_inv_val] at this`. Unfold `yP at this ⊢`. Rewrite using `[this, inv_pow]`.
-/
theorem frFac_eq (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) :
    frFac Z.δ p a = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((yP Z p)⁻¹ ^ (D.R.rS - a.val)) := by
  unfold frFac
  have e1 : (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((uP p : ℚ) : D.host.F)) := by
    rw [← (D.s.atP p).compat, map_ratCast (algebraMap D.host.F D.host.E)]
  rw [e1, ← map_mul, ← map_pow]
  have hy : (yP Z p) ^ (D.R.rS - a.val) ≠ 0 := pow_ne_zero _ (yP_ne Z p)
  have := Ring.inverse_unit ((Units.mk0 _ hy).map (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).toMonoidHom)
  simp only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.coe_map_inv,
    Units.val_inv_eq_inv_val] at this
  unfold yP at this ⊢
  rw [this, inv_pow]

/- English proof (translation)
The claim follows from `(D.s.atP p).cj.commutes z`.
-/
theorem cj_alg (p : PlF D) (z : (D.s.atP p).Fp) :
    (D.s.atP p).cj (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z) = algebraMap _ _ z :=
  (D.s.atP p).cj.commutes z

end Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf.AtPt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R : Type*} [CommRing R] {n : ℕ}

def Sg (R : Type*) [CommRing R] (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.diagonal fun b => (-1 : R) ^ (r - b.val)

/- English proof (translation)
Rewrite using `[Sg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem sg_sq (r : ℕ) : Sg R r * Sg R r = 1 := by
  rw [Sg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext b; rw [← mul_pow]; simp

/- English proof (translation)
Apply the tactic sequence `ext a b; by_cases h : a = b <;> simp [Sg, h]`.
-/
theorem sg_map {S : Type*} [CommRing S] (f : R →+* S) (r : ℕ) : (Sg R r).map f = Sg S r := by
  ext a b; by_cases h : a = b <;> simp [Sg, h]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[ZhatOM, Sg, Matrix.mul_diagonal, mul_comm]`.
-/
theorem zhatOM_eq {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) : ZhatOM Z = Z * Sg R r := by
  ext a b; simp [ZhatOM, Sg, Matrix.mul_diagonal, mul_comm]

/- English proof (translation)
Establish `h1 : ∀ X : Matrix (Fin n) (Fin n) R, Matrix.diagonal d' * (Matrix.diagonal d * X) = X`. Introduce `X`. Rewrite using `[← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]`. Simplify using `[h]`. Establish `h2 : ∀ X : Matrix (Fin n) (Fin n) R, Matrix.diagonal d * (Matrix.diagonal d' * X) = X`.

Establish `h' : ∀ a, d a * d' a = 1` using `fun a => by rw [mul_comm]; exact h a`. Introduce `X`. Rewrite using `[← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]`. Simplify using `[h']`. Simplify using `only [Matrix.mul_assoc, h1, h2]`.
-/
theorem regroup (d d' : Fin n → R) (h : ∀ a, d' a * d a = 1) (L W B : Matrix (Fin n) (Fin n) R) :
    Matrix.diagonal d * (L * W * B) * Matrix.diagonal d =
      (Matrix.diagonal d * L * Matrix.diagonal d') * (Matrix.diagonal d * W * Matrix.diagonal d) *
        (Matrix.diagonal d' * B * Matrix.diagonal d) := by
  have h1 : ∀ X : Matrix (Fin n) (Fin n) R, Matrix.diagonal d' * (Matrix.diagonal d * X) = X := by
    intro X; rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]; simp [h]
  have h2 : ∀ X : Matrix (Fin n) (Fin n) R, Matrix.diagonal d * (Matrix.diagonal d' * X) = X := by
    have h' : ∀ a, d a * d' a = 1 := fun a => by rw [mul_comm]; exact h a
    intro X; rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]; simp [h']
  simp only [Matrix.mul_assoc, h1, h2]

/- English proof (translation)
Assemble the required witnesses or components as `⟨L, U, fun a => ⟨hL.1 a, hU.1 a⟩, fun a b hab => ⟨hL.2 a b hab, hU.2 a b hab⟩, h⟩`.
-/
theorem goal_of {L U M Z : Matrix (Fin n) (Fin n) R} (hL : IsLo L) (hU : IsUp U) (h : Z = L * M * U) :
    ∃ uL uU : Matrix (Fin n) (Fin n) R, (∀ a, uL a a = 1 ∧ uU a a = 1) ∧
      (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧ Z = uL * M * uU :=
  ⟨L, U, fun a => ⟨hL.1 a, hU.1 a⟩, fun a b hab => ⟨hL.2 a b hab, hU.2 a b hab⟩, h⟩

end Gen

section Pts

variable {K : Type} [Zero K] {r : ℕ}

/- English proof (translation)
Establish `hs` using `w.2.2`. Use `pBlock w.1 a.val (by rw [hs]; exact a.2)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem pSig_lt' (w : Point K (r + 1)) (a : Fin (r + 1)) : pSig w.1 a.val < r + 1 := by
  have hs := w.2.2
  have := pBlock w.1 a.val (by rw [hs]; exact a.2)
  omega

def sgF (w : Point K (r + 1)) (a : Fin (r + 1)) : Fin (r + 1) := ⟨pSig w.1 a.val, pSig_lt' w a⟩

/- English proof (translation)
The claim follows from `Fin.ext (pSig_pSig w.1 a.val)`.
-/
theorem sgF_sgF (w : Point K (r + 1)) (a : Fin (r + 1)) : sgF w (sgF w a) = a :=
  Fin.ext (pSig_pSig w.1 a.val)

/- English proof (translation)
Unfold `ptMat`. Rewrite using `[ptEntry_eq]`. Simplify using `only [sgF, Fin.ext_iff]`.
-/
theorem ptMat_apply' (w : Point K (r + 1)) (a b : Fin (r + 1)) :
    ptMat w a b = if b = sgF w a then pTau w.1 a.val else 0 := by
  unfold ptMat; rw [ptEntry_eq]
  simp only [sgF, Fin.ext_iff]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.transpose_apply, ptMat_apply', ptMat_apply']`. Distinguish the cases in `h : b = sgF w a`. Rewrite using `[if_pos h, if_pos (by rw [h, sgF_sgF]), h]`. Conclude with `pTau_pSig w.1 a.val`.

Rewrite using `[if_neg h, if_neg (fun h' => h (by rw [h', sgF_sgF]))]`.
-/
theorem ptMat_transpose (w : Point K (r + 1)) : (ptMat w).transpose = ptMat w := by
  ext a b
  rw [Matrix.transpose_apply, ptMat_apply', ptMat_apply']
  by_cases h : b = sgF w a
  · rw [if_pos h, if_pos (by rw [h, sgF_sgF]), h]
    exact pTau_pSig w.1 a.val
  · rw [if_neg h, if_neg (fun h' => h (by rw [h', sgF_sgF]))]

/- English proof (translation)
The claim follows from `pTau_ne w.1 (fun b hb => (w.2.1 b hb).1) a.val (by rw [w.2.2]; exact a.2)`.
-/
theorem pTau_ne' (w : Point K (r + 1)) (a : Fin (r + 1)) : pTau w.1 a.val ≠ 0 :=
  pTau_ne w.1 (fun b hb => (w.2.1 b hb).1) a.val (by rw [w.2.2]; exact a.2)

/- English proof (translation)
Establish `hs` using `w.2.2`. Take `⟨h1, h2, h3, h4, h5⟩` from `pBlock w.1 a.val (by rw [hs]; exact a.2)`. Rewrite `h4`, `h5` using `[hs]`. Conclude with `⟨h1, h3, h4, fun ha => h5 (by omega)⟩`.
-/
theorem blk (w : Point K (r + 1)) (a : Fin (r + 1)) :
    pSt w.1 a.val ≤ a.val ∧ a.val + pSig w.1 a.val + 1 = 2 * pSt w.1 a.val + pSz w.1 a.val ∧
      pSt w.1 a.val + pSz w.1 a.val ≤ r + 1 ∧
      (a.val = r → pSt w.1 a.val + pSz w.1 a.val = r + 1) := by
  have hs := w.2.2
  obtain ⟨h1, h2, h3, h4, h5⟩ := pBlock w.1 a.val (by rw [hs]; exact a.2)
  rw [hs] at h4 h5
  exact ⟨h1, h3, h4, fun ha => h5 (by omega)⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c1, c2⟩`. Take `⟨h1, h2, h3, h4⟩` from `blk w a`. Establish `ha : a.val = r` using `by have := a.2; omega`. Establish `ha' : a = Fin.last r` using `Fin.ext ha`.

Substitute `ha'` using the available equality. Use `⟨rfl, Fin.ext ?_⟩` and prove the remaining obligations. Simplify using `only [sgF, Fin.val_last] at h1 h2 h3 h4 c1 c2 ⊢`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨rfl, hs⟩`.

Take `⟨l1, l2, l3, l4⟩` from `blk w (Fin.last r)`. Establish `hs' : pSig w.1 (Fin.last r).val = (Fin.last r).val` using `congrArg Fin.val hs`. Establish `l4'` using `l4 rfl`. Simplify using `only [Fin.val_last] at l1 l2 l3 l4' hs' ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem cond_iff (w : Point K (r + 1)) (a : Fin (r + 1)) :
    (1 + pSt w.1 a.val + pSz w.1 a.val - 1 = r + 1 ∧ pSz w.1 a.val = 1) ↔
      (a = Fin.last r ∧ sgF w (Fin.last r) = Fin.last r) := by
  constructor
  · rintro ⟨c1, c2⟩
    obtain ⟨h1, h2, h3, h4⟩ := blk w a
    have ha : a.val = r := by have := a.2; omega
    have ha' : a = Fin.last r := Fin.ext ha
    subst ha'
    refine ⟨rfl, Fin.ext ?_⟩
    simp only [sgF, Fin.val_last] at h1 h2 h3 h4 c1 c2 ⊢; omega
  · rintro ⟨rfl, hs⟩
    obtain ⟨l1, l2, l3, l4⟩ := blk w (Fin.last r)
    have hs' : pSig w.1 (Fin.last r).val = (Fin.last r).val := congrArg Fin.val hs
    have l4' := l4 rfl
    simp only [Fin.val_last] at l1 l2 l3 l4' hs' ⊢
    omega

/- English proof (translation)
Take `⟨h1, h2, h3, _⟩` from `blk w a`. Use `(sgF w a).2` as an intermediate fact. Simplify using `only [nu, sgF] at this ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem nu_eq (w : Point K (r + 1)) (a : Fin (r + 1)) :
    nu r (1 + pSt w.1 a.val) (1 + pSt w.1 a.val + pSz w.1 a.val - 1) = (r - a.val) + (r - (sgF w a).val) := by
  obtain ⟨h1, h2, h3, _⟩ := blk w a
  have := (sgF w a).2
  simp only [nu, sgF] at this ⊢
  omega

/- English proof (translation)
Take `⟨h1, h2, h3, _⟩` from `blk w a`. Use `(sgF w a).2` as an intermediate fact. Simplify using `only [sgF] at this ⊢`. Use `⟨r - pSt w.1 a.val, by omega⟩` and prove the remaining obligations.
-/
theorem nu_parity (w : Point K (r + 1)) (a : Fin (r + 1)) :
    Odd ((r - a.val) + (r - (sgF w a).val) + pSz w.1 a.val) := by
  obtain ⟨h1, h2, h3, _⟩ := blk w a
  have := (sgF w a).2
  simp only [sgF] at this ⊢
  refine ⟨r - pSt w.1 a.val, by omega⟩

end Pts

variable {D : D7}

/- English proof (translation)
Unfold `modMat`. Rewrite using `[ptEntry_eq, pSig_map, pTau_map _ _ _ _ (by rw [w.2.2]; exact a.2)]`. Simplify using `only [sgF, Fin.ext_iff]`.
-/
theorem modMat_apply' (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (a b : Fin (D.R.rS + 1)) :
    modMat δ T T' p w a b = if b = sgF w a then
      blkMod δ T T' p (1 + pSt w.1 a.val) (pSz w.1 a.val) (pTau w.1 a.val) else 0 := by
  unfold modMat
  rw [ptEntry_eq, pSig_map, pTau_map _ _ _ _ (by rw [w.2.2]; exact a.2)]
  simp only [sgF, Fin.ext_iff]

/- English proof (translation)
Take `⟨L, U, hL, hU, h⟩` from `Y.pt_cell γ hG hrel`. Use `⟨L, U, ⟨fun a => (hL a a).2 rfl, fun a b hab => (hL a b).1 hab⟩, ⟨fun a => (hU a a).2 rfl, fun a b hab => (hU b a).1 hab⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← zhatOM_eq]`. Conclude with `h`.
-/
theorem cell_decomp (Y : TermTie D) {u u' : D.what₂.Word} (γ : D.s.Term u u') (hG : D.s.Gterm γ ≠ 0)
    (hrel : D.s.relevant γ) :
    ∃ L U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsLo L ∧ IsUp U ∧
      ZhatL (Y.fl γ) (Y.fl' γ) * Sg D.host.E D.R.rS = L * ptMat (D.s.ptOf γ) * U := by
  obtain ⟨L, U, hL, hU, h⟩ := Y.pt_cell γ hG hrel
  refine ⟨L, U, ⟨fun a => (hL a a).2 rfl, fun a b hab => (hL a b).1 hab⟩,
    ⟨fun a => (hU a a).2 rfl, fun a b hab => (hU b a).1 hab⟩, ?_⟩
  rw [← zhatOM_eq]; exact h

/- English proof (translation)
Establish `e1 : (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((uP p : ℚ) : D.host.F))`. Rewrite using `[← (D.s.atP p).compat, map_ratCast (algebraMap D.host.F D.host.E)]`. Rewrite using `[e1, ← map_mul, ← map_pow]`. Establish `hy : (yP Z p) ^ k ≠ 0` using `pow_ne_zero _ (yP_ne Z p)`. Use `Ring.inverse_unit ((Units.mk0 _ hy).map (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).toMonoidHom)` as an intermediate fact.

Simplify using `only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.coe_map_inv, Units.val_inv_eq_inv_val] at this`. Unfold `yP at this ⊢`. Rewrite using `[this, inv_pow]`.
-/
theorem inv_pow_eq (Z : LocDat D) (p : PlF D) (k : ℕ) :
    Ring.inverse ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ k) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((yP Z p)⁻¹ ^ k) := by
  have e1 : (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((uP p : ℚ) : D.host.F)) := by
    rw [← (D.s.atP p).compat, map_ratCast (algebraMap D.host.F D.host.E)]
  rw [e1, ← map_mul, ← map_pow]
  have hy : (yP Z p) ^ k ≠ 0 := pow_ne_zero _ (yP_ne Z p)
  have := Ring.inverse_unit ((Units.mk0 _ hy).map (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).toMonoidHom)
  simp only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.coe_map_inv,
    Units.val_inv_eq_inv_val] at this
  unfold yP at this ⊢
  rw [this, inv_pow]

/- English proof (translation)
Take `⟨L, U, hL, hU, h⟩` from `hcell`. Use `⟨L, U, ⟨fun a => (hL a a).2 rfl, fun a b hab => (hL a b).1 hab⟩, ⟨fun a => (hU a a).2 rfl, fun a b hab => (hU b a).1 hab⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← zhatOM_eq]`. Conclude with `h`.
-/
theorem cell_decomp' {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (w : Point D.host.E (D.R.rS + 1)) (hcell : IsInCell (ZhatOM (ZhatL F F')) w) :
    ∃ L U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsLo L ∧ IsUp U ∧
      ZhatL F F' * Sg D.host.E D.R.rS = L * ptMat w * U := by
  obtain ⟨L, U, hL, hU, h⟩ := hcell
  refine ⟨L, U, ⟨fun a => (hL a a).2 rfl, fun a b hab => (hL a b).1 hab⟩,
    ⟨fun a => (hU a a).2 rfl, fun a b hab => (hU b a).1 hab⟩, ?_⟩
  rw [← zhatOM_eq]; exact h

end Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf.AtPt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Take `⟨h0, h1⟩` from `inv_unitri _ (admissibility_witness_unitriangular Λ F F').1 (admissibility_witness_unitriangular Λ F F').2`. Conclude with `isUp_map (algebraMap (𝓞 D.host.E) D.host.E) ⟨h1, fun a b hab => h0 b a hab⟩`.
-/
theorem xi_up (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') :
    IsUp (((admXi D Λ F F')⁻¹).map (algebraMap (𝓞 D.host.E) D.host.E)) := by
  obtain ⟨h0, h1⟩ := inv_unitri _ (admissibility_witness_unitriangular Λ F F').1 (admissibility_witness_unitriangular Λ F F').2
  exact isUp_map (algebraMap (𝓞 D.host.E) D.host.E) ⟨h1, fun a b hab => h0 b a hab⟩

/- English proof (translation)
Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem sgn_sq' {R : Type*} [CommRing R] (r : ℕ) (a : Fin (r + 1)) :
    (-1 : R) ^ (r - a.val) * (-1) ^ (r - a.val) = 1 := by rw [← mul_pow]; simp

/- English proof (translation)
Take `⟨L, U, hL, hU, hc⟩` from `cell_decomp' F F' w hcell`. Use `set ξi := ((admXi D Λ F F')⁻¹).map (algebraMap (𝓞 D.host.E) D.host.E)`. Establish `hξ : IsUp ξi` using `xi_up _ _ _`. Use `⟨L, U * (Sg D.host.E D.R.rS * ξi * Sg D.host.E D.R.rS), hL, isUp_mul hU (isUp_conj hξ _ _ (fun a => sgn_sq' D.R.rS a)), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[sg_sq, Matrix.mul_one]`. Use `_ = (ZhatL F F' * Sg D.host.E D.R.rS) * (Sg D.host.E D.R.rS * ξi * Sg D.host.E D.R.rS) := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hc]; simp only [Matrix.mul_assoc]`.
-/
theorem glob_fact (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)) (hcell : IsInCell (ZhatOM (ZhatL F F')) w) :
    ∃ L B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsLo L ∧ IsUp B ∧
      ZhatL F F' * ((admXi D Λ F F')⁻¹).map
        (algebraMap (𝓞 D.host.E) D.host.E) * Sg D.host.E D.R.rS = L * ptMat w * B := by
  obtain ⟨L, U, hL, hU, hc⟩ := cell_decomp' F F' w hcell
  set ξi := ((admXi D Λ F F')⁻¹).map (algebraMap (𝓞 D.host.E) D.host.E)
  have hξ : IsUp ξi := xi_up _ _ _
  refine ⟨L, U * (Sg D.host.E D.R.rS * ξi * Sg D.host.E D.R.rS), hL,
    isUp_mul hU (isUp_conj hξ _ _ (fun a => sgn_sq' D.R.rS a)), ?_⟩
  calc ZhatL F F' * ξi * Sg D.host.E D.R.rS
      = ZhatL F F' * (Sg D.host.E D.R.rS * Sg D.host.E D.R.rS) * ξi * Sg D.host.E D.R.rS := by
        rw [sg_sq, Matrix.mul_one]
    _ = (ZhatL F F' * Sg D.host.E D.R.rS) * (Sg D.host.E D.R.rS * ξi * Sg D.host.E D.R.rS) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hc]; simp only [Matrix.mul_assoc]

def cf (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) : (D.s.atP p).Fp := (yP Z p)⁻¹ ^ (D.R.rS - a.val)

def cfi (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) : (D.s.atP p).Fp := (yP Z p) ^ (D.R.rS - a.val)

/- English proof (translation)
Unfold `cf cfi`. Rewrite using `[← mul_pow, mul_inv_cancel₀ (yP_ne Z p), one_pow]`.
-/
theorem cfi_cf (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) : cfi Z p a * cf Z p a = 1 := by
  unfold cf cfi; rw [← mul_pow, mul_inv_cancel₀ (yP_ne Z p), one_pow]

/- English proof (translation)
Rewrite using `[mul_comm]`. Conclude with `cfi_cf Z p a`.
-/
theorem cf_cfi (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) : cf Z p a * cfi Z p a = 1 := by
  rw [mul_comm]; exact cfi_cf Z p a

/- English proof (translation)
Unfold `blkMod tMod`. Rewrite using `[inv_pow_eq, nu_eq, pow_add]`. Simplify using `only [cond_iff w a, cf]`.
-/
theorem modMat_blk (Z : LocDat D) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (a : Fin (D.R.rS + 1)) :
    blkMod Z.δ T T' p (1 + pSt w.1 a.val) (pSz w.1 a.val) (pTau w.1 a.val) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Z p a * cf Z p (sgF w a)) *
        twist p (pSz w.1 a.val) ((D.s.atP p).ιE (pTau w.1 a.val)) * Ring.inverse (qE p) -
      (if a = Fin.last D.R.rS ∧ sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then tau0 p T T' else 0) := by
  unfold blkMod tMod
  rw [inv_pow_eq, nu_eq, pow_add]
  simp only [cond_iff w a, cf]

/- English proof (translation)
Take `⟨L, B, hL, hB, hf⟩` from `glob_fact Λ F F' w hcell`. Use `set ι := (D.s.atP p).ιE`. Use `set al := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep`. Use `set A := ZhatL F F' * ((admXi D Λ F F')⁻¹).map (algebraMap (𝓞 D.host.E) D.host.E)`. Use `set fr : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => al (cf Z p a)`.

Use `set fri : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => al (cfi Z p a)`. Establish `hfr : ∀ a, fri a * fr a = 1` using `fun a => by simp only [fr, fri, ← map_mul, cfi_cf, map_one]`. Establish `hfr' : ∀ a, fr a * fri a = 1` using `fun a => by simp only [fr, fri, ← map_mul, cf_cfi, map_one]`. Establish `hZ : (locH Z p).ZZplus (locTerm Z p Λ F F' Tn T'n) = Matrix.diagonal fr * (A * Sg D.host.E D.R.rS).map ι * Matrix.diagonal fr`. Establish `e0 : (locH Z p).ZZplus (locTerm Z p Λ F F' Tn T'n) = (locH Z p).Zhat (locTerm Z p Λ F F' Tn T'n).f (locTerm Z p Λ F F' Tn T'n).f'`.

Simplify using `only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM]`. Rewrite using `[e0]`. Use extensionality with `a b`. Rewrite using `[zhat_loc]`. Simplify using `only [sgnP, sgnP', hR, frFac_eq, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, Sg, map_mul, map_pow, map_neg, map_one, one_mul, fr, al, cj_alg, cf, A]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hZ, hf, Matrix.map_mul, Matrix.map_mul, regroup fr fri hfr]`. Establish `hmod : Matrix.diagonal fr * (ptMat w).map ι * Matrix.diagonal fr = modMat Z.δ Tn T'n p w`. Use extensionality with `a b`. Rewrite using `[modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']`.

Distinguish the cases in `hb : b = sgF w a`. Rewrite using `[if_pos hb, if_pos hb, modMat_blk]`. Simplify using `only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul, fr]`. Substitute `hb` using the available equality. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]`. Rewrite using `[hmod]`. Conclude with `goal_of (isLo_conj (isLo_map ι hL) fr fri hfr') (isUp_conj (isUp_map ι hB) fri fr hfr) rfl`.
-/
theorem atPt_ord (Z : LocDat D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) (w : Point D.host.E (D.R.rS + 1))
    (hcell : IsInCell (ZhatOM (ZhatL F F')) w) (p : PlF D)
    (hR : (D.s.atP p).split = none) (hM : (Z.M p).split = none) :
    ∃ uL uU : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      (locH Z p).ZZplus (locTerm Z p Λ F F' Tn T'n) = uL * modMat Z.δ Tn T'n p w * uU := by
  obtain ⟨L, B, hL, hB, hf⟩ := glob_fact Λ F F' w hcell
  set ι := (D.s.atP p).ιE
  set al := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
  set A := ZhatL F F' * ((admXi D Λ F F')⁻¹).map
        (algebraMap (𝓞 D.host.E) D.host.E)
  set fr : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => al (cf Z p a)
  set fri : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => al (cfi Z p a)
  have hfr : ∀ a, fri a * fr a = 1 := fun a => by simp only [fr, fri, ← map_mul, cfi_cf, map_one]
  have hfr' : ∀ a, fr a * fri a = 1 := fun a => by simp only [fr, fri, ← map_mul, cf_cfi, map_one]
  have hZ : (locH Z p).ZZplus (locTerm Z p Λ F F' Tn T'n) = Matrix.diagonal fr * (A * Sg D.host.E D.R.rS).map ι *
      Matrix.diagonal fr := by
    have e0 : (locH Z p).ZZplus (locTerm Z p Λ F F' Tn T'n) =
        (locH Z p).Zhat (locTerm Z p Λ F F' Tn T'n).f (locTerm Z p Λ F F' Tn T'n).f' := by
      simp only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM]
    rw [e0]
    ext a b
    rw [zhat_loc]
    simp only [sgnP, sgnP', hR, frFac_eq, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, Sg,
      map_mul, map_pow, map_neg, map_one, one_mul, fr, al, cj_alg, cf, A]
    ring
  rw [hZ, hf, Matrix.map_mul, Matrix.map_mul, regroup fr fri hfr]
  have hmod : Matrix.diagonal fr * (ptMat w).map ι * Matrix.diagonal fr =
      modMat Z.δ Tn T'n p w := by
    ext a b
    rw [modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']
    by_cases hb : b = sgF w a
    · rw [if_pos hb, if_pos hb, modMat_blk]
      simp only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul, fr]
      subst hb
      ring
    · rw [if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]
  rw [hmod]
  exact goal_of (isLo_conj (isLo_map ι hL) fr fri hfr') (isUp_conj (isUp_map ι hB) fri fr hfr) rfl

end Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf.AtPt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Split

variable {Fp K : Type} [Field Fp] [CommRing K] [Algebra Fp K] (e : K ≃ₐ[Fp] Fp × Fp)

def p1 : K →+* Fp := (RingHom.fst Fp Fp).comp e.toRingEquiv.toRingHom

def p2 : K →+* Fp := (RingHom.snd Fp Fp).comp e.toRingEquiv.toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adeleInfiniteComponent_apply (x : K) : p1 e x = (e x).1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adele_ext_components (x : K) : p2 e x = (e x).2 := rfl

/- English proof (translation)
Rewrite using `[adeleInfiniteComponent_apply, AlgEquiv.commutes]`. Both sides reduce to the same expression.
-/
theorem fst_proj_algebraMap (z : Fp) : p1 e (algebraMap Fp K z) = z := by
  rw [adeleInfiniteComponent_apply, AlgEquiv.commutes]; rfl

/- English proof (translation)
Rewrite using `[adele_ext_components, AlgEquiv.commutes]`. Both sides reduce to the same expression.
-/
theorem snd_proj_algebraMap (z : Fp) : p2 e (algebraMap Fp K z) = z := by
  rw [adele_ext_components, AlgEquiv.commutes]; rfl

/- English proof (translation)
Rewrite using `[adeleInfiniteComponent_apply, AlgEquiv.apply_symm_apply]`.
-/
theorem fst_proj_symm (v : Fp × Fp) : p1 e (e.symm v) = v.1 := by rw [adeleInfiniteComponent_apply, AlgEquiv.apply_symm_apply]

/- English proof (translation)
Rewrite using `[adele_ext_components, AlgEquiv.apply_symm_apply]`.
-/
theorem snd_proj_symm (v : Fp × Fp) : p2 e (e.symm v) = v.2 := by rw [adele_ext_components, AlgEquiv.apply_symm_apply]

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Apply `e.injective` to reduce the goal to its premises. Conclude with `Prod.ext (congrFun (congrFun h1 a) b) (congrFun (congrFun h2 a) b)`.
-/
theorem mat_eq {A B : Matrix (Fin n) (Fin n) K} (h1 : A.map (p1 e) = B.map (p1 e))
    (h2 : A.map (p2 e) = B.map (p2 e)) : A = B := by
  ext a b
  apply e.injective
  exact Prod.ext (congrFun (congrFun h1 a) b) (congrFun (congrFun h2 a) b)

def glue (X Y : Matrix (Fin n) (Fin n) Fp) : Matrix (Fin n) (Fin n) K := Matrix.of fun a b => e.symm (X a b, Y a b)

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[glue, fst_proj_symm]`.
-/
theorem glue_map_fst (X Y : Matrix (Fin n) (Fin n) Fp) : (glue e X Y).map (p1 e) = X := by
  ext a b; simp [glue, fst_proj_symm]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[glue, snd_proj_symm]`.
-/
theorem glue_map_snd (X Y : Matrix (Fin n) (Fin n) Fp) : (glue e X Y).map (p2 e) = Y := by
  ext a b; simp [glue, snd_proj_symm]

/- English proof (translation)
Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Simplify using `only [glue, Matrix.of_apply, hX.1, hY.1]`. Conclude with `map_one e.symm`. Simplify using `only [glue, Matrix.of_apply, hX.2 a b hab, hY.2 a b hab]`. Conclude with `map_zero e.symm`.
-/
theorem isLo_glue {X Y : Matrix (Fin n) (Fin n) Fp} (hX : IsLo X) (hY : IsLo Y) : IsLo (glue e X Y) := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · simp only [glue, Matrix.of_apply, hX.1, hY.1]; exact map_one e.symm
  · simp only [glue, Matrix.of_apply, hX.2 a b hab, hY.2 a b hab]; exact map_zero e.symm

/- English proof (translation)
Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Simplify using `only [glue, Matrix.of_apply, hX.1, hY.1]`. Conclude with `map_one e.symm`. Simplify using `only [glue, Matrix.of_apply, hX.2 a b hab, hY.2 a b hab]`. Conclude with `map_zero e.symm`.
-/
theorem isUp_glue {X Y : Matrix (Fin n) (Fin n) Fp} (hX : IsUp X) (hY : IsUp Y) : IsUp (glue e X Y) := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · simp only [glue, Matrix.of_apply, hX.1, hY.1]; exact map_one e.symm
  · simp only [glue, Matrix.of_apply, hX.2 a b hab, hY.2 a b hab]; exact map_zero e.symm

end Split

/- English proof (translation)
Establish `h1 : (-1 : R) ^ x * (-1) ^ y * (-1) ^ s = -1` using `by rw [← pow_add, ← pow_add]; exact h.neg_one_pow`. Establish `hx : (-1 : R) ^ x * (-1) ^ x = 1` using `by rw [← mul_pow]; simp`. Establish `hy : (-1 : R) ^ y * (-1) ^ y = 1` using `by rw [← mul_pow]; simp`. Take the linear combination `((-1 : R) ^ x * (-1) ^ y) * h1 - (-1 : R) ^ s * (-1) ^ y * (-1) ^ y * hx - (-1 : R) ^ s * hy`.
-/
theorem sign_rel {R : Type*} [CommRing R] (x y s : ℕ) (h : Odd (x + y + s)) :
    (-1 : R) ^ s = -((-1) ^ x * (-1) ^ y) := by
  have h1 : (-1 : R) ^ x * (-1) ^ y * (-1) ^ s = -1 := by rw [← pow_add, ← pow_add]; exact h.neg_one_pow
  have hx : (-1 : R) ^ x * (-1) ^ x = 1 := by rw [← mul_pow]; simp
  have hy : (-1 : R) ^ y * (-1) ^ y = 1 := by rw [← mul_pow]; simp
  linear_combination ((-1 : R) ^ x * (-1) ^ y) * h1 - (-1 : R) ^ s * (-1) ^ y * (-1) ^ y * hx - (-1 : R) ^ s * hy

section Gen2

variable {K : Type*} [Field K] {n : ℕ}

/- English proof (translation)
Rewrite using `[regroup d d' h]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem fact1 (d d' : Fin n → K) (h : ∀ a, d' a * d a = 1) (κ : K) (L W B : Matrix (Fin n) (Fin n) K) :
    κ • (Matrix.diagonal d * (L * W * B) * Matrix.diagonal d) =
      (Matrix.diagonal d * L * Matrix.diagonal d') * (κ • (Matrix.diagonal d * W * Matrix.diagonal d)) *
        (Matrix.diagonal d' * B * Matrix.diagonal d) := by
  rw [regroup d d' h]; simp only [Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Establish `hSS : ∀ X : Matrix (Fin n) (Fin n) K, S * (S * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hS, Matrix.one_mul]`. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, hSt, hWt]`. Simplify using `only [Matrix.mul_assoc, hSS]`.
-/
theorem fact2 (S L W B : Matrix (Fin n) (Fin n) K) (hS : S * S = 1) (hSt : S.transpose = S)
    (hWt : W.transpose = W) :
    (L * W * B * S).transpose * S = (S * B.transpose * S) * (S * W * S) * (S * L.transpose * S) := by
  have hSS : ∀ X : Matrix (Fin n) (Fin n) K, S * (S * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hS, Matrix.one_mul]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, hSt, hWt]
  simp only [Matrix.mul_assoc, hSS]

/- English proof (translation)
Establish `hd' : ∀ a, d a * d' a = 1` using `fun a => by rw [mul_comm]; exact hd a`. Establish `hd0 : ∀ a, d a ≠ 0` using `fun a h => by have := hd a; rw [h, mul_zero] at this; exact zero_ne_one this`. Rewrite using `[fact1 d d' hd]`. Use `corner_form σ hσ (isLo_conj hL d d' hd') (isUp_conj hB d' d hd) ?_ c ?_` and prove the remaining obligations. Introduce `a b hb`.

Simplify using `only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hW a b hb, mul_zero, zero_mul, smul_eq_mul]`. Introduce `_`. Rewrite using `[isUnit_iff_ne_zero]`. Simplify using `only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul]`. Conclude with `mul_ne_zero hκ (mul_ne_zero (mul_ne_zero (hd0 _) (hWu _)) (hd0 _))`.
-/
theorem generic_comp (σ : Fin (n + 1) → Fin (n + 1)) (hσ : ∀ a, σ (σ a) = a)
    {L W B : Matrix (Fin (n + 1)) (Fin (n + 1)) K} (hL : IsLo L) (hB : IsUp B)
    (hW : ∀ a b, b ≠ σ a → W a b = 0) (hWu : ∀ a, W a (σ a) ≠ 0)
    (d d' : Fin (n + 1) → K) (hd : ∀ a, d' a * d a = 1) (κ : K) (hκ : κ ≠ 0) (c : K) :
    ∃ L' U' : Matrix (Fin (n + 1)) (Fin (n + 1)) K, IsLo L' ∧ IsUp U' ∧
      κ • (Matrix.diagonal d * (L * W * B) * Matrix.diagonal d) - c • Ecorner n =
        L' * (κ • (Matrix.diagonal d * W * Matrix.diagonal d) -
          (if σ (Fin.last n) = Fin.last n then c else 0) • Ecorner n) * U' := by
  have hd' : ∀ a, d a * d' a = 1 := fun a => by rw [mul_comm]; exact hd a
  have hd0 : ∀ a, d a ≠ 0 := fun a h => by have := hd a; rw [h, mul_zero] at this; exact zero_ne_one this
  rw [fact1 d d' hd]
  refine corner_form σ hσ (isLo_conj hL d d' hd') (isUp_conj hB d' d hd) ?_ c ?_
  · intro a b hb
    simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hW a b hb, mul_zero, zero_mul,
      smul_eq_mul]
  · intro _
    rw [isUnit_iff_ne_zero]
    simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul]
    exact mul_ne_zero hκ (mul_ne_zero (mul_ne_zero (hd0 _) (hWu _)) (hd0 _))

end Gen2

end Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf.AtPt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Amat (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  ZhatL F F' * ((admXi D Λ F F')⁻¹).map (algebraMap (𝓞 D.host.E) D.host.E)

/- English proof (translation)
Use `set A := Amat Λ F F' with hA`. Use `set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hqd`. Use `set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1`. Use `set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2`. Establish `hq : q ≠ 0` using `fun h => sg.q_irr.ne_zero (Subtype.ext h)`.

Establish `hcj1 : ∀ x, p1 sg.e ((D.s.atP p).cj x) = p2 sg.e x` using `fun x => by`. Rewrite using `[adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]`. Both sides reduce to the same expression. Establish `hcj2 : ∀ x, p2 sg.e ((D.s.atP p).cj x) = p1 sg.e x` using `fun x => by`. Rewrite using `[adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]`.

Both sides reduce to the same expression. Establish `hs1 : ∀ a, p1 sg.e (sgnP D p a) = (-1) ^ (D.R.rS - a.val)` using `fun a => by`. Simplify using `only [sgnP, hR, fst_proj_symm]`. Establish `hs2 : ∀ a, p2 sg.e (sgnP D p a) = 1` using `fun a => by`. Simplify using `only [sgnP, hR, snd_proj_symm]`.

Establish `hs' : ∀ b, sgnP' D p b = sgnP D p b` using `fun b => by simp only [sgnP', hR]`. Establish `hf1 : ∀ a, p1 sg.e (frFac Z.δ p a) = cf Z p a` using `fun a => by rw [frFac_eq, fst_proj_algebraMap]; rfl`. Establish `hf2 : ∀ a, p2 sg.e (frFac Z.δ p a) = cf Z p a` using `fun a => by rw [frFac_eq, snd_proj_algebraMap]; rfl`. Establish `hT : (locTerm Z p Λ F F' Tn T'n).T = ((Tn : ℕ) : (D.s.atP p).Fp)` using `rfl`. Use extensionality with `a b`.

Simplify using `only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, Matrix.map_apply, Matrix.of_apply, hge, hgq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, fst_proj_symm, apply_ite (p1 sg.e), map_zero, zhat_loc, map_mul, Prod.fst_mul, Prod.snd_mul, ← adeleInfiniteComponent_apply, ← …`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem local_split_type_zero_first (Z : LocDat D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)
    (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
    (hR : (D.s.atP p).split = some sg) (g : Loc.SplitG (Z.M p).L) (hM : (Z.M p).split = some g)
    (hge : g.e = sg.e) (hgq : g.q = sg.q) :
    ((locH Z p).ZZplus (locTerm Z p Λ F F' Tn T'n)).map (p1 sg.e) =
      (sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Z p) * (Amat Λ F F' * Sg D.host.E D.R.rS).map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Z p)) -
        (-(Tn : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
  set A := Amat Λ F F' with hA
  set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hqd
  set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1
  set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2
  have hq : q ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hcj1 : ∀ x, p1 sg.e ((D.s.atP p).cj x) = p2 sg.e x := fun x => by
    rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
  have hcj2 : ∀ x, p2 sg.e ((D.s.atP p).cj x) = p1 sg.e x := fun x => by
    rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
  have hs1 : ∀ a, p1 sg.e (sgnP D p a) = (-1) ^ (D.R.rS - a.val) := fun a => by
    simp only [sgnP, hR, fst_proj_symm]
  have hs2 : ∀ a, p2 sg.e (sgnP D p a) = 1 := fun a => by
    simp only [sgnP, hR, snd_proj_symm]
  have hs' : ∀ b, sgnP' D p b = sgnP D p b := fun b => by simp only [sgnP', hR]
  have hf1 : ∀ a, p1 sg.e (frFac Z.δ p a) = cf Z p a := fun a => by rw [frFac_eq, fst_proj_algebraMap]; rfl
  have hf2 : ∀ a, p2 sg.e (frFac Z.δ p a) = cf Z p a := fun a => by rw [frFac_eq, snd_proj_algebraMap]; rfl
  have hT : (locTerm Z p Λ F F' Tn T'n).T = ((Tn : ℕ) : (D.s.atP p).Fp) := rfl
  ext a b
  simp only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, Matrix.map_apply, Matrix.of_apply, hge, hgq,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, fst_proj_symm, apply_ite (p1 sg.e), map_zero, zhat_loc,
    map_mul, Prod.fst_mul, Prod.snd_mul, ← adeleInfiniteComponent_apply, ← adele_ext_components, hs', hs1, hcj1, hs2, hf1, hf2, Ecorner, hT, Matrix.mul_diagonal, Matrix.diagonal_mul, Sg, hA, Amat, hφ1, RingHom.comp_apply, map_pow, map_neg, map_one, hqd]
  split_ifs <;> ring

/- English proof (translation)
Use `set A := Amat Λ F F' with hA`. Use `set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hqd`. Use `set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1`. Use `set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2`. Establish `hq : q ≠ 0` using `fun h => sg.q_irr.ne_zero (Subtype.ext h)`.

Establish `hcj1 : ∀ x, p1 sg.e ((D.s.atP p).cj x) = p2 sg.e x` using `fun x => by`. Rewrite using `[adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]`. Both sides reduce to the same expression. Establish `hcj2 : ∀ x, p2 sg.e ((D.s.atP p).cj x) = p1 sg.e x` using `fun x => by`. Rewrite using `[adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]`.

Both sides reduce to the same expression. Establish `hs1 : ∀ a, p1 sg.e (sgnP D p a) = (-1) ^ (D.R.rS - a.val)` using `fun a => by`. Simplify using `only [sgnP, hR, fst_proj_symm]`. Establish `hs2 : ∀ a, p2 sg.e (sgnP D p a) = 1` using `fun a => by`. Simplify using `only [sgnP, hR, snd_proj_symm]`.

Establish `hs' : ∀ b, sgnP' D p b = sgnP D p b` using `fun b => by simp only [sgnP', hR]`. Establish `hf1 : ∀ a, p1 sg.e (frFac Z.δ p a) = cf Z p a` using `fun a => by rw [frFac_eq, fst_proj_algebraMap]; rfl`. Establish `hf2 : ∀ a, p2 sg.e (frFac Z.δ p a) = cf Z p a` using `fun a => by rw [frFac_eq, snd_proj_algebraMap]; rfl`. Establish `hT' : (locTerm Z p Λ F F' Tn T'n).T' = ((T'n : ℕ) : (D.s.atP p).Fp)` using `rfl`. Use extensionality with `a b`.

Simplify using `only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, Matrix.map_apply, Matrix.of_apply, hge, hgq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, snd_proj_symm, apply_ite (p2 sg.e), map_zero, zhat_loc, map_mul, Prod.fst_mul, Prod.snd_mul, ← adeleInfiniteComponent_apply, ← …`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem local_split_type_zero_second (Z : LocDat D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)
    (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
    (hR : (D.s.atP p).split = some sg) (g : Loc.SplitG (Z.M p).L) (hM : (Z.M p).split = some g)
    (hge : g.e = sg.e) (hgq : g.q = sg.q) :
    ((locH Z p).ZZplus (locTerm Z p Λ F F' Tn T'n)).map (p2 sg.e) =
      (-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Z p) * (((Amat Λ F F').map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
        Matrix.diagonal (cf Z p)) - ((T'n : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
  set A := Amat Λ F F' with hA
  set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hqd
  set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1
  set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2
  have hq : q ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hcj1 : ∀ x, p1 sg.e ((D.s.atP p).cj x) = p2 sg.e x := fun x => by
    rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
  have hcj2 : ∀ x, p2 sg.e ((D.s.atP p).cj x) = p1 sg.e x := fun x => by
    rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
  have hs1 : ∀ a, p1 sg.e (sgnP D p a) = (-1) ^ (D.R.rS - a.val) := fun a => by
    simp only [sgnP, hR, fst_proj_symm]
  have hs2 : ∀ a, p2 sg.e (sgnP D p a) = 1 := fun a => by
    simp only [sgnP, hR, snd_proj_symm]
  have hs' : ∀ b, sgnP' D p b = sgnP D p b := fun b => by simp only [sgnP', hR]
  have hf1 : ∀ a, p1 sg.e (frFac Z.δ p a) = cf Z p a := fun a => by rw [frFac_eq, fst_proj_algebraMap]; rfl
  have hf2 : ∀ a, p2 sg.e (frFac Z.δ p a) = cf Z p a := fun a => by rw [frFac_eq, snd_proj_algebraMap]; rfl
  have hT' : (locTerm Z p Λ F F' Tn T'n).T' = ((T'n : ℕ) : (D.s.atP p).Fp) := rfl
  ext a b
  simp only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, Matrix.map_apply, Matrix.of_apply, hge, hgq,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, snd_proj_symm, apply_ite (p2 sg.e), map_zero, zhat_loc,
    map_mul, Prod.fst_mul, Prod.snd_mul, ← adeleInfiniteComponent_apply, ← adele_ext_components, hs', hs1, hcj2, hs2, hf1, hf2, Ecorner, hT',
    Matrix.mul_diagonal, Matrix.diagonal_mul, Sg, hA, Amat, hφ2, RingHom.comp_apply, map_pow, map_neg, map_one, hqd,
    Matrix.transpose_apply]
  split_ifs <;> ring

/- English proof (translation)
Use `set A := Amat Λ F F' with hA`. Use `set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hqd`. Use `set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1`. Use `set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2`. Establish `hq : q ≠ 0` using `fun h => sg.q_irr.ne_zero (Subtype.ext h)`.

Establish `hcj1 : ∀ x, p1 sg.e ((D.s.atP p).cj x) = p2 sg.e x` using `fun x => by`. Rewrite using `[adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]`. Both sides reduce to the same expression. Establish `hcj2 : ∀ x, p2 sg.e ((D.s.atP p).cj x) = p1 sg.e x` using `fun x => by`. Rewrite using `[adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]`.

Both sides reduce to the same expression. Establish `hs1 : ∀ a, p1 sg.e (sgnP D p a) = (-1) ^ (D.R.rS - a.val)` using `fun a => by`. Simplify using `only [sgnP, hR, fst_proj_symm]`. Establish `hs2 : ∀ a, p2 sg.e (sgnP D p a) = 1` using `fun a => by`. Simplify using `only [sgnP, hR, snd_proj_symm]`.

Establish `hs' : ∀ b, sgnP' D p b = sgnP D p b` using `fun b => by simp only [sgnP', hR]`. Establish `hf1 : ∀ a, p1 sg.e (frFac Z.δ p a) = cf Z p a` using `fun a => by rw [frFac_eq, fst_proj_algebraMap]; rfl`. Establish `hf2 : ∀ a, p2 sg.e (frFac Z.δ p a) = cf Z p a` using `fun a => by rw [frFac_eq, snd_proj_algebraMap]; rfl`. Establish `hqi : Ring.inverse (qE p) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep q⁻¹`. Simplify using `only [qE, hR]`.

Use `Ring.inverse_unit ((Units.mk0 q hq).map (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).toMonoidHom)` as an intermediate fact. Simplify `this` using `only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.coe_map_inv, Units.val_inv_eq_inv_val]`. Establish `htw1 : ∀ s x, p1 sg.e (twist p s x) = p1 sg.e x` using `fun s x => by`. Simplify using `only [twist, hR]`. Rewrite using `[fst_proj_symm]`.

Both sides reduce to the same expression. Establish `htw2 : ∀ s x, p2 sg.e (twist p s x) = (-1) ^ s * p2 sg.e x` using `fun s x => by`. Simplify using `only [twist, hR]`. Rewrite using `[snd_proj_symm]`. Both sides reduce to the same expression.

Establish `hta1 : ∀ T T' : ℕ, p1 sg.e (tau0 p T T') = -(T : (D.s.atP p).Fp) * q⁻¹` using `fun T T' => by`. Simplify using `only [tau0, hR, map_mul, fst_proj_symm, hqi, fst_proj_algebraMap]`. Establish `hta2 : ∀ T T' : ℕ, p2 sg.e (tau0 p T T') = (T' : (D.s.atP p).Fp) * q⁻¹` using `fun T T' => by`. Simplify using `only [tau0, hR, map_mul, snd_proj_symm, hqi, snd_proj_algebraMap]`. Use extensionality with `a b`.

Simplify using `only [Matrix.map_apply, modMat_apply', Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal, Matrix.diagonal_mul, ptMat_apply', Ecorner, Matrix.of_apply]`. Distinguish the cases in `hb : b = sgF w a`. Substitute `hb` using the available equality. Simplify using `only [if_true, modMat_blk, map_sub, map_mul, fst_proj_algebraMap, htw1, hqi, apply_ite (p1 sg.e), hta1, map_zero, hφ1, RingHom.comp_apply]`. Distinguish the cases in `ha : a = Fin.last D.R.rS`.

Apply the tactic sequence `subst ha; split_ifs <;> first | ring1 | (exfalso; rename_i h1 h2; exact h2 h1.2) | (exfalso; rename_i h1 h2; exact h1 h2.2)`. Simplify using `only [ha, false_and, if_false]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hb, if_neg hb, map_zero, map_zero, mul_zero, zero_mul, mul_zero]`. Distinguish the cases in `ha : a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS`.

Take `⟨rfl, rfl⟩` from `ha`. Establish `: ¬ sgF w (Fin.last D.R.rS) = Fin.last D.R.rS` using `fun h => hb h.symm`. Simplify using `[this]`. Simplify using `[ha]`.
-/
theorem local_split_type_mixed_first (Z : LocDat D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)
    (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
    (hR : (D.s.atP p).split = some sg) (g : Loc.SplitG (Z.M p).L) (hM : (Z.M p).split = some g)
    (hge : g.e = sg.e) (hgq : g.q = sg.q) :
    (modMat Z.δ Tn T'n p w).map (p1 sg.e) =
      (sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Z p) * (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Z p)) -
        (if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then -(Tn : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp) else 0) •
          Ecorner D.R.rS := by
  set A := Amat Λ F F' with hA
  set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hqd
  set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1
  set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2
  have hq : q ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hcj1 : ∀ x, p1 sg.e ((D.s.atP p).cj x) = p2 sg.e x := fun x => by
    rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
  have hcj2 : ∀ x, p2 sg.e ((D.s.atP p).cj x) = p1 sg.e x := fun x => by
    rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
  have hs1 : ∀ a, p1 sg.e (sgnP D p a) = (-1) ^ (D.R.rS - a.val) := fun a => by
    simp only [sgnP, hR, fst_proj_symm]
  have hs2 : ∀ a, p2 sg.e (sgnP D p a) = 1 := fun a => by
    simp only [sgnP, hR, snd_proj_symm]
  have hs' : ∀ b, sgnP' D p b = sgnP D p b := fun b => by simp only [sgnP', hR]
  have hf1 : ∀ a, p1 sg.e (frFac Z.δ p a) = cf Z p a := fun a => by rw [frFac_eq, fst_proj_algebraMap]; rfl
  have hf2 : ∀ a, p2 sg.e (frFac Z.δ p a) = cf Z p a := fun a => by rw [frFac_eq, snd_proj_algebraMap]; rfl
  have hqi : Ring.inverse (qE p) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep q⁻¹ := by
    simp only [qE, hR]
    have := Ring.inverse_unit ((Units.mk0 q hq).map (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).toMonoidHom)
    simpa only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.coe_map_inv,
      Units.val_inv_eq_inv_val] using this
  have htw1 : ∀ s x, p1 sg.e (twist p s x) = p1 sg.e x := fun s x => by
    simp only [twist, hR]; rw [fst_proj_symm]; rfl
  have htw2 : ∀ s x, p2 sg.e (twist p s x) = (-1) ^ s * p2 sg.e x := fun s x => by
    simp only [twist, hR]; rw [snd_proj_symm]; rfl
  have hta1 : ∀ T T' : ℕ, p1 sg.e (tau0 p T T') = -(T : (D.s.atP p).Fp) * q⁻¹ := fun T T' => by
    simp only [tau0, hR, map_mul, fst_proj_symm, hqi, fst_proj_algebraMap]
  have hta2 : ∀ T T' : ℕ, p2 sg.e (tau0 p T T') = (T' : (D.s.atP p).Fp) * q⁻¹ := fun T T' => by
    simp only [tau0, hR, map_mul, snd_proj_symm, hqi, snd_proj_algebraMap]
  ext a b
  simp only [Matrix.map_apply, modMat_apply', Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul, ptMat_apply', Ecorner, Matrix.of_apply]
  by_cases hb : b = sgF w a
  · subst hb
    simp only [if_true, modMat_blk, map_sub, map_mul, fst_proj_algebraMap, htw1, hqi, apply_ite (p1 sg.e), hta1, map_zero,
      hφ1, RingHom.comp_apply]
    by_cases ha : a = Fin.last D.R.rS
    · subst ha; split_ifs <;> first | ring1 | (exfalso; rename_i h1 h2; exact h2 h1.2) | (exfalso; rename_i h1 h2; exact h1 h2.2)
    · simp only [ha, false_and, if_false]; ring
  · rw [if_neg hb, if_neg hb, map_zero, map_zero, mul_zero, zero_mul, mul_zero]
    by_cases ha : a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS
    · obtain ⟨rfl, rfl⟩ := ha
      have : ¬ sgF w (Fin.last D.R.rS) = Fin.last D.R.rS := fun h => hb h.symm
      simp [this]
    · simp [ha]

/- English proof (translation)
Use `set A := Amat Λ F F' with hA`. Use `set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hqd`. Use `set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1`. Use `set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2`. Establish `hq : q ≠ 0` using `fun h => sg.q_irr.ne_zero (Subtype.ext h)`.

Establish `hcj1 : ∀ x, p1 sg.e ((D.s.atP p).cj x) = p2 sg.e x` using `fun x => by`. Rewrite using `[adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]`. Both sides reduce to the same expression. Establish `hcj2 : ∀ x, p2 sg.e ((D.s.atP p).cj x) = p1 sg.e x` using `fun x => by`. Rewrite using `[adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]`.

Both sides reduce to the same expression. Establish `hs1 : ∀ a, p1 sg.e (sgnP D p a) = (-1) ^ (D.R.rS - a.val)` using `fun a => by`. Simplify using `only [sgnP, hR, fst_proj_symm]`. Establish `hs2 : ∀ a, p2 sg.e (sgnP D p a) = 1` using `fun a => by`. Simplify using `only [sgnP, hR, snd_proj_symm]`.

Establish `hs' : ∀ b, sgnP' D p b = sgnP D p b` using `fun b => by simp only [sgnP', hR]`. Establish `hf1 : ∀ a, p1 sg.e (frFac Z.δ p a) = cf Z p a` using `fun a => by rw [frFac_eq, fst_proj_algebraMap]; rfl`. Establish `hf2 : ∀ a, p2 sg.e (frFac Z.δ p a) = cf Z p a` using `fun a => by rw [frFac_eq, snd_proj_algebraMap]; rfl`. Establish `hqi : Ring.inverse (qE p) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep q⁻¹`. Simplify using `only [qE, hR]`.

Use `Ring.inverse_unit ((Units.mk0 q hq).map (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).toMonoidHom)` as an intermediate fact. Simplify `this` using `only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.coe_map_inv, Units.val_inv_eq_inv_val]`. Establish `htw1 : ∀ s x, p1 sg.e (twist p s x) = p1 sg.e x` using `fun s x => by`. Simplify using `only [twist, hR]`. Rewrite using `[fst_proj_symm]`.

Both sides reduce to the same expression. Establish `htw2 : ∀ s x, p2 sg.e (twist p s x) = (-1) ^ s * p2 sg.e x` using `fun s x => by`. Simplify using `only [twist, hR]`. Rewrite using `[snd_proj_symm]`. Both sides reduce to the same expression.

Establish `hta1 : ∀ T T' : ℕ, p1 sg.e (tau0 p T T') = -(T : (D.s.atP p).Fp) * q⁻¹` using `fun T T' => by`. Simplify using `only [tau0, hR, map_mul, fst_proj_symm, hqi, fst_proj_algebraMap]`. Establish `hta2 : ∀ T T' : ℕ, p2 sg.e (tau0 p T T') = (T' : (D.s.atP p).Fp) * q⁻¹` using `fun T T' => by`. Simplify using `only [tau0, hR, map_mul, snd_proj_symm, hqi, snd_proj_algebraMap]`. Use extensionality with `a b`.

Simplify using `only [Matrix.map_apply, modMat_apply', Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal, Matrix.diagonal_mul, ptMat_apply', Ecorner, Matrix.of_apply, Sg]`. Distinguish the cases in `hb : b = sgF w a`. Substitute `hb` using the available equality. Establish `hsr` using `sign_rel (R := (D.s.atP p).Fp) _ _ _ (nu_parity w a)`. Simplify using `only [if_true, modMat_blk, map_sub, map_mul, snd_proj_algebraMap, htw2, hqi, apply_ite (p2 sg.e), hta2, map_zero, hφ2, RingHom.comp_apply, hsr]`.

Distinguish the cases in `ha : a = Fin.last D.R.rS`. Apply the tactic sequence `subst ha; split_ifs <;> first | ring1 | (exfalso; rename_i h1 h2; exact h2 h1.2) | (exfalso; rename_i h1 h2; exact h1 h2.2)`. Simplify using `only [ha, false_and, if_false]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hb, if_neg hb, map_zero, map_zero, mul_zero, zero_mul, mul_zero, zero_mul]`.

Distinguish the cases in `ha : a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS`. Take `⟨rfl, rfl⟩` from `ha`. Establish `: ¬ sgF w (Fin.last D.R.rS) = Fin.last D.R.rS` using `fun h => hb h.symm`. Simplify using `[this]`. Simplify using `[ha]`.
-/
theorem local_split_type_mixed_second (Z : LocDat D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)
    (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
    (hR : (D.s.atP p).split = some sg) (g : Loc.SplitG (Z.M p).L) (hM : (Z.M p).split = some g)
    (hge : g.e = sg.e) (hgq : g.q = sg.q) :
    (modMat Z.δ Tn T'n p w).map (p2 sg.e) =
      (-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Z p) * (Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) *
        Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Z p)) -
        (if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then (T'n : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp) else 0) •
          Ecorner D.R.rS := by
  set A := Amat Λ F F' with hA
  set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hqd
  set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1
  set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2
  have hq : q ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hcj1 : ∀ x, p1 sg.e ((D.s.atP p).cj x) = p2 sg.e x := fun x => by
    rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
  have hcj2 : ∀ x, p2 sg.e ((D.s.atP p).cj x) = p1 sg.e x := fun x => by
    rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
  have hs1 : ∀ a, p1 sg.e (sgnP D p a) = (-1) ^ (D.R.rS - a.val) := fun a => by
    simp only [sgnP, hR, fst_proj_symm]
  have hs2 : ∀ a, p2 sg.e (sgnP D p a) = 1 := fun a => by
    simp only [sgnP, hR, snd_proj_symm]
  have hs' : ∀ b, sgnP' D p b = sgnP D p b := fun b => by simp only [sgnP', hR]
  have hf1 : ∀ a, p1 sg.e (frFac Z.δ p a) = cf Z p a := fun a => by rw [frFac_eq, fst_proj_algebraMap]; rfl
  have hf2 : ∀ a, p2 sg.e (frFac Z.δ p a) = cf Z p a := fun a => by rw [frFac_eq, snd_proj_algebraMap]; rfl
  have hqi : Ring.inverse (qE p) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep q⁻¹ := by
    simp only [qE, hR]
    have := Ring.inverse_unit ((Units.mk0 q hq).map (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).toMonoidHom)
    simpa only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.coe_map_inv,
      Units.val_inv_eq_inv_val] using this
  have htw1 : ∀ s x, p1 sg.e (twist p s x) = p1 sg.e x := fun s x => by
    simp only [twist, hR]; rw [fst_proj_symm]; rfl
  have htw2 : ∀ s x, p2 sg.e (twist p s x) = (-1) ^ s * p2 sg.e x := fun s x => by
    simp only [twist, hR]; rw [snd_proj_symm]; rfl
  have hta1 : ∀ T T' : ℕ, p1 sg.e (tau0 p T T') = -(T : (D.s.atP p).Fp) * q⁻¹ := fun T T' => by
    simp only [tau0, hR, map_mul, fst_proj_symm, hqi, fst_proj_algebraMap]
  have hta2 : ∀ T T' : ℕ, p2 sg.e (tau0 p T T') = (T' : (D.s.atP p).Fp) * q⁻¹ := fun T T' => by
    simp only [tau0, hR, map_mul, snd_proj_symm, hqi, snd_proj_algebraMap]
  ext a b
  simp only [Matrix.map_apply, modMat_apply', Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul, ptMat_apply', Ecorner, Matrix.of_apply, Sg]
  by_cases hb : b = sgF w a
  · subst hb
    have hsr := sign_rel (R := (D.s.atP p).Fp) _ _ _ (nu_parity w a)
    simp only [if_true, modMat_blk, map_sub, map_mul, snd_proj_algebraMap, htw2, hqi, apply_ite (p2 sg.e), hta2, map_zero,
      hφ2, RingHom.comp_apply, hsr]
    by_cases ha : a = Fin.last D.R.rS
    · subst ha; split_ifs <;> first | ring1 | (exfalso; rename_i h1 h2; exact h2 h1.2) | (exfalso; rename_i h1 h2; exact h1 h2.2)
    · simp only [ha, false_and, if_false]; ring
  · rw [if_neg hb, if_neg hb, map_zero, map_zero, mul_zero, zero_mul, mul_zero, zero_mul]
    by_cases ha : a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS
    · obtain ⟨rfl, rfl⟩ := ha
      have : ¬ sgF w (Fin.last D.R.rS) = Fin.last D.R.rS := fun h => hb h.symm
      simp [this]
    · simp [ha]

/- English proof (translation)
Take `⟨L, B, hL, hB, hf⟩` from `glob_fact Λ F F' w hcell`. Establish `hf' : Amat Λ F F' * Sg D.host.E D.R.rS = L * ptMat w * B` using `hf`. Establish `hq : (sg.q : (D.s.atP p).Fp) ≠ 0` using `fun h => sg.q_irr.ne_zero (Subtype.ext h)`. Establish `hA' : Amat Λ F F' = L * ptMat w * B * Sg D.host.E D.R.rS`. Rewrite using `[← hf', Matrix.mul_assoc, sg_sq, Matrix.mul_one]`.

Establish `hs0 : ∀ a : Fin (D.R.rS + 1), (-1 : (D.s.atP p).Fp) ^ (D.R.rS - a.val) ≠ 0` using `fun a => pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)`. Take `⟨L1, U1, hL1, hU1, h1⟩` from `generic_comp (sgF w) (sgF_sgF _) (isLo_map ((p1 sg.e).comp (D.s.atP p).ιE) hL) (isUp_map ((p1 sg.e).comp (D.s.atP p).ιE) hB) (W := (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE)) (fun a b hb => by simp only [Matrix.map_apply, ptMat_apply', if_neg hb, map_zero]) (fun a => by`. Simplify using `only [Matrix.map_apply, ptMat_apply', if_true]`. Conclude with `(map_ne_zero _).2 (pTau_ne' _ a))`. Use the proof step `(cf Z p) (cfi Z p) (cfi_cf Z p) (sg.q : (D.s.atP p).Fp)⁻¹ (inv_ne_zero hq)`.

Use the proof step `(-(Tn : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))`. Take `⟨L2, U2, hL2, hU2, h2⟩` from `generic_comp (sgF w) (sgF_sgF _) (isLo_conj (isLo_transpose (isUp_map ((p2 sg.e).comp (D.s.atP p).ιE) hB)) _ _ (fun a => sgn_sq' D.R.rS a) : IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS)) (isUp_conj (isUp_transpose …`. Simplify using `only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_neg hb, map_zero, mul_zero, zero_mul])`. Use the proof step `(fun a => by`. Simplify using `only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_true]`.

Conclude with `mul_ne_zero (mul_ne_zero (hs0 _) ((map_ne_zero _).2 (pTau_ne' _ a))) (hs0 _))`. Use the proof step `(cf Z p) (cfi Z p) (cfi_cf Z p) (-(sg.q : (D.s.atP p).Fp)⁻¹) (neg_ne_zero.2 (inv_ne_zero hq))`. Use the proof step `((T'n : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))`. Establish `e2 : ((Amat Λ F F').map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS = (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) * (Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * …`. Rewrite using `[hA', Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]`.

Conclude with `fact2 _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _) (by rw [← Matrix.transpose_map, ptMat_transpose])`. Use `goal_of (isLo_glue sg.e hL1 hL2) (isUp_glue sg.e hU1 hU2) (mat_eq sg.e ?_ ?_)` and prove the remaining obligations. Rewrite using `[Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, local_split_type_zero_first Z Λ F F' Tn T'n w p sg hR g hM hge hgq, hf', Matrix.map_mul, Matrix.map_mul, h1, local_split_type_mixed_first Z Λ F F' Tn T'n w p sg hR g hM hge hgq]`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, local_split_type_zero_second Z Λ F F' Tn T'n w p sg hR g hM hge hgq, e2, h2, local_split_type_mixed_second Z Λ F F' Tn T'n w p sg hR g hM hge hgq]`.
-/
theorem atPt_typed (Z : LocDat D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)
    (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
    (hR : (D.s.atP p).split = some sg) (g : Loc.SplitG (Z.M p).L) (hM : (Z.M p).split = some g)
    (hge : g.e = sg.e) (hgq : g.q = sg.q) (hcell : IsInCell (ZhatOM (ZhatL F F')) w) :
    ∃ uL uU : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      (locH Z p).ZZplus (locTerm Z p Λ F F' Tn T'n) = uL * modMat Z.δ Tn T'n p w * uU := by
  obtain ⟨L, B, hL, hB, hf⟩ := glob_fact Λ F F' w hcell
  have hf' : Amat Λ F F' * Sg D.host.E D.R.rS = L * ptMat w * B := hf
  have hq : (sg.q : (D.s.atP p).Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hA' : Amat Λ F F' = L * ptMat w * B * Sg D.host.E D.R.rS := by
    rw [← hf', Matrix.mul_assoc, sg_sq, Matrix.mul_one]
  have hs0 : ∀ a : Fin (D.R.rS + 1), (-1 : (D.s.atP p).Fp) ^ (D.R.rS - a.val) ≠ 0 :=
    fun a => pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)

  obtain ⟨L1, U1, hL1, hU1, h1⟩ := generic_comp (sgF w) (sgF_sgF _)
    (isLo_map ((p1 sg.e).comp (D.s.atP p).ιE) hL) (isUp_map ((p1 sg.e).comp (D.s.atP p).ιE) hB)
    (W := (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE))
    (fun a b hb => by simp only [Matrix.map_apply, ptMat_apply', if_neg hb, map_zero])
    (fun a => by
      simp only [Matrix.map_apply, ptMat_apply', if_true]
      exact (map_ne_zero _).2 (pTau_ne' _ a))
    (cf Z p) (cfi Z p) (cfi_cf Z p) (sg.q : (D.s.atP p).Fp)⁻¹ (inv_ne_zero hq)
    (-(Tn : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))

  obtain ⟨L2, U2, hL2, hU2, h2⟩ := generic_comp (sgF w) (sgF_sgF _)
    (isLo_conj (isLo_transpose (isUp_map ((p2 sg.e).comp (D.s.atP p).ιE) hB)) _ _ (fun a => sgn_sq' D.R.rS a) :
      IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    (isUp_conj (isUp_transpose (isLo_map ((p2 sg.e).comp (D.s.atP p).ιE) hL)) _ _ (fun a => sgn_sq' D.R.rS a) :
      IsUp (Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    (L := Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS)
    (B := Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS)
    (W := Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) *
      Sg (D.s.atP p).Fp D.R.rS)
    (fun a b hb => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_neg hb, map_zero,
        mul_zero, zero_mul])
    (fun a => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_true]
      exact mul_ne_zero (mul_ne_zero (hs0 _) ((map_ne_zero _).2 (pTau_ne' _ a))) (hs0 _))
    (cf Z p) (cfi Z p) (cfi_cf Z p) (-(sg.q : (D.s.atP p).Fp)⁻¹) (neg_ne_zero.2 (inv_ne_zero hq))
    ((T'n : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
  have e2 : ((Amat Λ F F').map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS =
      (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
        (Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) *
          Sg (D.s.atP p).Fp D.R.rS) *
        (Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) := by
    rw [hA', Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]
    exact fact2 _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _) (by rw [← Matrix.transpose_map, ptMat_transpose])
  refine goal_of (isLo_glue sg.e hL1 hL2) (isUp_glue sg.e hU1 hU2) (mat_eq sg.e ?_ ?_)
  · rw [Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, local_split_type_zero_first Z Λ F F' Tn T'n w p sg hR g hM hge hgq, hf',
      Matrix.map_mul, Matrix.map_mul, h1, local_split_type_mixed_first Z Λ F F' Tn T'n w p sg hR g hM hge hgq]
  · rw [Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, local_split_type_zero_second Z Λ F F' Tn T'n w p sg hR g hM hge hgq, e2, h2,
      local_split_type_mixed_second Z Λ F F' Tn T'n w p sg hR g hM hge hgq]

end Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.AtPt

/- English proof (translation)
Establish `hAg` using `(Z.agree p).2.2.2.2.2`. Apply the tactic sequence `rcases hM : (Z.M p).split with _ | g <;> rcases hR : (D.s.atP p).split with _ | sg <;>`. Simplify using `only [hM, hR] at hAg`. Conclude with `atPt_ord Z Λ F F' Tn T'n w hcell p hR hM`. Conclude with `atPt_typed Z Λ F F' Tn T'n w p sg hR g hM hAg.1 hAg.2 hcell`.
-/
theorem termLoc_atPt_frame {D : D7} (Z : LocDat D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) (w : Point D.host.E (D.R.rS + 1))
    (hcell : IsInCell (ZhatOM (ZhatL F F')) w) (p : PlF D) :
    ∃ uL uU : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      (locH Z p).ZZplus (locTerm Z p Λ F F' Tn T'n) = uL * modMat Z.δ Tn T'n p w * uU := by
  have hAg := (Z.agree p).2.2.2.2.2
  rcases hM : (Z.M p).split with _ | g <;> rcases hR : (D.s.atP p).split with _ | sg <;>
    simp only [hM, hR] at hAg
  · exact atPt_ord Z Λ F F' Tn T'n w hcell p hR hM
  · exact atPt_typed Z Λ F F' Tn T'n w p sg hR g hM hAg.1 hAg.2 hcell

/- English proof (translation)
Introduce `γ _ hG hrel p`. Conclude with `termLoc_atPt_frame Z (Y.abelian₂ γ) (Y.fl γ) (Y.fl' γ) (Tu D u) (Tu D u') (D.s.ptOf γ) (Y.pt_cell γ hG hrel) p`.
-/
theorem termLoc_atPtC {D : D7} (Z : LocDat D) (Y : TermTie D) (u u' : D.what₂.Word) : AtPtC D Z Y u u' := by
  intro γ _ hG hrel p
  exact termLoc_atPt_frame Z (Y.abelian₂ γ) (Y.fl γ) (Y.fl' γ) (Tu D u) (Tu D u') (D.s.ptOf γ) (Y.pt_cell γ hG hrel) p

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.Pf.AtPt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Minor

variable {R : Type*} [CommRing R] {n : ℕ}

/- English proof (translation)
Establish `e : ∑ c' : Fin l, f (Fin.castLE hl c') = ∑ c ∈ Finset.univ.map ⟨Fin.castLE hl, Fin.castLE_injective hl⟩, f c`. Rewrite using `[Finset.sum_map]`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `(Finset.sum_subset (Finset.subset_univ _) ?_).symm` and prove the remaining obligations.

Introduce `c _ hc`. Apply `hf` to reduce the goal to its premises. Assume the negation of the conclusion as `h`. Conclude with `hc (Finset.mem_map.2 ⟨⟨c.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)`.
-/
theorem sum_castLE {l : ℕ} (hl : l ≤ n) (f : Fin n → R) (hf : ∀ c : Fin n, l ≤ c.val → f c = 0) :
    ∑ c, f c = ∑ c' : Fin l, f (Fin.castLE hl c') := by
  have e : ∑ c' : Fin l, f (Fin.castLE hl c') =
      ∑ c ∈ Finset.univ.map ⟨Fin.castLE hl, Fin.castLE_injective hl⟩, f c := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro c _ hc
  apply hf
  by_contra h
  exact hc (Finset.mem_map.2 ⟨⟨c.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Rewrite using `[sum_castLE hl]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[sum_castLE hl]`.

Introduce `c hc`. Rewrite using `[hL.2 _ c (by have := i.2; simp only [Fin.lt_def, Fin.coe_castLE]; omega), zero_mul]`. Introduce `d hd`. Rewrite using `[hU.2 _ d (by have := j.2; simp only [Fin.lt_def, Fin.coe_castLE]; omega), mul_zero]`.
-/
theorem submatrix_LMU {L M U : Matrix (Fin n) (Fin n) R} (hL : IsLo L) (hU : IsUp U) {l : ℕ} (hl : l ≤ n) :
    (L * M * U).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      L.submatrix (Fin.castLE hl) (Fin.castLE hl) * M.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        U.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [sum_castLE hl]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [sum_castLE hl]
    intro c hc
    rw [hL.2 _ c (by have := i.2; simp only [Fin.lt_def, Fin.coe_castLE]; omega), zero_mul]
  · intro d hd
    rw [hU.2 _ d (by have := j.2; simp only [Fin.lt_def, Fin.coe_castLE]; omega), mul_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a => hL.1 _, fun a b hab => hL.2 _ _ (by simp only [Fin.lt_def, Fin.coe_castLE] at hab ⊢; exact hab)⟩`.
-/
theorem isLo_sub {L : Matrix (Fin n) (Fin n) R} (hL : IsLo L) {l : ℕ} (hl : l ≤ n) :
    IsLo (L.submatrix (Fin.castLE hl) (Fin.castLE hl)) :=
  ⟨fun a => hL.1 _, fun a b hab => hL.2 _ _ (by simp only [Fin.lt_def, Fin.coe_castLE] at hab ⊢; exact hab)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a => hU.1 _, fun a b hab => hU.2 _ _ (by simp only [Fin.lt_def, Fin.coe_castLE] at hab ⊢; exact hab)⟩`.
-/
theorem isUp_sub {U : Matrix (Fin n) (Fin n) R} (hU : IsUp U) {l : ℕ} (hl : l ≤ n) :
    IsUp (U.submatrix (Fin.castLE hl) (Fin.castLE hl)) :=
  ⟨fun a => hU.1 _, fun a b hab => hU.2 _ _ (by simp only [Fin.lt_def, Fin.coe_castLE] at hab ⊢; exact hab)⟩

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular L (fun i j hij => hL.2 i j hij)]`. Conclude with `Finset.prod_eq_one fun i _ => hL.1 i`.
-/
theorem det_lo {m : ℕ} {L : Matrix (Fin m) (Fin m) R} (hL : IsLo L) : L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L (fun i j hij => hL.2 i j hij)]
  exact Finset.prod_eq_one fun i _ => hL.1 i

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular (fun i j hij => hU.2 j i hij)]`. Conclude with `Finset.prod_eq_one fun i _ => hU.1 i`.
-/
theorem det_up {m : ℕ} {U : Matrix (Fin m) (Fin m) R} (hU : IsUp U) : U.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => hU.2 j i hij)]
  exact Finset.prod_eq_one fun i _ => hU.1 i

end Minor

variable {D : D7}

/- English proof (translation)
Unfold `leadMinorE`. Use `split_ifs with hl`. Rewrite using `[submatrix_LMU hL hU hl, Matrix.det_mul, Matrix.det_mul, det_lo (isLo_sub hL hl), det_up (isUp_sub hU hl), one_mul, mul_one]`. Both sides reduce to the same expression.
-/
theorem leadMinor_LMU {L M U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E} (hL : IsLo L) (hU : IsUp U)
    (l : ℕ) : leadMinorE (L * M * U) l = leadMinorE M l := by
  unfold leadMinorE
  split_ifs with hl
  · rw [submatrix_LMU hL hU hl, Matrix.det_mul, Matrix.det_mul, det_lo (isLo_sub hL hl), det_up (isUp_sub hU hl),
      one_mul, mul_one]
  · rfl

def epsL (r l : ℕ) (hl : l ≤ r + 1) : D.host.E := ∏ b : Fin l, (-1 : D.host.E) ^ (r - (Fin.castLE hl b).val)

/- English proof (translation)
Unfold `leadMinorE`. Rewrite using `[dif_pos hl, dif_pos hl]`. Establish `: (Zm * Sg D.host.E D.R.rS).submatrix (Fin.castLE hl) (Fin.castLE hl) = Zm.submatrix (Fin.castLE hl) (Fin.castLE hl) * Matrix.diagonal fun b : Fin l => (-1 : D.host.E) ^ (D.R.rS - (Fin.castLE hl b).val)`. Use extensionality with `i j`. Simplify using `[Sg, Matrix.mul_diagonal]`.

Rewrite using `[this, Matrix.det_mul, Matrix.det_diagonal]`. Both sides reduce to the same expression.
-/
theorem leadMinor_Sg (Zm : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    leadMinorE (Zm * Sg D.host.E D.R.rS) l = leadMinorE Zm l * epsL (D := D) D.R.rS l hl := by
  unfold leadMinorE
  rw [dif_pos hl, dif_pos hl]
  have : (Zm * Sg D.host.E D.R.rS).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Zm.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal fun b : Fin l => (-1 : D.host.E) ^ (D.R.rS - (Fin.castLE hl b).val) := by
    ext i j; simp [Sg, Matrix.mul_diagonal]
  rw [this, Matrix.det_mul, Matrix.det_diagonal]; rfl

/- English proof (translation)
Unfold `epsL`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun b _ => sgn_sq' D.R.rS _`.
-/
theorem epsL_sq (l : ℕ) (hl : l ≤ D.R.rS + 1) : epsL (D := D) D.R.rS l hl * epsL (D := D) D.R.rS l hl = 1 := by
  unfold epsL
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun b _ => sgn_sq' D.R.rS _

/- English proof (translation)
Unfold `epsL`. Rewrite using `[star_prod]`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[star_pow, star_neg, star_one]`.
-/
theorem star_epsL (l : ℕ) (hl : l ≤ D.R.rS + 1) : star (epsL (D := D) D.R.rS l hl) = epsL (D := D) D.R.rS l hl := by
  unfold epsL
  rw [star_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [star_pow, star_neg, star_one]

/- English proof (translation)
Rewrite using `[← h, star_mul', hs]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_eq_of (x y ε : D.host.E) (h : x * ε = y) (hε : ε * ε = 1) (hs : star ε = ε) :
    x * star x = y * star y := by
  rw [← h, star_mul', hs]
  calc x * star x = x * star x * (ε * ε) := by rw [hε, mul_one]
    _ = _ := by ring

/- English proof (translation)
Unfold `Dmin leadMinorE`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem dmin_eq' {m : ℕ} (w : Point D.host.E m) (l : ℕ) : Dmin w l = leadMinorE (ptMat w) l := by
  unfold Dmin leadMinorE
  split_ifs <;> rfl

/- English proof (translation)
The claim follows from `(D.conjF_eq x).trans (Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host) x).symm`.
-/
theorem conjF_star (x : D.host.E) : D.conjF x = star x := (D.conjF_eq x).trans (Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host) x).symm

/- English proof (translation)
Take `⟨L, U, hL, hU, hc⟩` from `cell_decomp Y γ hG hrel`. Establish `key : ∀ l (hl : l ≤ D.R.rS + 1), leadMinorE (ZhatL (Y.fl γ) (Y.fl' γ)) l * epsL (D` using `D) D.R.rS l hl = Dmin (D.s.ptOf γ) l := by`. Introduce `l hl`. Rewrite using `[← leadMinor_Sg, hc, leadMinor_LMU hL hU, dmin_eq']`. Establish `n1` using `norm_eq_of _ _ _ (key (D.R.rS + 1) le_rfl) (epsL_sq _ _) (star_epsL _ _)`.

Establish `n2` using `norm_eq_of _ _ _ (key D.R.rS (Nat.le_succ _)) (epsL_sq _ _) (star_epsL _ _)`. Simplify using `only [Gval, Gflag, Gpt, conjF_star]`. Unfold `Dl`. Rewrite using `[n1, n2]`. Both sides reduce to the same expression.
-/
theorem gval_eq_aux (Y : TermTie D) {u u' : D.what₂.Word} (γ : D.s.Term u u') (hG : D.s.Gterm γ ≠ 0)
    (hrel : D.s.relevant γ) : Gval (Y.fl γ) (Y.fl' γ) = Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ) := by
  obtain ⟨L, U, hL, hU, hc⟩ := cell_decomp Y γ hG hrel
  have key : ∀ l (hl : l ≤ D.R.rS + 1), leadMinorE (ZhatL (Y.fl γ) (Y.fl' γ)) l * epsL (D := D) D.R.rS l hl =
      Dmin (D.s.ptOf γ) l := by
    intro l hl
    rw [← leadMinor_Sg, hc, leadMinor_LMU hL hU, dmin_eq']
  have n1 := norm_eq_of _ _ _ (key (D.R.rS + 1) le_rfl) (epsL_sq _ _) (star_epsL _ _)
  have n2 := norm_eq_of _ _ _ (key D.R.rS (Nat.le_succ _)) (epsL_sq _ _) (star_epsL _ _)
  simp only [Gval, Gflag, Gpt, conjF_star]
  unfold Dl
  rw [n1, n2]
  rfl

variable (D) in

def PtOfConv (u u' : D.what₂.Word) : Prop :=
  ∀ γ : D.s.Term u u', ¬ (D.s.Gterm γ ≠ 0 ∧ D.s.relevant γ) → Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ) = 0

end Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.AtPt

/- English proof (translation)
Introduce `γ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hG, hrel⟩`. Rewrite using `[← gval_eq_aux Y γ hG hrel, ← Y.G_eq γ]`. Conclude with `(map_ne_zero _).2 hG`.

Introduce `h`. Assume the negation of the conclusion as `hn`. Conclude with `h (hconv γ hn)`.
-/
theorem termLoc_gPtC_of {D : D7} (Y : TermTie D) (u u' : D.what₂.Word) (hconv : PtOfConv D u u') : GPtC D u u' := by
  intro γ
  constructor
  · rintro ⟨hG, hrel⟩
    rw [← gval_eq_aux Y γ hG hrel, ← Y.G_eq γ]
    exact (map_ne_zero _).2 hG
  · intro h
    by_contra hn
    exact h (hconv γ hn)

end Formalism.L2.SG.Pf
