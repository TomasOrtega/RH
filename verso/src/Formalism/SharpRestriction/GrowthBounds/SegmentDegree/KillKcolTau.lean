import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ScaleSCoeffZero

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Abs

variable {R : Type} [CommRing R] {N r : ℕ}

def stg (ν : Fin (N + 1) → Fin r → ℤ) (i : ℕ) : Fin r → ℤ := if h : i < N + 1 then ν ⟨i, h⟩ else 0

/- English proof (translation)
Simplify using `[stg, h]`.
-/
theorem stg_eq (ν : Fin (N + 1) → Fin r → ℤ) (i : ℕ) (h : i < N + 1) : ν ⟨i, h⟩ = stg ν i := by
  simp [stg, h]

/- English proof (translation)
Rewrite using `[Kcol, dif_pos h, stg_eq ν j (by omega), stg_eq ν (j + 1) (by omega)]`.
-/
theorem Kcol_succ (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (j : ℕ) (h : j < N) :
    Kcol R ν c (j + 1) =
      colStep c (colH (stg ν j) c) (colH (stg ν (j + 1)) c) (letVec R ⟨j, h⟩) (Kcol R ν c j) := by
  rw [Kcol, dif_pos h, stg_eq ν j (by omega), stg_eq ν (j + 1) (by omega)]

def offN (n0 : ℕ) : Set (Fin N × Fin r) := {v | n0 ≤ v.1.val ∧ v.2.val + (v.1.val - n0) + 1 ≠ r}

/- English proof (translation)
The claim follows from `lift_colStep_map (kill (R := R) S : MvPolynomial (Fin N × Fin r) R →+* MvPolynomial (Fin N × Fin r) R) c hP hN x Kf J`.
-/
theorem kill_colStep (S : Set (Fin N × Fin r)) (c : ℤ) (hP hN : ℕ) (x : Fin r → MvPolynomial (Fin N × Fin r) R)
    (Kf : Finset (Fin r) → MvPolynomial (Fin N × Fin r) R) (J : Finset (Fin r)) :
    kill S (colStep c hP hN x Kf J) = colStep c hP hN (fun m => kill S (x m)) (fun J => kill S (Kf J)) J :=
  lift_colStep_map (kill (R := R) S : MvPolynomial (Fin N × Fin r) R →+* MvPolynomial (Fin N × Fin r) R) c hP hN x Kf J

/- English proof (translation)
Simplify using `[kill, hv]`.
-/
theorem kill_X_not (S : Set (Fin N × Fin r)) (v : Fin N × Fin r) (hv : v ∉ S) :
    kill (R := R) S (MvPolynomial.X v) = MvPolynomial.X v := by
  simp [kill, hv]

/- English proof (translation)
Simplify using `[kill, hv]`.
-/
theorem kill_X_mem (S : Set (Fin N × Fin r)) (v : Fin N × Fin r) (hv : v ∈ S) :
    kill (R := R) S (MvPolynomial.X v) = 0 := by
  simp [kill, hv]

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_ J`. Conclude with `lift_extOne_map (kill (R := R) (offN (N := N) (r := r) n0) : MvPolynomial (Fin N × Fin r) R →+* MvPolynomial (Fin N × Fin r) R) J`.

Consider the case `succ j ih`. Introduce `hj J`. Establish `hjN : j < N` using `by omega`. Rewrite using `[Kcol_succ ν c j hjN, kill_colStep]`. Establish `e1 : (fun m => kill (offN n0) (letVec R (N` using `N) (n := r) ⟨j, hjN⟩ m)) = letVec R ⟨j, hjN⟩ := by`.

Use function extensionality and compare the values at `m`. Apply `kill_X_not` to reduce the goal to its premises. Introduce `hv`. Establish `: n0 ≤ j` using `hv.1`. Use linear arithmetic over natural numbers and integers.

Establish `e2 : (fun J => kill (offN n0) (Kcol R ν c j J)) = Kcol R ν c j` using `funext (ih (by omega))`. Rewrite using `[e1, e2]`.
-/
theorem kill_Kcol_low (n0 : ℕ) (hn : n0 ≤ N) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ n0, ∀ J, kill (offN n0) (Kcol R ν c j J) = Kcol R ν c j J := by
  intro j
  induction j with
  | zero =>
    intro _ J
    exact lift_extOne_map (kill (R := R) (offN (N := N) (r := r) n0) :
      MvPolynomial (Fin N × Fin r) R →+* MvPolynomial (Fin N × Fin r) R) J
  | succ j ih =>
    intro hj J
    have hjN : j < N := by omega
    rw [Kcol_succ ν c j hjN, kill_colStep]
    have e1 : (fun m => kill (offN n0) (letVec R (N := N) (n := r) ⟨j, hjN⟩ m)) = letVec R ⟨j, hjN⟩ := by
      funext m
      apply kill_X_not
      intro hv
      have : n0 ≤ j := hv.1
      omega
    have e2 : (fun J => kill (offN n0) (Kcol R ν c j J)) = Kcol R ν c j := funext (ih (by omega))
    rw [e1, e2]

variable (n0 : ℕ) (hN : n0 + r = N)

def tauI (m : Fin r) : Fin N := ⟨n0 + (r - 1 - m.val), by have := m.isLt; omega⟩

def rises (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (i : ℕ) : Prop := colH (stg ν i) c < colH (stg ν (i + 1)) c

open Classical in

def riseA (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : ℕ) : Finset (Fin r) :=
  Finset.univ.filter fun m => r - 1 - m.val < t ∧ rises ν c (n0 + (r - 1 - m.val))

/- English proof (translation)
Introduce `t`. Proceed by induction on `t with`. Consider the case `zero`. Introduce `_ J _`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Establish `: riseA n0 ν c 0 = ∅`. Simplify using `[riseA]`. Rewrite using `[this]`. Simplify using `only [add_zero, pow_zero, Finset.prod_empty, mul_one, one_mul, Finset.sdiff_empty]`. Conclude with `kill_Kcol_low n0 (by omega) ν c n0 le_rfl J`.

Consider the case `succ t ih`. Introduce `ht J hJ`. Establish `htr : t < r` using `by omega`. Establish `hjN : n0 + t < N` using `by omega`. Set `mt : Fin r` to `⟨r - 1 - t, by omega⟩`.

Establish `hmt : r - 1 - mt.val = t` using `by simp only [mt]; omega`. Establish `hval : ∀ m : Fin r, r - 1 - m.val = t → m = mt`. Introduce `m hm`. Apply `Fin.ext` to reduce the goal to its premises. Use `m.isLt` as an intermediate fact.

Simplify using `only [mt]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[show n0 + (t + 1) = n0 + t + 1 by ring, Kcol_succ ν c (n0 + t) hjN, kill_colStep]`. Distinguish the cases in `hr : rises ν c (n0 + t)`. Establish `hA : riseA n0 ν c (t + 1) = insert mt (riseA n0 ν c t)`.

Use extensionality with `m`. Simplify using `only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Distinguish the cases in `h3 : r - 1 - m.val = t`.

Conclude with `Or.inl (hval m h3)`. Conclude with `Or.inr ⟨by omega, h2⟩`. Introduce and unpack `(h | ⟨h1, h2⟩)`. Substitute `h` using the available equality. Rewrite using `[hmt]; exact ⟨by omega, hr⟩`.

Conclude with `⟨by omega, h2⟩`. Establish `hnot : mt ∉ riseA n0 ν c t`. Simplify using `only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, not_and]`. Introduce `h`. Rewrite `h` using `[hmt]`.

Use linear arithmetic over natural numbers and integers. Establish `hmJ : mt ∈ J` using `hJ (by rw [hA]; exact Finset.mem_insert_self _ _)`. Establish `hsub : riseA n0 ν c t ⊆ J.erase mt`. Introduce `m hm`. Use `Finset.mem_erase.mpr ⟨fun h => hnot (h ▸ hm), hJ (by rw [hA]; exact Finset.mem_insert_of_mem hm)⟩` and prove the remaining obligations.

Take `⟨e, he⟩` from `ih (by omega) (J.erase mt) hsub`. Establish `hstep : colStep c (colH (stg ν (n0 + t)) c) (colH (stg ν (n0 + t + 1)) c) (fun m => kill (offN n0) (letVec R (N` using `N) (n := r) ⟨n0 + t, hjN⟩ m)) (fun J => kill (offN n0) (Kcol R ν c (n0 + t) J)) J = (-1) ^ (J.filter fun j => mt < j).card * MvPolynomial.X (tauI n0 hN mt, mt) * kill (offN n0) (Kcol R ν c (n0 + t) (J.erase mt)) := by`. Establish `hr' : colH (stg ν (n0 + t)) c < colH (stg ν (n0 + t + 1)) c` using `hr`. Unfold `colStep`. Rewrite using `[if_pos hr', if_pos hc]`.

Unfold `wedgeR`. Rewrite using `[Finset.sum_eq_single mt]`. Use `congr 2`. Establish `: (tauI n0 hN mt : Fin N) = ⟨n0 + t, hjN⟩`. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `only [tauI]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this]`. Apply `kill_X_not` to reduce the goal to its premises. Introduce `hv`.

Apply `hv.2` to reduce the goal to its premises. Simplify using `only [mt]`. Use linear arithmetic over natural numbers and integers. Introduce `m _ hm`. Establish `: kill (offN n0) (letVec R (N` using `N) (n := r) ⟨n0 + t, hjN⟩ m) = 0 := by`.

Apply `kill_X_mem` to reduce the goal to its premises. Use `⟨by simp, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hm` to reduce the goal to its premises. Apply `hval` to reduce the goal to its premises.

Simplify using `only [add_tsub_cancel_left] at h`. Use linear arithmetic over natural numbers and integers. Use `beta_reduce`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `h`. Conclude with `absurd hmJ h`. Rewrite using `[hstep, he, hA, Finset.prod_insert hnot]`. Use `⟨(J.filter fun j => mt < j).card + e, ?_⟩` and prove the remaining obligations. Establish `hset : J.erase mt \ riseA n0 ν c t = J \ insert mt (riseA n0 ν c t)`.

Use extensionality with `m`. Simplify using `only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]`. The claim follows by propositional logic. Rewrite using `[hset, pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hA : riseA n0 ν c (t + 1) = riseA n0 ν c t`. Use extensionality with `m`. Simplify using `only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Distinguish the cases in `h3 : r - 1 - m.val = t`. Rewrite `h2` using `[h3]`. Conclude with `absurd h2 hr`. Conclude with `⟨by omega, h2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨by omega, h2⟩`. Establish `heq : colH (stg ν (n0 + t)) c = colH (stg ν (n0 + t + 1)) c` using `le_antisymm (hmono t htr) (not_lt.mp hr)`. Rewrite `hJ`, the goal using `[hA]`. Take `⟨e, he⟩` from `ih (by omega) J hJ`. Use `⟨e, ?_⟩` and prove the remaining obligations.

Unfold `colStep`. Rewrite using `[heq, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]`. Conclude with `he`.
-/
theorem kill_Kcol_tau (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (hc : 1 ≤ c)
    (hmono : ∀ t < r, colH (stg ν (n0 + t)) c ≤ colH (stg ν (n0 + t + 1)) c) :
    ∀ t ≤ r, ∀ J, riseA n0 ν c t ⊆ J → ∃ e : ℕ, kill (offN n0) (Kcol R ν c (n0 + t) J) =
      (-1) ^ e * (∏ m ∈ riseA n0 ν c t, MvPolynomial.X (tauI n0 hN m, m)) * Kcol R ν c n0 (J \ riseA n0 ν c t) := by
  classical
  intro t
  induction t with
  | zero =>
    intro _ J _
    refine ⟨0, ?_⟩
    have : riseA n0 ν c 0 = ∅ := by
      simp [riseA]
    rw [this]
    simp only [add_zero, pow_zero, Finset.prod_empty, mul_one, one_mul, Finset.sdiff_empty]
    exact kill_Kcol_low n0 (by omega) ν c n0 le_rfl J
  | succ t ih =>
    intro ht J hJ
    have htr : t < r := by omega
    have hjN : n0 + t < N := by omega
    let mt : Fin r := ⟨r - 1 - t, by omega⟩
    have hmt : r - 1 - mt.val = t := by simp only [mt]; omega
    have hval : ∀ m : Fin r, r - 1 - m.val = t → m = mt := by
      intro m hm
      apply Fin.ext
      have := m.isLt
      simp only [mt]; omega
    rw [show n0 + (t + 1) = n0 + t + 1 by ring, Kcol_succ ν c (n0 + t) hjN, kill_colStep]
    by_cases hr : rises ν c (n0 + t)
    · have hA : riseA n0 ν c (t + 1) = insert mt (riseA n0 ν c t) := by
        ext m
        simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases h3 : r - 1 - m.val = t
          · exact Or.inl (hval m h3)
          · exact Or.inr ⟨by omega, h2⟩
        · rintro (h | ⟨h1, h2⟩)
          · subst h
            rw [hmt]; exact ⟨by omega, hr⟩
          · exact ⟨by omega, h2⟩
      have hnot : mt ∉ riseA n0 ν c t := by
        simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro h; rw [hmt] at h; omega
      have hmJ : mt ∈ J := hJ (by rw [hA]; exact Finset.mem_insert_self _ _)
      have hsub : riseA n0 ν c t ⊆ J.erase mt := by
        intro m hm
        refine Finset.mem_erase.mpr ⟨fun h => hnot (h ▸ hm), hJ (by rw [hA]; exact Finset.mem_insert_of_mem hm)⟩
      obtain ⟨e, he⟩ := ih (by omega) (J.erase mt) hsub
      have hstep : colStep c (colH (stg ν (n0 + t)) c) (colH (stg ν (n0 + t + 1)) c)
          (fun m => kill (offN n0) (letVec R (N := N) (n := r) ⟨n0 + t, hjN⟩ m))
          (fun J => kill (offN n0) (Kcol R ν c (n0 + t) J)) J =
          (-1) ^ (J.filter fun j => mt < j).card * MvPolynomial.X (tauI n0 hN mt, mt) *
            kill (offN n0) (Kcol R ν c (n0 + t) (J.erase mt)) := by
        have hr' : colH (stg ν (n0 + t)) c < colH (stg ν (n0 + t + 1)) c := hr
        unfold colStep
        rw [if_pos hr', if_pos hc]
        unfold wedgeR
        rw [Finset.sum_eq_single mt]
        · congr 2
          have : (tauI n0 hN mt : Fin N) = ⟨n0 + t, hjN⟩ := by
            apply Fin.ext; simp only [tauI]; omega
          rw [this]
          apply kill_X_not
          intro hv
          apply hv.2
          simp only [mt]; omega
        · intro m _ hm
          have : kill (offN n0) (letVec R (N := N) (n := r) ⟨n0 + t, hjN⟩ m) = 0 := by
            apply kill_X_mem
            refine ⟨by simp, ?_⟩
            intro h
            apply hm
            apply hval
            simp only [add_tsub_cancel_left] at h
            omega
          beta_reduce
          rw [this]; ring
        · intro h; exact absurd hmJ h
      rw [hstep, he, hA, Finset.prod_insert hnot]
      refine ⟨(J.filter fun j => mt < j).card + e, ?_⟩
      have hset : J.erase mt \ riseA n0 ν c t = J \ insert mt (riseA n0 ν c t) := by
        ext m
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
        tauto
      rw [hset, pow_add]
      ring
    · have hA : riseA n0 ν c (t + 1) = riseA n0 ν c t := by
        ext m
        simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases h3 : r - 1 - m.val = t
          · rw [h3] at h2; exact absurd h2 hr
          · exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
      have heq : colH (stg ν (n0 + t)) c = colH (stg ν (n0 + t + 1)) c :=
        le_antisymm (hmono t htr) (not_lt.mp hr)
      rw [hA] at hJ ⊢
      obtain ⟨e, he⟩ := ih (by omega) J hJ
      refine ⟨e, ?_⟩
      unfold colStep
      rw [heq, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
      exact he

end Abs

end Formalism.MainNotions.SelectionLemmas.Pf
