import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace

namespace Formalism.FourierDecayAlt.P.Fr2

section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact h0`. Consider the case `cons l w ih`. Establish `hl` using `h l (by simp)`. Establish `ih'` using `ih (fun l' hl' => h l' (by simp [hl']))`.

Distinguish the cases in `hp : l.plus`. Simplify using `only [ofWord, hp, if_true, FrameData.plus]`. Conclude with `⟨ih', hl.1, hl.2.1⟩`. Simplify using `only [ofWord, hp, FrameData.minus]`. Use `⟨ih', ?_, ?_⟩` and prove the remaining obligations.

Introduce `e`. Apply `hl.1` to reduce the goal to its premises. Take the linear combination `-e`. Introduce `e`. Apply `hl.2.2` to reduce the goal to its premises.

Take the linear combination `-e`.
-/
lemma mem_inv (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) (Y : ℂ)
    (h0 : Y ∈ st.inv) (h : ∀ l ∈ w, Y - l.pt ≠ 0 ∧ Y - l.pt ≠ 1 ∧ Y - l.pt ≠ -1) :
    Y ∈ (ofWord L st w).inv := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    by_cases hp : l.plus
    · simp only [ofWord, hp, if_true, FrameData.plus]
      exact ⟨ih', hl.1, hl.2.1⟩
    · simp only [ofWord, hp, FrameData.minus]
      refine ⟨ih', ?_, ?_⟩
      · intro e; apply hl.1; linear_combination -e
      · intro e; apply hl.2.2; linear_combination -e

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact h0`. Consider the case `cons l w ih`. Establish `hl` using `h l (by simp)`. Establish `ih'` using `ih (fun l' hl' => h l' (by simp [hl']))`.

Distinguish the cases in `hp : l.plus`. Simplify using `only [qw, hp, if_true]`. Use `mul_ne_zero ih' (div_ne_zero ?_ hl.1)` and prove the remaining obligations. Introduce `e`. Apply `hl.2` to reduce the goal to its premises.

Take the linear combination `e`. Simplify using `only [qw, hp]`. Use `mul_ne_zero ih' (div_ne_zero ?_ ?_)` and prove the remaining obligations. Introduce `e`. Apply `hl.1` to reduce the goal to its premises.

Take the linear combination `-e`. Introduce `e`. Apply `hl.2` to reduce the goal to its premises. Take the linear combination `-e`.
-/
lemma qw_ne (q : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (h0 : q Y ≠ 0)
    (h : ∀ l ∈ w, Y - l.pt ≠ 0 ∧ Y - l.pt ≠ -1) : qw q w Y ≠ 0 := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    by_cases hp : l.plus
    · simp only [qw, hp, if_true]
      refine mul_ne_zero ih' (div_ne_zero ?_ hl.1)
      intro e; apply hl.2; linear_combination e
    · simp only [qw, hp]
      refine mul_ne_zero ih' (div_ne_zero ?_ ?_)
      · intro e; apply hl.1; linear_combination -e
      · intro e; apply hl.2; linear_combination -e
end

/- English proof (translation)
Introduce `A S _ _ _ _ _ _ r L st w hL hst hA`. Proceed by induction on `w with`. Consider the case `nil => exact hS hM A S r L st hst`. Consider the case `cons l w ih`. Take `⟨hnd, hre, hpt, hpw⟩` from `hA`.

Establish `hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup` using `List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)`. Establish `hpw'` using `List.pairwise_cons.mp hpw`. Establish `hAw : admitted st w` using `⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩`. Establish `ihw` using `ih hAw`. Establish `hfree` using `hF A S r L st w l.intersection_update_fsHerm_neg_one hnd'.1`.

Take `⟨p0, p1, pm1, q0, qm1⟩` from `hpt l (by simp)`. Establish `hd` using `hpw'.1`. Establish `hq` using `(hW A S r L st w).2.2.1`. Establish `m0 : l.pt ∈ (ofWord L st w).inv` using `mem_inv L st w _ p0 (fun l' hl' => ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)`. Establish `m1 : l.pt + 1 ∈ (ofWord L st w).inv` using `mem_inv L st w _ p1 (fun l' hl' => ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e)⟩)`.

Establish `mm1 : l.pt - 1 ∈ (ofWord L st w).inv` using `mem_inv L st w _ pm1 (fun l' hl' => ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)`. Distinguish the cases in `hp : l.plus`. Establish `e : ofWord L st (l :: w) = (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt` using `by simp [ofWord, hp]`. Rewrite using `[e]`. Apply `hP` to reduce the goal to its premises.

Use `⟨hL, ihw, hfree, hre l (by simp), m0, m1, ?_⟩` and prove the remaining obligations. Rewrite using `[hq]`. Conclude with `qw_ne _ _ _ q0 (fun l' hl' => ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)`. Establish `e : ofWord L st (l :: w) = (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt` using `by simp [ofWord, hp]`. Rewrite using `[e]`.

Apply `hMi` to reduce the goal to its premises. Use `⟨hL, ihw, hfree, hre l (by simp), m0, m1, mm1, ?_⟩` and prove the remaining obligations. Rewrite using `[hq]`. Conclude with `qw_ne _ _ _ qm1 (fun l' hl' => ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)`.
-/
theorem frameAll (hS : StartFrame) (hM : StartModule) (hP : PlusStep) (hMi : MinusStep)
    (hF : FrameFree) (hW : WordJoint) : FrameAll := by
  intro A S _ _ _ _ _ _ r L st w hL hst hA
  induction w with
  | nil => exact hS hM A S r L st hst
  | cons l w ih =>
    obtain ⟨hnd, hre, hpt, hpw⟩ := hA
    have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup := List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    have hpw' := List.pairwise_cons.mp hpw
    have hAw : admitted st w :=
      ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
    have ihw := ih hAw
    have hfree := hF A S r L st w l.intersection_update_fsHerm_neg_one hnd'.1
    obtain ⟨p0, p1, pm1, q0, qm1⟩ := hpt l (by simp)
    have hd := hpw'.1
    have hq := (hW A S r L st w).2.2.1
    have m0 : l.pt ∈ (ofWord L st w).inv := mem_inv L st w _ p0 (fun l' hl' =>
      ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    have m1 : l.pt + 1 ∈ (ofWord L st w).inv := mem_inv L st w _ p1 (fun l' hl' =>
      ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e)⟩)
    have mm1 : l.pt - 1 ∈ (ofWord L st w).inv := mem_inv L st w _ pm1 (fun l' hl' =>
      ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
    by_cases hp : l.plus
    · have e : ofWord L st (l :: w) = (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e]
      apply hP
      refine ⟨hL, ihw, hfree, hre l (by simp), m0, m1, ?_⟩
      rw [hq]
      exact qw_ne _ _ _ q0 (fun l' hl' =>
        ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    · have e : ofWord L st (l :: w) = (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e]
      apply hMi
      refine ⟨hL, ihw, hfree, hre l (by simp), m0, m1, mm1, ?_⟩
      rw [hq]
      exact qw_ne _ _ _ qm1 (fun l' hl' =>
        ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)

/- English proof (translation)
Introduce `hS hM hP hMi hF hW`. Establish `hA` using `frameAll hS hM hP hMi hF hW`. Use `⟨hA, ?_⟩` and prove the remaining obligations. Introduce `A S _ _ _ _ _ _ r L st w hL hst hAd`. Establish `h` using `hA A S r L st w hL hst hAd`.

Take `⟨w1, w2, w3, w4, w5⟩` from `hW A S r L st w`. Use `⟨h.F_Fi, h.Fi_F, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `h.form` as an intermediate fact. Rewrite `this` using `[w1]`. Rewrite using `[this]`.

Simplify using `only [FrameData.d, w4]`. Introduce `Y hY`. Use `h.frame_τ Y (by rw [w5]; exact hY)` as an intermediate fact. Rewrite `this` using `[w2]`. Conclude with `this`.

Introduce `Y hY hY1`. Use `h.frame_l Y hY hY1` as an intermediate fact. Rewrite `this` using `[w2]`. Conclude with `this`.
-/
theorem frameAssemble : FrameAssemble := by
  intro hS hM hP hMi hF hW
  have hA := frameAll hS hM hP hMi hF hW
  refine ⟨hA, ?_⟩
  intro A S _ _ _ _ _ _ r L st w hL hst hAd
  have h := hA A S r L st w hL hst hAd
  obtain ⟨w1, w2, w3, w4, w5⟩ := hW A S r L st w
  refine ⟨h.F_Fi, h.Fi_F, ?_, ?_, ?_⟩
  · have := h.form
    rw [w1] at this
    rw [this]; simp only [FrameData.d, w4]
  · intro Y hY
    have := h.frame_τ Y (by rw [w5]; exact hY)
    rw [w2] at this; exact this
  · intro Y hY hY1
    have := h.frame_l Y hY hY1
    rw [w2] at this; exact this

section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons l w ih`. Distinguish the cases in `hp : l.plus`. Use function extensionality and compare the values at `Y`.

Simplify using `[ofWord, qw, hp, FrameData.plus, ih]`. Use function extensionality and compare the values at `Y`. Simplify using `[ofWord, qw, hp, FrameData.minus, ih]`.
-/
lemma q_eq (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) : (ofWord L st w).q = qw st.q w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    by_cases hp : l.plus
    · funext Y; simp [ofWord, qw, hp, FrameData.plus, ih]
    · funext Y; simp [ofWord, qw, hp, FrameData.minus, ih]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact h0`. Consider the case `cons l w ih`. Establish `hl` using `h l (by simp)`. Establish `ih'` using `ih (fun l' hl' => h l' (by simp [hl']))`.

Distinguish the cases in `hp : l.plus`. Simplify using `only [ypt, hp, if_true] at hl`. Simplify using `only [ofWord, hp, if_true, FrameData.plus]`. Conclude with `⟨ih', hl.1, hl.2⟩`. Simplify using `only [ypt, hp] at hl`.

Simplify using `only [ofWord, hp, FrameData.minus]`. Use `⟨ih', ?_, ?_⟩` and prove the remaining obligations. Introduce `e`. Apply `hl.2` to reduce the goal to its premises. Simplify using `only [Bool.false_eq_true, if_false]`.

Take the linear combination `-e`. Introduce `e`. Apply `hl.1` to reduce the goal to its premises. Simplify using `only [Bool.false_eq_true, if_false]`. Take the linear combination `-e`.
-/
lemma mem_invB (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) (Y : ℂ)
    (h0 : Y ∈ st.inv) (h : ∀ l ∈ w, Y - ypt l ≠ 0 ∧ Y - ypt l ≠ 1) :
    Y ∈ (ofWord L st w).inv := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    by_cases hp : l.plus
    · simp only [ypt, hp, if_true] at hl
      simp only [ofWord, hp, if_true, FrameData.plus]
      exact ⟨ih', hl.1, hl.2⟩
    · simp only [ypt, hp] at hl
      simp only [ofWord, hp, FrameData.minus]
      refine ⟨ih', ?_, ?_⟩
      · intro e; apply hl.2; simp only [Bool.false_eq_true, if_false]; linear_combination -e
      · intro e; apply hl.1; simp only [Bool.false_eq_true, if_false]; linear_combination -e

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact h0`. Consider the case `cons l w ih`. Establish `hl` using `h l (by simp)`. Establish `ih'` using `ih (fun l' hl' => h l' (by simp [hl']))`.

Distinguish the cases in `hp : l.plus`. Simplify using `only [ypt, hp, if_true] at hl`. Simplify using `only [qw, hp, if_true]`. Use `mul_ne_zero ih' (div_ne_zero ?_ hl.1)` and prove the remaining obligations. Introduce `e`.

Apply `hl.2.2` to reduce the goal to its premises. Take the linear combination `e`. Simplify using `only [ypt, hp] at hl`. Simplify using `only [qw, hp]`. Use `mul_ne_zero ih' (div_ne_zero ?_ ?_)` and prove the remaining obligations.

Introduce `e`. Apply `hl.2.1` to reduce the goal to its premises. Simplify using `only [Bool.false_eq_true, if_false]`. Take the linear combination `-e`. Introduce `e`.

Apply `hl.1` to reduce the goal to its premises. Simplify using `only [Bool.false_eq_true, if_false]`. Take the linear combination `-e`.
-/
lemma qw_neB (q : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (h0 : q Y ≠ 0)
    (h : ∀ l ∈ w, Y - ypt l ≠ 0 ∧ Y - ypt l ≠ 1 ∧ Y - ypt l ≠ -1) : qw q w Y ≠ 0 := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    by_cases hp : l.plus
    · simp only [ypt, hp, if_true] at hl
      simp only [qw, hp, if_true]
      refine mul_ne_zero ih' (div_ne_zero ?_ hl.1)
      intro e; apply hl.2.2; linear_combination e
    · simp only [ypt, hp] at hl
      simp only [qw, hp]
      refine mul_ne_zero ih' (div_ne_zero ?_ ?_)
      · intro e; apply hl.2.1; simp only [Bool.false_eq_true, if_false]; linear_combination -e
      · intro e; apply hl.1; simp only [Bool.false_eq_true, if_false]; linear_combination -e
end

/- English proof (translation)
Introduce `A S _ _ _ _ _ _ r L st w hA`. Proceed by induction on `w with`. Consider the case `nil => trivial`. Consider the case `cons l w ih`. Take `⟨hnd, hre, hpt, hpw⟩` from `hA`.

Establish `hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup` using `List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)`. Establish `hpw'` using `List.pairwise_cons.mp hpw`. Establish `hAw : admitted st w` using `⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩`. Take `⟨p0, p1, pm1, q0, qm1⟩` from `hpt l (by simp)`. Establish `hd` using `hpw'.1`.

Establish `m0 : l.pt ∈ (ofWord L st w).inv` using `mem_inv L st w _ p0 (fun l' hl' => ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)`. Establish `m1 : l.pt + 1 ∈ (ofWord L st w).inv` using `mem_inv L st w _ p1 (fun l' hl' => ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e)⟩)`. Establish `mm1 : l.pt - 1 ∈ (ofWord L st w).inv` using `mem_inv L st w _ pm1 (fun l' hl' => ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)`. Use `⟨ih hAw, hnd'.1, hre l (by simp), m0, m1, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hp : l.plus`.

Simplify using `only [hp, if_true]`. Rewrite using `[q_eq]`. Conclude with `qw_ne _ _ _ q0 (fun l' hl' => ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)`. Simplify using `only [hp]`. Use `⟨mm1, ?_⟩` and prove the remaining obligations.

Rewrite using `[q_eq]`. Conclude with `qw_ne _ _ _ qm1 (fun l' hl' => ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)`.
-/
theorem admissible_rec_of_admissible_word : AdmRecOfAdm := by
  intro A S _ _ _ _ _ _ r L st w hA
  induction w with
  | nil => trivial
  | cons l w ih =>
    obtain ⟨hnd, hre, hpt, hpw⟩ := hA
    have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup :=
      List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    have hpw' := List.pairwise_cons.mp hpw
    have hAw : admitted st w :=
      ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
    obtain ⟨p0, p1, pm1, q0, qm1⟩ := hpt l (by simp)
    have hd := hpw'.1
    have m0 : l.pt ∈ (ofWord L st w).inv := mem_inv L st w _ p0 (fun l' hl' =>
      ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    have m1 : l.pt + 1 ∈ (ofWord L st w).inv := mem_inv L st w _ p1 (fun l' hl' =>
      ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e)⟩)
    have mm1 : l.pt - 1 ∈ (ofWord L st w).inv := mem_inv L st w _ pm1 (fun l' hl' =>
      ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
    refine ⟨ih hAw, hnd'.1, hre l (by simp), m0, m1, ?_⟩
    by_cases hp : l.plus
    · simp only [hp, if_true]
      rw [q_eq]
      exact qw_ne _ _ _ q0 (fun l' hl' =>
        ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    · simp only [hp]
      refine ⟨mm1, ?_⟩
      rw [q_eq]
      exact qw_ne _ _ _ qm1 (fun l' hl' =>
        ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)

/- English proof (translation)
Introduce `A S _ _ _ _ _ _ r L st w hA`. Proceed by induction on `w with`. Consider the case `nil => trivial`. Consider the case `cons l w ih`. Take `⟨hnd, hre, hpt, hpw⟩` from `hA`.

Establish `hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup` using `List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)`. Establish `hpw'` using `List.pairwise_cons.mp hpw`. Establish `hAw : AdmBase st w` using `⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩`. Take `⟨p0, p1, p2, q0⟩` from `hpt l (by simp)`. Establish `hd` using `hpw'.1`.

Establish `m0 : ypt l ∈ (ofWord L st w).inv` using `mem_invB L st w _ p0 (fun l' hl' => ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e)⟩)`. Establish `m1 : ypt l + 1 ∈ (ofWord L st w).inv` using `mem_invB L st w _ p1 (fun l' hl' => ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)`. Establish `m2 : l.plus = false → ypt l + 2 ∈ (ofWord L st w).inv` using `fun hf => mem_invB L st w _ (p2 hf) (fun l' hl' => ⟨fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)`. Establish `qq : (ofWord L st w).q (ypt l) ≠ 0`. Rewrite using `[q_eq]`.

Conclude with `qw_neB _ _ _ q0 (fun l' hl' => ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e), fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)`. Distinguish the cases in `hp : l.plus`. Simplify using `only [ypt, hp, if_true] at m0 m1 qq`. Use `⟨ih hAw, hnd'.1, hre l (by simp), m0, m1, ?_⟩` and prove the remaining obligations. Simplify using `only [hp, if_true]`.

Conclude with `qq`. Establish `hf : l.plus = false` using `by simpa using hp`. Establish `m2'` using `m2 hf`. Simplify using `only [ypt, hf, Bool.false_eq_true, if_false] at m0 m1 m2' qq`. Use `⟨ih hAw, hnd'.1, hre l (by simp), ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `: l.pt - 1 + 1 = l.pt` using `by ring`. Rewrite `m1` using `[this]`. Then use the resulting hypothesis. Establish `: l.pt - 1 + 2 = l.pt + 1` using `by ring`. Rewrite `m2'` using `[this]`. Then use the resulting hypothesis. Simplify using `only [hf, Bool.false_eq_true, if_false]`.

Conclude with `⟨m0, qq⟩`.
-/
theorem admissible_rec_of_base : AdmRecOfBase := by
  intro A S _ _ _ _ _ _ r L st w hA
  induction w with
  | nil => trivial
  | cons l w ih =>
    obtain ⟨hnd, hre, hpt, hpw⟩ := hA
    have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup :=
      List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    have hpw' := List.pairwise_cons.mp hpw
    have hAw : AdmBase st w :=
      ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
    obtain ⟨p0, p1, p2, q0⟩ := hpt l (by simp)
    have hd := hpw'.1
    have m0 : ypt l ∈ (ofWord L st w).inv := mem_invB L st w _ p0 (fun l' hl' =>
      ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e)⟩)
    have m1 : ypt l + 1 ∈ (ofWord L st w).inv := mem_invB L st w _ p1 (fun l' hl' =>
      ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
    have m2 : l.plus = false → ypt l + 2 ∈ (ofWord L st w).inv := fun hf => mem_invB L st w _ (p2 hf) (fun l' hl' =>
      ⟨fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    have qq : (ofWord L st w).q (ypt l) ≠ 0 := by
      rw [q_eq]
      exact qw_neB _ _ _ q0 (fun l' hl' =>
        ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    by_cases hp : l.plus
    · simp only [ypt, hp, if_true] at m0 m1 qq
      refine ⟨ih hAw, hnd'.1, hre l (by simp), m0, m1, ?_⟩
      simp only [hp, if_true]; exact qq
    · have hf : l.plus = false := by simpa using hp
      have m2' := m2 hf
      simp only [ypt, hf, Bool.false_eq_true, if_false] at m0 m1 m2' qq
      refine ⟨ih hAw, hnd'.1, hre l (by simp), ?_, ?_, ?_⟩
      · have : l.pt - 1 + 1 = l.pt := by ring
        rwa [this] at m1
      · have : l.pt - 1 + 2 = l.pt + 1 := by ring
        rwa [this] at m2'
      · simp only [hf, Bool.false_eq_true, if_false]; exact ⟨m0, qq⟩

/- English proof (translation)
Introduce `h0 hm hp hn hf A S _ _ _ _ _ _ r L st w hL hs`. Proceed by induction on `w with`. Consider the case `nil => intro _`. Conclude with `h0 hm A S r L st hs`. Consider the case `cons l w ih`.

Introduce and unpack `⟨h1, h2, h3, h4, h5, h6⟩`. Establish `hw` using `ih h1`. Establish `hfr` using `hf A S r L st w l.intersection_update_fsHerm_neg_one h2`. Distinguish the cases in `hl : l.plus`. Simplify using `only [hl, if_true] at h6`.

Simplify using `only [ofWord, hl, if_true]`. Conclude with `hp A S r L _ l.intersection_update_fsHerm_neg_one l.pt ⟨hL, hw, hfr, h3, h4, h5, h6⟩`. Simplify using `only [hl] at h6`. Simplify using `only [ofWord, hl]`. Conclude with `hn A S r L _ l.intersection_update_fsHerm_neg_one l.pt ⟨hL, hw, hfr, h3, h4, h5, h6.1, h6.2⟩`.
-/
theorem frameRecAssemble : FrameRecAssemble := by
  intro h0 hm hp hn hf A S _ _ _ _ _ _ r L st w hL hs
  induction w with
  | nil => intro _; exact h0 hm A S r L st hs
  | cons l w ih =>
    rintro ⟨h1, h2, h3, h4, h5, h6⟩
    have hw := ih h1
    have hfr := hf A S r L st w l.intersection_update_fsHerm_neg_one h2
    by_cases hl : l.plus
    · simp only [hl, if_true] at h6
      simp only [ofWord, hl, if_true]
      exact hp A S r L _ l.intersection_update_fsHerm_neg_one l.pt ⟨hL, hw, hfr, h3, h4, h5, h6⟩
    · simp only [hl] at h6
      simp only [ofWord, hl]
      exact hn A S r L _ l.intersection_update_fsHerm_neg_one l.pt ⟨hL, hw, hfr, h3, h4, h5, h6.1, h6.2⟩

section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

/- English proof (translation)
Use extensionality with `x y`. Distinguish the cases in `hxy : x = y`. Substitute `hxy` using the available equality. Simplify using `[eU]`. Establish `: ¬ (x a = i ∧ y a = i ∧ ∀ b, b ≠ a → x b = y b)`.

Introduce and unpack `⟨h1, h2, h3⟩`. Apply `hxy` to reduce the goal to its premises. Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality.

Rewrite using `[h1, h2]`. Conclude with `h3 b hb`. Simplify using `[eU, Matrix.diagonal_apply_ne _ hxy, this]`.
-/
lemma eU_diag (a : S) (i : Fin 2) :
    (eU a i i : SlopeTestRemainingChoices S A) = Matrix.diagonal (fun e => if e a = i then 1 else 0) := by
  ext x y
  by_cases hxy : x = y
  · subst hxy; simp [eU]
  · have : ¬ (x a = i ∧ y a = i ∧ ∀ b, b ≠ a → x b = y b) := by
      rintro ⟨h1, h2, h3⟩
      apply hxy; funext b
      by_cases hb : b = a
      · subst hb; rw [h1, h2]
      · exact h3 b hb
    simp [eU, Matrix.diagonal_apply_ne _ hxy, this]

/- English proof (translation)
Simplify using `only [ins, Fin.sum_univ_two, eU_diag]`. Simplify using `only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one, mul_zero, add_zero, zero_add, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]`. Use `congr 1`. Use function extensionality and compare the values at `e`. Distinguish the cases in `h : e a = 0`.

Simplify using `[h]`. Establish `h1 : e a = 1` using `Fin.eq_one_of_ne_zero _ h`. Simplify using `[h1]`.
-/
lemma ins_diag (a : S) (X Y : Ix S → A) :
    ins a !![Matrix.diagonal X, 0; 0, Matrix.diagonal Y] =
      Matrix.diagonal (fun e => if e a = 0 then X e else Y e) := by
  simp only [ins, Fin.sum_univ_two, eU_diag]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one,
    mul_zero, add_zero, zero_add, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
  congr 1; funext e
  by_cases h : e a = 0
  · simp [h]
  · have h1 : e a = 1 := Fin.eq_one_of_ne_zero _ h
    simp [h1]

/- English proof (translation)
Establish `h1 : (φ • (1 : SlopeTestRemainingChoices S A)) = Matrix.diagonal (fun _ => algebraMap ℂ A φ)`. Rewrite using `[← Matrix.diagonal_one, ← Matrix.diagonal_smul]`. Use `congr 1`. Use function extensionality and compare the values at `_`. Simplify using `[Algebra.algebraMap_eq_smul_one]`.

Establish `h2 : (1 : SlopeTestRemainingChoices S A) = Matrix.diagonal (fun _ => (1 : A))` using `Matrix.diagonal_one.symm`. Rewrite using `[h1]`. Use `conv_lhs => rw [h2]`. Conclude with `ins_diag a _ _`.
-/
lemma ins_sc (a : S) (φ : ℂ) :
    (ins a !![φ • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] : SlopeTestRemainingChoices S A) =
      Matrix.diagonal (fun e => if e a = 0 then algebraMap ℂ A φ else 1) := by
  have h1 : (φ • (1 : SlopeTestRemainingChoices S A)) = Matrix.diagonal (fun _ => algebraMap ℂ A φ) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul]; congr 1; funext _
    simp [Algebra.algebraMap_eq_smul_one]
  have h2 : (1 : SlopeTestRemainingChoices S A) = Matrix.diagonal (fun _ => (1 : A)) := Matrix.diagonal_one.symm
  rw [h1]; conv_lhs => rw [h2]
  exact ins_diag a _ _
end

/- English proof (translation)
Introduce `A S _ _ _ _ _ _ r L st P κ x0 hx hxi w`. Establish `km : ∀ f g : P → ℂ, κ f * κ g = κ (fun ρ => f ρ * g ρ)` using `fun f g => (map_mul κ f g).symm`. Establish `kc : ∀ c : ℂ, algebraMap ℂ A c = κ (fun _ => c)` using `fun c => (AlgHom.commutes κ c).symm`. Establish `ks : ∀ (c : ℂ) (f : P → ℂ), c • κ f = κ (fun ρ => c * f ρ)` using `fun c f => (map_smul κ c f).symm`. Establish `k1 : (1 : A) = κ (fun _ => 1)` using `(map_one κ).symm`.

Proceed by induction on `w with`. Consider the case `nil`. Use `⟨fun Y => ?_, fun Y => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[ofWord, Start.frame, io, xs, hx, Matrix.scalar_apply]`. Simplify using `[ofWord, Start.frame, io, xs, hxi, Matrix.scalar_apply]`.

Simplify using `only [ofWord, Start.frame, cs, ← k1, Matrix.diagonal_one]`. Consider the case `cons l w ih`. Take `⟨ihx, ihxi, ihc⟩` from `ih`. Establish `hq : (ofWord L st w).q = qw st.q w` using `by clear ihx ihxi ihc`. Proceed by induction on `w with`.

Consider the case `nil => rfl`. Consider the case `cons l' w ih'`. Distinguish the cases in `hl : l'.plus`. Use function extensionality and compare the values at `Y`. Simplify using `[ofWord, hl, FrameData.plus, qw, ih']`.

Use function extensionality and compare the values at `Y`. Simplify using `[ofWord, hl, FrameData.minus, qw, ih']`. Distinguish the cases in `hp : l.plus`. Use `⟨fun Y => ?_, fun Y => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [ofWord, hp, if_true, FrameData.plus, ihx, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]`.

Use `congr 1`. Use function extensionality and compare the values at `e`. Apply the tactic sequence `split_ifs <;> simp [kc, km]`. Simplify using `only [ofWord, hp, if_true, FrameData.plus, ihxi, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]`. Use `congr 1`.

Use function extensionality and compare the values at `e`. Apply the tactic sequence `split_ifs <;> simp [kc, km, inv_div, mul_comm]`. Simplify using `only [ofWord, hp, if_true, FrameData.plus, ihx, ihxi, ihc, hq, ← Matrix.diagonal_smul, ins_diag, Matrix.diagonal_mul_diagonal, cs]`. Use `congr 1`. Use function extensionality and compare the values at `e`.

Apply the tactic sequence `split_ifs <;> simp [ks, km, div_eq_mul_inv]`. Establish `hp' : l.plus = false` using `by simpa using hp`. Use `⟨fun Y => ?_, fun Y => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [ofWord, hp', Bool.false_eq_true, if_false, FrameData.minus, ihx, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]`. Use `congr 1`.

Use function extensionality and compare the values at `e`. Apply the tactic sequence `split_ifs <;> simp [kc, km]`. Simplify using `only [ofWord, hp', Bool.false_eq_true, if_false, FrameData.minus, ihxi, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]`. Use `congr 1`. Use function extensionality and compare the values at `e`.

Apply the tactic sequence `split_ifs <;> simp [kc, km, inv_div, mul_comm]`. Simplify using `only [ofWord, hp', Bool.false_eq_true, if_false, FrameData.minus, ihx, ihxi, ihc, hq, ← Matrix.diagonal_smul, ins_diag, Matrix.diagonal_mul_diagonal, cs]`. Use `congr 1`. Use function extensionality and compare the values at `e`. Apply the tactic sequence `split_ifs <;> simp [ks, km, div_eq_mul_inv]`.
-/
theorem cDiag : CDiag := by
  intro A S _ _ _ _ _ _ r L st P κ x0 hx hxi w
  have km : ∀ f g : P → ℂ, κ f * κ g = κ (fun ρ => f ρ * g ρ) := fun f g => (map_mul κ f g).symm
  have kc : ∀ c : ℂ, algebraMap ℂ A c = κ (fun _ => c) := fun c => (AlgHom.commutes κ c).symm
  have ks : ∀ (c : ℂ) (f : P → ℂ), c • κ f = κ (fun ρ => c * f ρ) := fun c f => (map_smul κ c f).symm
  have k1 : (1 : A) = κ (fun _ => 1) := (map_one κ).symm
  induction w with
  | nil =>
    refine ⟨fun Y => ?_, fun Y => ?_, ?_⟩
    · simp [ofWord, Start.frame, io, xs, hx, Matrix.scalar_apply]
    · simp [ofWord, Start.frame, io, xs, hxi, Matrix.scalar_apply]
    · simp only [ofWord, Start.frame, cs, ← k1, Matrix.diagonal_one]
  | cons l w ih =>
    obtain ⟨ihx, ihxi, ihc⟩ := ih
    have hq : (ofWord L st w).q = qw st.q w := by
      clear ihx ihxi ihc
      induction w with
      | nil => rfl
      | cons l' w ih' =>
        by_cases hl : l'.plus
        · funext Y; simp [ofWord, hl, FrameData.plus, qw, ih']
        · funext Y; simp [ofWord, hl, FrameData.minus, qw, ih']
    by_cases hp : l.plus
    · refine ⟨fun Y => ?_, fun Y => ?_, ?_⟩
      · simp only [ofWord, hp, if_true, FrameData.plus, ihx, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]
        congr 1; funext e
        split_ifs <;> simp [kc, km]
      · simp only [ofWord, hp, if_true, FrameData.plus, ihxi, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]
        congr 1; funext e
        split_ifs <;> simp [kc, km, inv_div, mul_comm]
      · simp only [ofWord, hp, if_true, FrameData.plus, ihx, ihxi, ihc, hq, ← Matrix.diagonal_smul, ins_diag,
          Matrix.diagonal_mul_diagonal, cs]
        congr 1; funext e
        split_ifs <;> simp [ks, km, div_eq_mul_inv]
    · have hp' : l.plus = false := by simpa using hp
      refine ⟨fun Y => ?_, fun Y => ?_, ?_⟩
      · simp only [ofWord, hp', Bool.false_eq_true, if_false, FrameData.minus, ihx, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]
        congr 1; funext e
        split_ifs <;> simp [kc, km]
      · simp only [ofWord, hp', Bool.false_eq_true, if_false, FrameData.minus, ihxi, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]
        congr 1; funext e
        split_ifs <;> simp [kc, km, inv_div, mul_comm]
      · simp only [ofWord, hp', Bool.false_eq_true, if_false, FrameData.minus, ihx, ihxi, ihc, hq, ← Matrix.diagonal_smul, ins_diag,
          Matrix.diagonal_mul_diagonal, cs]
        congr 1; funext e
        split_ifs <;> simp [ks, km, div_eq_mul_inv]

/- English proof (translation)
Take `⟨a1, a2⟩` from `ha`. Take `⟨b1, b2⟩` from `hb`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `[Complex.mul_re, a2, b2]`. Check the signs of the components of the expression.

Simplify using `[Complex.mul_im, a2, b2]`.
-/
lemma pos_mul {a b : ℂ} (ha : Pos a) (hb : Pos b) : Pos (a * b) := by
  obtain ⟨a1, a2⟩ := ha; obtain ⟨b1, b2⟩ := hb
  refine ⟨?_, ?_⟩
  · simp [Complex.mul_re, a2, b2]; positivity
  · simp [Complex.mul_im, a2, b2]

/- English proof (translation)
Assemble the required witnesses or components as `⟨by simpa using h, by simp⟩`.
-/
lemma pos_ofReal {x : ℝ} (h : 0 < x) : Pos (x : ℂ) := ⟨by simpa using h, by simp⟩

/- English proof (translation)
Apply the tactic sequence `apply Complex.ext <;> simp [ha.2]`.
-/
lemma pos_eq {a : ℂ} (ha : Pos a) : a = (a.re : ℂ) := by
  apply Complex.ext <;> simp [ha.2]

/- English proof (translation)
Rewrite using `[pos_eq ha, pos_eq hb, ← Complex.ofReal_div]`. Conclude with `pos_ofReal (div_pos ha.1 hb.1)`.
-/
lemma pos_div {a b : ℂ} (ha : Pos a) (hb : Pos b) : Pos (a / b) := by
  rw [pos_eq ha, pos_eq hb, ← Complex.ofReal_div]
  exact pos_ofReal (div_pos ha.1 hb.1)

/- English proof (translation)
Apply the tactic sequence `have e : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]`. Rewrite using `[e, ← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_div]`. Apply `pos_ofReal` to reduce the goal to its premises. Establish `hb : z.re + b ≠ 0` using `by intro h0; simp [h0] at h`. Establish `: (z.re + a) / (z.re + b) = (z.re + a) * (z.re + b) / (z.re + b) ^ 2`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Check the signs of the components of the expression.
-/
lemma frac (z : ℂ) (hz : z.im = 0) (a b : ℝ) (h : 0 < (z.re + a) * (z.re + b)) :
    Pos ((z + a) / (z + b)) := by
  have e : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [e, ← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_div]
  apply pos_ofReal
  have hb : z.re + b ≠ 0 := by intro h0; simp [h0] at h
  have : (z.re + a) / (z.re + b) = (z.re + a) * (z.re + b) / (z.re + b) ^ 2 := by
    field_simp
  rw [this]; positivity

section
variable {S : Type} [Fintype S] [DecidableEq S]

/- English proof (translation)
Break down `lt_abs.mp h with h | h` into its components or cases. Apply the tactic sequence `constructor <;> nlinarith`. Apply the tactic sequence `constructor <;> nlinarith`.
-/
lemma gt1 {t : ℝ} (h : 1 < |t|) : 0 < t * (t - 1) ∧ 0 < t * (t + 1) := by
  rcases lt_abs.mp h with h | h
  · constructor <;> nlinarith
  · constructor <;> nlinarith

/- English proof (translation)
Take `⟨g1, g2⟩` from `gt1 h`. Unfold `phiL`. Use `split_ifs`. Use `frac (Y - l.pt) (by simp [hY, hl]) 0 (-1) (by simp; nlinarith)` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg]`.

Use `frac (l.pt - Y) (by simp [hY, hl]) 0 (-1) (by simp; nlinarith)` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg]`.
-/
lemma phi_pos (l : Letter ℂ S) (Y : ℂ) (hY : Y.im = 0) (hl : l.pt.im = 0) (h : 1 < |Y.re - l.pt.re|) :
    Pos (phiL l Y) := by
  obtain ⟨g1, g2⟩ := gt1 h
  unfold phiL
  split_ifs
  · have := frac (Y - l.pt) (by simp [hY, hl]) 0 (-1) (by simp; nlinarith)
    simpa [sub_eq_add_neg] using this
  · have := frac (l.pt - Y) (by simp [hY, hl]) 0 (-1) (by simp; nlinarith)
    simpa [sub_eq_add_neg] using this

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact h0`. Consider the case `cons l w ih`. Establish `hl` using `h l (by simp)`. Establish `ih'` using `ih (fun l' hl' => h l' (by simp [hl']))`.

Simplify using `only [xs]`. Apply `pos_mul ih'` to reduce the goal to its premises. Use `split_ifs`. Conclude with `phi_pos l Y hY hl.1 hl.2`. Conclude with `⟨by simp, by simp⟩`.
-/
lemma xs_pos (x0 : ℂ → ℂ) (w : List (Letter ℂ S)) (e : Ix S) (Y : ℂ) (hY : Y.im = 0) (h0 : Pos (x0 Y))
    (h : ∀ l ∈ w, l.pt.im = 0 ∧ 1 < |Y.re - l.pt.re|) : Pos (xs x0 w e Y) := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    simp only [xs]
    apply pos_mul ih'
    split_ifs
    · exact phi_pos l Y hY hl.1 hl.2
    · exact ⟨by simp, by simp⟩

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact h0`. Consider the case `cons l w ih`. Establish `hl` using `h l (by simp)`. Establish `ih'` using `ih (fun l' hl' => h l' (by simp [hl']))`.

Take `⟨g1, g2⟩` from `gt1 hl.2`. Simplify using `only [qw]`. Use `split_ifs`. Apply `pos_mul ih'` to reduce the goal to its premises. Use `frac (Y - l.pt) (by simp [hY, hl.1]) 1 0 (by simp; nlinarith)` as an intermediate fact.

Simplify `this` using `[sub_eq_add_neg]`. Apply `pos_mul ih'` to reduce the goal to its premises. Use `frac (l.pt - Y) (by simp [hY, hl.1]) 0 (-1) (by simp; nlinarith)` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg]`.
-/
lemma qw_pos (q0 : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (hY : Y.im = 0) (h0 : Pos (q0 Y))
    (h : ∀ l ∈ w, l.pt.im = 0 ∧ 1 < |Y.re - l.pt.re|) : Pos (qw q0 w Y) := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    obtain ⟨g1, g2⟩ := gt1 hl.2
    simp only [qw]
    split_ifs
    · apply pos_mul ih'
      have := frac (Y - l.pt) (by simp [hY, hl.1]) 1 0 (by simp; nlinarith)
      simpa [sub_eq_add_neg] using this
    · apply pos_mul ih'
      have := frac (l.pt - Y) (by simp [hY, hl.1]) 0 (-1) (by simp; nlinarith)
      simpa [sub_eq_add_neg] using this
end

/- English proof (translation)
Introduce `S _ _ x0 q0 w him hpw hpos e`. Proceed by induction on `w with`. Consider the case `nil => exact ⟨by simp [cs], by simp [cs]⟩`. Consider the case `cons l w ih`. Establish `hpw'` using `List.pairwise_cons.mp hpw`.

Establish `ih'` using `ih (fun l' h => him l' (by simp [h])) hpw'.2 (fun l' h => hpos l' (by simp [h]))`. Take `⟨x1, x2, x3, q1, q2⟩` from `hpos l (by simp)`. Establish `hl` using `him l (by simp)`. Establish `d0 : ∀ l' ∈ w, l'.pt.im = 0 ∧ 1 < |(l.pt).re - l'.pt.re|` using `fun l' h => ⟨him l' (by simp [h]), by have := hpw'.1 l' h; linarith⟩`. Establish `d1 : ∀ l' ∈ w, l'.pt.im = 0 ∧ 1 < |(l.pt + 1).re - l'.pt.re|` using `fun l' h => ⟨him l' (by simp [h]), by`.

Use `hpw'.1 l' h` as an intermediate fact. Simplify using `only [Complex.add_re, Complex.one_re]`. Break down `lt_abs.mp this with g | g` into its components or cases. Conclude with `lt_abs.mpr (Or.inl (by linarith))`. Conclude with `lt_abs.mpr (Or.inr (by linarith))⟩`.

Establish `dm : ∀ l' ∈ w, l'.pt.im = 0 ∧ 1 < |(l.pt - 1).re - l'.pt.re|` using `fun l' h => ⟨him l' (by simp [h]), by`. Use `hpw'.1 l' h` as an intermediate fact. Simplify using `only [Complex.sub_re, Complex.one_re]`. Break down `lt_abs.mp this with g | g` into its components or cases. Conclude with `lt_abs.mpr (Or.inl (by linarith))`.

Conclude with `lt_abs.mpr (Or.inr (by linarith))⟩`. Simplify using `only [cs]`. Apply `pos_mul ih'` to reduce the goal to its premises. Use `split_ifs`. Conclude with `pos_div (qw_pos q0 w _ hl q1 d0) (xs_pos x0 w e _ (by simp [hl]) x2 d1)`.

Conclude with `xs_pos x0 w e _ hl x1 d0`. Conclude with `pos_div (qw_pos q0 w _ (by simp [hl]) q2 dm) (xs_pos x0 w e _ (by simp [hl]) x3 dm)`. Conclude with `xs_pos x0 w e _ hl x1 d0`.
-/
theorem cPos : CPos := by
  intro S _ _ x0 q0 w him hpw hpos e
  induction w with
  | nil => exact ⟨by simp [cs], by simp [cs]⟩
  | cons l w ih =>
    have hpw' := List.pairwise_cons.mp hpw
    have ih' := ih (fun l' h => him l' (by simp [h])) hpw'.2 (fun l' h => hpos l' (by simp [h]))
    obtain ⟨x1, x2, x3, q1, q2⟩ := hpos l (by simp)
    have hl := him l (by simp)
    have d0 : ∀ l' ∈ w, l'.pt.im = 0 ∧ 1 < |(l.pt).re - l'.pt.re| := fun l' h =>
      ⟨him l' (by simp [h]), by have := hpw'.1 l' h; linarith⟩
    have d1 : ∀ l' ∈ w, l'.pt.im = 0 ∧ 1 < |(l.pt + 1).re - l'.pt.re| := fun l' h =>
      ⟨him l' (by simp [h]), by
        have := hpw'.1 l' h
        simp only [Complex.add_re, Complex.one_re]
        rcases lt_abs.mp this with g | g
        · exact lt_abs.mpr (Or.inl (by linarith))
        · exact lt_abs.mpr (Or.inr (by linarith))⟩
    have dm : ∀ l' ∈ w, l'.pt.im = 0 ∧ 1 < |(l.pt - 1).re - l'.pt.re| := fun l' h =>
      ⟨him l' (by simp [h]), by
        have := hpw'.1 l' h
        simp only [Complex.sub_re, Complex.one_re]
        rcases lt_abs.mp this with g | g
        · exact lt_abs.mpr (Or.inl (by linarith))
        · exact lt_abs.mpr (Or.inr (by linarith))⟩
    simp only [cs]
    apply pos_mul ih'
    split_ifs
    · exact pos_div (qw_pos q0 w _ hl q1 d0) (xs_pos x0 w e _ (by simp [hl]) x2 d1)
    · exact xs_pos x0 w e _ hl x1 d0
    · exact pos_div (qw_pos q0 w _ (by simp [hl]) q2 dm) (xs_pos x0 w e _ (by simp [hl]) x3 dm)
    · exact xs_pos x0 w e _ hl x1 d0

section
variable {S : Type} [Fintype S] [DecidableEq S]

/- English proof (translation)
Unfold `phiL`. Unfold `ypt at h`. Use `split_ifs at h ⊢`. Use `frac (Y - l.pt) (by simp [hY, hl]) 0 (-1) (by simp; nlinarith)` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg]`.

Use `frac (l.pt - Y) (by simp [hY, hl]) 0 (-1) (by simp at h ⊢; nlinarith)` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg]`.
-/
lemma phi_posB (l : Letter ℂ S) (Y : ℂ) (hY : Y.im = 0) (hl : l.pt.im = 0)
    (h : 0 < (Y.re - (ypt l).re) * (Y.re - (ypt l).re - 1)) : Pos (phiL l Y) := by
  unfold phiL
  unfold ypt at h
  split_ifs at h ⊢
  · have := frac (Y - l.pt) (by simp [hY, hl]) 0 (-1) (by simp; nlinarith)
    simpa [sub_eq_add_neg] using this
  · have := frac (l.pt - Y) (by simp [hY, hl]) 0 (-1) (by simp at h ⊢; nlinarith)
    simpa [sub_eq_add_neg] using this

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact h0`. Consider the case `cons l w ih`. Establish `hl` using `h l (by simp)`. Establish `ih'` using `ih (fun l' hl' => h l' (by simp [hl']))`.

Simplify using `only [xs]`. Apply `pos_mul ih'` to reduce the goal to its premises. Use `split_ifs`. Conclude with `phi_posB l Y hY hl.1 hl.2`. Conclude with `⟨by simp, by simp⟩`.
-/
lemma xs_posB (x0 : ℂ → ℂ) (w : List (Letter ℂ S)) (e : Ix S) (Y : ℂ) (hY : Y.im = 0) (h0 : Pos (x0 Y))
    (h : ∀ l ∈ w, l.pt.im = 0 ∧ 0 < (Y.re - (ypt l).re) * (Y.re - (ypt l).re - 1)) : Pos (xs x0 w e Y) := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    simp only [xs]
    apply pos_mul ih'
    split_ifs
    · exact phi_posB l Y hY hl.1 hl.2
    · exact ⟨by simp, by simp⟩

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact h0`. Consider the case `cons l w ih`. Take `⟨hl, g1, g2⟩` from `h l (by simp)`. Establish `ih'` using `ih (fun l' hl' => h l' (by simp [hl']))`.

Simplify using `only [qw]`. Unfold `ypt at g1 g2`. Use `split_ifs at g1 g2 ⊢`. Apply `pos_mul ih'` to reduce the goal to its premises. Use `frac (Y - l.pt) (by simp [hY, hl]) 1 0 (by simp; nlinarith)` as an intermediate fact.

Simplify `this` using `[sub_eq_add_neg]`. Apply `pos_mul ih'` to reduce the goal to its premises. Use `frac (l.pt - Y) (by simp [hY, hl]) 0 (-1) (by simp at g1 g2 ⊢; nlinarith)` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg]`.
-/
lemma qw_posB (q0 : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (hY : Y.im = 0) (h0 : Pos (q0 Y))
    (h : ∀ l ∈ w, l.pt.im = 0 ∧ 0 < (Y.re - (ypt l).re) * (Y.re - (ypt l).re - 1) ∧
      0 < (Y.re - (ypt l).re) * (Y.re - (ypt l).re + 1)) : Pos (qw q0 w Y) := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    obtain ⟨hl, g1, g2⟩ := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    simp only [qw]
    unfold ypt at g1 g2
    split_ifs at g1 g2 ⊢
    · apply pos_mul ih'
      have := frac (Y - l.pt) (by simp [hY, hl]) 1 0 (by simp; nlinarith)
      simpa [sub_eq_add_neg] using this
    · apply pos_mul ih'
      have := frac (l.pt - Y) (by simp [hY, hl]) 0 (-1) (by simp at g1 g2 ⊢; nlinarith)
      simpa [sub_eq_add_neg] using this
end

/- English proof (translation)
Introduce `S _ _ x0 q0 w him hpw hpos e`. Proceed by induction on `w with`. Consider the case `nil => exact ⟨by simp [cs], by simp [cs]⟩`. Consider the case `cons l w ih`. Establish `hpw'` using `List.pairwise_cons.mp hpw`.

Establish `ih'` using `ih (fun l' h => him l' (by simp [h])) hpw'.2 (fun l' h => hpos l' (by simp [h]))`. Take `⟨x1, x2, q1⟩` from `hpos l (by simp)`. Establish `hl` using `him l (by simp)`. Apply the tactic sequence `have hy : (ypt l).im = 0 := by unfold ypt; split_ifs <;> simp [hl]`. Establish `d0 : ∀ l' ∈ w, l'.pt.im = 0 ∧ 0 < ((ypt l).re - (ypt l').re) * ((ypt l).re - (ypt l').re - 1) ∧ 0 < ((ypt l).re - (ypt l').re) * ((ypt l).re - (ypt l').re + 1)` using `fun l' h => ⟨him l' (by simp [h]), by`.

Apply the tactic sequence `rcases lt_abs.mp (hpw'.1 l' h) with g | g <;> constructor <;> nlinarith⟩`. Establish `d1 : ∀ l' ∈ w, l'.pt.im = 0 ∧ 0 < ((ypt l + 1).re - (ypt l').re) * ((ypt l + 1).re - (ypt l').re - 1)` using `fun l' h => ⟨him l' (by simp [h]), by`. Simplify using `only [Complex.add_re, Complex.one_re]`. Apply the tactic sequence `rcases lt_abs.mp (hpw'.1 l' h) with g | g <;> nlinarith⟩`. Establish `X0` using `xs_posB x0 w e _ hy x1 (fun l' h => ⟨(d0 l' h).1, (d0 l' h).2.1⟩)`.

Establish `X1` using `xs_posB x0 w e _ (by simp [hy]) x2 d1`. Establish `Q0` using `qw_posB q0 w _ hy q1 d0`. Simplify using `only [cs]`. Apply `pos_mul ih'` to reduce the goal to its premises. Unfold `ypt at X0 X1 Q0`.

Use `split_ifs at X0 X1 Q0 ⊢`. Conclude with `pos_div Q0 X1`. Conclude with `X0`. Conclude with `pos_div Q0 X0`. Simplify using `using X1`.
-/
theorem cPosBase : CPosBase := by
  intro S _ _ x0 q0 w him hpw hpos e
  induction w with
  | nil => exact ⟨by simp [cs], by simp [cs]⟩
  | cons l w ih =>
    have hpw' := List.pairwise_cons.mp hpw
    have ih' := ih (fun l' h => him l' (by simp [h])) hpw'.2 (fun l' h => hpos l' (by simp [h]))
    obtain ⟨x1, x2, q1⟩ := hpos l (by simp)
    have hl := him l (by simp)
    have hy : (ypt l).im = 0 := by unfold ypt; split_ifs <;> simp [hl]
    have d0 : ∀ l' ∈ w, l'.pt.im = 0 ∧ 0 < ((ypt l).re - (ypt l').re) * ((ypt l).re - (ypt l').re - 1) ∧
        0 < ((ypt l).re - (ypt l').re) * ((ypt l).re - (ypt l').re + 1) := fun l' h =>
      ⟨him l' (by simp [h]), by
        rcases lt_abs.mp (hpw'.1 l' h) with g | g <;> constructor <;> nlinarith⟩
    have d1 : ∀ l' ∈ w, l'.pt.im = 0 ∧
        0 < ((ypt l + 1).re - (ypt l').re) * ((ypt l + 1).re - (ypt l').re - 1) := fun l' h =>
      ⟨him l' (by simp [h]), by
        simp only [Complex.add_re, Complex.one_re]
        rcases lt_abs.mp (hpw'.1 l' h) with g | g <;> nlinarith⟩
    have X0 := xs_posB x0 w e _ hy x1 (fun l' h => ⟨(d0 l' h).1, (d0 l' h).2.1⟩)
    have X1 := xs_posB x0 w e _ (by simp [hy]) x2 d1
    have Q0 := qw_posB q0 w _ hy q1 d0
    simp only [cs]
    apply pos_mul ih'
    unfold ypt at X0 X1 Q0
    split_ifs at X0 X1 Q0 ⊢
    · exact pos_div Q0 X1
    · exact X0
    · exact pos_div Q0 X0
    · simpa using X1

/- English proof (translation)
Establish `hu` using `antitone_on (u_step h)`. Establish `hu'` using `antitone_on (u_step (interlaces_swap h))`. Establish `hl : l ∈ Icc 1 k` using `mem_Icc.2 ⟨hl1, hlk⟩`. Rewrite using `[← mul_prod_erase _ _ hl]`. Apply `mul_neg_of_neg_of_pos` to reduce the goal to its premises.

Apply the tactic sequence `apply mul_neg_of_neg_of_pos <;> linarith`. Apply `prod_pos` to reduce the goal to its premises. Introduce `i hi`. Establish `hne` using `ne_of_mem_erase hi`. Establish `hi'` using `mem_Icc.1 (mem_of_mem_erase hi)`.

Break down `lt_or_gt_of_ne hne with hil | hil` into its components or cases. Take `⟨a, b, c, d⟩` from `h i (mem_Icc.2 ⟨hi'.1, by omega⟩)`. Establish `h1` using `hu' (i + 1) l (by omega) (by omega) hlk`. Establish `h2` using `hu' i l hi'.1 (by omega) hlk`. Apply the tactic sequence `apply mul_pos <;> linarith`.

Take `⟨j, rfl⟩ : ∃ j, i = j + 1` from `⟨i - 1, by omega⟩`. Take `⟨a, b, c, d⟩` from `h j (mem_Icc.2 ⟨by omega, by omega⟩)`. Establish `h1` using `hu l (j + 1) hl1 (by omega) hi'.2`. Establish `h2` using `hu l j hl1 (by omega) (by omega)`. Apply the tactic sequence `apply mul_pos_of_neg_of_neg <;> linarith`.
-/
lemma q_core' (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    ∏ i ∈ Icc 1 k, ((Y - 1 + 1/2 + u i) * (Y - 1 + 1/2 + u' i)) < 0 := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  have hl : l ∈ Icc 1 k := mem_Icc.2 ⟨hl1, hlk⟩
  rw [← mul_prod_erase _ _ hl]
  apply mul_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos <;> linarith
  · apply prod_pos
    intro i hi
    have hne := ne_of_mem_erase hi
    have hi' := mem_Icc.1 (mem_of_mem_erase hi)
    rcases lt_or_gt_of_ne hne with hil | hil
    · obtain ⟨a, b, c, d⟩ := h i (mem_Icc.2 ⟨hi'.1, by omega⟩)
      have h1 := hu' (i + 1) l (by omega) (by omega) hlk
      have h2 := hu' i l hi'.1 (by omega) hlk
      apply mul_pos <;> linarith
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      obtain ⟨a, b, c, d⟩ := h j (mem_Icc.2 ⟨by omega, by omega⟩)
      have h1 := hu l (j + 1) hl1 (by omega) hi'.2
      have h2 := hu l j hl1 (by omega) (by omega)
      apply mul_pos_of_neg_of_neg <;> linarith

/- English proof (translation)
Use `q_core' k u' u ρ l Y hl1 hlk (interlaces_swap h) hA` as an intermediate fact. Rewrite `this` using `[prod_congr rfl (fun i _ => mul_comm (Y - 1 + 1/2 + u' i) (Y - 1 + 1/2 + u i))]`. Then use the resulting hypothesis.
-/
lemma q_core'' (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u' l + 2 ≤ -Y ∧ -Y ≤ u l - 2) :
    ∏ i ∈ Icc 1 k, ((Y - 1 + 1/2 + u i) * (Y - 1 + 1/2 + u' i)) < 0 := by
  have := q_core' k u' u ρ l Y hl1 hlk (interlaces_swap h) hA
  rwa [prod_congr rfl (fun i _ => mul_comm (Y - 1 + 1/2 + u' i) (Y - 1 + 1/2 + u i))] at this

/- English proof (translation)
Introduce `k u u' ρ l Y T T' hl1 hlk h hc hT hT'`. Establish `hTT : 0 < T * T'` using `mul_pos hT hT'`. Establish `hP : ∏ i ∈ Icc 1 k, ((Y - 1 + 1/2 + u i) * (Y - 1 + 1/2 + u' i)) < 0`. Break down `hc with hA | hB` into its components or cases. Conclude with `q_core' k u u' ρ l Y hl1 hlk h hA`.

Conclude with `q_core'' k u u' ρ l Y hl1 hlk h hB`. Unfold `qpoly`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem qPositiveShift : QPositiveShift := by
  intro k u u' ρ l Y T T' hl1 hlk h hc hT hT'
  have hTT : 0 < T * T' := mul_pos hT hT'
  have hP : ∏ i ∈ Icc 1 k, ((Y - 1 + 1/2 + u i) * (Y - 1 + 1/2 + u' i)) < 0 := by
    rcases hc with hA | hB
    · exact q_core' k u u' ρ l Y hl1 hlk h hA
    · exact q_core'' k u u' ρ l Y hl1 hlk h hB
  unfold qpoly
  nlinarith

/- English proof (translation)
Introduce `hI hQ hQs hC S _ _ k u u' ρ l T T' w hl1 hlk hint hT hT' hpts hpw e`. Apply `hC S _ _ w (fun a ha => (hpts a ha).1) hpw` to reduce the goal to its premises. Introduce `a ha`. Take `⟨him, hcut⟩` from `hpts a ha`. Apply the tactic sequence `obtain ⟨y, hy⟩ : ∃ y : ℝ, a.pt = (y : ℂ) := ⟨a.pt.re, by apply Complex.ext <;> simp [him]⟩`.

Establish `hcut' : OnCut u u' l y` using `by simpa [hy] using hcut`. Establish `hx : ∀ e : ℝ, e ∈ ({-1, 0, 1} : Finset ℝ) → Pos ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((y + e : ℝ) : ℂ) + (ρ i : ℂ)))`. Introduce `e he`. Use `hI k u u' ρ l y hl1 hlk hint hcut' e he` as an intermediate fact. Establish `c : ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((y + e : ℝ) : ℂ) + (ρ i : ℂ))) = (((-1 : ℝ) ^ (k - l) * xpoly k ρ (y + e) : ℝ) : ℂ)`.

Unfold `xpoly`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[c]`. Conclude with `pos_ofReal this`.

Establish `hq : ∀ z : ℝ, 0 < qpoly k T T' u u' z → Pos (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ)))`. Introduce `z hz`. Establish `c : (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ))) = ((qpoly k T T' u u' z : ℝ) : ℂ)`. Unfold `qpoly`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[c]`. Conclude with `pos_ofReal hz`. Rewrite using `[hy]`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `hx 0 (by simp); simpa using this` as an intermediate fact. Use `hx 1 (by simp); simpa using this` as an intermediate fact. Use `hx (-1) (by simp); simpa [sub_eq_add_neg] using this` as an intermediate fact. Conclude with `hq y (hQ k u u' ρ l y T T' hl1 hlk hint hcut' hT hT')`. Use `hq (y - 1) (hQs k u u' ρ l y T T' hl1 hlk hint hcut' hT hT')` as an intermediate fact.

Simplify using `using this`.
-/
theorem cPosCut : CPosCut := by
  intro hI hQ hQs hC S _ _ k u u' ρ l T T' w hl1 hlk hint hT hT' hpts hpw e
  apply hC S _ _ w (fun a ha => (hpts a ha).1) hpw
  intro a ha
  obtain ⟨him, hcut⟩ := hpts a ha
  obtain ⟨y, hy⟩ : ∃ y : ℝ, a.pt = (y : ℂ) := ⟨a.pt.re, by apply Complex.ext <;> simp [him]⟩
  have hcut' : OnCut u u' l y := by simpa [hy] using hcut
  have hx : ∀ e : ℝ, e ∈ ({-1, 0, 1} : Finset ℝ) →
      Pos ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((y + e : ℝ) : ℂ) + (ρ i : ℂ))) := by
    intro e he
    have := hI k u u' ρ l y hl1 hlk hint hcut' e he
    have c : ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((y + e : ℝ) : ℂ) + (ρ i : ℂ))) =
        (((-1 : ℝ) ^ (k - l) * xpoly k ρ (y + e) : ℝ) : ℂ) := by
      unfold xpoly; push_cast; ring
    rw [c]; exact pos_ofReal this
  have hq : ∀ z : ℝ, 0 < qpoly k T T' u u' z →
      Pos (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ))) := by
    intro z hz
    have c : (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ))) =
        ((qpoly k T T' u u' z : ℝ) : ℂ) := by
      unfold qpoly; push_cast; ring
    rw [c]; exact pos_ofReal hz
  rw [hy]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := hx 0 (by simp); simpa using this
  · have := hx 1 (by simp); simpa using this
  · have := hx (-1) (by simp); simpa [sub_eq_add_neg] using this
  · exact hq y (hQ k u u' ρ l y T T' hl1 hlk hint hcut' hT hT')
  · have := hq (y - 1) (hQs k u u' ρ l y T T' hl1 hlk hint hcut' hT hT'); simpa using this

/- English proof (translation)
Introduce `hI hQ hQs hC S _ _ k u u' ρ l T T' w hl1 hlk hint hT hT' hpts hpw e`. Apply `hC S _ _ w (fun a ha => (hpts a ha).1) hpw` to reduce the goal to its premises. Introduce `a ha`. Take `⟨him, hcut⟩` from `hpts a ha`. Apply the tactic sequence `have himy : (ypt a).im = 0 := by unfold ypt; split_ifs <;> simp [him]`.

Apply the tactic sequence `obtain ⟨y, hy⟩ : ∃ y : ℝ, ypt a = (y : ℂ) := ⟨(ypt a).re, by apply Complex.ext <;> simp [himy]⟩`. Establish `hcut' : OnCut u u' l y ∨ OnCut u u' l (y + 1)` using `by simpa [hy] using hcut`. Establish `hx : ∀ z : ℝ, 0 < (-1 : ℝ) ^ (k - l) * xpoly k ρ z → Pos ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((z : ℝ) : ℂ) + (ρ i : ℂ)))`. Introduce `z hz`. Establish `c : ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((z : ℝ) : ℂ) + (ρ i : ℂ))) = (((-1 : ℝ) ^ (k - l) * xpoly k ρ z : ℝ) : ℂ)`.

Unfold `xpoly`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[c]`. Conclude with `pos_ofReal hz`.

Establish `hq : ∀ z : ℝ, 0 < qpoly k T T' u u' z → Pos (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ)))`. Introduce `z hz`. Establish `c : (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ))) = ((qpoly k T T' u u' z : ℝ) : ℂ)`. Unfold `qpoly`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[c]`. Conclude with `pos_ofReal hz`. Rewrite using `[hy]`. Break down `hcut' with hc | hc` into its components or cases.

Establish `a0` using `hI k u u' ρ l y hl1 hlk hint hc 0 (by simp)`. Establish `a1` using `hI k u u' ρ l y hl1 hlk hint hc 1 (by simp)`. Rewrite `a0` using `[add_zero]`. Use `⟨hx y a0, ?_, hq y (hQ k u u' ρ l y T T' hl1 hlk hint hc hT hT')⟩` and prove the remaining obligations. Use `hx (y + 1) a1` as an intermediate fact.

Simplify using `using this`. Establish `a0` using `hI k u u' ρ l (y + 1) hl1 hlk hint hc 0 (by simp)`. Establish `a1` using `hI k u u' ρ l (y + 1) hl1 hlk hint hc (-1) (by simp)`. Establish `b` using `hQs k u u' ρ l (y + 1) T T' hl1 hlk hint hc hT hT'`. Rewrite `a0` using `[add_zero]`.

Establish `e1 : y + 1 + -1 = y` using `by ring`. Establish `e2 : y + 1 - 1 = y` using `by ring`. Rewrite `a1` using `[e1]`. Rewrite `b` using `[e2]`. Use `⟨hx y a1, ?_, hq y b⟩` and prove the remaining obligations.

Use `hx (y + 1) a0` as an intermediate fact. Simplify using `using this`.
-/
theorem cPosCutBase : CPosCutBase := by
  intro hI hQ hQs hC S _ _ k u u' ρ l T T' w hl1 hlk hint hT hT' hpts hpw e
  apply hC S _ _ w (fun a ha => (hpts a ha).1) hpw
  intro a ha
  obtain ⟨him, hcut⟩ := hpts a ha
  have himy : (ypt a).im = 0 := by unfold ypt; split_ifs <;> simp [him]
  obtain ⟨y, hy⟩ : ∃ y : ℝ, ypt a = (y : ℂ) := ⟨(ypt a).re, by apply Complex.ext <;> simp [himy]⟩
  have hcut' : OnCut u u' l y ∨ OnCut u u' l (y + 1) := by simpa [hy] using hcut
  have hx : ∀ z : ℝ, 0 < (-1 : ℝ) ^ (k - l) * xpoly k ρ z →
      Pos ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((z : ℝ) : ℂ) + (ρ i : ℂ))) := by
    intro z hz
    have c : ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((z : ℝ) : ℂ) + (ρ i : ℂ))) =
        (((-1 : ℝ) ^ (k - l) * xpoly k ρ z : ℝ) : ℂ) := by
      unfold xpoly; push_cast; ring
    rw [c]; exact pos_ofReal hz
  have hq : ∀ z : ℝ, 0 < qpoly k T T' u u' z →
      Pos (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ))) := by
    intro z hz
    have c : (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ))) =
        ((qpoly k T T' u u' z : ℝ) : ℂ) := by
      unfold qpoly; push_cast; ring
    rw [c]; exact pos_ofReal hz
  rw [hy]
  rcases hcut' with hc | hc
  · have a0 := hI k u u' ρ l y hl1 hlk hint hc 0 (by simp)
    have a1 := hI k u u' ρ l y hl1 hlk hint hc 1 (by simp)
    rw [add_zero] at a0
    refine ⟨hx y a0, ?_, hq y (hQ k u u' ρ l y T T' hl1 hlk hint hc hT hT')⟩
    have := hx (y + 1) a1; simpa using this
  · have a0 := hI k u u' ρ l (y + 1) hl1 hlk hint hc 0 (by simp)
    have a1 := hI k u u' ρ l (y + 1) hl1 hlk hint hc (-1) (by simp)
    have b := hQs k u u' ρ l (y + 1) T T' hl1 hlk hint hc hT hT'
    rw [add_zero] at a0
    have e1 : y + 1 + -1 = y := by ring
    have e2 : y + 1 - 1 = y := by ring
    rw [e1] at a1; rw [e2] at b
    refine ⟨hx y a1, ?_, hq y b⟩
    have := hx (y + 1) a0; simpa using this

end Formalism.FourierDecayAlt.P.Fr2

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `Fr2.frameAssemble`.
-/
theorem frame_of_steps : Formalism.FourierDecayAlt.Fr.FrameAssemble := Fr2.frameAssemble

/- English proof (translation)
The claim follows from `Fr2.cDiag`.
-/
theorem c_diagonal : Formalism.FourierDecayAlt.Fr.CDiag := Fr2.cDiag

/- English proof (translation)
The claim follows from `Fr2.cPos`.
-/
theorem cPos_true : Formalism.FourierDecayAlt.Fr.CPos := Fr2.cPos

/- English proof (translation)
The claim follows from `Fr2.qPositiveShift`.
-/
theorem q_positive_shift : Formalism.FourierDecayAlt.Fr.QPositiveShift := Fr2.qPositiveShift

/- English proof (translation)
The claim follows from `Fr2.cPosCut`.
-/
theorem c_pos_truncated : Formalism.FourierDecayAlt.Fr.CPosCut := Fr2.cPosCut

/- English proof (translation)
The claim follows from `Fr2.cPosBase`.
-/
theorem c_pos_base : Formalism.FourierDecayAlt.Fr.CPosBase := Fr2.cPosBase

/- English proof (translation)
The claim follows from `Fr2.admissible_rec_of_admissible_word`.
-/
theorem admissible_rec_of_admissible : Formalism.FourierDecayAlt.Fr.AdmRecOfAdm := Fr2.admissible_rec_of_admissible_word

/- English proof (translation)
The claim follows from `Fr2.admissible_rec_of_base`.
-/
theorem admissible_rec_of_base_case : Formalism.FourierDecayAlt.Fr.AdmRecOfBase := Fr2.admissible_rec_of_base

/- English proof (translation)
The claim follows from `Fr2.frameRecAssemble`.
-/
theorem frame_rec_of_steps : Formalism.FourierDecayAlt.Fr.FrameRecAssemble := Fr2.frameRecAssemble

/- English proof (translation)
The claim follows from `Fr2.cPosCutBase`.
-/
theorem c_pos_truncated_base : Formalism.FourierDecayAlt.Fr.CPosCutBase := Fr2.cPosCutBase

end Formalism.FourierDecayAlt.P
