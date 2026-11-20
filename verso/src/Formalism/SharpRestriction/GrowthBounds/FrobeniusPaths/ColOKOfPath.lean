import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftedColumnCongruence

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section Strip

/- English proof (translation)
Take `⟨h1, h2, _⟩` from `h`. Prove the components needed by the constructor for the conclusion. Unfold `colH`. Use `Finset.card_le_card fun m hm => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢`.

Conclude with `hm.trans (h1 m)`. Unfold `colH set A := univ.filter fun m : Fin n => c ≤ mu' m with hA`. Establish `e : A.card = (A.filter fun m => m.val = 0).card + (A.filter fun m => ¬ m.val = 0).card` using `(Finset.card_filter_add_card_filter_not _).symm`. Establish `e1 : (A.filter fun m => m.val = 0).card ≤ 1`. Rewrite using `[Finset.card_le_one]`.

Introduce `a ha b hb`. Simplify using `only [Finset.mem_filter] at ha hb`. Conclude with `Fin.ext (by omega)`. Establish `e2 : (A.filter fun m => ¬ m.val = 0).card ≤ (univ.filter fun m : Fin n => c ≤ nu m).card`. Use `Finset.card_le_card_of_injOn (fun m => ⟨m.val - 1, by have := m.isLt; omega⟩) ?_ ?_` and prove the remaining obligations.

Introduce `m hm`. Simplify using `only [Finset.coe_filter, Finset.mem_filter, hA, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hm ⊢`. Establish `hlt : (m.val - 1) + 1 < n` using `by have := m.isLt; omega`. Use `h2 ⟨m.val - 1, by have := m.isLt; omega⟩ hlt` as an intermediate fact. Establish `em : (⟨(m.val - 1) + 1, hlt⟩ : Fin n) = m` using `Fin.ext (by simp; omega)`.

Simplify using `only [em] at this`. Conclude with `hm.1.trans this`. Introduce `a ha b hb hab`. Simplify using `only [Finset.coe_filter, Finset.mem_filter, Set.mem_ofPred_eq] at ha hb`. Simplify using `only [Fin.mk.injEq] at hab`.

Conclude with `Fin.ext (by omega)`. Use linear arithmetic over natural numbers and integers.
-/
lemma colH_strip {n : ℕ} (nu mu' : Fin n → ℤ) (b : ℕ) (h : HStrip nu mu' b) (c : ℤ) :
    colH nu c ≤ colH mu' c ∧ colH mu' c ≤ colH nu c + 1 := by
  classical
  obtain ⟨h1, h2, _⟩ := h
  constructor
  · unfold colH
    refine Finset.card_le_card fun m hm => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    exact hm.trans (h1 m)
  · unfold colH
    set A := univ.filter fun m : Fin n => c ≤ mu' m with hA
    have e : A.card = (A.filter fun m => m.val = 0).card + (A.filter fun m => ¬ m.val = 0).card :=
      (Finset.card_filter_add_card_filter_not _).symm
    have e1 : (A.filter fun m => m.val = 0).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      exact Fin.ext (by omega)
    have e2 : (A.filter fun m => ¬ m.val = 0).card ≤ (univ.filter fun m : Fin n => c ≤ nu m).card := by
      refine Finset.card_le_card_of_injOn (fun m => ⟨m.val - 1, by have := m.isLt; omega⟩) ?_ ?_
      · intro m hm
        simp only [Finset.coe_filter, Finset.mem_filter, hA, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hm ⊢
        have hlt : (m.val - 1) + 1 < n := by have := m.isLt; omega
        have := h2 ⟨m.val - 1, by have := m.isLt; omega⟩ hlt
        have em : (⟨(m.val - 1) + 1, hlt⟩ : Fin n) = m := Fin.ext (by simp; omega)
        simp only [em] at this
        exact hm.1.trans this
      · intro a ha b hb hab
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_ofPred_eq] at ha hb
        simp only [Fin.mk.injEq] at hab
        exact Fin.ext (by omega)
    omega

end Strip

section Col

variable {N r K : ℕ}

structure ColOK (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) : Prop where
  rise : ∀ (j : ℕ) (h : j < N), colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c →
    LL.vec ⟨j, h⟩ = true ∧ colH (mu ⟨j + 1, by omega⟩) c = colH (mu ⟨j, by omega⟩) c + 1
  fall : ∀ (j : ℕ) (h : j < N), colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c →
    LL.vec ⟨j, h⟩ = false ∧ colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c + 1
  start : 1 ≤ c → colH (mu ⟨0, by omega⟩) c = 0
  dual : ¬ 1 ≤ c → ∀ (j : ℕ) (h : j ≤ N), r < colH (mu ⟨j, by omega⟩) c

/- English proof (translation)
Establish `step : ∀ (j : ℕ) (h : j < N), (LL.vec ⟨j, h⟩ = true ∧ colH (P.mu ⟨j, by omega⟩) c ≤ colH (P.mu ⟨j + 1, by omega⟩) c ∧ colH (P.mu ⟨j + 1, by omega⟩) c ≤ colH (P.mu ⟨j, by omega⟩) c + 1) ∨ (LL.vec ⟨j, h⟩ = false ∧ colH (P.mu ⟨j + 1, by omega⟩) c ≤ colH (P.mu ⟨j, by omega⟩) c ∧ colH …`. Introduce `j h`. Establish `hs` using `P.step ⟨j, h⟩`. Distinguish the cases in `hv : LL.vec ⟨j, h⟩ = true`. Rewrite `hs` using `[if_pos hv]`.

Conclude with `Or.inl ⟨hv, colH_strip _ _ _ hs c⟩`. Rewrite `hs` using `[if_neg hv]`. Conclude with `Or.inr ⟨by simpa using hv, colH_strip _ _ _ hs c⟩`. Establish `hz : P.mu ⟨0, by omega⟩ = 0` using `P.zero`. Use `⟨fun j h hlt => ?_, fun j h hlt => ?_, fun hc => ?_, fun hc => ?_⟩` and prove the remaining obligations.

Break down `step j h with ⟨hv, h1, h2⟩ | ⟨hv, h1, h2⟩` into its components or cases. Conclude with `⟨hv, by omega⟩`. Use linear arithmetic over natural numbers and integers. Break down `step j h with ⟨hv, h1, h2⟩ | ⟨hv, h1, h2⟩` into its components or cases. Use linear arithmetic over natural numbers and integers.

Conclude with `⟨hv, by omega⟩`. Rewrite using `[hz]`. Unfold `colH`. Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce `m _`.

Simplify using `only [Pi.zero_apply]`. Use linear arithmetic over natural numbers and integers. Establish `h0 : colH (P.mu ⟨0, by omega⟩) c = r + K`. Rewrite using `[hz]`. Unfold `colH`.

Rewrite using `[Finset.filter_true_of_mem (fun m _ => by simp only [Pi.zero_apply]; omega)]`. Simplify using the standard rewrite rules. Establish `hind : ∀ (j : ℕ) (h : j ≤ N), r + K ≤ colH (P.mu ⟨j, by omega⟩) c + j`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => intro _`. Use linear arithmetic over natural numbers and integers. Consider the case `succ j ih`. Introduce `h`. Use `ih (by omega)` as an intermediate fact.

Apply the tactic sequence `rcases step j h with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> omega`. Introduce `j h`. Use `hind j h` as an intermediate fact. Use `NeZero.pos r` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma colOK_of_path [NeZero r] (LL : LiftLetters (Fin N)) (B : Fin N → ℕ) (hK : N + r ≤ K)
    (P : PPath (r + K) N LL.toLetters B) (c : ℤ) : ColOK LL P.mu c := by
  have step : ∀ (j : ℕ) (h : j < N),
      (LL.vec ⟨j, h⟩ = true ∧ colH (P.mu ⟨j, by omega⟩) c ≤ colH (P.mu ⟨j + 1, by omega⟩) c ∧
        colH (P.mu ⟨j + 1, by omega⟩) c ≤ colH (P.mu ⟨j, by omega⟩) c + 1) ∨
      (LL.vec ⟨j, h⟩ = false ∧ colH (P.mu ⟨j + 1, by omega⟩) c ≤ colH (P.mu ⟨j, by omega⟩) c ∧
        colH (P.mu ⟨j, by omega⟩) c ≤ colH (P.mu ⟨j + 1, by omega⟩) c + 1) := by
    intro j h
    have hs := P.step ⟨j, h⟩
    by_cases hv : LL.vec ⟨j, h⟩ = true
    · rw [if_pos hv] at hs
      exact Or.inl ⟨hv, colH_strip _ _ _ hs c⟩
    · rw [if_neg hv] at hs
      exact Or.inr ⟨by simpa using hv, colH_strip _ _ _ hs c⟩
  have hz : P.mu ⟨0, by omega⟩ = 0 := P.zero
  refine ⟨fun j h hlt => ?_, fun j h hlt => ?_, fun hc => ?_, fun hc => ?_⟩
  · rcases step j h with ⟨hv, h1, h2⟩ | ⟨hv, h1, h2⟩
    · exact ⟨hv, by omega⟩
    · omega
  · rcases step j h with ⟨hv, h1, h2⟩ | ⟨hv, h1, h2⟩
    · omega
    · exact ⟨hv, by omega⟩
  · rw [hz]; unfold colH
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _; simp only [Pi.zero_apply]; omega
  · have h0 : colH (P.mu ⟨0, by omega⟩) c = r + K := by
      rw [hz]; unfold colH
      rw [Finset.filter_true_of_mem (fun m _ => by simp only [Pi.zero_apply]; omega)]
      simp
    have hind : ∀ (j : ℕ) (h : j ≤ N), r + K ≤ colH (P.mu ⟨j, by omega⟩) c + j := by
      intro j
      induction j with
      | zero => intro _; omega
      | succ j ih =>
        intro h
        have := ih (by omega)
        rcases step j h with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> omega
    intro j h
    have := hind j h
    have := NeZero.pos r
    omega

/- English proof (translation)
Rewrite using `[show (univ.filter fun a : Fin (r + K) => a.val < r) = (univ : Finset (Fin r)).image (Fin.castAdd K) from ?_, Finset.card_image_of_injective _ (Fin.castAdd_injective r K), Finset.card_fin]`. Use extensionality with `a`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `⟨⟨a.val, h⟩, Fin.ext rfl⟩`. Introduce and unpack `⟨b, rfl⟩`. Conclude with `b.isLt`.
-/
lemma plane_card : (univ.filter fun a : Fin (r + K) => a.val < r).card = r := by
  classical
  rw [show (univ.filter fun a : Fin (r + K) => a.val < r) = (univ : Finset (Fin r)).image (Fin.castAdd K) from ?_,
    Finset.card_image_of_injective _ (Fin.castAdd_injective r K), Finset.card_fin]
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h; exact ⟨⟨a.val, h⟩, Fin.ext rfl⟩
  · rintro ⟨b, rfl⟩; exact b.isLt

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
lemma costly_iff (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (j : ℕ) (h : j < N) :
    IsCostly mu c ⟨j, h⟩ ↔
      (colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c ∧ r ≤ colH (mu ⟨j, by omega⟩) c) ∨
      (colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c ∧ colH (mu ⟨j, by omega⟩) c ≤ r) := Iff.rfl

/- English proof (translation)
Assume the negation of the conclusion as `hh`. Conclude with `h (by unfold nomL; rw [if_neg hh])`.
-/
lemma nomL_ne {R : Type} [CommRing R] (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ)
    (i : Fin N) (m : Fin (r + K)) (h : nomL R LL mu c i m ≠ 0) : condUS LL i m ↔ IsCostly mu c i := by
  classical
  by_contra hh
  exact h (by unfold nomL; rw [if_neg hh])

/- English proof (translation)
Take `⟨m, hm, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Use `⟨m, hm, fun e => hne (by rw [e]; simp), fun e => hne (by rw [e]; simp)⟩` and prove the remaining obligations.
-/
lemma wedgeR_ne {R : Type} [CommRing R] {k : ℕ} (x : Fin k → R) (Kv : Finset (Fin k) → R) (J : Finset (Fin k))
    (h : wedgeR x Kv J ≠ 0) : ∃ m ∈ J, x m ≠ 0 ∧ Kv (J.erase m) ≠ 0 := by
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨m, hm, fun e => hne (by rw [e]; simp), fun e => hne (by rw [e]; simp)⟩

/- English proof (translation)
Take `⟨m, hm, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Use `⟨m, by simpa using hm, fun e => hne (by rw [e]; simp), fun e => hne (by rw [e]; simp)⟩` and prove the remaining obligations.
-/
lemma contrR_ne {R : Type} [CommRing R] {k : ℕ} (x : Fin k → R) (Kv : Finset (Fin k) → R) (J : Finset (Fin k))
    (h : contrR x Kv J ≠ 0) : ∃ m, m ∉ J ∧ x m ≠ 0 ∧ Kv (insert m J) ≠ 0 := by
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨m, by simpa using hm, fun e => hne (by rw [e]; simp), fun e => hne (by rw [e]; simp)⟩

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Introduce `J hJ`. Establish `: J = ∅`. Assume the negation of the conclusion as `hne; exact hJ (by simp only [SgW]; unfold extOne; rw [if_neg hne])`.

Substitute `this` using the available equality. Use `⟨fun hc => ⟨by rw [H.start hc]; simp, fun hr a ha => ?_, by simp⟩, by simp⟩` and prove the remaining obligations. Rewrite `hr` using `[H.start hc]`. Use linear arithmetic over natural numbers and integers. Consider the case `succ j ih`.

Introduce `J hJ`. Establish `h : j < N` using `hj`. Establish `ih'` using `ih (by omega)`. Simplify using `only [SgW, dif_pos h] at hJ`. Unfold `colStep at hJ`.

Establish `hci` using `costly_iff mu c j h`. Use `split_ifs at hJ with h1 h2 h3 h4`. Take `⟨hv, hN⟩` from `H.rise j h h1`. Take `⟨m, hm, hn, hK⟩` from `wedgeR_ne _ _ _ hJ`. Establish `hc` using `nomL_ne LL mu c _ m hn`.

Take `⟨hcard, hA, hB⟩` from `(ih' _ hK).1 h2`. Establish `hmr : r ≤ m.val ↔ r ≤ colH (mu ⟨j, by omega⟩) c`. Rewrite `hc` using `[hci]`. Unfold `condUS at hc`. Simplify using `only [hv, true_and] at hc`.

Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `intro hh; rcases hc.mp (Or.inl hh) with ⟨_, x⟩ | ⟨x, _⟩ <;> omega`. Introduce `hh`. Break down `hc.mpr (Or.inl ⟨h1, hh⟩) with x | ⟨x, _⟩` into its components or cases. Conclude with `x`.

Conclude with `absurd x (by simp)`. Establish `hcJ : J.card = colH (mu ⟨j + 1, by omega⟩) c`. Rewrite `hcard` using `[Finset.card_erase_of_mem hm]`. Use `Finset.card_pos.mpr ⟨m, hm⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hsub : colH (mu ⟨j, by omega⟩) c < r → ∀ a ∈ J, a.val < r`. Introduce `hlt a ha`. Distinguish the cases in `ham : a = m`. Substitute `ham; by_contra hh; have := hmr.mp (by omega); omega` using the available equality. Conclude with `hB (by omega) a (Finset.mem_erase.mpr ⟨ham, ha⟩)`.

Use `⟨fun _ => ⟨hcJ, fun hr a ha => ?_, fun hr => hsub (by omega)⟩, fun hc' => absurd h2 hc'⟩` and prove the remaining obligations. Distinguish the cases in `hr' : r ≤ colH (mu ⟨j, by omega⟩) c`. Conclude with `Finset.mem_of_mem_erase (hA hr' a ha)`. Establish `hs` using `hsub (by omega)`. Establish `: J = univ.filter fun a : Fin (r + K) => a.val < r`.

Use `Finset.eq_of_subset_of_card_le (fun a ha => by simpa using hs a ha) ?_` and prove the remaining obligations. Rewrite using `[plane_card]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this]`. Simplify using `using ha`.

Take `⟨hv, hN⟩` from `H.rise j h h1`. Take `⟨m, hm, hn, hK⟩` from `contrR_ne _ _ _ hJ`. Conclude with `⟨fun hc' => absurd hc' h2, fun _ a ha => (ih' _ hK).2 h2 a (Finset.mem_insert_of_mem ha)⟩`. Take `⟨hv, hP⟩` from `H.fall j h h3`. Take `⟨m, hm, hn, hK⟩` from `contrR_ne _ _ _ hJ`.

Establish `hc` using `nomL_ne LL mu c _ m hn`. Take `⟨hcard, hA, hB⟩` from `(ih' _ hK).1 h4`. Establish `hmr : m.val < r ↔ colH (mu ⟨j, by omega⟩) c ≤ r`. Rewrite `hc` using `[hci]`. Unfold `condUS at hc`.

Simplify using `only [hv, true_and] at hc`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `intro hh; rcases hc.mp (Or.inr hh) with ⟨x, _⟩ | ⟨_, x⟩ <;> omega`. Introduce `hh`. Break down `hc.mpr (Or.inr ⟨h3, hh⟩) with ⟨x, _⟩ | x` into its components or cases.

Conclude with `absurd x (by simp)`. Conclude with `x`. Establish `hcJ : J.card = colH (mu ⟨j + 1, by omega⟩) c`. Rewrite `hcard` using `[Finset.card_insert_of_notMem hm]`. Use linear arithmetic over natural numbers and integers.

Establish `hsup : r < colH (mu ⟨j, by omega⟩) c → ∀ a : Fin (r + K), a.val < r → a ∈ J`. Introduce `hlt a ha`. Use `hA (by omega) a ha` as an intermediate fact. Break down `Finset.mem_insert.mp this with e | e` into its components or cases. Substitute `e` using the available equality.

Use `hmr.mp ha` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `e`. Use `⟨fun _ => ⟨hcJ, fun hr => hsup (by omega), fun hr a ha => ?_⟩, fun hc' => absurd h4 hc'⟩` and prove the remaining obligations. Distinguish the cases in `hr' : colH (mu ⟨j, by omega⟩) c ≤ r`.

Conclude with `hB hr' a (Finset.mem_insert_of_mem ha)`. Establish `hs` using `hsup (by omega)`. Establish `: (univ.filter fun a : Fin (r + K) => a.val < r) = J`. Use `Finset.eq_of_subset_of_card_le (fun a ha => hs a (by simpa using ha)) ?_` and prove the remaining obligations. Rewrite using `[plane_card]`.

Use linear arithmetic over natural numbers and integers. Rewrite `ha` using `[← this]`. Simplify using `using ha`. Take `⟨hv, hP⟩` from `H.fall j h h3`. Take `⟨m, hm, hn, hK⟩` from `wedgeR_ne _ _ _ hJ`.

Establish `hc` using `nomL_ne LL mu c _ m hn`. Establish `hd` using `H.dual h4 j (by omega)`. Use `⟨fun hc' => absurd hc' h4, fun _ a ha => ?_⟩` and prove the remaining obligations. Distinguish the cases in `ham : a = m`. Substitute `ham` using the available equality.

Assume the negation of the conclusion as `hh`. Rewrite `hc` using `[hci]`. Unfold `condUS at hc`. Apply the tactic sequence `rcases hc.mp (Or.inr ⟨hv, by omega⟩) with ⟨x, _⟩ | ⟨_, x⟩ <;> omega`. Conclude with `(ih' _ hK).2 h4 a (Finset.mem_erase.mpr ⟨ham, ha⟩)`.

Establish `e : colH (mu ⟨j + 1, by omega⟩) c = colH (mu ⟨j, by omega⟩) c` using `by omega`. Rewrite using `[e]`. Conclude with `ih' J hJ`.
-/
lemma SgW_supp {R : Type} [CommRing R] (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ)
    (H : ColOK LL mu c) (j : ℕ) (hj : j ≤ N) :
    ∀ J, SgW R LL mu c j J ≠ 0 →
      (1 ≤ c → J.card = colH (mu ⟨j, by omega⟩) c ∧
        (r ≤ colH (mu ⟨j, by omega⟩) c → ∀ a : Fin (r + K), a.val < r → a ∈ J) ∧
        (colH (mu ⟨j, by omega⟩) c ≤ r → ∀ a ∈ J, a.val < r)) ∧
      (¬ 1 ≤ c → ∀ a ∈ J, r ≤ a.val) := by
  classical
  induction j with
  | zero =>
    intro J hJ
    have : J = ∅ := by
      by_contra hne; exact hJ (by simp only [SgW]; unfold extOne; rw [if_neg hne])
    subst this
    refine ⟨fun hc => ⟨by rw [H.start hc]; simp, fun hr a ha => ?_, by simp⟩, by simp⟩
    rw [H.start hc] at hr; omega
  | succ j ih =>
    intro J hJ
    have h : j < N := hj
    have ih' := ih (by omega)
    simp only [SgW, dif_pos h] at hJ
    unfold colStep at hJ
    have hci := costly_iff mu c j h
    split_ifs at hJ with h1 h2 h3 h4
    ·
      obtain ⟨hv, hN⟩ := H.rise j h h1
      obtain ⟨m, hm, hn, hK⟩ := wedgeR_ne _ _ _ hJ
      have hc := nomL_ne LL mu c _ m hn
      obtain ⟨hcard, hA, hB⟩ := (ih' _ hK).1 h2
      have hmr : r ≤ m.val ↔ r ≤ colH (mu ⟨j, by omega⟩) c := by
        rw [hci] at hc; unfold condUS at hc; simp only [hv, true_and] at hc
        constructor
        · intro hh; rcases hc.mp (Or.inl hh) with ⟨_, x⟩ | ⟨x, _⟩ <;> omega
        · intro hh; rcases hc.mpr (Or.inl ⟨h1, hh⟩) with x | ⟨x, _⟩
          · exact x
          · exact absurd x (by simp)
      have hcJ : J.card = colH (mu ⟨j + 1, by omega⟩) c := by
        rw [Finset.card_erase_of_mem hm] at hcard
        have := Finset.card_pos.mpr ⟨m, hm⟩; omega
      have hsub : colH (mu ⟨j, by omega⟩) c < r → ∀ a ∈ J, a.val < r := by
        intro hlt a ha
        by_cases ham : a = m
        · subst ham; by_contra hh; have := hmr.mp (by omega); omega
        · exact hB (by omega) a (Finset.mem_erase.mpr ⟨ham, ha⟩)
      refine ⟨fun _ => ⟨hcJ, fun hr a ha => ?_, fun hr => hsub (by omega)⟩, fun hc' => absurd h2 hc'⟩
      by_cases hr' : r ≤ colH (mu ⟨j, by omega⟩) c
      · exact Finset.mem_of_mem_erase (hA hr' a ha)
      · have hs := hsub (by omega)
        have : J = univ.filter fun a : Fin (r + K) => a.val < r := by
          refine Finset.eq_of_subset_of_card_le (fun a ha => by simpa using hs a ha) ?_
          rw [plane_card]; omega
        rw [this]; simpa using ha
    ·
      obtain ⟨hv, hN⟩ := H.rise j h h1
      obtain ⟨m, hm, hn, hK⟩ := contrR_ne _ _ _ hJ
      exact ⟨fun hc' => absurd hc' h2, fun _ a ha => (ih' _ hK).2 h2 a (Finset.mem_insert_of_mem ha)⟩
    ·
      obtain ⟨hv, hP⟩ := H.fall j h h3
      obtain ⟨m, hm, hn, hK⟩ := contrR_ne _ _ _ hJ
      have hc := nomL_ne LL mu c _ m hn
      obtain ⟨hcard, hA, hB⟩ := (ih' _ hK).1 h4
      have hmr : m.val < r ↔ colH (mu ⟨j, by omega⟩) c ≤ r := by
        rw [hci] at hc; unfold condUS at hc; simp only [hv, true_and] at hc
        constructor
        · intro hh; rcases hc.mp (Or.inr hh) with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
        · intro hh; rcases hc.mpr (Or.inr ⟨h3, hh⟩) with ⟨x, _⟩ | x
          · exact absurd x (by simp)
          · exact x
      have hcJ : J.card = colH (mu ⟨j + 1, by omega⟩) c := by
        rw [Finset.card_insert_of_notMem hm] at hcard; omega
      have hsup : r < colH (mu ⟨j, by omega⟩) c → ∀ a : Fin (r + K), a.val < r → a ∈ J := by
        intro hlt a ha
        have := hA (by omega) a ha
        rcases Finset.mem_insert.mp this with e | e
        · subst e; have := hmr.mp ha; omega
        · exact e
      refine ⟨fun _ => ⟨hcJ, fun hr => hsup (by omega), fun hr a ha => ?_⟩, fun hc' => absurd h4 hc'⟩
      by_cases hr' : colH (mu ⟨j, by omega⟩) c ≤ r
      · exact hB hr' a (Finset.mem_insert_of_mem ha)
      · have hs := hsup (by omega)
        have : (univ.filter fun a : Fin (r + K) => a.val < r) = J := by
          refine Finset.eq_of_subset_of_card_le (fun a ha => hs a (by simpa using ha)) ?_
          rw [plane_card]; omega
        rw [← this] at ha; simpa using ha
    ·
      obtain ⟨hv, hP⟩ := H.fall j h h3
      obtain ⟨m, hm, hn, hK⟩ := wedgeR_ne _ _ _ hJ
      have hc := nomL_ne LL mu c _ m hn
      have hd := H.dual h4 j (by omega)
      refine ⟨fun hc' => absurd hc' h4, fun _ a ha => ?_⟩
      by_cases ham : a = m
      · subst ham
        by_contra hh
        rw [hci] at hc; unfold condUS at hc
        rcases hc.mp (Or.inr ⟨hv, by omega⟩) with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
      · exact (ih' _ hK).2 h4 a (Finset.mem_erase.mpr ⟨ham, ha⟩)
    ·
      have e : colH (mu ⟨j + 1, by omega⟩) c = colH (mu ⟨j, by omega⟩) c := by omega
      rw [e]; exact ih' J hJ

/- English proof (translation)
Introduce `j h hc m hm J`. Rewrite `hc` using `[costly_iff]`. Unfold `condUS at hm`. Use `⟨fun hw hmJ => ?_, fun hw hmJ => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Establish `hs` using `SgW_supp LL mu c H j (by omega) _ hne`. Break down `hw with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Take `⟨hv, _⟩` from `H.rise j h h1`. Establish `hmr : m.val < r` using `by by_contra hh; exact hm (Or.inl ⟨hv, by omega⟩)`. Apply the tactic sequence `have hr : r ≤ colH (mu ⟨j, by omega⟩) c := by rcases hc with ⟨_, x⟩ | ⟨x, _⟩ <;> omega`.

Conclude with `(Finset.notMem_erase m J) ((hs.1 h2).2.1 hr m hmr)`. Use `H.dual h2 j (by omega)` as an intermediate fact. Apply the tactic sequence `rcases hc with ⟨x, _⟩ | ⟨_, x⟩ <;> omega`. Assume the negation of the conclusion as `hne`. Establish `hs` using `SgW_supp LL mu c H j (by omega) _ hne`.

Break down `hw with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Take `⟨hv, _⟩` from `H.rise j h h1`. Establish `hmr : m.val < r` using `by by_contra hh; exact hm (Or.inl ⟨hv, by omega⟩)`. Use `hs.2 h2 m (Finset.mem_insert_self m J)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Take `⟨hv, _⟩` from `H.fall j h h1`. Establish `hmr : ¬ m.val < r` using `fun hh => hm (Or.inr ⟨hv, hh⟩)`. Apply the tactic sequence `have hr : colH (mu ⟨j, by omega⟩) c ≤ r := by rcases hc with ⟨x, _⟩ | ⟨_, x⟩ <;> omega`. Conclude with `hmr ((hs.1 h2).2.2 hr m (Finset.mem_insert_self m J))`.
-/
lemma SgVanish_of (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ)
    (H : ColOK LL mu c) : SgVanish LL mu c := by
  intro j h hc m hm J
  rw [costly_iff] at hc
  unfold condUS at hm
  refine ⟨fun hw hmJ => ?_, fun hw hmJ => ?_⟩
  · by_contra hne
    have hs := SgW_supp LL mu c H j (by omega) _ hne
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨hv, _⟩ := H.rise j h h1
      have hmr : m.val < r := by by_contra hh; exact hm (Or.inl ⟨hv, by omega⟩)
      have hr : r ≤ colH (mu ⟨j, by omega⟩) c := by rcases hc with ⟨_, x⟩ | ⟨x, _⟩ <;> omega
      exact (Finset.notMem_erase m J) ((hs.1 h2).2.1 hr m hmr)
    · have := H.dual h2 j (by omega)
      rcases hc with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
  · by_contra hne
    have hs := SgW_supp LL mu c H j (by omega) _ hne
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨hv, _⟩ := H.rise j h h1
      have hmr : m.val < r := by by_contra hh; exact hm (Or.inl ⟨hv, by omega⟩)
      have := hs.2 h2 m (Finset.mem_insert_self m J); omega
    · obtain ⟨hv, _⟩ := H.fall j h h1
      have hmr : ¬ m.val < r := fun hh => hm (Or.inr ⟨hv, hh⟩)
      have hr : colH (mu ⟨j, by omega⟩) c ≤ r := by rcases hc with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
      exact hmr ((hs.1 h2).2.2 hr m (Finset.mem_insert_self m J))

end Col

end Formalism.MainNotions.LemmaBAlt
