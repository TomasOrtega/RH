import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerAntidiagonalExact
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFourthCondition

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace C2x4

variable {m : ℕ}

def Cond (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) : Prop :=
  ∀ a b : Fin m, a < b → w b < w a →
    ((b.val = a.val + 1 ↔ (w a).val = (w b).val + 1) ∧ (b.val = a.val + 1 → d a = d b))

def IsCut (w : Equiv.Perm (Fin m)) (c : Fin m) : Prop := ∀ x y : Fin m, x ≤ c → c < y → w x < w y

/- English proof (translation)
Establish `key : ∀ n : ℕ, ∀ x y : Fin m, x ≤ a → a < y → w y < w x → (w x).val - (w y).val = n → False`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `x y hx hy hxy hn`.

Establish `hxy' : x < y` using `lt_of_le_of_lt hx hy`. Distinguish the cases in `h1 : (w x).val = (w y).val + 1`. Use `((hC x y hxy' hxy).1).mpr h1` as an intermediate fact. Establish `hxa : x = a`. Apply `Fin.ext` to reduce the goal to its premises.

Rewrite `hx` using `[Fin.le_def]`. Rewrite `hy` using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Establish `hya : y = ⟨a.val + 1, ha⟩`. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `only`. Rewrite `hx` using `[Fin.le_def]`. Rewrite `hy` using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Rewrite `hxy` using `[hxa, hya]`.

Conclude with `absurd hasc (not_lt.mpr (le_of_lt hxy))`. Establish `hlt : (w y).val + 1 < (w x).val`. Rewrite `hxy` using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Use `set v : Fin m := ⟨(w y).val + 1, by omega⟩ with hv`.

Use `set z := w.symm v with hz`. Establish `hwz : w z = v` using `by rw [hz, Equiv.apply_symm_apply]`. Distinguish the cases in `hza : z ≤ a`. Apply `ih ((w z).val - (w y).val) (by rw [hwz]; simp only [hv]; omega) z y hza hy (by rw [hwz, Fin.lt_def]; simp only [hv]; omega) rfl` to reduce the goal to its premises. Use `push_neg at hza`.

Apply `ih ((w x).val - (w z).val) (by rw [hwz]; simp only [hv]; omega) x z hx hza (by rw [hwz, Fin.lt_def]; simp only [hv]; omega) rfl` to reduce the goal to its premises. Introduce `x y hx hy`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hne : w y ≠ w x` using `fun e => (ne_of_lt (lt_of_le_of_lt hx hy)) (w.injective e).symm`.

Conclude with `key _ x y hx hy (lt_of_le_of_ne hcon hne) rfl`.
-/
lemma cut_of_ascent (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hC : Cond w d) (a : Fin m)
    (ha : a.val + 1 < m) (hasc : w a < w ⟨a.val + 1, ha⟩) : IsCut w a := by
  have key : ∀ n : ℕ, ∀ x y : Fin m, x ≤ a → a < y → w y < w x → (w x).val - (w y).val = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x y hx hy hxy hn
      have hxy' : x < y := lt_of_le_of_lt hx hy
      by_cases h1 : (w x).val = (w y).val + 1
      · have := ((hC x y hxy' hxy).1).mpr h1
        have hxa : x = a := by
          apply Fin.ext; rw [Fin.le_def] at hx; rw [Fin.lt_def] at hy; omega
        have hya : y = ⟨a.val + 1, ha⟩ := by
          apply Fin.ext; simp only; rw [Fin.le_def] at hx; rw [Fin.lt_def] at hy; omega
        rw [hxa, hya] at hxy
        exact absurd hasc (not_lt.mpr (le_of_lt hxy))
      · have hlt : (w y).val + 1 < (w x).val := by
          rw [Fin.lt_def] at hxy; omega
        set v : Fin m := ⟨(w y).val + 1, by omega⟩ with hv
        set z := w.symm v with hz
        have hwz : w z = v := by rw [hz, Equiv.apply_symm_apply]
        by_cases hza : z ≤ a
        · apply ih ((w z).val - (w y).val) (by rw [hwz]; simp only [hv]; omega) z y hza hy
            (by rw [hwz, Fin.lt_def]; simp only [hv]; omega) rfl
        · push_neg at hza
          apply ih ((w x).val - (w z).val) (by rw [hwz]; simp only [hv]; omega) x z hx hza
            (by rw [hwz, Fin.lt_def]; simp only [hv]; omega) rfl
  intro x y hx hy
  by_contra hcon
  push_neg at hcon
  have hne : w y ≠ w x := fun e => (ne_of_lt (lt_of_le_of_lt hx hy)) (w.injective e).symm
  exact key _ x y hx hy (lt_of_le_of_ne hcon hne) rfl

/- English proof (translation)
Use `set S := Finset.univ.filter (fun x : Fin m => x ≤ c) with hS`. Use `set T := Finset.univ.filter (fun x : Fin m => w x ≤ c) with hT`. Establish `hTS : T = S.map w.symm.toEmbedding`. Use extensionality with `x`. Simplify using `only [hS, hT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Equiv.coe_toEmbedding]`.

Prove the components needed by the constructor for the conclusion. Introduce `h; exact ⟨w x, h, by simp⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `using hy`. Establish `hcard : T.card = S.card` using `by rw [hTS, Finset.card_map]`.

Establish `hsub : S ⊆ T`. Introduce `x hx`. Assume the negation of the conclusion as `hxT`. Establish `hTnot : ¬ T ⊆ S`. Introduce `hTS'`.

Use `Finset.eq_of_subset_of_card_le hTS' (le_of_eq hcard.symm)` as an intermediate fact. Rewrite `hxT` using `[this]`. Conclude with `hxT hx`. Take `⟨y, hyT, hyS⟩` from `Finset.not_subset.mp hTnot`. Simplify using `only [hS, hT, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hx hxT hyT hyS`.

Use `hc x y hx hyS` as an intermediate fact. Conclude with `absurd (lt_of_le_of_lt hyT hxT) (not_lt.mpr (le_of_lt this))`. Establish `hEq : S = T` using `Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard)`. Use `congrArg (fun F => x ∈ F) hEq` as an intermediate fact. Simplify `this` using `[hS, hT]`.
-/
lemma cut_preserves (w : Equiv.Perm (Fin m)) (c : Fin m) (hc : IsCut w c) (x : Fin m) :
    x ≤ c ↔ w x ≤ c := by
  set S := Finset.univ.filter (fun x : Fin m => x ≤ c) with hS
  set T := Finset.univ.filter (fun x : Fin m => w x ≤ c) with hT
  have hTS : T = S.map w.symm.toEmbedding := by
    ext x; simp only [hS, hT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.coe_toEmbedding]
    constructor
    · intro h; exact ⟨w x, h, by simp⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  have hcard : T.card = S.card := by rw [hTS, Finset.card_map]
  have hsub : S ⊆ T := by
    intro x hx
    by_contra hxT
    have hTnot : ¬ T ⊆ S := by
      intro hTS'
      have := Finset.eq_of_subset_of_card_le hTS' (le_of_eq hcard.symm)
      rw [this] at hxT; exact hxT hx
    obtain ⟨y, hyT, hyS⟩ := Finset.not_subset.mp hTnot
    simp only [hS, hT, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hx hxT hyT hyS
    have := hc x y hx hyS
    exact absurd (lt_of_le_of_lt hyT hxT) (not_lt.mpr (le_of_lt this))
  have hEq : S = T := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard)
  have := congrArg (fun F => x ∈ F) hEq
  simpa [hS, hT] using this

open Classical in

noncomputable def blk (w : Equiv.Perm (Fin m)) (a : Fin m) : ℕ :=
  (Finset.univ.filter (fun c : Fin m => c < a ∧ IsCut w c)).card

/- English proof (translation)
Introduce `a b hab`. Unfold `blk`. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `c hc`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢`.

Conclude with `⟨lt_of_lt_of_le hc.1 hab, hc.2⟩`.
-/
lemma blk_mono (w : Equiv.Perm (Fin m)) : Monotone (blk w) := by
  intro a b hab
  unfold blk
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  exact ⟨lt_of_lt_of_le hc.1 hab, hc.2⟩

/- English proof (translation)
Unfold `blk`. Use `congr 1`. Use extensionality with `c`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Use `⟨?_, h2⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use `(cut_preserves w c h2 a).mp h` as an intermediate fact.

Conclude with `absurd h1 (not_lt.mpr this)`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨?_, h2⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Use `(cut_preserves w c h2 a).mpr h` as an intermediate fact. Conclude with `absurd h1 (not_lt.mpr this)`.
-/
lemma blk_w (w : Equiv.Perm (Fin m)) (a : Fin m) : blk w (w a) = blk w a := by
  unfold blk
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra h; push_neg at h
    have := (cut_preserves w c h2 a).mp h
    exact absurd h1 (not_lt.mpr this)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra h; push_neg at h
    have := (cut_preserves w c h2 a).mpr h
    exact absurd h1 (not_lt.mpr this)

/- English proof (translation)
Introduce `hcut`. Establish `hss : Finset.univ.filter (fun c : Fin m => c < a ∧ IsCut w c) ⊂ Finset.univ.filter (fun c : Fin m => c < b ∧ IsCut w c)`. Rewrite using `[Finset.ssubset_iff_of_subset]`. Use `⟨j, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`.

Conclude with `⟨hj2, hcut⟩`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]`. Introduce `h`. Conclude with `absurd h (not_lt.mpr hj1)`. Introduce `c hc`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢`. Conclude with `⟨lt_trans hc.1 (lt_of_le_of_lt hj1 hj2), hc.2⟩`. Use `Finset.card_lt_card hss` as an intermediate fact. Unfold `blk at hab`. Rewrite `this` using `[hab]`.

Conclude with `lt_irrefl _ this`.
-/
lemma no_cut_between (w : Equiv.Perm (Fin m)) (a b j : Fin m) (hab : blk w a = blk w b)
    (hj1 : a ≤ j) (hj2 : j < b) : ¬ IsCut w j := by
  intro hcut
  classical
  have hss : Finset.univ.filter (fun c : Fin m => c < a ∧ IsCut w c) ⊂
      Finset.univ.filter (fun c : Fin m => c < b ∧ IsCut w c) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨j, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hj2, hcut⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro h; exact absurd h (not_lt.mpr hj1)
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact ⟨lt_trans hc.1 (lt_of_le_of_lt hj1 hj2), hc.2⟩
  have := Finset.card_lt_card hss
  unfold blk at hab
  rw [hab] at this
  exact lt_irrefl _ this

/- English proof (translation)
Establish `h : j.val + 1 < m` using `lt_of_le_of_lt hj2 b.isLt`. Use `⟨h, ?_⟩` and prove the remaining obligations. Establish `hne : w ⟨j.val + 1, h⟩ ≠ w j` using `fun e => by`. Use `congrArg Fin.val (w.injective e)` as an intermediate fact. Simplify using `at this`.

Break down `lt_or_gt_of_ne hne with h1 | h1` into its components or cases. Conclude with `h1`. It suffices to derive a contradiction. Conclude with `no_cut_between w a b j hab hj1 (by rw [Fin.lt_def]; omega) (cut_of_ascent w d hC j h h1)`.
-/
lemma desc_in_block (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hC : Cond w d) (a b : Fin m)
    (hab : blk w a = blk w b) (j : Fin m) (hj1 : a ≤ j) (hj2 : j.val + 1 ≤ b.val) :
    ∃ h : j.val + 1 < m, w ⟨j.val + 1, h⟩ < w j := by
  have h : j.val + 1 < m := lt_of_le_of_lt hj2 b.isLt
  refine ⟨h, ?_⟩
  have hne : w ⟨j.val + 1, h⟩ ≠ w j := fun e => by
    have := congrArg Fin.val (w.injective e); simp at this
  rcases lt_or_gt_of_ne hne with h1 | h1
  · exact h1
  · exfalso
    exact no_cut_between w a b j hab hj1 (by rw [Fin.lt_def]; omega) (cut_of_ascent w d hC j h h1)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `b hb hab`. Take `⟨h, hd⟩` from `desc_in_block w d hC a b hab a le_rfl (by omega)`.

Establish `hbe : b = ⟨a.val + 1, h⟩` using `Fin.ext (by simp only; omega)`. Substitute `hbe` using the available equality. Use `⟨hd, ?_⟩` and prove the remaining obligations. Conclude with `(hC a _ (by rw [Fin.lt_def]; simp) hd).2 rfl`. Consider the case `succ n ih`.

Introduce `b hb hab`. Use `set j : Fin m := ⟨a.val + n + 1, by omega⟩ with hj`. Establish `hmono` using `blk_mono w`. Establish `haj : blk w a = blk w j`. Apply `le_antisymm (hmono (by rw [Fin.le_def]; simp only [hj]; omega))` to reduce the goal to its premises.

Rewrite using `[hab]; exact hmono (by rw [Fin.le_def]; simp only [hj]; omega)`. Take `⟨h1, h2⟩` from `ih j rfl haj`. Take `⟨h, hd⟩` from `desc_in_block w d hC a b hab j (by rw [Fin.le_def]; simp only [hj]; omega) (by simp only [hj]; omega)`. Establish `hbe : b = ⟨j.val + 1, h⟩` using `Fin.ext (by simp only [hj]; omega)`. Rewrite `hab`, the goal using `[hbe]`.

Use `⟨lt_trans hd h1, ?_⟩` and prove the remaining obligations. Rewrite using `[h2]`. Conclude with `(hC j _ (by rw [Fin.lt_def]; simp) hd).2 rfl`.
-/
lemma chain (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hC : Cond w d) (a : Fin m) :
    ∀ n : ℕ, ∀ b : Fin m, b.val = a.val + n + 1 → blk w a = blk w b → w b < w a ∧ d a = d b := by
  intro n
  induction n with
  | zero =>
    intro b hb hab
    obtain ⟨h, hd⟩ := desc_in_block w d hC a b hab a le_rfl (by omega)
    have hbe : b = ⟨a.val + 1, h⟩ := Fin.ext (by simp only; omega)
    subst hbe
    refine ⟨hd, ?_⟩
    exact (hC a _ (by rw [Fin.lt_def]; simp) hd).2 rfl
  | succ n ih =>
    intro b hb hab
    set j : Fin m := ⟨a.val + n + 1, by omega⟩ with hj
    have hmono := blk_mono w
    have haj : blk w a = blk w j := by
      apply le_antisymm (hmono (by rw [Fin.le_def]; simp only [hj]; omega))
      rw [hab]; exact hmono (by rw [Fin.le_def]; simp only [hj]; omega)
    obtain ⟨h1, h2⟩ := ih j rfl haj
    obtain ⟨h, hd⟩ := desc_in_block w d hC a b hab j (by rw [Fin.le_def]; simp only [hj]; omega)
      (by simp only [hj]; omega)
    have hbe : b = ⟨j.val + 1, h⟩ := Fin.ext (by simp only [hj]; omega)
    rw [hbe] at hab ⊢
    refine ⟨lt_trans hd h1, ?_⟩
    rw [h2]
    exact (hC j _ (by rw [Fin.lt_def]; simp) hd).2 rfl

end C2x4

open C2x4

/- English proof (translation)
Introduce `m w d`. Prove the components needed by the constructor for the conclusion. Introduce `hC`. Use `⟨blk w, blk_mono w, blk_w w, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab hlt`.

Conclude with `(chain w d hC a (b.val - a.val - 1) b (by rw [Fin.lt_def] at hlt; omega) hab).1`. Introduce `a b hab`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Conclude with `(chain w d hC a (b.val - a.val - 1) b (by rw [Fin.lt_def] at h; omega) hab).2`. Both sides reduce to the same expression.

Conclude with `((chain w d hC b (a.val - b.val - 1) a (by rw [Fin.lt_def] at h; omega) hab.symm).2).symm`. Introduce and unpack `⟨bl, hmono, hw, hrev, hd⟩ a b hab hwab`. Establish `hsame : bl a = bl b`. Apply `le_antisymm (hmono (le_of_lt hab))` to reduce the goal to its premises. Rewrite using `[← hw a, ← hw b]`.

Conclude with `hmono (le_of_lt hwab)`. Establish `hin : ∀ c : Fin m, a ≤ c → c ≤ b → bl c = bl a`. Introduce `c h1 h2`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[hsame]`.

Conclude with `hmono h2`. Conclude with `hmono h1`. Establish `hinv : ∀ c : Fin m, w b ≤ c → c ≤ w a → bl (w.symm c) = bl a`. Introduce `c h1 h2`. Establish `: bl c = bl a`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← hw a]`. Conclude with `hmono h2`. Rewrite using `[hsame, ← hw b]`. Conclude with `hmono h1`.

Rewrite using `[← hw (w.symm c), Equiv.apply_symm_apply, this]`. Use `⟨⟨fun h => ?_, fun h => ?_⟩, fun h => hd a b hsame⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hlt : (w b).val + 1 < (w a).val` using `by rw [Fin.lt_def] at hwab; omega`. Use `set c : Fin m := ⟨(w b).val + 1, by omega⟩ with hc`.

Establish `hcb : bl (w.symm c) = bl a` using `hinv c (by rw [Fin.le_def]; simp only [hc]; omega) (by rw [Fin.le_def]; simp only [hc]; omega)`. Establish `hwc : w (w.symm c) = c` using `Equiv.apply_symm_apply w c`. Establish `h1 : a < w.symm c`. Break down `lt_trichotomy (w.symm c) a with h' | h' | h'` into its components or cases. Use `hrev (w.symm c) a (hcb.trans rfl) h'` as an intermediate fact.

Rewrite `this` using `[hwc]`. Rewrite `this` using `[Fin.lt_def]`. Simplify using `only [hc] at this`. Use linear arithmetic over natural numbers and integers. Rewrite `hlt` using `[← h', hwc]`.

Simplify using `only [hc] at hlt`. Use linear arithmetic over natural numbers and integers. Conclude with `h'`. Establish `h2 : w.symm c < b`. Break down `lt_trichotomy (w.symm c) b with h' | h' | h'` into its components or cases.

Conclude with `h'`. Rewrite `hwc` using `[h', hc]`. Use `congrArg Fin.val hwc` as an intermediate fact. Simplify using `at this`. Use `hrev b (w.symm c) (hsame.symm.trans hcb.symm) h'` as an intermediate fact.

Rewrite `this` using `[hwc]`. Rewrite `this` using `[Fin.lt_def]`. Simplify using `only [hc] at this`. Use linear arithmetic over natural numbers and integers. Rewrite `h1`, `h2` using `[Fin.lt_def]`.

Use linear arithmetic over natural numbers and integers. Assume the negation of the conclusion as `hne`. Establish `hlt : a.val + 1 < b.val` using `by rw [Fin.lt_def] at hab; omega`. Use `set c : Fin m := ⟨a.val + 1, by omega⟩ with hc`. Establish `hca : bl c = bl a` using `hin c (by rw [Fin.le_def]; simp only [hc]; omega) (by rw [Fin.le_def]; simp only [hc]; omega)`.

Establish `e1` using `hrev a c hca.symm (by rw [Fin.lt_def]; simp only [hc]; omega)`. Establish `e2` using `hrev c b (hca.trans hsame) (by rw [Fin.lt_def]; simp only [hc]; omega)`. Rewrite `e1`, `e2` using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers.
-/
theorem relevant_criterion : C2.RelevantCrit := by
  intro m w d
  constructor
  · intro hC
    refine ⟨blk w, blk_mono w, blk_w w, ?_, ?_⟩
    · intro a b hab hlt
      exact (chain w d hC a (b.val - a.val - 1) b (by rw [Fin.lt_def] at hlt; omega) hab).1
    · intro a b hab
      rcases lt_trichotomy a b with h | rfl | h
      · exact (chain w d hC a (b.val - a.val - 1) b (by rw [Fin.lt_def] at h; omega) hab).2
      · rfl
      · exact ((chain w d hC b (a.val - b.val - 1) a (by rw [Fin.lt_def] at h; omega) hab.symm).2).symm
  · rintro ⟨bl, hmono, hw, hrev, hd⟩ a b hab hwab
    have hsame : bl a = bl b := by
      apply le_antisymm (hmono (le_of_lt hab))
      rw [← hw a, ← hw b]; exact hmono (le_of_lt hwab)

    have hin : ∀ c : Fin m, a ≤ c → c ≤ b → bl c = bl a := by
      intro c h1 h2
      apply le_antisymm
      · rw [hsame]; exact hmono h2
      · exact hmono h1
    have hinv : ∀ c : Fin m, w b ≤ c → c ≤ w a → bl (w.symm c) = bl a := by
      intro c h1 h2
      have : bl c = bl a := by
        apply le_antisymm
        · rw [← hw a]; exact hmono h2
        · rw [hsame, ← hw b]; exact hmono h1
      rw [← hw (w.symm c), Equiv.apply_symm_apply, this]
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => hd a b hsame⟩
    ·
      by_contra hne
      have hlt : (w b).val + 1 < (w a).val := by rw [Fin.lt_def] at hwab; omega
      set c : Fin m := ⟨(w b).val + 1, by omega⟩ with hc
      have hcb : bl (w.symm c) = bl a :=
        hinv c (by rw [Fin.le_def]; simp only [hc]; omega) (by rw [Fin.le_def]; simp only [hc]; omega)
      have hwc : w (w.symm c) = c := Equiv.apply_symm_apply w c

      have h1 : a < w.symm c := by
        rcases lt_trichotomy (w.symm c) a with h' | h' | h'
        · have := hrev (w.symm c) a (hcb.trans rfl) h'
          rw [hwc] at this; rw [Fin.lt_def] at this; simp only [hc] at this; omega
        · rw [← h', hwc] at hlt; simp only [hc] at hlt; omega
        · exact h'
      have h2 : w.symm c < b := by
        rcases lt_trichotomy (w.symm c) b with h' | h' | h'
        · exact h'
        · rw [h', hc] at hwc; have := congrArg Fin.val hwc; simp at this
        · have := hrev b (w.symm c) (hsame.symm.trans hcb.symm) h'
          rw [hwc] at this; rw [Fin.lt_def] at this; simp only [hc] at this; omega
      rw [Fin.lt_def] at h1 h2; omega
    ·
      by_contra hne
      have hlt : a.val + 1 < b.val := by rw [Fin.lt_def] at hab; omega
      set c : Fin m := ⟨a.val + 1, by omega⟩ with hc
      have hca : bl c = bl a := hin c (by rw [Fin.le_def]; simp only [hc]; omega)
        (by rw [Fin.le_def]; simp only [hc]; omega)
      have e1 := hrev a c hca.symm (by rw [Fin.lt_def]; simp only [hc]; omega)
      have e2 := hrev c b (hca.trans hsame) (by rw [Fin.lt_def]; simp only [hc]; omega)
      rw [Fin.lt_def] at e1 e2; omega

/- English proof (translation)
Unfold `C2.simpleLow`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun q _ => ?_)` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨q.val + 1, h⟩]`.

Simplify using the standard rewrite rules. Introduce `p _ hp`. Rewrite using `[if_neg]`. Introduce `e`. Conclude with `hp (Fin.ext e)`.

Simplify using the standard rewrite rules. Apply `(Finset.sum_eq_zero (fun p _ => ?_)).symm` to reduce the goal to its premises. Rewrite using `[if_neg]`. Introduce `e`. Use `p.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
lemma c2x4_simpleLow_double {m : ℕ} (l : Matrix (Fin m) (Fin m) ℂ) :
    C2.simpleLow l = ∑ p : Fin m, ∑ q : Fin m, if p.val = q.val + 1 then l p q else 0 := by
  unfold C2.simpleLow
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨q.val + 1, h⟩]
    · simp
    · intro p _ hp; rw [if_neg]; intro e; exact hp (Fin.ext e)
    · simp
  · apply (Finset.sum_eq_zero (fun p _ => ?_)).symm
    rw [if_neg]; intro e; have := p.isLt; omega

/- English proof (translation)
Unfold `C2.simpleUp`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨a.val + 1, h⟩]`. Simplify using the standard rewrite rules.

Introduce `p _ hp`. Rewrite using `[if_neg]`. Introduce `e`. Conclude with `hp (Fin.ext e)`. Simplify using the standard rewrite rules.

Apply `(Finset.sum_eq_zero (fun p _ => ?_)).symm` to reduce the goal to its premises. Rewrite using `[if_neg]`. Introduce `e`. Use `p.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma c2x4_simpleUp_double {m : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) :
    C2.simpleUp u = ∑ a : Fin m, ∑ b : Fin m, if b.val = a.val + 1 then u a b else 0 := by
  unfold C2.simpleUp
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val + 1, h⟩]
    · simp
    · intro p _ hp; rw [if_neg]; intro e; exact hp (Fin.ext e)
    · simp
  · apply (Finset.sum_eq_zero (fun p _ => ?_)).symm
    rw [if_neg]; intro e; have := p.isLt; omega

/- English proof (translation)
Take `⟨bv, hbv⟩` from `b`. Simplify using `only at hb`. Substitute `hb` using the available equality. Conclude with `C2x2.ut_inv_super hu a hbv`.
-/
lemma c2x4_ut_inv_super' {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) (a b : Fin m)
    (hb : b.val = a.val + 1) : u⁻¹ a b = -u a b := by
  obtain ⟨bv, hbv⟩ := b
  simp only at hb
  subst hb
  exact C2x2.ut_inv_super hu a hbv

/- English proof (translation)
Establish `hPu` using `C2x2.isUnit_det_monomialMatrix w d hd`. Establish `hinv : (C2.monoP w d)⁻¹ * l * C2.monoP w d = u'⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv _ (C2x2.ut_unit hu), Matrix.mul_one]`. Use `_ = (C2.monoP w d)⁻¹ * (l * C2.monoP w d * u') * u'⁻¹ := by simp only [Matrix.mul_assoc]`.

Use `_ = u'⁻¹ := by rw [he, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul]`. Establish `hent : ∀ a b : Fin m, l (w a) (w b) = d a * u'⁻¹ a b / d b`. Introduce `a b`. Use `congrFun (congrFun hinv a) b` as an intermediate fact. Rewrite `this` using `[C2x2.monomialMatrix_conj_apply w d hd]`.

Rewrite using `[← this]`. Clear denominators, using `[hd a, hd b]` for the nonvanishing conditions. Establish `hui` using `C2x2.ut_inv hu`. Rewrite using `[c2x4_simpleLow_double, c2x4_simpleUp_double]`. Rewrite using `[← Equiv.sum_comp w]`.

Repeatedly rewrite using `[← Equiv.sum_comp w (fun q => if (w _).val = q.val + 1 then l (w _) q else 0)]`. Rewrite using `[← Finset.sum_add_distrib]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[← Finset.sum_add_distrib]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Distinguish the cases in `h1 : b.val = a.val + 1`. Establish `hab : a < b` using `by rw [Fin.lt_def]; omega`. Establish `hsup` using `C2x2.ut_inv_super hu a (by omega)`.

Establish `hbe : b = ⟨a.val + 1, by omega⟩` using `Fin.ext h1`. Distinguish the cases in `h2 : (w a).val = (w b).val + 1`. Establish `hwab : w b < w a` using `by rw [Fin.lt_def]; omega`. Establish `hda` using `(hC a b hab hwab).2 h1`. Rewrite using `[if_pos h2, if_pos h1, hent, hda]`.

Establish `e : d b * u'⁻¹ a b / d b = u'⁻¹ a b` using `by field_simp [hd b]`. Rewrite using `[e, c2x4_ut_inv_super' hu a b h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h2, if_pos h1, zero_add]`. Establish `hwab : w a < w b`.

Break down `lt_or_gt_of_ne (fun e : w a = w b => (ne_of_lt hab) (w.injective e)) with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd ((hC a b hab h).1.mp h1) h2`. Establish `hz` using `hl.1 (w a) (w b) hwab`. Rewrite `hz` using `[hent]`.

Establish `: u'⁻¹ a b = 0`. Break down `mul_eq_zero.mp (div_eq_zero_iff.mp hz |>.resolve_right (hd b)) with h | h` into its components or cases. Conclude with `absurd h (hd a)`. Conclude with `h`. Rewrite `this` using `[c2x4_ut_inv_super' hu a b h1, neg_eq_zero]`.

Conclude with `this`. Rewrite using `[if_neg h1, add_zero]`. Distinguish the cases in `h2 : (w a).val = (w b).val + 1`. Rewrite using `[if_pos h2, hent]`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases.

Establish `hwab : w b < w a` using `by rw [Fin.lt_def]; omega`. Conclude with `absurd ((hC a b h hwab).1.mpr h2) h1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hui.1 a b h]`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h2]`.
-/
lemma c2x4_stab_sum_zero {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (hC : Cond w d) (l u' : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ C2.LTset m) (hu : u' ∈ C2.UTset m)
    (he : l * C2.monoP w d * u' = C2.monoP w d) : C2.simpleLow l + C2.simpleUp u' = 0 := by
  have hPu := C2x2.isUnit_det_monomialMatrix w d hd
  have hinv : (C2.monoP w d)⁻¹ * l * C2.monoP w d = u'⁻¹ := by
    calc (C2.monoP w d)⁻¹ * l * C2.monoP w d
        = (C2.monoP w d)⁻¹ * l * C2.monoP w d * (u' * u'⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ (C2x2.ut_unit hu), Matrix.mul_one]
      _ = (C2.monoP w d)⁻¹ * (l * C2.monoP w d * u') * u'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = u'⁻¹ := by rw [he, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul]
  have hent : ∀ a b : Fin m, l (w a) (w b) = d a * u'⁻¹ a b / d b := by
    intro a b
    have := congrFun (congrFun hinv a) b
    rw [C2x2.monomialMatrix_conj_apply w d hd] at this
    rw [← this]; field_simp [hd a, hd b]
  have hui := C2x2.ut_inv hu
  rw [c2x4_simpleLow_double, c2x4_simpleUp_double]
  rw [← Equiv.sum_comp w]
  simp_rw [← Equiv.sum_comp w (fun q => if (w _).val = q.val + 1 then l (w _) q else 0)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro b _
  by_cases h1 : b.val = a.val + 1
  · have hab : a < b := by rw [Fin.lt_def]; omega
    have hsup := C2x2.ut_inv_super hu a (by omega)
    have hbe : b = ⟨a.val + 1, by omega⟩ := Fin.ext h1
    by_cases h2 : (w a).val = (w b).val + 1
    · have hwab : w b < w a := by rw [Fin.lt_def]; omega
      have hda := (hC a b hab hwab).2 h1
      rw [if_pos h2, if_pos h1, hent, hda]
      have e : d b * u'⁻¹ a b / d b = u'⁻¹ a b := by field_simp [hd b]
      rw [e, c2x4_ut_inv_super' hu a b h1]; ring
    · rw [if_neg h2, if_pos h1, zero_add]
      have hwab : w a < w b := by
        rcases lt_or_gt_of_ne (fun e : w a = w b => (ne_of_lt hab) (w.injective e)) with h | h
        · exact h
        · exact absurd ((hC a b hab h).1.mp h1) h2
      have hz := hl.1 (w a) (w b) hwab
      rw [hent] at hz
      have : u'⁻¹ a b = 0 := by
        rcases mul_eq_zero.mp (div_eq_zero_iff.mp hz |>.resolve_right (hd b)) with h | h
        · exact absurd h (hd a)
        · exact h
      rw [c2x4_ut_inv_super' hu a b h1, neg_eq_zero] at this
      exact this
  · rw [if_neg h1, add_zero]
    by_cases h2 : (w a).val = (w b).val + 1
    · rw [if_pos h2, hent]
      rcases lt_trichotomy a b with h | rfl | h
      · have hwab : w b < w a := by rw [Fin.lt_def]; omega
        exact absurd ((hC a b h hwab).1.mpr h2) h1
      · omega
      · rw [hui.1 a b h]; simp
    · rw [if_neg h2]

/- English proof (translation)
Introduce `m w d c hd hc`. Rewrite using `[← relevant_criterion m w d]`. Prove the components needed by the constructor for the conclusion. Introduce `hall a b hab hwab`. Rewrite using `[← relevant_trivial_case m w d c hd hc a b hab hwab]`.

Introduce `x`. Take `⟨h1, h2, h3, h4⟩` from `relevant_pair_criterion m w d hd a b hab hwab x`. Rewrite using `[← h4]`. Conclude with `hall _ h1 _ h2 h3`. Introduce `hC l hl u' hu he`.

Rewrite using `[c2x4_stab_sum_zero w d hd hC l u' hl hu he]`. Simplify using `[C2.psiC]`.
-/
theorem relevant_monotone : C2.RelevantMono := by
  intro m w d c hd hc
  rw [← relevant_criterion m w d]
  constructor
  · intro hall a b hab hwab
    rw [← relevant_trivial_case m w d c hd hc a b hab hwab]
    intro x
    obtain ⟨h1, h2, h3, h4⟩ := relevant_pair_criterion m w d hd a b hab hwab x
    rw [← h4]
    exact hall _ h1 _ h2 h3
  · intro hC l hl u' hu he
    rw [c2x4_stab_sum_zero w d hd hC l u' hl hu he]
    simp [C2.psiC]

/- English proof (translation)
Introduce `_ _ _ _` and use `relevant_monotone`.
-/
theorem relevant_monotone_of_parts_alt : C2.RelevantMonoOfParts := fun _ _ _ _ => relevant_monotone

end Formalism.FourierDecayAlt.P
