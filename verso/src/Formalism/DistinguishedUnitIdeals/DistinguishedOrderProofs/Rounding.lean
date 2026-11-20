import Mathlib
import Formalism.DistinguishedUnitIdeals.UnivPart

namespace Formalism.ExponentWindows

section Rounding

variable {K D : Type} [Field K] [AddCommGroup D] [Module K D]

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k : ℕ, c = a + k` from `⟨(c - a).toNat, by omega⟩`. Use `clear hac`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Establish `e1` using `ih (fun u h1 h2 => h u h1 (by omega))`. Establish `e2` using `h (a + k) (by omega) (by omega)`. Rewrite using `[e1, e2]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma filt_eq_of_no_jump (Fil : ℤ → Submodule K D) (a c : ℤ) (hac : a ≤ c)
    (h : ∀ u, a ≤ u → u < c → Fil u = Fil (u+1)) : Fil a = Fil c := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, c = a + k := ⟨(c - a).toNat, by omega⟩
  clear hac
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 := ih (fun u h1 h2 => h u h1 (by omega))
    have e2 := h (a + k) (by omega) (by omega)
    rw [e1, e2]
    congr 1
    push_cast
    ring

/- English proof (translation)
Introduce `u hu`. Break down `le_or_gt u lo with hul | hul` into its components or cases. Conclude with `top_unique (by rw [← hlo]; exact hA hul)`. Rewrite using `[← filt_eq_of_no_jump Fil lo u hul.le (fun v _ h2 => h v (by omega)), hlo]`.
-/
lemma filt_eq_top_of_no_jump_below (Fil : ℤ → Submodule K D) (hA : Antitone Fil) (lo : ℤ) (hlo : Fil lo = ⊤) (a : ℤ)
    (h : ∀ u, u < a → Fil u = Fil (u+1)) : ∀ u, u ≤ a → Fil u = ⊤ := by
  intro u hu
  rcases le_or_gt u lo with hul | hul
  · exact top_unique (by rw [← hlo]; exact hA hul)
  · rw [← filt_eq_of_no_jump Fil lo u hul.le (fun v _ h2 => h v (by omega)), hlo]

/- English proof (translation)
Introduce `u hu`. Break down `le_or_gt hi u with hul | hul` into its components or cases. Conclude with `le_bot_iff.mp (by rw [← hhi]; exact hA hul)`. Rewrite using `[filt_eq_of_no_jump Fil u hi hul.le (fun v h1 _ => h v (by omega)), hhi]`.
-/
lemma filt_eq_bot_of_no_jump_above (Fil : ℤ → Submodule K D) (hA : Antitone Fil) (hi : ℤ) (hhi : Fil hi = ⊥) (a : ℤ)
    (h : ∀ u, a ≤ u → Fil u = Fil (u+1)) : ∀ u, a ≤ u → Fil u = ⊥ := by
  intro u hu
  rcases le_or_gt hi u with hul | hul
  · exact le_bot_iff.mp (by rw [← hhi]; exact hA hul)
  · rw [filt_eq_of_no_jump Fil u hi hul.le (fun v h1 _ => h v (by omega)), hhi]

/- English proof (translation)
Introduce `u hu huc`. Conclude with `filt_eq_of_no_jump Fil u c huc (fun v h1 h2 => h v (by omega) h2)`.
-/
lemma filt_eq_of_no_jump_between (Fil : ℤ → Submodule K D) (a c : ℤ)
    (h : ∀ u, a ≤ u → u < c → Fil u = Fil (u+1)) : ∀ u, a ≤ u → u ≤ c → Fil u = Fil c := by
  intro u hu huc
  exact filt_eq_of_no_jump Fil u c huc (fun v h1 h2 => h v (by omega) h2)

/- English proof (translation)
Unfold `Rounding`. Introduce `K D _ _ _ Fil G S η g b hF hG hS hη hGg hSg hηg hgb`. Simplify using `only [IsFilt, NbThin, NbUp, NbDown] at hF ⊢`. Take `⟨hA, ⟨lo, hlo⟩, ⟨hi, hhi⟩⟩` from `hF`. Use `⟨fun hj i => ?_, fun hj i => ?_, fun hj i => ?_⟩` and prove the remaining obligations.

Establish `top : ∀ u, u ≤ -G → Fil u = ⊤` using `filt_eq_top_of_no_jump_below Fil hA lo hlo (-G) (fun u hu => by_contra fun hne => by have := hj u hne; omega)`. Establish `bot : ∀ u, G + 1 ≤ u → Fil u = ⊥` using `filt_eq_bot_of_no_jump_above Fil hA hi hhi (G + 1) (fun u hu => by_contra fun hne => by have := hj u hne; omega)`. Prove the components needed by the constructor for the conclusion. Use `split_ifs with h1`. Conclude with `bot_le`.

Rewrite using `[top (-i) (by omega)]`. Use `split_ifs with h1`. Rewrite using `[bot (-i) (by omega)]`. Conclude with `le_top`. Establish `top : ∀ u, u ≤ -η → Fil u = ⊤` using `filt_eq_top_of_no_jump_below Fil hA lo hlo (-η) (fun u hu => by_contra fun hne => by have := hj u hne; omega)`.

Establish `bot : ∀ u, b + S + 1 ≤ u → Fil u = ⊥` using `filt_eq_bot_of_no_jump_above Fil hA hi hhi (b + S + 1) (fun u hu => by_contra fun hne => by have := hj u hne; omega)`. Establish `mid : ∀ u, η + 1 ≤ u → u ≤ b → Fil u = Fil b` using `filt_eq_of_no_jump_between Fil (η + 1) b (fun u hu hu' => by_contra fun hne => by have := hj u hne; omega)`. Prove the components needed by the constructor for the conclusion. Use `split_ifs with h1 h2`. Conclude with `bot_le`.

Conclude with `hA (show -i ≤ b by omega)`. Rewrite using `[top (-i) (by omega)]`. Use `split_ifs with h1 h2`. Rewrite using `[bot (-i) (by omega)]`. Break down `le_or_gt b (-i) with h3 | h3` into its components or cases.

Conclude with `hA h3`. Rewrite using `[mid (-i) (by omega) (by omega)]`. Conclude with `le_top`. Establish `top : ∀ u, u ≤ -b - S → Fil u = ⊤` using `filt_eq_top_of_no_jump_below Fil hA lo hlo (-b - S) (fun u hu => by_contra fun hne => by have := hj u hne; omega)`. Establish `bot : ∀ u, η + 1 ≤ u → Fil u = ⊥` using `filt_eq_bot_of_no_jump_above Fil hA hi hhi (η + 1) (fun u hu => by_contra fun hne => by have := hj u hne; omega)`.

Establish `mid : ∀ u, -b + 1 ≤ u → u ≤ -η → Fil u = Fil (-η)` using `filt_eq_of_no_jump_between Fil (-b + 1) (-η) (fun u hu hu' => by_contra fun hne => by have := hj u hne; omega)`. Prove the components needed by the constructor for the conclusion. Use `split_ifs with h1 h2`. Conclude with `bot_le`. Conclude with `hA (show -i ≤ -η by omega)`.

Rewrite using `[top (-i) (by omega)]`. Use `split_ifs with h1 h2`. Rewrite using `[bot (-i) (by omega)]`. Break down `le_or_gt (-η) (-i) with h3 | h3` into its components or cases. Conclude with `hA h3`.

Rewrite using `[mid (-i) (by omega) (by omega)]`. Conclude with `le_top`.
-/
theorem filtration_rounding : Rounding := by
  unfold Rounding
  intro K D _ _ _ Fil G S η g b hF hG hS hη hGg hSg hηg hgb
  simp only [IsFilt, NbThin, NbUp, NbDown] at hF ⊢
  obtain ⟨hA, ⟨lo, hlo⟩, ⟨hi, hhi⟩⟩ := hF
  refine ⟨fun hj i => ?_, fun hj i => ?_, fun hj i => ?_⟩
  · have top : ∀ u, u ≤ -G → Fil u = ⊤ :=
      filt_eq_top_of_no_jump_below Fil hA lo hlo (-G)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    have bot : ∀ u, G + 1 ≤ u → Fil u = ⊥ :=
      filt_eq_bot_of_no_jump_above Fil hA hi hhi (G + 1)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    constructor
    · split_ifs with h1
      · exact bot_le
      · rw [top (-i) (by omega)]
    · split_ifs with h1
      · rw [bot (-i) (by omega)]
      · exact le_top
  · have top : ∀ u, u ≤ -η → Fil u = ⊤ :=
      filt_eq_top_of_no_jump_below Fil hA lo hlo (-η)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    have bot : ∀ u, b + S + 1 ≤ u → Fil u = ⊥ :=
      filt_eq_bot_of_no_jump_above Fil hA hi hhi (b + S + 1)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    have mid : ∀ u, η + 1 ≤ u → u ≤ b → Fil u = Fil b :=
      filt_eq_of_no_jump_between Fil (η + 1) b
        (fun u hu hu' => by_contra fun hne => by have := hj u hne; omega)
    constructor
    · split_ifs with h1 h2
      · exact bot_le
      · exact hA (show -i ≤ b by omega)
      · rw [top (-i) (by omega)]
    · split_ifs with h1 h2
      · rw [bot (-i) (by omega)]
      · rcases le_or_gt b (-i) with h3 | h3
        · exact hA h3
        · rw [mid (-i) (by omega) (by omega)]
      · exact le_top
  · have top : ∀ u, u ≤ -b - S → Fil u = ⊤ :=
      filt_eq_top_of_no_jump_below Fil hA lo hlo (-b - S)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    have bot : ∀ u, η + 1 ≤ u → Fil u = ⊥ :=
      filt_eq_bot_of_no_jump_above Fil hA hi hhi (η + 1)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    have mid : ∀ u, -b + 1 ≤ u → u ≤ -η → Fil u = Fil (-η) :=
      filt_eq_of_no_jump_between Fil (-b + 1) (-η)
        (fun u hu hu' => by_contra fun hne => by have := hj u hne; omega)
    constructor
    · split_ifs with h1 h2
      · exact bot_le
      · exact hA (show -i ≤ -η by omega)
      · rw [top (-i) (by omega)]
    · split_ifs with h1 h2
      · rw [bot (-i) (by omega)]
      · rcases le_or_gt (-η) (-i) with h3 | h3
        · exact hA h3
        · rw [mid (-i) (by omega) (by omega)]
      · exact le_top

end Rounding

end Formalism.ExponentWindows
